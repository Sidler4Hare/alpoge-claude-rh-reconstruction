"""Verify the manuscript's source citations and their saved root paths with Python 3."""
import argparse
import csv
import gzip
import hashlib
from pathlib import Path
import re
import tarfile
from collections import Counter

PAPER = Path(__file__).resolve().parents[1]
CITATION = re.compile(r"\\src\{(src/[^{}\n]+\.lean)\}\{(\d+)\}\{")
COLUMNS = ("id", "declaration", "kind", "parent_id", "parent", "via", "depth")
ARCHIVE_SHA256 = "9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"


def citations(paper):
    for path in sorted([paper / "main.tex", *(paper / "sections").glob("*.tex")]):
        for n, line in enumerate(path.read_text(encoding="utf-8-sig").splitlines(), 1):
            for m in CITATION.finditer(line):
                yield path.relative_to(paper).as_posix(), n, m[1], int(m[2])


def read_tsv(path):
    with path.open(encoding="utf-8-sig", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def source_namespace(lines):
    scopes = []
    for line in lines:
        scope = re.fullmatch(r"(?:(?:noncomputable|public|meta) )*(namespace|section|end)(?: (\S+))?", line)
        if scope:
            kind, name = scope.groups()
            if kind == "end":
                if not scopes or (name and name != scopes[-1][1]):
                    raise ValueError("unmatched Lean scope at " + line)
                scopes.pop()
            else:
                scopes.append((kind, name))
    return ".".join(name for kind, name in scopes if kind == "namespace")


def check(paper, source, full_tree, archive=None):
    audit = paper / "audit"
    entries = read_tsv(audit / "source-witnesses.tsv")
    expected = [(r["manuscript"], int(r["manuscript_line"]), r["source"],
                 int(r["source_line"])) for r in entries]
    if expected != list(citations(paper)):
        raise ValueError("the manuscript citations differ from the saved list")
    files = {}
    paths = {r["id"]: r for r in read_tsv(audit / "root-paths.tsv")}
    saved_names = {r["declaration"] for r in paths.values()}
    source_only = set()
    roots = [r for r in paths.values() if r["via"] == "root"]
    if len(roots) != 1 or roots[0]["declaration"] != "riemannHypothesis":
        raise ValueError("the path table does not have the expected unique root")
    for row in entries:
        name = row["source"]
        if name not in files:
            raw = (source / name).read_bytes()
            files[name] = (hashlib.sha256(raw).hexdigest(),
                           raw.decode("utf-8-sig").splitlines())
        digest, lines = files[name]
        if digest != row["file_sha256"] or not 1 <= int(row["source_line"]) <= len(lines):
            raise ValueError("source or line changed in " + name)
        if lines[int(row["source_line"]) - 1].strip()[:145] != row["source_excerpt"]:
            raise ValueError("quoted source line changed in " + name)
        header = row["declaration_line"]
        if not header or not row["declaration"] or not 1 <= int(header) <= int(row["source_line"]):
            raise ValueError("missing or impossible enclosing declaration in " + name)
        if row["root_status"] == "source_only":
            # A source-only citation pins the theorem header in its named
            # namespace. It makes no claim to a record in the full export.
            declaration = row["declaration"]
            namespace, _, theorem = declaration.rpartition(".")
            if (row["export_id"] or row["depth"] or declaration in saved_names
                    or header != row["source_line"] or namespace != source_namespace(lines[:int(header)-1])
                    or not lines[int(header) - 1].startswith("theorem " + theorem + " ")):
                raise ValueError("invalid source-only theorem header or path claim for " + declaration)
            source_only.add(declaration)
            continue
        if row["root_status"] not in {"reached", "exported_outside_classical_root"}:
            raise ValueError("no checked dependency path for " + row["declaration"])
        if row["root_status"] == "reached":
            node = paths[row["export_id"]]
            if (node["declaration"], node["depth"]) != (row["declaration"], row["depth"]):
                raise ValueError("declaration mismatch for " + row["declaration"])
    for row in paths.values():
        parent = paths[row["parent_id"]]
        if row["parent"] != parent["declaration"]:
            raise ValueError("parent mismatch for " + row["declaration"])
        if row["via"] == "root":
            if parent != row or row["depth"] != "0":
                raise ValueError("invalid root record")
        elif row["via"] not in {"value", "type", "structure"} or int(row["depth"]) != int(parent["depth"]) + 1:
            raise ValueError("invalid path for " + row["declaration"])
    sibling_ends = {}
    for row in read_tsv(audit / "sibling-paths.tsv"):
        key = row["root"], row["target"]
        prior = sibling_ends.get(key)
        if row["via"] not in {"value", "type", "structure"}:
            raise ValueError("invalid edge in sibling path")
        if prior is None:
            valid = row["from"] == row["root"] and row["step"] == "1"
        else:
            valid = (row["from_id"] == prior["to_id"] and row["from"] == prior["to"]
                     and int(row["step"]) == int(prior["step"]) + 1)
        if not valid:
            raise ValueError("disconnected path from " + row["root"])
        sibling_ends[key] = row
    expected_siblings = {(r["declaration"], r["export_id"]) for r in entries
                         if r["root_status"] == "exported_outside_classical_root"}
    actual_siblings = set()
    for (_, target), end in sibling_ends.items():
        if target != end["to"]:
            raise ValueError("wrong endpoint for " + target)
        actual_siblings.add((target, end["to_id"]))
    if expected_siblings != actual_siblings:
        raise ValueError("the manuscript and sibling endpoints differ")
    if full_tree:
        missing = set(paths)
        with gzip.open(full_tree, "rt", encoding="utf-8", newline="") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                if row["declaration"] in source_only:
                    raise ValueError("source-only citation occurs in the classical root tree: " + row["declaration"])
                if row["id"] in missing:
                    if any(row[k] != paths[row["id"]][k] for k in COLUMNS):
                        raise ValueError("export-walk record disagrees for " + row["declaration"])
                    missing.remove(row["id"])
        if missing:
            raise ValueError(f"{len(missing)} path records missing from the full tree")
    print(f"{len(entries)} source citations, {len(files)} distinct files, {len(paths)} saved path nodes.")
    print("Source-citation roles:", dict(Counter(r["root_status"] for r in entries)))
    if full_tree:
        print("All saved path records match the full dependency walk.")
    if archive:
        with archive.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != ARCHIVE_SHA256:
            raise ValueError("the archive differs from the published SHA-256")
        pending = {"lean/" + name: item[0] for name, item in files.items()}
        count = 0
        with tarfile.open(archive, "r|gz") as bundle:
            for entry in bundle:
                if entry.isfile() and entry.name.startswith("lean/src/") and entry.name.endswith(".lean"):
                    count += 1
                if entry.name in pending:
                    with bundle.extractfile(entry) as stream:
                        if hashlib.sha256(stream.read()).hexdigest() != pending.pop(entry.name):
                            raise ValueError("archived source differs for " + entry.name)
        if pending or count != 175187:
            raise ValueError(f"{len(pending)} cited files missing, {count} project modules")
        print(f"Archive SHA-256: {digest}")
        print(f"{count} project Lean modules, {len(files)} distinct cited files matched byte for byte.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", type=Path, default=PAPER)
    parser.add_argument("--source", type=Path, default=PAPER.parent / "lean",
                        help="project root containing src/Main.lean")
    parser.add_argument("--tree", type=Path,
                        help="optional full rh-dependency-tree.tsv.gz for independent comparison")
    parser.add_argument("--archive", type=Path,
                        help="also check every cited file against the original lean.tar.gz (Python 3.11+)")
    opts = parser.parse_args()
    check(opts.paper, opts.source, opts.tree, opts.archive)
