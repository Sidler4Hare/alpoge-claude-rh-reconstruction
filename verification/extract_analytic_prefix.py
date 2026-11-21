from pathlib import Path
import csv
import hashlib
import json
import sys
import zstandard

SOURCE_HASH = "61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381"
SOURCE_BYTES = 7699933588

def extract(source, output, receipt):
    names = {}
    declaration_ids = {}
    digest = hashlib.sha256()
    total = 0
    records = 0
    if source.stat().st_size != SOURCE_BYTES:
        raise RuntimeError("Unexpected source size")
    with source.open("rb") as src:
        if hashlib.file_digest(src,"sha256").hexdigest() != SOURCE_HASH:
            raise RuntimeError("Unexpected source SHA-256")
        src.seek(0)
        with zstandard.ZstdDecompressor(max_window_size=1<<30).stream_reader(src) as data, output.open("wb") as out:
            from io import BufferedReader
            pending = bytearray()
            for line in BufferedReader(data,buffer_size=2<<20):
                pending.extend(line)
                if len(pending) >= 4<<20:
                    out.write(pending)
                    digest.update(pending)
                    total += len(pending)
                    pending.clear()
                if line.startswith(b'{"in"') and any(x in line for x in (b'"Deduction"',b'"landau_window"',b'"poleData"',b'"Formalism"',b'"VW"',b'"rh_of_every"')):
                    item = json.loads(line)
                    kind = item.get("str", {})
                    name = kind.get("str")
                    owner = kind.get("pre")
                    if name is None: continue
                    label = names.get(owner)
                    if (owner == 0 and name in {"Deduction","Formalism"}) or (label,name) in {
                        ("Deduction","landau_window"),("Deduction","poleData"),("Formalism","VW"),("Formalism.VW","rh_of_every")
                    }:
                        names[item["in"]] = f"{label}.{name}" if label else name
                elif line.startswith((b'{"thm"',b'{"def"',b'{"opaque"',b'{"quot"',b'{"axiom"',b'{"inductive"')):
                    records += 1
                    if line.startswith(b'{"thm"'):
                        theorem = json.loads(line)["thm"]
                        label = names.get(theorem["name"])
                        if label in {"Deduction.poleData","Formalism.VW.rh_of_every","Deduction.landau_window"}:
                            declaration_ids[label] = theorem
                            if label == "Deduction.landau_window":
                                out.write(pending)
                                digest.update(pending)
                                total += len(pending)
                                break
            else:
                raise RuntimeError("Deduction.landau_window was not found")
    data = {"source_sha256":SOURCE_HASH,"source_bytes":SOURCE_BYTES,"prefix_sha256":digest.hexdigest(),
            "prefix_bytes":total,"prefix_declaration_records":records,"theorems":declaration_ids}
    receipt.write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    print(json.dumps(data),flush=True)

if __name__=="__main__":
    extract(*(Path(p) for p in sys.argv[1:]))

