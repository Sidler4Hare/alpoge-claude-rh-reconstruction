"""Locate exact qualified declaration names in the unchanged NDJSON prefix."""

import json
import sys
from pathlib import Path


def locate(prefix: Path, symbols: set[str]) -> dict:
    components = {part for name in symbols for part in name.split(".")}
    markers = tuple(json.dumps(part, ensure_ascii=False).encode() for part in components)
    ancestors = {0: ""}
    targets = {}
    results = dict.fromkeys(sorted(symbols))

    with prefix.open("rb", buffering=4 << 20) as stream:
        for raw in stream:
            if raw.startswith(b'{"in"') and b',"str":{' in raw[:50]:
                if not any(marker in raw for marker in markers):
                    continue
                record = json.loads(raw)
                name = record["str"]
                part, parent = name.get("str"), name.get("pre")
                if part not in components or parent not in ancestors:
                    continue
                qualified = ".".join(filter(None, (ancestors[parent], part)))
                if qualified in symbols:
                    targets[record["in"]] = qualified
                if qualified in symbols or any(s.startswith(qualified + ".") for s in symbols):
                    ancestors[record["in"]] = qualified
            elif raw.startswith((b'{"thm"', b'{"def"', b'{"opaque"')):
                record = next(iter(json.loads(raw).values()))
                qualified = targets.get(record.get("name"))
                if qualified is not None:
                    results[qualified] = record
    return results


if __name__ == "__main__":
    print(json.dumps(locate(Path(sys.argv[1]), set(sys.argv[2:])), indent=2))
