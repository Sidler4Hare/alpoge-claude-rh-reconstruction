"""Compile the new modules against a built copy of the original project.

Run from the original project with: lake env python /path/to/check_lean.py
"""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    source = Path(__file__).resolve().parent
    lean = shutil.which(os.environ.get("LEAN", "lean"))
    if not lean:
        raise SystemExit("Set LEAN to the Lean 4.33.1 binary or run under lake env.")
    # Resolve an elan proxy while the caller is still in the pinned project.
    prefix = Path(subprocess.check_output([lean, "--print-prefix"], text=True).strip())
    lean = prefix / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    print(version, flush=True)
    if "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
        raise SystemExit("This development uses Lean 4.33.1.")
    paths = [str(Path(p).resolve()) for p in os.getenv("LEAN_PATH", "").split(os.pathsep) if p]
    with tempfile.TemporaryDirectory(prefix="levent151-") as build:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([build, *paths]))
        for module in ("Pointwise", "Sharper", "Quadratic", "Window", "Extraction",
                       "PowerWindows", "Downstream", "FamilyGeometry", "Family", "Equation151",
                       "MeanExtraction", "Equation152", "OrbitLoss", "WeightSpacing",
                       "PrimeWindow", "RankMeanBudget", "PrimePrefix", "FamilyPrefix",
                       "TranslateUniformity", "MeanLossRefinement", "MeanDeterminant",
                       "RelativeFinitePart", "RecordedMixedComparison", "RecordedVolumeCarry",
                       "RankTailTransfer", "ExceptionalRowDegree", "PeriodRadical", "PeriodWitnessChain",
                       "RamifiedOrbitPeriod", "LevelPrimeOrbitSupply", "ReselectedRealization",
                       "ReselectedHost", "ReselectedPointSupply", "OneWordWindow",
                       "PrimeWindowInterpolation", "OrbitLossAtSelectedPoints",
                       "DutyCentresOnFixedHosts", "RecordedHeightInput"):
            print(f"Checking {module}", flush=True)
            subprocess.run([lean, "--tstack=400000", "-j1", "-DmaxHeartbeats=4000000",
                            "-o", str(Path(build) / f"{module}.olean"), f"{module}.lean"],
                           cwd=source, env=env, check=True)


if __name__ == "__main__":
    main()
