#!/usr/bin/env python3
"""Generate or check the arc assumption inventory using Lean-elaborated signatures.

Run after `lake build`: python3 scripts/audit_assumptions.py
CI checks the committed inventory with --check docs/assumptions.md.
"""
import argparse
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Basic", "Degenerate", "Structure", "Measure"]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", type=Path)
args = parser.parse_args()
items = []
for module in MODULES:
    source = (ROOT / f"ArcsForMathlib/Sphere/Arc/{module}.lean").read_text()
    if module != "Measure":
        assert not re.search(r"∠|∡|Real\.Angle|Module\.Oriented", source), module
    for match in re.finditer(r"^(?:(private)\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure)\s+(\w+)", source, re.M):
        if not match[1]:
            items.append((module, match[2]))
commands = ["import ArcsForMathlib.Sphere.Arc.Measure"]
for _, name in items:
    full = "EuclideanGeometry.Sphere." + ("Arc" if name == "Arc" else "Arc." + name)
    commands.append("#check " + full)
with tempfile.TemporaryDirectory(prefix="arc-assumptions-") as temporary:
    path = Path(temporary) / "Audit.lean"
    path.write_text("\n".join(commands) + "\n")
    output = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                            check=True, text=True, capture_output=True).stdout
signatures = {}
for block in re.split(r"(?=^EuclideanGeometry\.Sphere\.Arc(?:\.|\{))", output, flags=re.M):
    match = re.match(r"EuclideanGeometry\.Sphere\.Arc(?:\.(\w+))?\.\{", block)
    if match:
        signatures[match[1] or "Arc"] = " ".join(block.split())
assert len(signatures) == len(items), "Missing or duplicate signatures"

def listing(pattern):
    groups = []
    for module in MODULES:
        names = [name for mod, name in items if mod == module and re.search(pattern, signatures[name])]
        if names:
            groups.append("in `" + module + "`, " + ", ".join("`" + name + "`" for name in names))
    return "; ".join(groups)

text = "# Public assumption audit\n\n"
text += f"Generated from {len(items)} explicitly named public declarations by `scripts/audit_assumptions.py`. "
text += "Signatures include inherited section parameters. Conclusions and proof bodies are excluded from the premise lists.\n\n"
text += "First, exactly the following public declarations require two-dimensionality: "
text += listing(r"\[Fact \(Module\.finrank ℝ V = 2\)\]")
text += ". No other public declaration in these modules carries a `[Fact (Module.finrank ℝ V = 2)]` assumption.\n\n"
text += "Second, exactly the following public declarations take `s.radius ≠ 0` as an explicit parameter: "
text += listing(r"\(\w+ : s\.radius ≠ 0\)")
text += ". No other public declaration in these modules takes `s.radius ≠ 0` explicitly.\n\n"
text += "Third, exactly the following public declarations take `¬a.IsSinglePoint` as an explicit parameter: "
text += listing(r"\(\w+ : ¬a\.IsSinglePoint\)")
text += ". No other public declaration in these modules takes `¬a.IsSinglePoint` explicitly.\n\n"
assert not listing(r"\(\w+ : ¬a\.IsDegenerate\)"), "Nondegeneracy premise returned"
text += "No public declaration in these four modules takes `¬a.IsDegenerate` as an explicit parameter.\n\n"
text += "## Structural-layer checks\n\n"
text += "`Basic`, `Structure`, and `Degenerate` contain none of `∠`, `∡`, `Real.Angle`, or `Module.Oriented`.\n\n"
# Retain the exact search evidence used to remove the obsolete usage claim.
text += "Occurrences of `left_ne_right_iff_not_isDegenerate` in the four modules:\n\n```text\n"
for module in MODULES:
    for number, line in enumerate((ROOT / f"ArcsForMathlib/Sphere/Arc/{module}.lean").read_text().splitlines(), 1):
        if "left_ne_right_iff_not_isDegenerate" in line:
            text += f"{module}.lean:{number}:{line}\n"
text += "```\n"
if args.check:
    assert (ROOT / args.check).read_text() == text, "Regenerate the assumption inventory"
    print("Public assumption inventory and structural-layer checks passed.")
else:
    print(text, end="")
