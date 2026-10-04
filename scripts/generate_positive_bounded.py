#!/usr/bin/env python3
"""Generate only kernel proof commands for the complete pruned census.

No Python result is trusted: each block and the complete coverage proof are
checked by Lean. The source equations, enumeration and certificates are Lean
definitions from PositiveBoundedBase/PositiveBoundedTable.
"""
from pathlib import Path

root = Path(__file__).resolve().parents[1] / "SerreMarkov"
for a in range(20):
    previous = "PositiveBoundedBase" if a == 0 else f"PositiveBoundedPart{a-1:02}"
    lines = [f"import SerreMarkov.{previous}", "", "namespace SerreMarkov.PositiveBounded", "",
             "set_option Elab.async false", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 200000000", "set_option linter.unusedVariables false", ""]
    for b in range(20-a):
        lines += [f"theorem block_{a:02}_{b:02} : blockCheck {a} {b} = true := by decide +kernel", ""]
    lines += [f"theorem checked_row_{a:02} (b : Fin 20) (h : {a}+b.val ≤ 19) :",
              f"    blockCheck {a} b.val = true := by", "  fin_cases b"]
    for b in range(20):
        lines.append(f"  · exact block_{a:02}_{b:02}" if a+b <= 19 else "  · norm_num at h")
    lines += ["", "end SerreMarkov.PositiveBounded", ""]
    (root / f"PositiveBoundedPart{a:02}.lean").write_text("\n".join(lines))

lines = ["import SerreMarkov.PositiveBoundedPart19", "", "namespace SerreMarkov.PositiveBounded", "",
         "theorem all_blocks_checked (a b : Fin 20) (h : a.val+b.val ≤ 19) :",
         "    blockCheck a.val b.val = true := by", "  fin_cases a"]
for a in range(20):
    lines.append(f"  · exact checked_row_{a:02} b h")
lines += ["", "end SerreMarkov.PositiveBounded", ""]
(root / "PositiveBoundedChecks.lean").write_text("\n".join(lines))
print("Generated 210 independent kernel checks and their structural assembly.")
