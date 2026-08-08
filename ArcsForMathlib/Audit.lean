import ArcsForMathlib

/-!
# Axiom audit

This file makes the axiom claim for the four final case-study theorems executable. Each
`#guard_msgs` block checks the complete informational message produced by `#print axioms`, so the
file fails to elaborate if a theorem gains or loses an axiom dependency.

Run it with:

```bash
lake env lean ArcsForMathlib/Audit.lean
```
-/

/--
info: 'IncenterArcMidpoint.result' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms IncenterArcMidpoint.result

/--
info: 'BMO1_2018P4.result' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BMO1_2018P4.result

/--
info: 'ChinaMO2010P1.result' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ChinaMO2010P1.result

/--
info: 'ChinaMO2012P1.result' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ChinaMO2012P1.result
