import ArcsForMathlib

/-!
# Repository audit

This file makes the axiom claim for the four final case-study theorems executable. Each
`#guard_msgs` block checks the complete informational message produced by `#print axioms`, so the
file fails to elaborate if a theorem gains or loses an axiom dependency.

It also records representation-level regressions that should remain explicit in the public API.
At present there is one: the `Arc` structure docstring in `Arc.Basic` states that the coercion to
`Set P` is not injective, because reversing the named endpoints of a `minor` arc with distinct
endpoints preserves its point set but changes `left`. That claim is what forces the object-level
uniqueness theorems in `Arc.Structure` to fix the *ordered* endpoints, so the example below turns
it into a checked statement rather than prose.

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

/-! ## Arc representation regression -/

namespace EuclideanGeometry.Sphere.Arc

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-
Reversing the named endpoints of a nontrivial minor arc preserves its point set but changes the
`Arc` object. This guards against accidentally treating the coercion to `Set P` as injective.

`#guard_msgs` deliberately expects zero diagnostics here, so a future `sorry` warning becomes an
error. Keep this as an ordinary comment: a doc comment would be parsed as expected diagnostic text.
-/
#guard_msgs in
example {s : Sphere P} {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hNotDiamAC : ¬s.IsDiameter A C) (hNotDiamCA : ¬s.IsDiameter C A) (hAC : A ≠ C) :
    ((minor hA hC hNotDiamAC : Arc s) : Set P) =
        ((minor hC hA hNotDiamCA : Arc s) : Set P) ∧
      minor hA hC hNotDiamAC ≠ minor hC hA hNotDiamCA := by
  have hmid : (minor hA hC hNotDiamAC).mid = (minor hC hA hNotDiamCA).mid := by
    change minorMidpoint s A C = minorMidpoint s C A
    exact minorMidpoint_comm s A C
  have hline : s.lineOrOrthRadius A C = s.lineOrOrthRadius C A :=
    lineOrOrthRadius_comm
  constructor
  · ext Q
    change Q ∈ minor hA hC hNotDiamAC ↔ Q ∈ minor hC hA hNotDiamCA
    rw [mem_iff, mem_iff]
    simp only [minor_left, minor_right]
    rw [hmid, hline]
    tauto
  · intro heq
    apply hAC
    have hleft := congrArg Arc.left heq
    simpa only [minor_left] using hleft

end EuclideanGeometry.Sphere.Arc
