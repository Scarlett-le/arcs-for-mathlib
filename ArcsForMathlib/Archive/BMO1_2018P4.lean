/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
import Mathlib
import ArcsForMathlib.Auxlemma
import ArcsForMathlib.Sphere.Arc.Basic
import ArcsForMathlib.Sphere.Arc.Degenerate
import ArcsForMathlib.Sphere.Arc.Structure
import ArcsForMathlib.Sphere.Arc.Measure

/-!
# BMO Round 1, 2018, Problem 4

Let `Γ` be a semicircle with diameter `AB`. The point `C` lies on the diameter `AB` and points
`E` and `D` lie on the arc `BA`, with `E` between `B` and `D`. Let the tangents to `Γ` at `D` and
`E` meet at `F`. Suppose that `∠ACD = ∠ECB`. Prove that `∠EFD = ∠ACD + ∠ECB`.

## Solution outline

Following the `Archive`/`IMO 2019 Q2` (`jsm`) convention, we bundle the hypotheses into a
configuration structure `Cfg` and build up the argument as a sequence of lemmas on `Cfg`.

Write `O := ω.center` (the centre of the circle, which is the midpoint of the diameter `AB`, so
`O` lies on line `AB`).  The proof rests on three milestones:

* **(kite)** `∠EFD = π − ∠DOE`.  Since `FD`, `FE` are tangents, `OD ⊥ FD` and `OE ⊥ FE`, so `D`
  and `E` lie on the circle with diameter `FO` (Thales).  On that circle `F` and `O` are the two
  endpoints of a diameter, lying on opposite arcs cut by the chord `DE`, so the inscribed angles
  `∠DFE` and `∠DOE` are supplementary.

* **(reflection crux)** `∠DOE = ∠DCE`.  This is the heart of the problem and the only place the
  hypothesis `∠ACD = ∠ECB` is used: reflect `E` in the diameter line `AB`, prove
  `D, C, E'` are collinear, and compare both angles with `2 * ∠DE'E`.

* **(straight line / ray split)** `∠ACD + ∠DCB = π` (because `A, C, B` are collinear with `C`
  between) and `∠DCB = ∠DCE + ∠ECB` (because, on the semicircle, the ray `CE` lies inside the
  angle `∠DCB`).

Combining: `∠EFD = π − ∠DOE = π − ∠DCE = π − (π − ∠ACD − ∠ECB) = ∠ACD + ∠ECB`.

Note that, exactly as in the `IMO 2019 Q2` formalisation, much of the work is in the
nondegeneracy bookkeeping rather than the angle chase itself.

## Reference

UK Mathematics Trust, *British Mathematical Olympiad, Round 1*, competition paper,
Friday 30 November 2018, Problem 4.
https://ukmt.org.uk/wp-content/uploads/2023/08/bmo1-2018.pdf
-/

open scoped Real EuclideanGeometry Affine RealInnerProductSpace
open Affine EuclideanGeometry Module Sphere

namespace BMO1_2018P4

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- A configuration satisfying the conditions of BMO 2018 P4.  We bundle the hypotheses into a
structure (mirroring `Imo2019q2Cfg`) so that the many derived facts can be proved without passing
the hypotheses around by hand; the final statement is then deduced from this structure. -/
structure Cfg (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
    [NormedAddTorsor V Pt] where
  (A B C D E F : Pt)
  (ω : Sphere Pt)
  A_ne_B : A ≠ B
  ω_eq : ω = Sphere.ofDiameter A B
  sbtw_A_C_B : Sbtw ℝ A C B
  -- (derivable from `ω_eq`; kept for the `Arc.avoiding` construction below)
  A_mem_ω : A ∈ (ω : Set Pt)
  B_mem_ω : B ∈ (ω : Set Pt)
  D_mem_ω : D ∈ (ω : Set Pt)
  A_ne_D : A ≠ D
  B_ne_D : B ≠ D
  E_mem_interior_arc_BD :
    E ∈ (Sphere.Arc.avoiding B_mem_ω A_mem_ω D_mem_ω A_ne_B A_ne_D).interior
  isTangentAt_D : ω.IsTangentAt D line[ℝ, F, D]
  isTangentAt_E : ω.IsTangentAt E line[ℝ, F, E]
  angle_ACD_eq_ECB : ∠ A C D = ∠ E C B

namespace Cfg

variable [Fact (finrank ℝ V = 2)] (cfg : Cfg V Pt)

local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

noncomputable local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

/-! ### Memberships and the centre -/

omit [Fact (finrank ℝ V = 2)] in
theorem D_mem : cfg.D ∈ cfg.ω := cfg.D_mem_ω

omit [Fact (finrank ℝ V = 2)] in
theorem E_mem : cfg.E ∈ cfg.ω := cfg.E_mem_interior_arc_BD.1

omit [Fact (finrank ℝ V = 2)] in
/-- The centre of `ω` is the midpoint of the diameter `AB`; in particular it lies on line `AB`,
together with `C`. -/
theorem center_eq_midpoint : cfg.ω.center = midpoint ℝ cfg.A cfg.B := by
  rw [cfg.ω_eq]; rfl

omit [Fact (finrank ℝ V = 2)] in
/-- `ω` has nonzero radius, since it contains the two distinct points `A` and `B`. -/
theorem radius_ne_zero : cfg.ω.radius ≠ 0 :=
  Sphere.radius_ne_zero_of_mem_of_mem_of_ne cfg.A_mem_ω cfg.B_mem_ω cfg.A_ne_B

omit [Fact (finrank ℝ V = 2)] in
/-- Since `C` lies strictly between the diameter endpoints, it is strictly inside `ω`. -/
theorem dist_center_C_lt_radius : dist cfg.ω.center cfg.C < cfg.ω.radius :=
  cfg.ω.dist_center_lt_radius_of_sbtw cfg.A_mem_ω cfg.B_mem_ω cfg.sbtw_A_C_B

omit [Fact (finrank ℝ V = 2)] in
/-- The interior point `C` is not on the circle. -/
theorem C_not_mem : cfg.C ∉ cfg.ω :=
  fun hC => cfg.dist_center_C_lt_radius.ne (by simpa [dist_comm] using mem_sphere.mp hC)

omit [Fact (finrank ℝ V = 2)] in
/-- The interior point `C` is distinct from `D`. -/
theorem C_ne_D : cfg.C ≠ cfg.D := fun h => cfg.C_not_mem (h.symm ▸ cfg.D_mem)

omit [Fact (finrank ℝ V = 2)] in
/-- The interior point `C` is distinct from `E`. -/
theorem C_ne_E : cfg.C ≠ cfg.E := fun h => cfg.C_not_mem (h.symm ▸ cfg.E_mem)

/-! ### Nondegeneracy of the points `D`, `E`, `F` -/

/-- `E` is an interior point of the arc `BD`, so it is not the endpoint `D`. -/
theorem E_ne_D : cfg.E ≠ cfg.D := by
  have h := Arc.ne_right_of_mem_interior _ cfg.E_mem_interior_arc_BD
  rwa [Arc.avoiding_right cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D] at h

omit [Fact (finrank ℝ V = 2)] in
/-- `E` is an interior point of the arc `BD`, so it is not the endpoint `B`. -/
theorem E_ne_B : cfg.E ≠ cfg.B := by
  have h := Arc.ne_left_of_mem_interior _ cfg.E_mem_interior_arc_BD
  rwa [Arc.avoiding_left cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D] at h

/-- `E` is on the arc from `B` to `D` avoiding `A`, hence it is not `A`. -/
theorem E_ne_A : cfg.E ≠ cfg.A := by
  intro hEA
  have hA_not :
      cfg.A ∉ Sphere.Arc.avoiding cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D :=
    Sphere.Arc.not_mem_avoiding cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D
      cfg.B_ne_D
  apply hA_not
  refine Arc.mem_iff.mpr ⟨by simpa [hEA] using cfg.E_mem_interior_arc_BD.1,
    Or.inr (Or.inr ?_)⟩
  simpa [hEA] using cfg.E_mem_interior_arc_BD.2

/-- `F` (the meeting point of the two tangents) is distinct from the tangent point `D`: otherwise
`D` would lie on the tangent line at `E`, forcing `D = E`. -/
theorem F_ne_D : cfg.F ≠ cfg.D := by
  intro h
  apply cfg.E_ne_D
  symm
  apply cfg.isTangentAt_E.eq_of_mem_of_mem cfg.D_mem
  rw [← h]
  exact left_mem_affineSpan_pair ℝ cfg.F cfg.E

/-- `F` is distinct from the tangent point `E`: otherwise `E` would lie on the tangent line at
`D`, forcing `E = D`. -/
theorem F_ne_E : cfg.F ≠ cfg.E := by
  intro h
  apply cfg.E_ne_D
  apply cfg.isTangentAt_D.eq_of_mem_of_mem cfg.E_mem
  rw [← h]
  exact left_mem_affineSpan_pair ℝ cfg.F cfg.D

/-! ### Tangent right angles and equal tangent lengths -/

omit [Fact (finrank ℝ V = 2)] in
/-- The radius `OD` is perpendicular to the tangent `FD`: `∠ F D O = π / 2`. -/
theorem angle_FDO : ∠ cfg.F cfg.D cfg.ω.center = π / 2 :=
  cfg.isTangentAt_D.angle_eq_pi_div_two (left_mem_affineSpan_pair ℝ cfg.F cfg.D)

omit [Fact (finrank ℝ V = 2)] in
/-- The radius `OE` is perpendicular to the tangent `FE`: `∠ F E O = π / 2`. -/
theorem angle_FEO : ∠ cfg.F cfg.E cfg.ω.center = π / 2 :=
  cfg.isTangentAt_E.angle_eq_pi_div_two (left_mem_affineSpan_pair ℝ cfg.F cfg.E)

omit [Fact (finrank ℝ V = 2)] in
/-- The two tangent segments from the external point `F` have equal length. -/
theorem dist_FD_eq_FE : dist cfg.F cfg.D = dist cfg.F cfg.E :=
  cfg.isTangentAt_D.dist_eq_of_mem_of_mem cfg.isTangentAt_E
    (left_mem_affineSpan_pair ℝ cfg.F cfg.D) (left_mem_affineSpan_pair ℝ cfg.F cfg.E)

/-! ### Milestone 1 (kite): `∠EFD = π − ∠DOE`

The supporting geometric facts: `D, E, F` configuration relative to the centre `O`, that `O` and
`F` lie on opposite sides of the chord `DE`, and finally the kite supplementarity itself. -/

omit [Fact (finrank ℝ V = 2)] in
theorem D_ne_center : cfg.D ≠ cfg.ω.center := by
  intro h; exact cfg.radius_ne_zero (by rw [← mem_sphere.mp cfg.D_mem, h, dist_self])

omit [Fact (finrank ℝ V = 2)] in
theorem E_ne_center : cfg.E ≠ cfg.ω.center := by
  intro h; exact cfg.radius_ne_zero (by rw [← mem_sphere.mp cfg.E_mem, h, dist_self])

omit [Fact (finrank ℝ V = 2)] in
/-- The chord-midpoint `M` lies on the line `DE`. -/
theorem midpoint_mem_line_DE : midpoint ℝ cfg.D cfg.E ∈ line[ℝ, cfg.D, cfg.E] :=
  (wbtw_midpoint ℝ cfg.D cfg.E).mem_affineSpan

omit [Fact (finrank ℝ V = 2)] in
/-- The tangent at `D` is perpendicular to the radius `OD`: `⟪F −ᵥ D, D −ᵥ O⟫ = 0`. -/
theorem inner_F_sub_D : ⟪cfg.F -ᵥ cfg.D, cfg.D -ᵥ cfg.ω.center⟫ = 0 :=
  cfg.isTangentAt_D.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ cfg.F cfg.D)

omit [Fact (finrank ℝ V = 2)] in
/-- The tangent at `E` is perpendicular to the radius `OE`: `⟪F −ᵥ E, E −ᵥ O⟫ = 0`. -/
theorem inner_F_sub_E : ⟪cfg.F -ᵥ cfg.E, cfg.E -ᵥ cfg.ω.center⟫ = 0 :=
  cfg.isTangentAt_E.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ cfg.F cfg.E)

omit [Fact (finrank ℝ V = 2)] in
/-- `O −ᵥ M` is orthogonal to the chord direction `E −ᵥ D` (the centre projects to the chord
midpoint). -/
theorem inner_center_sub_mid :
    ⟪cfg.ω.center -ᵥ midpoint ℝ cfg.D cfg.E, cfg.E -ᵥ cfg.D⟫ = 0 :=
  Sphere.inner_vsub_center_midpoint_vsub cfg.D_mem cfg.E_mem

omit [Fact (finrank ℝ V = 2)] in
/-- `F −ᵥ M` is orthogonal to the chord direction `E −ᵥ D` (since `FD = FE`, `F` lies on the
perpendicular bisector of `DE`). -/
theorem inner_F_sub_mid :
    ⟪cfg.F -ᵥ midpoint ℝ cfg.D cfg.E, cfg.E -ᵥ cfg.D⟫ = 0 :=
  AffineSubspace.mem_perpBisector_iff_inner_eq_zero.mp
    (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr cfg.dist_FD_eq_FE)

/-- The external point `F` is not on the chord line `DE`: otherwise `F = M`, but `F` is outside
the circle while `M` is inside. -/
theorem F_not_mem_line_DE : cfg.F ∉ line[ℝ, cfg.D, cfg.E] := by
  intro hF
  have hmem : cfg.F -ᵥ midpoint ℝ cfg.D cfg.E ∈
      (line[ℝ, cfg.D, cfg.E] : AffineSubspace ℝ Pt).direction :=
    AffineSubspace.vsub_mem_direction hF cfg.midpoint_mem_line_DE
  rw [direction_affineSpan, vectorSpan_pair] at hmem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  have hED_ne : cfg.E -ᵥ cfg.D ≠ 0 := vsub_ne_zero.mpr cfg.E_ne_D
  have hperp := cfg.inner_F_sub_mid
  rw [← hk, real_inner_smul_left,
      show cfg.D -ᵥ cfg.E = -(cfg.E -ᵥ cfg.D) from (neg_vsub_eq_vsub_rev _ _).symm,
      inner_neg_left, real_inner_self_eq_norm_sq, mul_neg] at hperp
  have hk0 : k = 0 := by
    have hpos : (0:ℝ) < ‖cfg.E -ᵥ cfg.D‖ ^ 2 := pow_pos (norm_pos_iff.mpr hED_ne) 2
    nlinarith [hperp]
  have hFM : cfg.F = midpoint ℝ cfg.D cfg.E := by
    rw [← vsub_eq_zero_iff_eq, ← hk, hk0, zero_smul]
  have h1 : dist cfg.ω.center cfg.F < cfg.ω.radius := by
    rw [hFM]; exact Sphere.dist_center_midpoint_lt_radius cfg.D_mem cfg.E_mem cfg.E_ne_D.symm
  have h2 : cfg.ω.radius < dist cfg.F cfg.ω.center :=
    cfg.isTangentAt_D.radius_lt_dist_center (left_mem_affineSpan_pair ℝ cfg.F cfg.D) cfg.F_ne_D
  rw [dist_comm] at h1
  linarith

/-- The centre `O` is not on the chord line `DE`: otherwise `DE` would be a diameter, but the two
tangents at antipodal points are parallel and could not meet at `F`. -/
theorem center_not_mem_line_DE : cfg.ω.center ∉ line[ℝ, cfg.D, cfg.E] := by
  intro hO
  have hdiam : cfg.ω.IsDiameter cfg.D cfg.E :=
    (Sphere.center_mem_affineSpan_pair_iff_isDiameter cfg.D_mem cfg.E_mem cfg.E_ne_D.symm).mp hO
  have hmid : midpoint ℝ cfg.D cfg.E = cfg.ω.center := hdiam.midpoint_eq_center
  have hanti : cfg.E -ᵥ cfg.ω.center = -(cfg.D -ᵥ cfg.ω.center) := by
    rw [← hmid, right_vsub_midpoint, left_vsub_midpoint, ← smul_neg, neg_vsub_eq_vsub_rev]
  have h2 : ⟪cfg.F -ᵥ cfg.E, cfg.D -ᵥ cfg.ω.center⟫ = 0 := by
    rw [show cfg.D -ᵥ cfg.ω.center = -(cfg.E -ᵥ cfg.ω.center) from by rw [hanti, neg_neg],
        inner_neg_right, cfg.inner_F_sub_E, neg_zero]
  have hED : ⟪cfg.E -ᵥ cfg.D, cfg.D -ᵥ cfg.ω.center⟫ = 0 := by
    rw [show cfg.E -ᵥ cfg.D = (cfg.F -ᵥ cfg.D) - (cfg.F -ᵥ cfg.E) from
          (vsub_sub_vsub_cancel_left _ _ _).symm,
        inner_sub_left, cfg.inner_F_sub_D, h2, sub_zero]
  have hED2 : cfg.E -ᵥ cfg.D = (-2 : ℝ) • (cfg.D -ᵥ cfg.ω.center) := by
    rw [show cfg.E -ᵥ cfg.D = (cfg.E -ᵥ cfg.ω.center) - (cfg.D -ᵥ cfg.ω.center) from
          (vsub_sub_vsub_cancel_right _ _ _).symm, hanti]
    module
  rw [hED2, real_inner_smul_left, real_inner_self_eq_norm_sq] at hED
  have hnorm : ‖cfg.D -ᵥ cfg.ω.center‖ ^ 2 = 0 := by linarith
  rw [pow_eq_zero_iff (by norm_num), norm_eq_zero, vsub_eq_zero_iff_eq] at hnorm
  exact cfg.D_ne_center hnorm

/-- `O` and `F` lie on **opposite** sides of the chord line `DE`: the displacements `O −ᵥ M` and
`F −ᵥ M` from the chord midpoint `M` point along the same normal but with opposite signs
(the coefficient `c` below is `≤ 0`). -/
theorem sOppSide_line_DE : (line[ℝ, cfg.D, cfg.E]).SOppSide cfg.F cfg.ω.center := by
  set M := midpoint ℝ cfg.D cfg.E with hMdef
  have hFM_ne : cfg.F -ᵥ M ≠ 0 := by
    intro h0
    refine cfg.F_not_mem_line_DE ?_
    rw [vsub_eq_zero_iff_eq] at h0
    rw [h0]; exact cfg.midpoint_mem_line_DE
  have hspan : cfg.ω.center -ᵥ M ∈ Submodule.span ℝ ({cfg.F -ᵥ M} : Set V) :=
    Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
      (vsub_ne_zero.mpr cfg.E_ne_D) hFM_ne
      (by rw [real_inner_comm]; exact cfg.inner_center_sub_mid)
      (by rw [real_inner_comm]; exact cfg.inner_F_sub_mid)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have key : ∀ P : Pt, ⟪cfg.F -ᵥ P, P -ᵥ cfg.ω.center⟫ = 0 →
      ⟪cfg.ω.center -ᵥ P, cfg.F -ᵥ cfg.ω.center⟫ = -‖P -ᵥ cfg.ω.center‖ ^ 2 := by
    intro P hP
    have hPF0 : ⟪cfg.ω.center -ᵥ P, cfg.F -ᵥ P⟫ = 0 := by
      rw [real_inner_comm,
          show cfg.ω.center -ᵥ P = -(P -ᵥ cfg.ω.center) from (neg_vsub_eq_vsub_rev _ _).symm,
          inner_neg_right, hP, neg_zero]
    rw [show cfg.F -ᵥ cfg.ω.center = (cfg.F -ᵥ P) + (P -ᵥ cfg.ω.center) from
          (vsub_add_vsub_cancel _ _ _).symm, inner_add_right, hPF0,
        show cfg.ω.center -ᵥ P = -(P -ᵥ cfg.ω.center) from (neg_vsub_eq_vsub_rev _ _).symm,
        inner_neg_left, real_inner_self_eq_norm_sq]
    ring
  have b1 : ⟪cfg.ω.center -ᵥ cfg.D, cfg.F -ᵥ cfg.ω.center⟫ =
      -‖cfg.D -ᵥ cfg.ω.center‖ ^ 2 :=
    key cfg.D cfg.inner_F_sub_D
  have b2 : ⟪cfg.ω.center -ᵥ cfg.E, cfg.F -ᵥ cfg.ω.center⟫ =
      -‖cfg.E -ᵥ cfg.ω.center‖ ^ 2 :=
    key cfg.E cfg.inner_F_sub_E
  have hOMF : ⟪cfg.ω.center -ᵥ M, cfg.F -ᵥ cfg.ω.center⟫ = -cfg.ω.radius ^ 2 := by
    rw [hMdef, vsub_midpoint, inner_add_left, real_inner_smul_left, real_inner_smul_left, b1, b2,
        norm_vsub_center_eq_radius cfg.D_mem, norm_vsub_center_eq_radius cfg.E_mem, invOf_eq_inv]
    ring
  have hFMFO : ⟪cfg.F -ᵥ M, cfg.F -ᵥ cfg.ω.center⟫ = ‖cfg.F -ᵥ cfg.ω.center‖ ^ 2 + -cfg.ω.radius ^ 2 := by
    rw [show cfg.F -ᵥ M = (cfg.F -ᵥ cfg.ω.center) + (cfg.ω.center -ᵥ M) from
          (vsub_add_vsub_cancel _ _ _).symm, inner_add_left, real_inner_self_eq_norm_sq, hOMF]
  have hFOpos : cfg.ω.radius ^ 2 < ‖cfg.F -ᵥ cfg.ω.center‖ ^ 2 := by
    have hd := cfg.isTangentAt_D.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ cfg.F cfg.D)
    rw [dist_eq_norm_vsub V cfg.F cfg.ω.center] at hd
    nlinarith [hd, dist_pos.mpr cfg.F_ne_D]
  have hrpos : 0 < cfg.ω.radius := Sphere.radius_pos_of_mem cfg.D_mem cfg.radius_ne_zero
  have hsign : c ≤ 0 := by
    have e : c * ⟪cfg.F -ᵥ M, cfg.F -ᵥ cfg.ω.center⟫ = ⟪cfg.ω.center -ᵥ M, cfg.F -ᵥ cfg.ω.center⟫ := by
      rw [← hc, real_inner_smul_left]
    rw [hFMFO, hOMF] at e
    nlinarith [e, hFOpos, pow_pos hrpos 2]
  exact AffineSubspace.sOppSide_of_vsub_eq_smul (m := cfg.F -ᵥ M) (c₁ := 1) (c₂ := c)
    cfg.midpoint_mem_line_DE cfg.midpoint_mem_line_DE (one_smul ℝ _).symm hc.symm
    (by rw [one_mul]; exact hsign) cfg.F_not_mem_line_DE cfg.center_not_mem_line_DE

/-- **Tangent kite.** The tangent right angles put `D` and `E` on the circle with diameter `FO`,
where `F` and `O` lie on opposite arcs cut by chord `DE`. -/
theorem angle_EFD_eq_pi_sub_angle_DOE :
    ∠ cfg.E cfg.F cfg.D = π - ∠ cfg.D cfg.ω.center cfg.E := by
  -- The circle `s'` with diameter `F O`; by Thales `D` and `E` lie on it.
  set s' : Sphere Pt := Sphere.ofDiameter cfg.F cfg.ω.center with hs'
  have hDs' : cfg.D ∈ s' :=
    Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.mp cfg.angle_FDO
  have hEs' : cfg.E ∈ s' :=
    Sphere.angle_eq_pi_div_two_iff_mem_sphere_ofDiameter.mp cfg.angle_FEO
  have hFs' : cfg.F ∈ s' := (Sphere.isDiameter_ofDiameter cfg.F cfg.ω.center).left_mem
  have hOs' : cfg.ω.center ∈ s' := (Sphere.isDiameter_ofDiameter cfg.F cfg.ω.center).right_mem
  -- the arc `D → E` of `s'` through `F`
  set a : Arc s' := Arc.through hDs' hFs' hEs' cfg.F_ne_D cfg.F_ne_E with ha
  have haL : a.left = cfg.D := rfl
  have haR : a.right = cfg.E := Arc.through_right hDs' hFs' hEs' cfg.F_ne_D cfg.F_ne_E
  have hLeq : s'.lineOrOrthRadius a.left a.right = line[ℝ, cfg.D, cfg.E] := by
    rw [haL, haR, lineOrOrthRadius_of_ne cfg.E_ne_D.symm]
  have hF_int : cfg.F ∈ a.interior := Arc.mem_interior_through hDs' hFs' hEs' cfg.F_ne_D cfg.F_ne_E
  -- `O` lies in the opposite arc's interior, because it is on the opposite side of `DE` from `F`
  have hne : a.left ≠ a.right := by
    rw [haL, haR]
    exact cfg.E_ne_D.symm
  have hFss : (line[ℝ, cfg.D, cfg.E]).SSameSide a.mid cfg.F := by
    have h := hF_int.2; rwa [hLeq] at h
  have hmid_opp : (line[ℝ, cfg.D, cfg.E]).SOppSide a.mid a.opposite.mid := by
    have h := Arc.sOppSide_mid_opposite_mid a hne
    rwa [hLeq] at h
  have hoppO : (line[ℝ, cfg.D, cfg.E]).SSameSide a.opposite.mid cfg.ω.center :=
    hmid_opp.symm.trans (hFss.trans_sOppSide cfg.sOppSide_line_DE)
  have hO_int : cfg.ω.center ∈ a.opposite.interior := by
    refine ⟨hOs', ?_⟩
    show (s'.lineOrOrthRadius a.opposite.left a.opposite.right).SSameSide a.opposite.mid cfg.ω.center
    rw [Arc.opposite_left, Arc.opposite_right, hLeq]
    exact hoppO
  -- opposite inscribed angles on `s'` subtending `DE` are supplementary
  have key := Arc.angle_add_angle_opposite_eq_pi a hO_int hF_int
    (by rw [haL]; exact cfg.D_ne_center.symm) (by rw [haR]; exact cfg.E_ne_center.symm)
    (by rw [haL]; exact cfg.F_ne_D) (by rw [haR]; exact cfg.F_ne_E)
  rw [haL, haR] at key
  rw [angle_comm cfg.E cfg.F cfg.D]
  linarith [key]

/-! ### Configuration / side facts (route 1)

These extract the orientation information implicit in the figure (which the informal solution reads
off the diagram) from the arc hypothesis `E ∈ interior(avoiding B A D)`. -/

/-- `A` and `E` lie on strictly opposite sides of the chord `BD`.  This is the orientation content
of the hypothesis `E ∈ interior(avoiding B A D)`: `A` is in the interior of the arc `B → D` through
`A`, while `E` is in the interior of the opposite arc. -/
theorem sOppSide_BD_A_E : (cfg.ω.lineOrOrthRadius cfg.B cfg.D).SOppSide cfg.A cfg.E := by
  set tA : Arc cfg.ω := Arc.through cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D with htA
  have hLeft : tA.left = cfg.B := rfl
  have hRight : tA.right = cfg.D :=
    Arc.through_right cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D
  have hA_int : cfg.A ∈ tA.interior :=
    Arc.mem_interior_through cfg.B_mem_ω cfg.A_mem_ω cfg.D_mem_ω cfg.A_ne_B cfg.A_ne_D
  have hE_int : cfg.E ∈ tA.opposite.interior := cfg.E_mem_interior_arc_BD
  have h := Arc.sOppSide_of_mem_interior_of_mem_opposite_interior tA
    (by rw [hLeft, hRight]; exact cfg.B_ne_D) hA_int hE_int
  rwa [hLeft, hRight] at h

omit [Fact (finrank ℝ V = 2)] in
/-- A non-endpoint point of the diameter circle cannot lie on the diameter line. -/
theorem D_not_mem_line_AB : cfg.D ∉ line[ℝ, cfg.A, cfg.B] := by
  rw [← lineOrOrthRadius_of_ne (s := cfg.ω) cfg.A_ne_B]
  exact not_mem_lineOrOrthRadius_of_mem_sphere cfg.A_mem_ω cfg.D_mem cfg.B_mem_ω
    cfg.A_ne_D.symm cfg.B_ne_D.symm

omit [Fact (finrank ℝ V = 2)] in
/-- The interior point `C` is not on the chord line `BD`. -/
theorem C_not_mem_line_BD : cfg.C ∉ cfg.ω.lineOrOrthRadius cfg.B cfg.D := by
  intro hCline
  rw [lineOrOrthRadius_of_ne cfg.B_ne_D] at hCline
  have hBC_eq_BD : line[ℝ, cfg.B, cfg.C] = line[ℝ, cfg.B, cfg.D] :=
    affineSpan_pair_eq_of_right_mem_of_ne hCline cfg.sbtw_A_C_B.ne_right
  have hBC_eq_AB : line[ℝ, cfg.B, cfg.C] = line[ℝ, cfg.A, cfg.B] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
      cfg.sbtw_A_C_B.wbtw.mem_affineSpan
      cfg.sbtw_A_C_B.right_ne
  apply cfg.D_not_mem_line_AB
  have hD_BC : cfg.D ∈ line[ℝ, cfg.B, cfg.C] := by
    rw [hBC_eq_BD]
    exact right_mem_affineSpan_pair ℝ cfg.B cfg.D
  rwa [hBC_eq_AB] at hD_BC

/-- A non-endpoint point of the diameter circle cannot lie on the diameter line. -/
theorem E_not_mem_line_AB : cfg.E ∉ line[ℝ, cfg.A, cfg.B] := by
  rw [← lineOrOrthRadius_of_ne (s := cfg.ω) cfg.A_ne_B]
  exact not_mem_lineOrOrthRadius_of_mem_sphere cfg.A_mem_ω cfg.E_mem cfg.B_mem_ω
    cfg.E_ne_A cfg.E_ne_B

/-- `A` and `C` lie on the same side of the chord line `BD`. -/
theorem sSameSide_BD_A_C : (cfg.ω.lineOrOrthRadius cfg.B cfg.D).SSameSide cfg.A cfg.C := by
  refine ⟨cfg.sbtw_A_C_B.wbtw.wSameSide₁₂ left_mem_lineOrOrthRadius,
    cfg.sOppSide_BD_A_E.left_notMem, cfg.C_not_mem_line_BD⟩

/-- Consequently, `C` and `E` lie on opposite sides of the chord line `BD`. -/
theorem sOppSide_BD_C_E : (cfg.ω.lineOrOrthRadius cfg.B cfg.D).SOppSide cfg.C cfg.E :=
  cfg.sSameSide_BD_A_C.symm.trans_sOppSide cfg.sOppSide_BD_A_E

/-- The line `CE` meets the chord `BD` at a point inside the chord. -/
theorem exists_sbtw_B_X_D_and_C_X_E :
    ∃ X, Sbtw ℝ cfg.B X cfg.D ∧ Sbtw ℝ cfg.C X cfg.E := by
  obtain ⟨X, hX_BD, hC_X_E⟩ := cfg.sOppSide_BD_C_E.exists_sbtw
  have hX_BD_line : X ∈ line[ℝ, cfg.B, cfg.D] := by
    rwa [lineOrOrthRadius_of_ne cfg.B_ne_D] at hX_BD
  have hX_inside : dist cfg.ω.center X < cfg.ω.radius := by
    rw [dist_comm]
    refine (hC_X_E.dist_lt_max_dist cfg.ω.center).trans_le (max_le ?_ ?_)
    · rw [dist_comm]; exact cfg.dist_center_C_lt_radius.le
    · exact (mem_sphere.mp cfg.E_mem).le
  have hcolBXD : Collinear ℝ ({cfg.B, X, cfg.D} : Set Pt) := by
    simpa [Set.insert_comm] using collinear_insert_of_mem_affineSpan_pair hX_BD_line
  exact ⟨X, sbtw_of_collinear_of_dist_center_lt_radius hcolBXD cfg.B_mem_ω
    (by rwa [dist_comm]) cfg.D_mem_ω cfg.B_ne_D, hC_X_E⟩

/-- `D` and `E` lie on the same strict side of the diameter line `AB`.

This is derived from the arc hypothesis rather than assumed: the line `CE` meets the chord `BD`
at a point `X`; then `B-X-D` and `C-X-E` force `X`, `D`, and `E` to be in the same open half-plane
bounded by `AB`. -/
theorem sSameSide_AB_D_E : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.D cfg.E := by
  obtain ⟨X, hBXD, hC_X_E⟩ := cfg.exists_sbtw_B_X_D_and_C_X_E
  have hB_mem_AB : cfg.B ∈ line[ℝ, cfg.A, cfg.B] :=
    right_mem_affineSpan_pair ℝ cfg.A cfg.B
  have hC_mem_AB : cfg.C ∈ line[ℝ, cfg.A, cfg.B] :=
    cfg.sbtw_A_C_B.wbtw.mem_affineSpan
  have hX_not_AB : X ∉ line[ℝ, cfg.A, cfg.B] := by
    intro hX_AB
    apply cfg.D_not_mem_line_AB
    have hD_BX : cfg.D ∈ line[ℝ, cfg.B, X] := hBXD.right_mem_affineSpan
    have hBX_eq_AB : line[ℝ, cfg.B, X] = line[ℝ, cfg.A, cfg.B] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne hB_mem_AB hX_AB hBXD.ne_left.symm
    rwa [hBX_eq_AB] at hD_BX
  have hXD : (line[ℝ, cfg.A, cfg.B]).SSameSide X cfg.D :=
    ⟨hBXD.wbtw.wSameSide₂₃ hB_mem_AB, hX_not_AB, cfg.D_not_mem_line_AB⟩
  have hXE : (line[ℝ, cfg.A, cfg.B]).SSameSide X cfg.E :=
    ⟨hC_X_E.wbtw.wSameSide₂₃ hC_mem_AB, hX_not_AB, cfg.E_not_mem_line_AB⟩
  exact hXD.symm.trans hXE

/-! ### Milestone 2 (concyclic crux): `∠DOE = ∠DCE` -/

/-- **Reflection crux.** Reflecting `E` across the diameter line turns the hypothesis into the
collinearity needed to compare both angles with the same doubled inscribed angle. -/
theorem angle_DOE_eq_angle_DCE :
    ∠ cfg.D cfg.ω.center cfg.E = ∠ cfg.D cfg.C cfg.E := by
  classical
  let L : AffineSubspace ℝ Pt := line[ℝ, cfg.A, cfg.B]
  let E' : Pt := EuclideanGeometry.reflection L cfg.E
  have hB_mem_L : cfg.B ∈ L := right_mem_affineSpan_pair ℝ cfg.A cfg.B
  have hC_mem_L : cfg.C ∈ L := cfg.sbtw_A_C_B.wbtw.mem_affineSpan
  have hO_mem_L : cfg.ω.center ∈ L := by
    rw [cfg.center_eq_midpoint]
    exact (wbtw_midpoint ℝ cfg.A cfg.B).mem_affineSpan
  have hB_fix : EuclideanGeometry.reflection L cfg.B = cfg.B :=
    (reflection_eq_self_iff cfg.B).mpr hB_mem_L
  have hC_fix : EuclideanGeometry.reflection L cfg.C = cfg.C :=
    (reflection_eq_self_iff cfg.C).mpr hC_mem_L
  have hO_fix : EuclideanGeometry.reflection L cfg.ω.center = cfg.ω.center :=
    (reflection_eq_self_iff cfg.ω.center).mpr hO_mem_L
  have h_ref_angle : ∠ E' cfg.C cfg.B = ∠ cfg.E cfg.C cfg.B := by
    have h := (EuclideanGeometry.reflection L).toAffineIsometry.angle_map cfg.E cfg.C cfg.B
    simpa [E', hB_fix, hC_fix] using h
  have h_angle : ∠ cfg.A cfg.C cfg.D = ∠ cfg.B cfg.C E' := by
    rw [angle_comm cfg.B cfg.C E', h_ref_angle]
    exact cfg.angle_ACD_eq_ECB
  have hE'_ne_C : E' ≠ cfg.C := by
    intro h
    apply cfg.C_ne_E
    have h' : EuclideanGeometry.reflection L E' = EuclideanGeometry.reflection L cfg.C := by
      rw [h]
    symm
    simpa [E', hC_fix] using h'
  have hD_E'_opp : L.SOppSide cfg.D E' := by
    have hE_E'_opp : L.SOppSide cfg.E E' := by
      let P : Pt := (orthogonalProjection L cfg.E : Pt)
      have hP_mem : P ∈ L := by
        dsimp [P]
        exact orthogonalProjection_mem cfg.E
      have hE_not : cfg.E ∉ L := by
        simpa [L] using cfg.E_not_mem_line_AB
      have hE'_eq : E' = (AffineEquiv.pointReflection ℝ P) cfg.E := by
        dsimp [E', P]
        rw [EuclideanGeometry.reflection_apply']
        rfl
      rw [hE'_eq]
      exact AffineSubspace.sOppSide_pointReflection hP_mem hE_not
    exact cfg.sSameSide_AB_D_E.trans_sOppSide hE_E'_opp
  have hsign : (∡ cfg.A cfg.C cfg.D).sign = (∡ cfg.B cfg.C E').sign := by
    have hCD_B : (∡ cfg.C cfg.D cfg.B).sign = (∡ cfg.A cfg.D cfg.C).sign :=
      (cfg.sbtw_A_C_B.oangle_sign_eq cfg.D).symm
    have hCDA : (∡ cfg.C cfg.D cfg.A).sign = -(∡ cfg.C cfg.D cfg.B).sign := by
      rw [hCD_B, ← oangle_swap₁₃_sign cfg.A cfg.D cfg.C]
    have hCEB : (∡ cfg.C E' cfg.B).sign = -(∡ cfg.C cfg.D cfg.B).sign :=
      hD_E'_opp.oangle_sign_eq_neg hC_mem_L hB_mem_L
    rw [← oangle_rotate_sign cfg.A cfg.C cfg.D,
      ← oangle_rotate_sign cfg.B cfg.C E', hCDA, hCEB]
  have ho : ∡ cfg.A cfg.C cfg.D = ∡ cfg.B cfg.C E' :=
    oangle_eq_of_angle_eq_of_sign_eq h_angle hsign
  have hleft : ∡ cfg.A cfg.C cfg.D = ∡ cfg.B cfg.C cfg.D + π :=
    cfg.sbtw_A_C_B.oangle_eq_add_pi_left cfg.C_ne_D.symm
  have hadd := oangle_add cfg.sbtw_A_C_B.right_ne cfg.C_ne_D.symm hE'_ne_C
  have hπ : ∡ cfg.D cfg.C E' = π := by
    rw [← ho, hleft] at hadd
    exact add_left_cancel hadd
  have hS : Sbtw ℝ cfg.D cfg.C E' := oangle_eq_pi_iff_sbtw.mp hπ
  have hE'_mem : E' ∈ cfg.ω := by
    rw [mem_sphere]
    have hdist := (EuclideanGeometry.reflection L).dist_map cfg.E cfg.ω.center
    simpa [E', hO_fix] using hdist.trans (mem_sphere.mp cfg.E_mem)
  have hE'_ne_E : E' ≠ cfg.E := by
    intro h
    have hfix : EuclideanGeometry.reflection L cfg.E = cfg.E := by
      simpa [E'] using h
    exact cfg.E_not_mem_line_AB ((reflection_eq_self_iff cfg.E).mp hfix)
  have hE'_ne_D : E' ≠ cfg.D := hS.left_ne_right.symm
  have hCE' : dist cfg.C E' = dist cfg.C cfg.E := by
    simpa [E'] using dist_reflection_eq_of_mem L hC_mem_L cfg.E
  have hbase : ∠ cfg.C E' cfg.E = ∠ cfg.C cfg.E E' :=
    angle_eq_angle_of_dist_eq hCE'
  have htri := angle_add_angle_add_angle_eq_pi cfg.E hE'_ne_C
  have htri2 : 2 * ∠ cfg.C E' cfg.E + ∠ cfg.E cfg.C E' = π := by
    linarith [htri, hbase, angle_comm E' cfg.E cfg.C]
  have hstraight := angle_add_angle_eq_pi_of_angle_eq_pi cfg.E hS.angle₁₂₃_eq_pi
  have hstraight2 : ∠ cfg.D cfg.C cfg.E + ∠ cfg.E cfg.C E' = π := by
    rwa [angle_comm cfg.E cfg.C cfg.D] at hstraight
  have hC_to_D : ∠ cfg.C E' cfg.E = ∠ cfg.D E' cfg.E :=
    hS.symm.angle_eq_left cfg.E
  have hDCE_two : ∠ cfg.D cfg.C cfg.E = 2 * ∠ cfg.D E' cfg.E := by
    linarith [htri2, hstraight2, hC_to_D]
  have hDOE_two : ∠ cfg.D cfg.ω.center cfg.E = 2 * ∠ cfg.D E' cfg.E := by
    exact cfg.ω.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi
      cfg.D_mem hE'_mem cfg.E_mem hE'_ne_D hE'_ne_E
      (by linarith [hDCE_two, angle_le_pi cfg.D cfg.C cfg.E])
  linarith

/-! ### Milestone 3 (straight line / ray split) -/

omit [Fact (finrank ℝ V = 2)] in
/-- Straight-line split at `C`: since `A, C, B` are collinear with `C` strictly between `A` and
`B`, the angles `∠ACD` and `∠DCB` are supplementary.  (Fully proved.) -/
theorem angle_ACD_add_angle_DCB_eq_pi :
    ∠ cfg.A cfg.C cfg.D + ∠ cfg.D cfg.C cfg.B = π := by
  have hπ : ∠ cfg.A cfg.C cfg.B = π := cfg.sbtw_A_C_B.angle₁₂₃_eq_pi
  have h := angle_add_angle_eq_pi_of_angle_eq_pi cfg.D hπ
  rwa [angle_comm cfg.D cfg.C cfg.A] at h

/-- Ray split at `C`: the line `CE` meets the chord line `BD` at a point `X`, and the circle
interior test gives `B-X-D`.  Thus the ray `CE` is the same as the ray `CX`, which lies inside
`∠DCB`, so `∠DCB = ∠DCE + ∠ECB`. -/
theorem angle_DCB_eq_angle_DCE_add_angle_ECB :
    ∠ cfg.D cfg.C cfg.B = ∠ cfg.D cfg.C cfg.E + ∠ cfg.E cfg.C cfg.B := by
  obtain ⟨X, hBXD, hC_X_E⟩ := cfg.exists_sbtw_B_X_D_and_C_X_E
  have hDXB : Sbtw ℝ cfg.D X cfg.B := hBXD.symm
  have hsame : SameRay ℝ (X -ᵥ cfg.C) (cfg.E -ᵥ cfg.C) :=
    hC_X_E.wbtw.sameRay_vsub_left
  exact (angle_add_angle_eq_of_sbtw_of_sameRay hDXB hsame cfg.C_ne_E.symm).symm

/-! ### Assembling the milestones -/

/-- The configuration-level conclusion `∠EFD = ∠ACD + ∠ECB`, assembled from the three milestones.
The hypothesis `∠ACD = ∠ECB` enters only through `angle_DOE_eq_angle_DCE`. -/
theorem main : ∠ cfg.E cfg.F cfg.D = ∠ cfg.A cfg.C cfg.D + ∠ cfg.E cfg.C cfg.B := by
  rw [cfg.angle_EFD_eq_pi_sub_angle_DOE, cfg.angle_DOE_eq_angle_DCE]
  linarith [cfg.angle_ACD_add_angle_DCB_eq_pi, cfg.angle_DCB_eq_angle_DCE_add_angle_ECB]

end Cfg

/-- BMO Round 1, 2018 Problem 4
Let Γ be a semicircle with diameter AB. The point C lies on the diameter AB and points
E and D lie on the arc BA, with E between B and D. Let the tangents to Γ at D and E
meet at F. Suppose that ∠ACD = ∠ECB.
Prove that ∠EFD = ∠ACD + ∠ECB. -/
theorem result [Fact (finrank ℝ V = 2)]
    {A B C D E F : Pt}
    {ω : Sphere Pt}
    (A_ne_B : A ≠ B)
    (ω_eq : ω = Sphere.ofDiameter A B)
    (sbtw_A_C_B : Sbtw ℝ A C B)
    -- (derivable from ω_eq; kept for Arc.avoiding construction)
    (A_mem_ω : A ∈ (ω : Set Pt))
    (B_mem_ω : B ∈ (ω : Set Pt))
    (D_mem_ω : D ∈ (ω : Set Pt))
    (A_ne_D : A ≠ D)
    (B_ne_D : B ≠ D)
    (E_mem_interior_arc_BD :
      E ∈ (Sphere.Arc.avoiding B_mem_ω A_mem_ω D_mem_ω A_ne_B A_ne_D).interior)
    (isTangentAt_D : ω.IsTangentAt D line[ℝ, F, D])
    (isTangentAt_E : ω.IsTangentAt E line[ℝ, F, E])
    (angle_ACD_eq_ECB : ∠ A C D = ∠ E C B)
    : ∠ E F D = ∠ A C D + ∠ E C B :=
  (⟨A, B, C, D, E, F, ω, A_ne_B, ω_eq, sbtw_A_C_B, A_mem_ω, B_mem_ω, D_mem_ω, A_ne_D, B_ne_D,
      E_mem_interior_arc_BD, isTangentAt_D, isTangentAt_E, angle_ACD_eq_ECB⟩ :
    Cfg V Pt).main

end BMO1_2018P4
