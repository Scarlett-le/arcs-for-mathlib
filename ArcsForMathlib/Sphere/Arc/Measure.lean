/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import ArcsForMathlib.Sphere.Arc.Structure
public import ArcsForMathlib.Sphere.Arc.Degenerate
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Arc Measure

This file defines the measure of an arc on a sphere and proves basic properties relating it to
chord length, inscribed angles, and the `minor` / `major` / `through` constructions.

## Main definitions

* `EuclideanGeometry.Sphere.Arc.measure`: The measure of an arc, a real number in `[0, 2π]`.
* `EuclideanGeometry.Sphere.Arc.midpoint`: The measure-bisecting midpoint of an arc.

## Main results

* `EuclideanGeometry.Sphere.Arc.measure_opposite`: opposite arcs have measures summing to `2π`.
* `EuclideanGeometry.Sphere.Arc.measure_minor` / `measure_major`: the measure of the minor arc
  is the central angle, and the measure of the major arc is `2π` minus the central angle.
* `EuclideanGeometry.Sphere.Arc.measure_through_eq_angle_add_angle_of_mem_minor_interior`:
  the measure of an arc through an interior point of the minor arc splits as the sum of two
  central angles.
* `EuclideanGeometry.Sphere.Arc.dist_eq_of_measure_eq`: equal measure gives equal chord length.
* `EuclideanGeometry.Sphere.Arc.midpoint_eq_mid`: the measure-bisecting midpoint coincides with
  the structural mid.
* `EuclideanGeometry.Sphere.Arc.inscribed_angle_eq_half_measure`: the inscribed angle theorem,
  stated via arc measure.
-/

@[expose] public section

namespace EuclideanGeometry

namespace Sphere

namespace Arc

open scoped EuclideanGeometry RealInnerProductSpace Real

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable {s : Sphere P}

noncomputable section

/-! ### Measure and basic scalar properties -/

open Classical in
/-- The measure of an arc, a real number in `[0, 2π]` giving the central angle it subtends.
If `s.radius = 0` the measure is `0`. Otherwise it is `∠ a.left s.center a.right` when `a.mid` is
not strictly on the same side of the chord as `s.center`, and `2π` minus that angle when it is. -/
def measure (a : Arc s) : ℝ :=
  if s.radius = 0 then 0
  else if (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center then
    2 * π - ∠ a.left s.center a.right
  else
    ∠ a.left s.center a.right

/-- Arc measure is nonnegative. -/
theorem measure_nonneg (a : Arc s) : 0 ≤ a.measure := by
  rw [measure]
  split_ifs <;> linarith
    [Real.pi_pos, angle_nonneg a.left s.center a.right, angle_le_pi a.left s.center a.right]

/-- Arc measure is at most `2π`. -/
theorem measure_le_two_pi (a : Arc s) : a.measure ≤ 2 * π := by
  rw [measure]
  split_ifs <;> linarith
    [Real.pi_pos, angle_nonneg a.left s.center a.right, angle_le_pi a.left s.center a.right]

/-- A single-point arc has measure zero. -/
theorem measure_eq_zero_of_isSinglePoint (a : Arc s) (h : a.IsSinglePoint) :
    a.measure = 0 := by
  rw [measure]
  split_ifs with hr hss
  · rfl
  · exfalso
    apply hss.2.1
    rw [h]
    exact left_mem_lineOrOrthRadius
  · rw [← left_eq_right_of_isSinglePoint a h]
    apply angle_self_of_ne
    intro heq
    have hdist := mem_sphere.mp a.left_mem
    rw [heq, dist_self] at hdist
    exact hr hdist.symm

/-- A full-circle arc has measure `2π`. -/
theorem measure_eq_two_pi_of_isFullCircle (a : Arc s)
    (hr : s.radius ≠ 0) (h : a.IsFullCircle) :
    a.measure = 2 * π := by
  have h_lr := left_eq_right_of_isFullCircle a h
  have h_mid := mid_eq_pointReflection_center_left_of_isFullCircle a h
  have h_left_ne_center : a.left ≠ s.center := by
    intro heq
    have hdist := mem_sphere.mp a.left_mem
    rw [heq, dist_self] at hdist
    exact hr hdist.symm
  have hradius : ‖a.left -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.left_mem
  have hr_sq_pos : 0 < s.radius ^ 2 := by
    have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr
    positivity
  have h_mid_sub : a.mid -ᵥ a.left = (2 : ℝ) • (s.center -ᵥ a.left) := by
    rw [h_mid, AffineEquiv.pointReflection_apply, vadd_vsub_assoc]
    module
  have hL_eq : s.lineOrOrthRadius a.left a.right = s.orthRadius a.left := by
    rw [h_lr]; exact lineOrOrthRadius_of_eq rfl
  have h_inner_self : ⟪s.center -ᵥ a.left, a.left -ᵥ s.center⟫ = -(s.radius ^ 2) := by
    rw [show s.center -ᵥ a.left = -(a.left -ᵥ s.center : V) from
          (neg_vsub_eq_vsub_rev _ _).symm,
        inner_neg_left, real_inner_self_eq_norm_sq, hradius]
  have hcenter_not_L : s.center ∉ s.lineOrOrthRadius a.left a.right := by
    rw [hL_eq, mem_orthRadius_iff_inner_left, h_inner_self]
    linarith
  have hmid_not_L : a.mid ∉ s.lineOrOrthRadius a.left a.right := by
    rw [hL_eq, mem_orthRadius_iff_inner_left, h_mid_sub, real_inner_smul_left,
        h_inner_self]
    linarith
  have hSS : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
    refine AffineSubspace.sSameSide_of_vsub_eq_smul
      (m := s.center -ᵥ a.left) (c₁ := 2) (c₂ := 1)
      left_mem_lineOrOrthRadius left_mem_lineOrOrthRadius h_mid_sub ?_ ?_
      hmid_not_L hcenter_not_L
    · rw [one_smul]
    · norm_num
  rw [measure, if_neg hr, if_pos hSS, ← h_lr,
      angle_self_of_ne h_left_ne_center]
  ring

/-- On a sphere of nonzero radius, an arc has measure zero if and only if it is a single point. -/
theorem measure_eq_zero_iff_isSinglePoint (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = 0 ↔ a.IsSinglePoint := by
  refine ⟨fun hmeas => ?_, measure_eq_zero_of_isSinglePoint a⟩
  have hangle_zero : ∠ a.left s.center a.right = 0 := by
    rw [measure, if_neg hr] at hmeas
    split_ifs at hmeas with hss
    · linarith [angle_le_pi a.left s.center a.right, Real.pi_pos]
    · exact hmeas
  rcases isSinglePoint_or_isFullCircle_of_left_eq_right a
      ((angle_center_eq_zero_iff_eq a.left_mem a.right_mem hr).mp hangle_zero) with hsp | hfc
  · exact hsp
  · exfalso
    have h2 := measure_eq_two_pi_of_isFullCircle a hr hfc
    rw [hmeas] at h2
    linarith [Real.pi_pos]

/-- On a sphere of nonzero radius, an arc has measure `2π` if and only if it is a full circle. -/
theorem measure_eq_two_pi_iff_isFullCircle (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = 2 * π ↔ a.IsFullCircle := by
  refine ⟨fun hmeas => ?_, measure_eq_two_pi_of_isFullCircle a hr⟩
  have hangle_zero : ∠ a.left s.center a.right = 0 := by
    rw [measure, if_neg hr] at hmeas
    split_ifs at hmeas with hss
    · linarith
    · exfalso
      linarith [angle_le_pi a.left s.center a.right, Real.pi_pos]
  rcases isSinglePoint_or_isFullCircle_of_left_eq_right a
      ((angle_center_eq_zero_iff_eq a.left_mem a.right_mem hr).mp hangle_zero) with hsp | hfc
  · exfalso
    have h0 := measure_eq_zero_of_isSinglePoint a hsp
    rw [h0] at hmeas
    linarith [Real.pi_pos]
  · exact hfc

/-! ### Measure of opposite arcs -/

/-- An arc's measure equals its central angle if and only if `a.mid` is not strictly on the same
side of the chord as `s.center`. -/
theorem measure_eq_angle_iff_not_sSameSide (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = ∠ a.left s.center a.right ↔
      ¬(s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
  rw [measure, if_neg hr]
  refine ⟨fun hmeas hss => ?_, fun hnss => ?_⟩
  · rw [if_pos hss] at hmeas
    have h_pi : ∠ a.left s.center a.right = π := by linarith
    have h_sbtw : Sbtw ℝ a.left s.center a.right :=
      angle_eq_pi_iff_sbtw.mp h_pi
    have hne : a.left ≠ a.right := h_sbtw.left_ne_right
    have h_mem : s.center ∈ s.lineOrOrthRadius a.left a.right := by
      rw [lineOrOrthRadius_of_ne hne]; exact h_sbtw.wbtw.mem_affineSpan
    exact hss.2.2 h_mem
  · rw [if_neg hnss]

/-- On a sphere of nonzero radius, an arc with distinct endpoints has measure `π` if and only if
its endpoints are diametrically opposite. -/
theorem measure_eq_pi_iff_isDiameter (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = π ↔ s.IsDiameter a.left a.right := by
  rw [← angle_center_eq_pi_iff_isDiameter a.left_mem a.right_mem hr, measure, if_neg hr]
  split_ifs with hss
  · constructor <;> intro h <;> linarith
  · rfl

/-- The opposite arc has measure `2π` minus the arc's measure. -/
theorem measure_opposite [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hr : s.radius ≠ 0) :
    a.opposite.measure = 2 * π - a.measure := by
  have h_left_ne_center : a.left ≠ s.center := fun heq => by
    have := mem_sphere.mp a.left_mem
    rw [heq, dist_self] at this
    exact hr this.symm
  by_cases hLR : a.left = a.right
  · rcases isSinglePoint_or_isFullCircle_of_left_eq_right a hLR with hsp | hfc
    · have h_a : a.measure = 0 := measure_eq_zero_of_isSinglePoint a hsp
      have h_opp_full : a.opposite.IsFullCircle := by
        refine ⟨?_, ?_⟩
        · show a.left = a.opposite.right
          rw [opposite_right]; exact hLR
        · show AffineEquiv.pointReflection ℝ s.center a.mid ≠ a.left
          rw [hsp]
          intro h
          rw [AffineEquiv.pointReflection_fixed_iff_of_module] at h
          exact h_left_ne_center h
      have h_b : a.opposite.measure = 2 * π :=
        measure_eq_two_pi_of_isFullCircle a.opposite hr h_opp_full
      linarith
    · have h_a : a.measure = 2 * π := measure_eq_two_pi_of_isFullCircle a hr hfc
      have h_opp_sp : a.opposite.IsSinglePoint := by
        show AffineEquiv.pointReflection ℝ s.center a.mid = a.left
        rw [mid_eq_pointReflection_center_left_of_isFullCircle a hfc]
        exact AffineEquiv.pointReflection_involutive ℝ s.center a.left
      have h_b : a.opposite.measure = 0 :=
        measure_eq_zero_of_isSinglePoint a.opposite h_opp_sp
      linarith
  · by_cases hcenter : s.center ∈ line[ℝ, a.left, a.right]
    · have h_diam : s.IsDiameter a.left a.right :=
        (Sphere.center_mem_affineSpan_pair_iff_isDiameter a.left_mem a.right_mem hLR).mp hcenter
      have h_diam_opp : s.IsDiameter a.opposite.left a.opposite.right := by
        show s.IsDiameter a.left a.opposite.right
        rw [opposite_right]; exact h_diam
      have h_a : a.measure = π :=
        (measure_eq_pi_iff_isDiameter a hr).mpr h_diam
      have h_b : a.opposite.measure = π :=
        (measure_eq_pi_iff_isDiameter a.opposite hr).mpr h_diam_opp
      linarith
    · have h_iff := sSameSide_opposite_mid_iff a hLR hcenter
      have hL_eq : s.lineOrOrthRadius a.opposite.left a.opposite.right =
                   s.lineOrOrthRadius a.left a.right := by
        show s.lineOrOrthRadius a.left a.opposite.right = _
        rw [opposite_right]
      have hθ_eq : ∠ a.opposite.left s.center a.opposite.right =
                   ∠ a.left s.center a.right := by
        show ∠ a.left s.center a.opposite.right = _
        rw [opposite_right]
      by_cases hss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
      · have h_opp_not :
            ¬ (s.lineOrOrthRadius a.opposite.left a.opposite.right).SSameSide
              a.opposite.mid s.center := by
          rw [hL_eq]; exact fun h => h_iff.mp h hss
        have h_a : a.measure = 2 * π - ∠ a.left s.center a.right := by
          rw [measure, if_neg hr, if_pos hss]
        have h_b : a.opposite.measure = ∠ a.left s.center a.right := by
          have ho := (measure_eq_angle_iff_not_sSameSide a.opposite hr).mpr h_opp_not
          rw [ho, hθ_eq]
        linarith
      · have h_opp_yes :
            (s.lineOrOrthRadius a.opposite.left a.opposite.right).SSameSide
              a.opposite.mid s.center := by
          rw [hL_eq]; exact h_iff.mpr hss
        have h_a : a.measure = ∠ a.left s.center a.right :=
          (measure_eq_angle_iff_not_sSameSide a hr).mpr hss
        have h_b : a.opposite.measure = 2 * π - ∠ a.left s.center a.right := by
          rw [measure, if_neg hr, if_pos h_opp_yes, hθ_eq]
        linarith

/-- An arc and its opposite have measures summing to `2π`. -/
theorem measure_add_measure_opposite [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure + a.opposite.measure = 2 * π := by
  rw [measure_opposite a hr]; ring

/-! ### Measure on minor and major arcs -/

/-- The displacement from the sphere center to any point on the chord line (or the orthogonal
radius in the equal-endpoint case) has constant inner product with the minor midpoint direction. -/
theorem inner_vsub_center_minorMidpoint_of_mem_lineOrOrthRadius
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C)
    {p : P} (hp : p ∈ s.lineOrOrthRadius A C) :
    ⟪p -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫ =
      s.radius * ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖ / 2 := by
  have hr_ne : s.radius ≠ 0 := fun hr0 => hND ⟨hA, by
    have hA_eq : A = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hA).trans hr0)
    have hC_eq : C = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hC).trans hr0)
    rw [hA_eq, hC_eq, midpoint_self]⟩
  have hr_pos : 0 < s.radius := radius_pos_of_mem hA hr_ne
  have hA_norm : ‖A -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hA
  have hC_norm : ‖C -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hC
  set v : V := (A -ᵥ s.center) + (C -ᵥ s.center) with hv_def
  have hv_ne : v ≠ 0 := sum_vsub_center_ne_zero_of_not_isDiameter hA hND
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hM_sub : (minor hA hC hND).mid -ᵥ s.center = (s.radius / ‖v‖) • v := by
    rw [minor_mid, vadd_vsub]
  have h_v_norm_sq :
      ‖v‖ ^ 2 = 2 * s.radius ^ 2 + 2 * ⟪A -ᵥ s.center, C -ᵥ s.center⟫ := by
    have hh : ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖ ^ 2 =
        ‖A -ᵥ s.center‖ ^ 2 + 2 * ⟪A -ᵥ s.center, C -ᵥ s.center⟫
          + ‖C -ᵥ s.center‖ ^ 2 := norm_add_sq_real _ _
    rw [hA_norm, hC_norm, ← hv_def] at hh
    linarith
  have h_AC_inner :
      ⟪A -ᵥ s.center, C -ᵥ s.center⟫ = (‖v‖ ^ 2 - 2 * s.radius ^ 2) / 2 := by linarith
  have h_A_v_inner : ⟪A -ᵥ s.center, v⟫ = ‖v‖ ^ 2 / 2 := by
    show ⟪A -ᵥ s.center, (A -ᵥ s.center) + (C -ᵥ s.center)⟫ = _
    rw [inner_add_right, real_inner_self_eq_norm_sq, hA_norm, h_AC_inner]
    ring
  have h_C_v_inner : ⟪C -ᵥ s.center, v⟫ = ‖v‖ ^ 2 / 2 := by
    show ⟪C -ᵥ s.center, (A -ᵥ s.center) + (C -ᵥ s.center)⟫ = _
    rw [inner_add_right, real_inner_self_eq_norm_sq, hC_norm,
        real_inner_comm (A -ᵥ s.center) (C -ᵥ s.center), h_AC_inner]
    ring
  have h_A_M_inner :
      ⟪A -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫ = s.radius * ‖v‖ / 2 := by
    rw [hM_sub, real_inner_smul_right, h_A_v_inner]
    field_simp
  have h_C_M_inner :
      ⟪C -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫ = s.radius * ‖v‖ / 2 := by
    rw [hM_sub, real_inner_smul_right, h_C_v_inner]
    field_simp
  by_cases hAC : A = C
  · rw [lineOrOrthRadius_of_eq hAC, mem_orthRadius_iff_inner_left] at hp
    have h_v_eq : v = (2 : ℝ) • (A -ᵥ s.center) := by
      show (A -ᵥ s.center) + (C -ᵥ s.center) = _
      rw [← hAC, two_smul]
    have h_v_norm : ‖v‖ = 2 * s.radius := by
      rw [h_v_eq, norm_smul, Real.norm_eq_abs, abs_of_pos two_pos, hA_norm]
    have hM_eq_A_sub : (minor hA hC hND).mid -ᵥ s.center = A -ᵥ s.center := by
      rw [hM_sub, h_v_norm, h_v_eq, smul_smul,
          show s.radius / (2 * s.radius) * 2 = 1 from by field_simp,
          one_smul]
    rw [hM_eq_A_sub,
        show (p -ᵥ s.center : V) = (p -ᵥ A) + (A -ᵥ s.center) from
          (vsub_add_vsub_cancel _ _ _).symm,
        inner_add_left, hp, zero_add, real_inner_self_eq_norm_sq, hA_norm,
        h_v_norm]
    ring
  · rw [lineOrOrthRadius_of_ne hAC] at hp
    have hm_perp_d :
        ⟪C -ᵥ A, (minor hA hC hND).mid -ᵥ s.center⟫ = 0 := by
      rw [show (C -ᵥ A : V) = (C -ᵥ s.center) - (A -ᵥ s.center) from
            (vsub_sub_vsub_cancel_right _ _ _).symm,
          inner_sub_left, h_C_M_inner, h_A_M_inner]
      ring
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
    rw [AffineMap.lineMap_apply] at ht
    have h_p_sub : (p -ᵥ A : V) = t • (C -ᵥ A) := by rw [← ht, vadd_vsub]
    rw [show (p -ᵥ s.center : V) = (p -ᵥ A) + (A -ᵥ s.center) from
          (vsub_add_vsub_cancel _ _ _).symm,
        h_p_sub, inner_add_left, real_inner_smul_left, hm_perp_d, mul_zero,
        zero_add, h_A_M_inner]

/-- The measure of a minor arc equals the central angle `∠ A s.center C`. -/
@[simp]
theorem measure_minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C) :
    (minor hA hC hND).measure = ∠ A s.center C := by
  have hr_ne : s.radius ≠ 0 := fun hr0 => hND ⟨hA, by
    have hA_eq : A = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hA).trans hr0)
    have hC_eq : C = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hC).trans hr0)
    rw [hA_eq, hC_eq, midpoint_self]⟩
  have hr_pos : 0 < s.radius := radius_pos_of_mem hA hr_ne
  have hA_norm : ‖A -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hA
  have hC_norm : ‖C -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hC
  set v : V := (A -ᵥ s.center) + (C -ᵥ s.center) with hv_def
  have hv_ne : v ≠ 0 := sum_vsub_center_ne_zero_of_not_isDiameter hA hND
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hv_norm_le : ‖v‖ ≤ 2 * s.radius := by
    calc ‖v‖ ≤ ‖A -ᵥ s.center‖ + ‖C -ᵥ s.center‖ := norm_add_le _ _
      _ = 2 * s.radius := by rw [hA_norm, hC_norm]; ring
  have h_M_norm : ‖(minor hA hC hND).mid -ᵥ s.center‖ = s.radius := by
    exact norm_vsub_center_eq_radius (minor hA hC hND).mid_mem
  have h_M_M_inner :
      ⟪(minor hA hC hND).mid -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫
        = s.radius ^ 2 := by
    rw [real_inner_self_eq_norm_sq, h_M_norm]
  have h_L_inner : ∀ p, p ∈ s.lineOrOrthRadius A C →
      ⟪p -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫ = s.radius * ‖v‖ / 2 := by
    intro p hp
    simpa [hv_def] using
      inner_vsub_center_minorMidpoint_of_mem_lineOrOrthRadius hA hC hND hp
  rw [measure, if_neg hr_ne]
  suffices h : ¬ (s.lineOrOrthRadius (minor hA hC hND).left (minor hA hC hND).right).SSameSide
                (minor hA hC hND).mid s.center by
    rw [if_neg h, minor_left, minor_right]
  rw [minor_left, minor_right]
  intro hss
  obtain ⟨p₁, hp₁, p₂, hp₂, hsr⟩ := hss.1
  have hα :
      ⟪(minor hA hC hND).mid -ᵥ p₁, (minor hA hC hND).mid -ᵥ s.center⟫
        = s.radius ^ 2 - s.radius * ‖v‖ / 2 := by
    rw [show ((minor hA hC hND).mid -ᵥ p₁ : V) =
            ((minor hA hC hND).mid -ᵥ s.center) - (p₁ -ᵥ s.center) from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        inner_sub_left, h_M_M_inner, h_L_inner p₁ hp₁]
  have hβ :
      ⟪s.center -ᵥ p₂, (minor hA hC hND).mid -ᵥ s.center⟫
        = -(s.radius * ‖v‖ / 2) := by
    rw [show (s.center -ᵥ p₂ : V) = -(p₂ -ᵥ s.center) from
          (neg_vsub_eq_vsub_rev _ _).symm,
        inner_neg_left, h_L_inner p₂ hp₂]
  have hα_nonneg : 0 ≤ s.radius ^ 2 - s.radius * ‖v‖ / 2 := by nlinarith
  have hβ_neg : -(s.radius * ‖v‖ / 2) < 0 := by nlinarith
  rcases hsr with hM_zero | hcen_zero | ⟨a, b, ha_pos, hb_pos, h_ab_eq⟩
  · exact hss.2.1 ((vsub_eq_zero_iff_eq.mp hM_zero).symm ▸ hp₁)
  · exact hss.2.2 ((vsub_eq_zero_iff_eq.mp hcen_zero).symm ▸ hp₂)
  · have h_inner_eq :
        a * (s.radius ^ 2 - s.radius * ‖v‖ / 2) = b * -(s.radius * ‖v‖ / 2) := by
      have := congrArg (fun x => ⟪x, (minor hA hC hND).mid -ᵥ s.center⟫) h_ab_eq
      simp only at this
      rw [real_inner_smul_left, real_inner_smul_left, hα, hβ] at this
      exact this
    nlinarith

/-- The measure of a major arc equals `2π` minus the central angle `∠ A s.center C`. -/
@[simp]
theorem measure_major {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C) :
    (major hA hC hND).measure = 2 * π - ∠ A s.center C := by
  have hr_ne : s.radius ≠ 0 := fun hr0 => hND ⟨hA, by
    have hA_eq : A = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hA).trans hr0)
    have hC_eq : C = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp hC).trans hr0)
    rw [hA_eq, hC_eq, midpoint_self]⟩
  have hr_pos : 0 < s.radius := radius_pos_of_mem hA hr_ne
  have hA_norm : ‖A -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hA
  have hC_norm : ‖C -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius hC
  set v : V := (A -ᵥ s.center) + (C -ᵥ s.center) with hv_def
  have hv_ne : v ≠ 0 := sum_vsub_center_ne_zero_of_not_isDiameter hA hND
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hv_norm_le : ‖v‖ ≤ 2 * s.radius := by
    calc ‖v‖ ≤ ‖A -ᵥ s.center‖ + ‖C -ᵥ s.center‖ := norm_add_le _ _
      _ = 2 * s.radius := by rw [hA_norm, hC_norm]; ring
  have hM_sub :
      (major hA hC hND).mid -ᵥ s.center = -((s.radius / ‖v‖) • v) := by
    rw [major_mid, AffineEquiv.pointReflection_apply, vadd_vsub, minor_mid,
        ← neg_vsub_eq_vsub_rev, vadd_vsub]
  have h_M_norm : ‖(major hA hC hND).mid -ᵥ s.center‖ = s.radius := by
    exact norm_vsub_center_eq_radius (major hA hC hND).mid_mem
  have h_M_M_inner :
      ⟪(major hA hC hND).mid -ᵥ s.center, (major hA hC hND).mid -ᵥ s.center⟫
        = s.radius ^ 2 := by
    rw [real_inner_self_eq_norm_sq, h_M_norm]
  have hminorM_sub :
      (minor hA hC hND).mid -ᵥ s.center = (s.radius / ‖v‖) • v := by
    rw [minor_mid, vadd_vsub]
  have h_major_mid_neg_minor :
      (major hA hC hND).mid -ᵥ s.center =
        -((minor hA hC hND).mid -ᵥ s.center : V) := by
    rw [hM_sub, hminorM_sub]
  have h_L_inner : ∀ p, p ∈ s.lineOrOrthRadius A C →
      ⟪p -ᵥ s.center, (major hA hC hND).mid -ᵥ s.center⟫
        = -(s.radius * ‖v‖ / 2) := by
    intro p hp
    have hminor :
        ⟪p -ᵥ s.center, (minor hA hC hND).mid -ᵥ s.center⟫ =
          s.radius * ‖v‖ / 2 := by
      simpa [hv_def] using
        inner_vsub_center_minorMidpoint_of_mem_lineOrOrthRadius hA hC hND hp
    rw [h_major_mid_neg_minor, inner_neg_right, hminor]
  rw [measure, if_neg hr_ne]
  suffices h : (s.lineOrOrthRadius (major hA hC hND).left
                  (major hA hC hND).right).SSameSide
                (major hA hC hND).mid s.center by
    rw [if_pos h, major_left, major_right]
  rw [major_left, major_right]
  have h_M_not_in_L : (major hA hC hND).mid ∉ s.lineOrOrthRadius A C := by
    intro hM
    have h := h_L_inner _ hM
    rw [h_M_M_inner] at h
    nlinarith
  have h_O_not_in_L : s.center ∉ s.lineOrOrthRadius A C := by
    intro hO
    have h := h_L_inner _ hO
    rw [vsub_self, inner_zero_left] at h
    nlinarith
  by_cases hAC : A = C
  · have hAL : A ∈ s.lineOrOrthRadius A C := left_mem_lineOrOrthRadius
    have h_v_eq : v = (2 : ℝ) • (A -ᵥ s.center) := by
      show (A -ᵥ s.center) + (C -ᵥ s.center) = _
      rw [← hAC, two_smul]
    have h_v_norm : ‖v‖ = 2 * s.radius := by
      rw [h_v_eq, norm_smul, Real.norm_eq_abs, abs_of_pos two_pos, hA_norm]
    have hM_to_O : (major hA hC hND).mid -ᵥ s.center = -(A -ᵥ s.center) := by
      rw [hM_sub, h_v_norm, h_v_eq, smul_smul,
          show s.radius / (2 * s.radius) * 2 = 1 from by field_simp,
          one_smul]
    have hM_minus_A :
        ((major hA hC hND).mid -ᵥ A : V) = (-2 : ℝ) • (A -ᵥ s.center) := by
      have h1 : ((major hA hC hND).mid -ᵥ A : V) =
          ((major hA hC hND).mid -ᵥ s.center) - (A -ᵥ s.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, hM_to_O]; module
    have hO_minus_A : (s.center -ᵥ A : V) = (-1 : ℝ) • (A -ᵥ s.center) := by
      rw [show (s.center -ᵥ A : V) = -(A -ᵥ s.center) from
            (neg_vsub_eq_vsub_rev _ _).symm, neg_one_smul]
    exact AffineSubspace.sSameSide_of_vsub_eq_smul hAL hAL hM_minus_A hO_minus_A
      (by norm_num) h_M_not_in_L h_O_not_in_L
  · set F : P := midpoint ℝ A C with hF_def
    have hF_in_L : F ∈ s.lineOrOrthRadius A C := by
      rw [lineOrOrthRadius_of_ne hAC, hF_def]
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hF_minus_O : (F -ᵥ s.center : V) = (⅟ (2 : ℝ)) • v := by
      rw [hF_def, hv_def, midpoint_vsub, smul_add]
    have hO_minus_F : (s.center -ᵥ F : V) = -((⅟ (2 : ℝ)) • v) := by
      rw [show (s.center -ᵥ F : V) = -(F -ᵥ s.center) from
            (neg_vsub_eq_vsub_rev _ _).symm, hF_minus_O]
    have hM_minus_F : ((major hA hC hND).mid -ᵥ F : V) =
        (-(⅟ (2 : ℝ) + s.radius / ‖v‖)) • v := by
      have h1 : ((major hA hC hND).mid -ᵥ F : V) =
          ((major hA hC hND).mid -ᵥ s.center) - (F -ᵥ s.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, hM_sub, hF_minus_O]; module
    have hO_minus_F' : (s.center -ᵥ F : V) = (-(⅟ (2 : ℝ))) • v := by
      rw [hO_minus_F, neg_smul]
    have h_half_pos : (0 : ℝ) < ⅟ (2 : ℝ) := by
      rw [invOf_eq_inv]; norm_num
    have hβ_pos : (0 : ℝ) < ⅟ (2 : ℝ) + s.radius / ‖v‖ := by
      have hsr : 0 < s.radius / ‖v‖ := div_pos hr_pos hv_norm_pos
      linarith
    exact AffineSubspace.sSameSide_of_vsub_eq_smul hF_in_L hF_in_L
      hM_minus_F hO_minus_F' (by nlinarith) h_M_not_in_L h_O_not_in_L

/-- A minor arc has measure at most `π`. -/
theorem measure_minor_le_pi {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    (minor hA hC hND).measure ≤ π := by
  rw [measure_minor]
  exact angle_le_pi A s.center C

/-- A major arc has measure at least `π`. -/
theorem measure_major_ge_pi {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    π ≤ (major hA hC hND).measure := by
  rw [measure_major]
  linarith [angle_le_pi A s.center C]

/-- A minor arc between distinct endpoints has positive measure. -/
theorem measure_minor_pos_of_ne {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) (hne : A ≠ C) :
    0 < (minor hA hC hND).measure := by
  rw [measure_minor]
  refine lt_of_le_of_ne (angle_nonneg _ _ _) ?_
  intro hzero
  have hr_ne : s.radius ≠ 0 := radius_ne_zero_of_mem_of_mem_of_ne hA hC hne
  exact hne ((angle_center_eq_zero_iff_eq hA hC hr_ne).mp hzero.symm)

/-- The minor and major arcs between two points have measures summing to `2π`. -/
theorem measure_minor_add_measure_major {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    (minor hA hC hND).measure + (major hA hC hND).measure = 2 * π := by
  rw [measure_minor, measure_major]; ring

/-- A non-diametral chord with distinct endpoints cuts a minor arc of measure below `π`. -/
theorem measure_minor_lt_pi {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) (hAC : A ≠ C) :
    (minor hA hC hND).measure < π :=
  lt_of_le_of_ne (measure_minor_le_pi hA hC hND) fun h => hND <| by
    simpa only [minor_left, minor_right] using
      (measure_eq_pi_iff_isDiameter _ (radius_ne_zero_of_mem_of_mem_of_ne hA hC hAC)).mp h

/-- Dually, the major arc has measure above `π`. -/
theorem pi_lt_measure_major {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) (hAC : A ≠ C) :
    π < (major hA hC hND).measure := by
  linarith [measure_minor_add_measure_major hA hC hND,
    measure_minor_lt_pi hA hC hND hAC]

/-! ### Arc addition -/

/-- When `B` lies in the interior of the minor arc from `A` to `C`, the measure of the arc through
`B` equals `∠ A s.center B + ∠ B s.center C`. -/
theorem measure_through_eq_angle_add_angle_of_mem_minor_interior
    [Fact (Module.finrank ℝ V = 2)] {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hAC : A ≠ C)
    (hND : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hND).interior) :
    (through hA hB hC hBA hBC).measure =
      ∠ A s.center B + ∠ B s.center C := by
  haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
  set a : V := A -ᵥ s.center with ha_def
  set b : V := B -ᵥ s.center with hb_def
  set c : V := C -ᵥ s.center with hc_def
  have hr_ne : s.radius ≠ 0 := radius_ne_zero_of_mem_of_mem_of_ne hA hC hAC
  have hr_pos : 0 < s.radius := radius_pos_of_mem hA hr_ne
  have ha_norm : ‖a‖ = s.radius := by rw [ha_def]; exact norm_vsub_center_eq_radius hA
  have hb_norm : ‖b‖ = s.radius := by rw [hb_def]; exact norm_vsub_center_eq_radius hB
  have hc_norm : ‖c‖ = s.radius := by rw [hc_def]; exact norm_vsub_center_eq_radius hC
  have ha_ne : a ≠ 0 := by rw [← norm_ne_zero_iff, ha_norm]; exact hr_ne
  have hb_ne : b ≠ 0 := by rw [← norm_ne_zero_iff, hb_norm]; exact hr_ne
  have hc_ne : c ≠ 0 := by rw [← norm_ne_zero_iff, hc_norm]; exact hr_ne
  set v : V := a + c with hv_def
  set d : V := c - a with hd_def
  have hv_ne : v ≠ 0 := sum_vsub_center_ne_zero_of_not_isDiameter hA hND
  have hd_ne : d ≠ 0 := by
    intro h
    apply hAC
    have h_eq : (C -ᵥ s.center : V) = A -ᵥ s.center := by
      have hh : c - a = 0 := h
      have : c = a := sub_eq_zero.mp hh
      exact this
    exact (vsub_left_cancel h_eq).symm
  set γ : ℝ := ⟪a, c⟫ with hγ_def
  have hv_norm_sq : ‖v‖ ^ 2 = 2 * (s.radius ^ 2 + γ) := by
    have h1 : ‖a + c‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, c⟫ + ‖c‖ ^ 2 := norm_add_sq_real _ _
    show ‖a + c‖ ^ 2 = _
    rw [h1, ha_norm, hc_norm, ← hγ_def]; ring
  have hd_norm_sq : ‖d‖ ^ 2 = 2 * (s.radius ^ 2 - γ) := by
    have h1 : ‖c - a‖ ^ 2 = ‖c‖ ^ 2 - 2 * ⟪c, a⟫ + ‖a‖ ^ 2 := norm_sub_sq_real _ _
    show ‖c - a‖ ^ 2 = _
    rw [h1, ha_norm, hc_norm, real_inner_comm a c, ← hγ_def]; ring
  have hv_d_perp : ⟪v, d⟫ = 0 := by
    show ⟪a + c, c - a⟫ = 0
    rw [inner_add_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
        real_inner_comm a c, ha_norm, hc_norm]
    ring
  have hd_v_perp : ⟪d, v⟫ = 0 := by rw [real_inner_comm]; exact hv_d_perp
  have hpg : 0 < s.radius ^ 2 + γ := by
    have hp : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv_ne) 2
    linarith [hv_norm_sq]
  have hng : 0 < s.radius ^ 2 - γ := by
    have hp : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.mpr hd_ne) 2
    linarith [hd_norm_sq]
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  have hd_norm_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hv_norm_sq_pos : 0 < ‖v‖ ^ 2 := pow_pos hv_norm_pos 2
  have hd_norm_sq_pos : 0 < ‖d‖ ^ 2 := pow_pos hd_norm_pos 2
  set ρ : ℝ := s.radius / ‖v‖ with hρ_def
  have hρ_pos : 0 < ρ := div_pos hr_pos hv_norm_pos
  have hρ_gt_half : 1 / 2 < ρ := by
    rw [hρ_def, lt_div_iff₀ hv_norm_pos]
    have h_lt : ‖v‖ < 2 * s.radius := by
      have h1 : ‖v‖ ^ 2 < (2 * s.radius) ^ 2 := by
        rw [hv_norm_sq, mul_pow]; nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by linarith) h1
    linarith
  have hMin_sub : (minor hA hC hND).mid -ᵥ s.center = ρ • v := by
    rw [minor_mid, vadd_vsub, hρ_def, hv_def]
  set L : AffineSubspace ℝ P := s.lineOrOrthRadius A C with hL_def
  have hL_eq : L = line[ℝ, A, C] := lineOrOrthRadius_of_ne hAC
  set F : P := midpoint ℝ A C with hF_def
  have hF_in_L : F ∈ L := by
    rw [hL_eq, hF_def]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hF_sub : F -ᵥ s.center = (2⁻¹ : ℝ) • v := by
    rw [hF_def, midpoint_vsub, ← ha_def, ← hc_def, ← smul_add, hv_def, invOf_eq_inv]
  have h_inner_v_of_mem_L : ∀ p ∈ L, ⟪p -ᵥ s.center, v⟫ = s.radius ^ 2 + γ := by
    intro p hp
    rw [hL_eq] at hp
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
    rw [AffineMap.lineMap_apply] at ht
    have hd_eq : d = C -ᵥ A := by
      rw [hd_def]
      show (C -ᵥ s.center) - (A -ᵥ s.center) = C -ᵥ A
      exact vsub_sub_vsub_cancel_right _ _ _
    have h_p_sub : p -ᵥ s.center = a + t • d := by
      have h1 : (p -ᵥ s.center : V) = (p -ᵥ A) + (A -ᵥ s.center) :=
        (vsub_add_vsub_cancel _ _ _).symm
      have h2 : (p -ᵥ A : V) = t • d := by
        rw [← ht, vadd_vsub, hd_eq]
      rw [h1, h2, ← ha_def]; abel
    rw [h_p_sub, inner_add_left, real_inner_smul_left, hd_v_perp,
        mul_zero, add_zero]
    show ⟪a, a + c⟫ = s.radius ^ 2 + γ
    rw [inner_add_right, real_inner_self_eq_norm_sq, ha_norm, ← hγ_def]
  set σ : ℝ := ⟪b, v⟫ with hσ_def
  have hMin_ss_B : L.SSameSide (minor hA hC hND).mid B := by
    have h := sSameSide_of_mem_interior hB_minor
    simp only [minor_left, minor_right] at h
    exact h
  have hMin_not_in_L : (minor hA hC hND).mid ∉ L := hMin_ss_B.left_notMem
  have hB_not_in_L : B ∉ L := hMin_ss_B.right_notMem
  have hMin_F_sub : (minor hA hC hND).mid -ᵥ F = (ρ - 2⁻¹) • v := by
    have h1 : (minor hA hC hND).mid -ᵥ F =
        ((minor hA hC hND).mid -ᵥ s.center) - (F -ᵥ s.center) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [h1, hMin_sub, hF_sub, ← sub_smul]
  have hMin_F_inner_v_pos :
      0 < ⟪(minor hA hC hND).mid -ᵥ F, v⟫ := by
    rw [hMin_F_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos (by linarith) hv_norm_sq_pos
  obtain ⟨_, _, p₂, hp₂_in_L, hSR⟩ :=
    (AffineSubspace.sSameSide_iff_exists_left hF_in_L).mp hMin_ss_B
  have hB_p2_inner_v : ⟪B -ᵥ p₂, v⟫ = σ - (s.radius ^ 2 + γ) := by
    rw [show (B -ᵥ p₂ : V) = (B -ᵥ s.center) - (p₂ -ᵥ s.center) from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        ← hb_def, inner_sub_left, h_inner_v_of_mem_L p₂ hp₂_in_L, ← hσ_def]
  have hσ_gt : σ > s.radius ^ 2 + γ := by
    rcases hSR with hl_zero | hr_zero | ⟨k₁, k₂, hk₁_pos, hk₂_pos, hk_eq⟩
    · exfalso; apply hMin_not_in_L
      have : (minor hA hC hND).mid = F := vsub_eq_zero_iff_eq.mp hl_zero
      rw [this]; exact hF_in_L
    · exfalso; apply hB_not_in_L
      have : B = p₂ := vsub_eq_zero_iff_eq.mp hr_zero
      rw [this]; exact hp₂_in_L
    · have h_inner_eq : k₁ * ⟪(minor hA hC hND).mid -ᵥ F, v⟫
            = k₂ * ⟪B -ᵥ p₂, v⟫ := by
        have hh := congrArg (fun x => ⟪x, v⟫) hk_eq
        simp only at hh
        rw [real_inner_smul_left, real_inner_smul_left] at hh
        exact hh
      have h_lhs_pos : 0 < k₁ * ⟪(minor hA hC hND).mid -ᵥ F, v⟫ :=
        mul_pos hk₁_pos hMin_F_inner_v_pos
      have h_rhs_pos : 0 < k₂ * ⟪B -ᵥ p₂, v⟫ := by linarith
      rw [hB_p2_inner_v] at h_rhs_pos
      have : 0 < σ - (s.radius ^ 2 + γ) :=
        (mul_pos_iff_of_pos_left hk₂_pos).mp h_rhs_pos
      linarith
  set ν : ℝ := σ / ‖v‖ ^ 2 with hν_def
  set μ : ℝ := ⟪b, d⟫ / ‖d‖ ^ 2 with hμ_def
  have hν_gt_half : 1 / 2 < ν := by
    rw [hν_def, hv_norm_sq, lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * (s.radius ^ 2 + γ))]
    linarith
  have hb_decomp : b = ν • v + μ • d := by
    have h_perp_v : ⟪v, b - ν • v⟫ = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
          ← real_inner_comm v b, ← hσ_def, hν_def,
          div_mul_cancel₀ _ hv_norm_sq_pos.ne']
      ring
    have h_in_span : b - ν • v ∈ Submodule.span ℝ ({d} : Set V) :=
      Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
        hv_ne hd_ne h_perp_v hv_d_perp
    obtain ⟨μ', hμ'⟩ := Submodule.mem_span_singleton.mp h_in_span
    have hμ'_eq : μ' = μ := by
      have hh := congrArg (fun x => ⟪x, d⟫) hμ'
      simp only at hh
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq,
          inner_sub_left, real_inner_smul_left,
          show ⟪v, d⟫ = 0 from hv_d_perp, mul_zero, sub_zero] at hh
      rw [hμ_def, eq_div_iff hd_norm_sq_pos.ne']
      linarith
    rw [show b = (ν • v) + (b - ν • v) from by abel, ← hμ', hμ'_eq]
  have hb_norm_sq : ‖b‖ ^ 2 = ν ^ 2 * ‖v‖ ^ 2 + μ ^ 2 * ‖d‖ ^ 2 := by
    have h_pyth : ‖ν • v + μ • d‖ ^ 2 = ‖ν • v‖ ^ 2 + ‖μ • d‖ ^ 2 := by
      rw [@norm_add_sq_real V _ _ (ν • v) (μ • d), real_inner_smul_left,
          real_inner_smul_right, hv_d_perp]
      ring
    rw [hb_decomp, h_pyth, norm_smul, norm_smul, mul_pow, mul_pow,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have hμ_abs_lt_half : |μ| < 1 / 2 := by
    have h_constr : ν ^ 2 * (2 * (s.radius ^ 2 + γ)) +
                    μ ^ 2 * (2 * (s.radius ^ 2 - γ)) = s.radius ^ 2 := by
      have := hb_norm_sq
      rw [hv_norm_sq, hd_norm_sq, hb_norm] at this
      linarith
    have h_ν_sq : ν ^ 2 > 1 / 4 := by nlinarith [hν_gt_half, hν_def]
    have h_μ_sq : μ ^ 2 < 1 / 4 := by nlinarith
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by ring,
              Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 / 2)]]
    rw [show |μ| = Real.sqrt (μ ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h_μ_sq
  have h_b_in_cone : b ∈ Submodule.span (NNReal) ({a, c} : Set V) := by
    rw [Submodule.mem_span_pair]
    have hα_nn : 0 ≤ ν - μ := by
      have h_abs : μ ≤ |μ| := le_abs_self μ
      linarith
    have hβ_nn : 0 ≤ ν + μ := by
      have h_abs : -μ ≤ |μ| := neg_le_abs μ
      linarith
    refine ⟨⟨ν - μ, hα_nn⟩, ⟨ν + μ, hβ_nn⟩, ?_⟩
    show (ν - μ) • a + (ν + μ) • c = b
    rw [hb_decomp]
    show (ν - μ) • a + (ν + μ) • c = ν • v + μ • d
    rw [hv_def, hd_def, smul_add, smul_sub]
    module
  have h_angle_add : ∠ A s.center C = ∠ A s.center B + ∠ B s.center C := by
    show InnerProductGeometry.angle a c =
      InnerProductGeometry.angle a b + InnerProductGeometry.angle b c
    exact InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span hb_ne h_b_in_cone
  have hT_ss_B : L.SSameSide (through hA hB hC hBA hBC).mid B := by
    have h := sSameSide_of_mem_interior (mem_interior_through hA hB hC hBA hBC)
    simp only [through_left, through_right hA hB hC hBA hBC] at h
    exact h
  have hMin_not_ss_center :
      ¬ L.SSameSide (minor hA hC hND).mid s.center := by
    simpa only [minor_left, minor_right, ← hL_def] using
      (measure_eq_angle_iff_not_sSameSide (minor hA hC hND) hr_ne).mp
        (by simpa only [minor_left, minor_right] using measure_minor hA hC hND)
  have hT_not_ss : ¬ L.SSameSide (through hA hB hC hBA hBC).mid s.center := by
    intro hss
    apply hMin_not_ss_center
    exact (hMin_ss_B.trans hT_ss_B.symm).trans hss
  have hT_meas : (through hA hB hC hBA hBC).measure = ∠ A s.center C := by
    have h_iff := (measure_eq_angle_iff_not_sSameSide
      (through hA hB hC hBA hBC) hr_ne).mpr (by
      simp only [through_left, through_right hA hB hC hBA hBC]
      rw [← hL_def]
      exact hT_not_ss)
    simp only [through_left, through_right hA hB hC hBA hBC] at h_iff
    exact h_iff
  rw [hT_meas, h_angle_add]

/-- When `B` lies in the interior of the minor arc and `Q` lies in the interior of the arc through
`B`, the central angle `∠ A s.center Q` equals that arc's measure minus `∠ Q s.center C`. -/
theorem angle_eq_measure_sub_angle_of_mem_through_interior [Fact (Module.finrank ℝ V = 2)]
    {A B C Q : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hQ : Q ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hQA : Q ≠ A) (hQC : Q ≠ C)
    (hAC : A ≠ C)
    (hND : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hND).interior)
    (hQ_in : Q ∈ (through hA hB hC hBA hBC).interior) :
    ∠ A s.center Q =
      (through hA hB hC hBA hBC).measure - ∠ Q s.center C := by
  have hr_ne : s.radius ≠ 0 := radius_ne_zero_of_mem_of_mem_of_ne hA hC hAC
  have h_t_B : (s.lineOrOrthRadius A C).SSameSide
      (through hA hB hC hBA hBC).mid B := by
    have h := sSameSide_of_mem_interior (mem_interior_through hA hB hC hBA hBC)
    simp only [through_left, through_right hA hB hC hBA hBC] at h
    exact h
  have h_t_Q : (s.lineOrOrthRadius A C).SSameSide
      (through hA hB hC hBA hBC).mid Q := by
    have h := sSameSide_of_mem_interior hQ_in
    simp only [through_left, through_right hA hB hC hBA hBC] at h
    exact h
  have h_min_B : (s.lineOrOrthRadius A C).SSameSide
      (minor hA hC hND).mid B := by
    have h := sSameSide_of_mem_interior hB_minor
    simp only [minor_left, minor_right] at h
    exact h
  have hQ_minor : Q ∈ (minor hA hC hND).interior := by
    refine mem_interior_iff.mpr ⟨hQ, ?_⟩
    simp only [minor_left, minor_right]
    exact (h_min_B.trans h_t_B.symm).trans h_t_Q
  have h_at_Q : (through hA hQ hC hQA hQC).measure =
      ∠ A s.center Q + ∠ Q s.center C :=
    measure_through_eq_angle_add_angle_of_mem_minor_interior
      hA hQ hC hQA hQC hAC hND hQ_minor
  have h_min_meas : (minor hA hC hND).measure = ∠ A s.center C :=
    measure_minor hA hC hND
  have h_min_not_ss_center : ¬ (s.lineOrOrthRadius A C).SSameSide
      (minor hA hC hND).mid s.center := by
    have h_iff := measure_eq_angle_iff_not_sSameSide (minor hA hC hND) hr_ne
    simp only [minor_left, minor_right] at h_iff
    exact h_iff.mp h_min_meas
  have h_through_B_eq_AOC :
      (through hA hB hC hBA hBC).measure = ∠ A s.center C := by
    have h_iff := measure_eq_angle_iff_not_sSameSide
      (through hA hB hC hBA hBC) hr_ne
    simp only [through_left, through_right hA hB hC hBA hBC] at h_iff
    refine h_iff.mpr ?_
    intro hss
    exact h_min_not_ss_center ((h_min_B.trans h_t_B.symm).trans hss)
  have h_t_Q_Q : (s.lineOrOrthRadius A C).SSameSide
      (through hA hQ hC hQA hQC).mid Q := by
    have h := sSameSide_of_mem_interior (mem_interior_through hA hQ hC hQA hQC)
    simp only [through_left, through_right hA hQ hC hQA hQC] at h
    exact h
  have h_min_Q : (s.lineOrOrthRadius A C).SSameSide
      (minor hA hC hND).mid Q := by
    have h := sSameSide_of_mem_interior hQ_minor
    simp only [minor_left, minor_right] at h
    exact h
  have h_through_Q_eq_AOC :
      (through hA hQ hC hQA hQC).measure = ∠ A s.center C := by
    have h_iff := measure_eq_angle_iff_not_sSameSide
      (through hA hQ hC hQA hQC) hr_ne
    simp only [through_left, through_right hA hQ hC hQA hQC] at h_iff
    refine h_iff.mpr ?_
    intro hss
    exact h_min_not_ss_center ((h_min_Q.trans h_t_Q_Q.symm).trans hss)
  linarith [h_through_B_eq_AOC, h_through_Q_eq_AOC, h_at_Q]

/-! ### Arcs and chords -/

/-- The chord of an arc has length `2 * s.radius * Real.sin (∠ a.left s.center a.right / 2)`. -/
theorem dist_left_right_eq_two_mul_radius_mul_sin (a : Arc s) :
    dist a.left a.right =
      2 * s.radius * Real.sin (∠ a.left s.center a.right / 2) := by
  set v : V := a.left -ᵥ s.center with hv_def
  set w : V := a.right -ᵥ s.center with hw_def
  have hv_norm : ‖v‖ = s.radius := by rw [hv_def]; exact norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖w‖ = s.radius := by rw [hw_def]; exact norm_vsub_center_eq_radius a.right_mem
  have hr_nn : 0 ≤ s.radius := hv_norm ▸ norm_nonneg _
  set θ : ℝ := ∠ a.left s.center a.right with hθ_def
  have hθ_eq : θ = InnerProductGeometry.angle v w := rfl
  have hθ_nn : 0 ≤ θ := angle_nonneg _ _ _
  have hθ_le_pi : θ ≤ π := angle_le_pi _ _ _
  have h_half_nn : 0 ≤ θ / 2 := by linarith
  have h_half_le_pi : θ / 2 ≤ π := by linarith [Real.pi_pos]
  have h_sin_nn : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi h_half_nn h_half_le_pi
  have h_rhs_nn : 0 ≤ 2 * s.radius * Real.sin (θ / 2) := by positivity
  have h_inner : ⟪v, w⟫ = Real.cos θ * s.radius ^ 2 := by
    have hcos := InnerProductGeometry.cos_angle_mul_norm_mul_norm v w
    rw [← hθ_eq, hv_norm, hw_norm] at hcos
    rw [← hcos]; ring
  have h_lhs_sq :
      (dist a.left a.right) ^ 2 = 2 * s.radius ^ 2 * (1 - Real.cos θ) := by
    rw [dist_eq_norm_vsub V,
        show (a.left -ᵥ a.right : V) = v - w from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        @norm_sub_sq_real V _ _ v w, hv_norm, hw_norm, h_inner]
    ring
  have h_sin_sq : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h := Real.sin_sq_eq_half_sub (θ / 2)
    rw [show (2 : ℝ) * (θ / 2) = θ from by ring] at h
    linarith
  have h_rhs_sq :
      (2 * s.radius * Real.sin (θ / 2)) ^ 2 = 2 * s.radius ^ 2 * (1 - Real.cos θ) := by
    rw [mul_pow, mul_pow, h_sin_sq]; ring
  exact (sq_eq_sq₀ dist_nonneg h_rhs_nn).mp (h_lhs_sq.trans h_rhs_sq.symm)

/-- The chord of an arc has length `2 * s.radius * Real.sin (a.measure / 2)`. -/
theorem dist_left_right_eq_two_mul_radius_mul_sin_measure (a : Arc s) :
    dist a.left a.right = 2 * s.radius * Real.sin (a.measure / 2) := by
  by_cases hr : s.radius = 0
  · have hL : a.left = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp a.left_mem).trans hr)
    have hR : a.right = s.center :=
      dist_eq_zero.mp ((mem_sphere.mp a.right_mem).trans hr)
    rw [hL, hR, dist_self, hr]; ring
  · rw [dist_left_right_eq_two_mul_radius_mul_sin a, measure, if_neg hr]
    split_ifs with hss
    · rw [show (2 * π - ∠ a.left s.center a.right) / 2 =
            π - ∠ a.left s.center a.right / 2 from by ring,
          Real.sin_pi_sub]
    · rfl

/-- On a minor arc, the chord length is `2 * s.radius * Real.sin (measure / 2)`. -/
theorem dist_left_right_eq_two_mul_radius_mul_sin_measure_of_minor
    {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    dist A C = 2 * s.radius * Real.sin ((minor hA hC hND).measure / 2) := by
  simpa only [minor_left, minor_right] using
    dist_left_right_eq_two_mul_radius_mul_sin_measure (minor hA hC hND)

/-- Arcs of equal measure have equal chord length. -/
theorem dist_eq_of_measure_eq {a b : Arc s} (h : a.measure = b.measure) :
    dist a.left a.right = dist b.left b.right := by
  rw [dist_left_right_eq_two_mul_radius_mul_sin_measure a,
      dist_left_right_eq_two_mul_radius_mul_sin_measure b, h]

/-- Two arcs with equal chord length and measure at most `π` have equal measure. -/
theorem measure_eq_of_dist_eq_of_le_pi {a b : Arc s}
    (h_dist : dist a.left a.right = dist b.left b.right)
    (ha_le : a.measure ≤ π) (hb_le : b.measure ≤ π) :
    a.measure = b.measure := by
  rw [dist_left_right_eq_two_mul_radius_mul_sin_measure a,
      dist_left_right_eq_two_mul_radius_mul_sin_measure b] at h_dist
  by_cases hr : s.radius = 0
  · have ha_zero : a.measure = 0 := by rw [measure, if_pos hr]
    have hb_zero : b.measure = 0 := by rw [measure, if_pos hr]
    rw [ha_zero, hb_zero]
  · have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr
    have h_two_r_ne : (2 * s.radius) ≠ 0 := by positivity
    have h_sin : Real.sin (a.measure / 2) = Real.sin (b.measure / 2) :=
      mul_left_cancel₀ h_two_r_ne h_dist
    have ha_half_in : a.measure / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := by
      refine ⟨?_, by linarith⟩
      linarith [measure_nonneg a, Real.pi_pos]
    have hb_half_in : b.measure / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := by
      refine ⟨?_, by linarith⟩
      linarith [measure_nonneg b, Real.pi_pos]
    have h_eq_half : a.measure / 2 = b.measure / 2 :=
      Real.injOn_sin ha_half_in hb_half_in h_sin
    linarith

/-- Two minor arcs have equal measure if and only if they have equal chord length. -/
theorem measure_minor_eq_iff_dist_eq {A B C D : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hD : D ∈ s)
    (hND₁ : ¬s.IsDiameter A B) (hND₂ : ¬s.IsDiameter C D) :
    (minor hA hB hND₁).measure = (minor hC hD hND₂).measure ↔
      dist A B = dist C D := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h_dist := dist_eq_of_measure_eq h
    simpa only [minor_left, minor_right] using h_dist
  · apply measure_eq_of_dist_eq_of_le_pi
    · simpa only [minor_left, minor_right] using h
    · exact measure_minor_le_pi hA hB hND₁
    · exact measure_minor_le_pi hC hD hND₂

/-- If a point on the sphere subtends equal central angles to the two endpoints, it lies on the
perpendicular bisector of the chord. -/
theorem mem_perpBisector_of_angle_center_eq {A M C : P}
    (hA : A ∈ s) (hM : M ∈ s) (hC : C ∈ s)
    (hMA : M ≠ A) (hAC : A ≠ C)
    (h_bisect : ∠ A s.center M = ∠ M s.center C) :
    M ∈ AffineSubspace.perpBisector A C := by
  rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
  have hr : s.radius ≠ 0 := radius_ne_zero_of_mem_of_mem_of_ne hM hA hMA
  have h_bisect' : ∠ M s.center A = ∠ M s.center C := by
    rw [angle_comm M s.center A]; exact h_bisect
  have h_not_diam_MA : ¬s.IsDiameter M A := fun h_diam_MA => by
    have h_pi_MA : ∠ M s.center A = π :=
      (angle_center_eq_pi_iff_isDiameter hM hA hr).mpr h_diam_MA
    have h_pi_MC : ∠ M s.center C = π := h_bisect'.symm.trans h_pi_MA
    have h_diam_MC : s.IsDiameter M C :=
      (angle_center_eq_pi_iff_isDiameter hM hC hr).mp h_pi_MC
    exact hAC (h_diam_MA.right_eq_of_isDiameter h_diam_MC)
  have h_not_diam_MC : ¬s.IsDiameter M C := fun h_diam_MC => by
    have h_pi_MC : ∠ M s.center C = π :=
      (angle_center_eq_pi_iff_isDiameter hM hC hr).mpr h_diam_MC
    have h_pi_MA : ∠ M s.center A = π := h_bisect'.trans h_pi_MC
    have h_diam_MA : s.IsDiameter M A :=
      (angle_center_eq_pi_iff_isDiameter hM hA hr).mp h_pi_MA
    exact hAC (h_diam_MA.right_eq_of_isDiameter h_diam_MC)
  rw [dist_left_right_eq_two_mul_radius_mul_sin_measure_of_minor hM hA h_not_diam_MA,
      dist_left_right_eq_two_mul_radius_mul_sin_measure_of_minor hM hC h_not_diam_MC,
      measure_minor hM hA h_not_diam_MA, measure_minor hM hC h_not_diam_MC, h_bisect']

/-! ### The measure-bisecting midpoint -/

open Classical in
/-- The measure-bisecting midpoint of an arc. It normalizes a direction vector derived from the
chord and `a.mid`; in the semicircle case the direction is obtained by orthogonalizing
`a.mid -ᵥ s.center` against the chord. -/
def midpoint (a : Arc s) : P :=
  let v := a.left -ᵥ s.center
  let w := a.right -ᵥ s.center
  let u := v + w
  if u = 0 then
    let m := a.mid -ᵥ s.center
    let proj := m - (⟪m, v⟫ / ⟪v, v⟫) • v
    (s.radius / ‖proj‖) • proj +ᵥ s.center
  else
    let signed_u :=
      if (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center then -u else u
    (s.radius / ‖signed_u‖) • signed_u +ᵥ s.center

private theorem sum_left_right_vsub_center_mem_span_mid (a : Arc s) :
    (a.left -ᵥ s.center) + (a.right -ᵥ s.center) ∈ ℝ ∙ (a.mid -ᵥ s.center) := by
  classical
  let L : AffineSubspace ℝ P := line[ℝ, s.center, a.mid]
  have hL_dir_eq : L.direction =
      ℝ ∙ (a.mid -ᵥ s.center) := by
    dsimp [L]
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have h_right_reflect :
      (a.right -ᵥ s.center : V) = L.direction.reflection (a.left -ᵥ s.center) := by
    rw [a.right_eq_reflection]
    have h :=
      reflection_apply_of_mem L a.left (x := s.center)
        (show s.center ∈ L from left_mem_affineSpan_pair ℝ s.center a.mid)
    rw [h, vadd_vsub]
  rw [← hL_dir_eq, h_right_reflect, Submodule.reflection_apply]
  have hmem : (2 : ℝ) • L.direction.starProjection (a.left -ᵥ s.center) ∈ L.direction :=
    Submodule.smul_mem L.direction (2 : ℝ)
      (Submodule.starProjection_apply_mem L.direction (a.left -ᵥ s.center))
  convert hmem using 1
  abel_nf
  norm_num [two_smul]

/-- For a non-degenerate arc, the measure-bisecting midpoint coincides with the structural mid. -/
theorem midpoint_eq_mid (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint = a.mid := by
  classical
  have hmid_left : a.mid ≠ a.left := fun h => hnd (Or.inl h)
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne a.mid_mem a.left_mem hmid_left
  have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr_ne
  have hLR : a.left ≠ a.right :=
    (left_ne_right_iff_not_isDegenerate a).mpr hnd
  have hv_norm : ‖a.left -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖a.right -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.right_mem
  have hm_norm : ‖a.mid -ᵥ s.center‖ = s.radius := norm_vsub_center_eq_radius a.mid_mem
  have hm_ne : (a.mid -ᵥ s.center : V) ≠ 0 :=
    norm_ne_zero_iff.mp (hm_norm.symm ▸ hr_ne)
  have h_perp : ⟪a.mid -ᵥ s.center, a.right -ᵥ a.left⟫ = 0 :=
    a.inner_mid_vsub_center_right_vsub_left
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (sum_left_right_vsub_center_mem_span_mid a)
  have h_u_eq : (a.left -ᵥ s.center) + (a.right -ᵥ s.center) =
      k • (a.mid -ᵥ s.center) := by
    exact hk.symm
  have h_k_abs_lt_2 : |k| < 2 := by
    have h_u_norm : ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖ = |k| * s.radius := by
      rw [h_u_eq, norm_smul, Real.norm_eq_abs, hm_norm]
    have h_u_norm_le : ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖ ≤ 2 * s.radius := by
      calc ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖
          ≤ ‖a.left -ᵥ s.center‖ + ‖a.right -ᵥ s.center‖ := norm_add_le _ _
        _ = 2 * s.radius := by rw [hv_norm, hw_norm]; ring
    have h_abs_le : |k| ≤ 2 := by
      have := h_u_norm ▸ h_u_norm_le
      nlinarith
    rcases lt_or_eq_of_le h_abs_le with h_lt | h_eq
    · exact h_lt
    · exfalso
      have h_u_norm_eq : ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖ = 2 * s.radius := by
        rw [h_u_norm, h_eq]
      have h_u_sq : ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖ ^ 2 = 4 * s.radius ^ 2 := by
        rw [h_u_norm_eq]; ring
      have h_u_inner : ‖(a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖ ^ 2 =
          2 * s.radius ^ 2 + 2 * ⟪a.left -ᵥ s.center, a.right -ᵥ s.center⟫ := by
        rw [norm_add_sq_real, hv_norm, hw_norm]; ring
      have h_vw : ⟪a.left -ᵥ s.center, a.right -ᵥ s.center⟫ = s.radius ^ 2 := by
        linarith [h_u_sq.symm.trans h_u_inner]
      have h_vw_norm_prod : ⟪a.left -ᵥ s.center, a.right -ᵥ s.center⟫ =
          ‖a.left -ᵥ s.center‖ * ‖a.right -ᵥ s.center‖ := by
        rw [h_vw, hv_norm, hw_norm]; ring
      have h_smul_eq : ‖a.right -ᵥ s.center‖ • (a.left -ᵥ s.center : V) =
          ‖a.left -ᵥ s.center‖ • (a.right -ᵥ s.center) :=
        inner_eq_norm_mul_iff_real.mp h_vw_norm_prod
      rw [hv_norm, hw_norm] at h_smul_eq
      have h_vw_eq : (a.left -ᵥ s.center : V) = a.right -ᵥ s.center :=
        smul_right_injective V hr_ne h_smul_eq
      apply hLR
      have h1 : (a.left -ᵥ s.center) +ᵥ s.center =
          (a.right -ᵥ s.center) +ᵥ s.center := by rw [h_vw_eq]
      rwa [vsub_vadd, vsub_vadd] at h1
  have h_k_lt_2 : k < 2 := (abs_lt.mp h_k_abs_lt_2).2
  have h_one_sub_pos : (0 : ℝ) < 1 - k / 2 := by linarith
  suffices h_vec : a.midpoint -ᵥ s.center = a.mid -ᵥ s.center by
    have h1 : (a.midpoint -ᵥ s.center) +ᵥ s.center =
        (a.mid -ᵥ s.center) +ᵥ s.center := by rw [h_vec]
    rwa [vsub_vadd, vsub_vadd] at h1
  show (if (a.left -ᵥ s.center) + (a.right -ᵥ s.center) = 0 then
    (s.radius /
        ‖(a.mid -ᵥ s.center) -
            (⟪a.mid -ᵥ s.center, a.left -ᵥ s.center⟫ /
              ⟪a.left -ᵥ s.center, a.left -ᵥ s.center⟫) •
              (a.left -ᵥ s.center)‖) •
      ((a.mid -ᵥ s.center) -
        (⟪a.mid -ᵥ s.center, a.left -ᵥ s.center⟫ /
          ⟪a.left -ᵥ s.center, a.left -ᵥ s.center⟫) •
          (a.left -ᵥ s.center)) +ᵥ
    s.center
  else
    (s.radius /
        ‖if (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
          then -((a.left -ᵥ s.center) + (a.right -ᵥ s.center))
          else (a.left -ᵥ s.center) + (a.right -ᵥ s.center)‖) •
      (if (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
        then -((a.left -ᵥ s.center) + (a.right -ᵥ s.center))
        else (a.left -ᵥ s.center) + (a.right -ᵥ s.center)) +ᵥ
    s.center) -ᵥ s.center = a.mid -ᵥ s.center
  have hL_eq : s.lineOrOrthRadius a.left a.right = line[ℝ, a.left, a.right] :=
    lineOrOrthRadius_of_ne hLR
  set F : P := _root_.midpoint ℝ a.left a.right with hF_def
  have hF_mem : F ∈ s.lineOrOrthRadius a.left a.right := by
    rw [hL_eq, hF_def]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hF_sub : F -ᵥ s.center = (k / 2) • (a.mid -ᵥ s.center) := by
    rw [hF_def, midpoint_vsub, ← smul_add, h_u_eq, smul_smul, invOf_eq_inv]
    congr 1
    ring
  have hmid_minus_F : a.mid -ᵥ F = (1 - k / 2) • (a.mid -ᵥ s.center) := by
    have h1 : (a.mid -ᵥ F : V) = (a.mid -ᵥ s.center) - (F -ᵥ s.center) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [h1, hF_sub]; module
  have hctr_minus_F : s.center -ᵥ F = (-(k / 2)) • (a.mid -ᵥ s.center) := by
    rw [show (s.center -ᵥ F : V) = -(F -ᵥ s.center) from
          (neg_vsub_eq_vsub_rev _ _).symm,
        hF_sub, neg_smul]
  have hL_dir_chord : (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction =
      ℝ ∙ (a.right -ᵥ a.left) := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  have h_c_zero_of_mem : ∀ c : ℝ,
      (c • (a.mid -ᵥ s.center) : V) ∈
        (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction → c = 0 := by
    intro c hmem
    rw [hL_dir_chord] at hmem
    have h1 : c • (a.mid -ᵥ s.center) ∈ (ℝ ∙ (a.right -ᵥ a.left))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_smul_left]
      rw [show ⟪a.mid -ᵥ s.center, a.right -ᵥ a.left⟫ = 0 from h_perp]
      ring
    have h_inter : c • (a.mid -ᵥ s.center) ∈
        (ℝ ∙ (a.right -ᵥ a.left)) ⊓ (ℝ ∙ (a.right -ᵥ a.left))ᗮ :=
      Submodule.mem_inf.mpr ⟨hmem, h1⟩
    rw [(Submodule.orthogonal_disjoint _).eq_bot, Submodule.mem_bot] at h_inter
    rcases smul_eq_zero.mp h_inter with hc | hm0
    · exact hc
    · exact absurd hm0 hm_ne
  have h_mid_not_in_L : a.mid ∉ s.lineOrOrthRadius a.left a.right := by
    intro hmem
    rw [hL_eq] at hmem
    have hdir_mem : (a.mid -ᵥ F : V) ∈
        (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction :=
      AffineSubspace.vsub_mem_direction hmem
        (show F ∈ line[ℝ, a.left, a.right] from hL_eq ▸ hF_mem)
    rw [hmid_minus_F] at hdir_mem
    have h_one_sub_zero := h_c_zero_of_mem _ hdir_mem
    linarith
  split_ifs with hu hss
  · rw [vadd_vsub]
    have h_mv_zero : ⟪a.mid -ᵥ s.center, a.left -ᵥ s.center⟫ = 0 := by
      have h_right_eq_neg_left :
          (a.right -ᵥ s.center : V) = -(a.left -ᵥ s.center) := by
        calc
          (a.right -ᵥ s.center : V) =
              0 - (a.left -ᵥ s.center) := by
                rw [← hu]; abel
          _ = -(a.left -ᵥ s.center) := by rw [zero_sub]
      have h_chord : (a.right -ᵥ a.left : V) =
          (a.right -ᵥ s.center) - (a.left -ᵥ s.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      have h_perp' := h_perp
      rw [h_chord, h_right_eq_neg_left, inner_sub_right, inner_neg_right] at h_perp'
      linarith
    rw [h_mv_zero, zero_div, zero_smul, sub_zero]
    rw [hm_norm, div_self hr_ne, one_smul]
  · rw [vadd_vsub]
    have hk_ne : k ≠ 0 := by
      intro hk_zero
      apply hu
      rw [h_u_eq, hk_zero, zero_smul]
    have h_k_neg : k < 0 := by
      rcases lt_or_gt_of_ne hk_ne with h_neg | h_pos
      · exact h_neg
      · exfalso
        have hwopp : (s.lineOrOrthRadius a.left a.right).WOppSide a.mid s.center := by
          have h_pos_1 : (0 : ℝ) < 1 - k / 2 := h_one_sub_pos
          have h_pos_2 : (0 : ℝ) < k / 2 := by linarith
          exact AffineSubspace.wOppSide_of_vsub_eq_smul
            (m := a.mid -ᵥ s.center) (c₁ := 1 - k / 2) (c₂ := -(k / 2))
            hF_mem hF_mem hmid_minus_F hctr_minus_F
            (mul_nonpos_of_nonneg_of_nonpos h_pos_1.le (by linarith))
        have h_ctr_not_in_L : s.center ∉ s.lineOrOrthRadius a.left a.right := by
          intro hctr
          rw [hL_eq] at hctr
          have hdir_mem : (s.center -ᵥ F : V) ∈
              (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction :=
            AffineSubspace.vsub_mem_direction hctr
              (show F ∈ line[ℝ, a.left, a.right] from hL_eq ▸ hF_mem)
          rw [hctr_minus_F] at hdir_mem
          have hzero := h_c_zero_of_mem _ hdir_mem
          have : k = 0 := by linarith
          exact hk_ne this
        have hsopp : (s.lineOrOrthRadius a.left a.right).SOppSide a.mid s.center :=
          ⟨hwopp, h_mid_not_in_L, h_ctr_not_in_L⟩
        exact hsopp.not_sSameSide hss
    rw [show -((a.left -ᵥ s.center) + (a.right -ᵥ s.center)) = (-k) • (a.mid -ᵥ s.center)
          from by rw [h_u_eq, neg_smul]]
    have h_neg_k_pos : (0 : ℝ) < -k := by linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_neg_k_pos, hm_norm, smul_smul]
    rw [show s.radius / (-k * s.radius) * -k = 1 from by field_simp]
    rw [one_smul]
  · rw [vadd_vsub]
    have hk_ne : k ≠ 0 := by
      intro hk_zero
      apply hu
      rw [h_u_eq, hk_zero, zero_smul]
    have h_k_pos : 0 < k := by
      rcases lt_or_gt_of_ne hk_ne with h_neg | h_pos
      · exfalso
        have hwsame : (s.lineOrOrthRadius a.left a.right).WSameSide a.mid s.center := by
          have h_pos_1 : (0 : ℝ) < 1 - k / 2 := h_one_sub_pos
          have h_pos_2 : (0 : ℝ) < -(k / 2) := by linarith
          exact AffineSubspace.wSameSide_of_vsub_eq_smul
            (m := a.mid -ᵥ s.center) (c₁ := 1 - k / 2) (c₂ := -(k / 2))
            hF_mem hF_mem hmid_minus_F hctr_minus_F (mul_nonneg h_pos_1.le h_pos_2.le)
        have h_ctr_not_in_L : s.center ∉ s.lineOrOrthRadius a.left a.right := by
          intro hctr
          rw [hL_eq] at hctr
          have hdir_mem : (s.center -ᵥ F : V) ∈
              (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction :=
            AffineSubspace.vsub_mem_direction hctr
              (show F ∈ line[ℝ, a.left, a.right] from hL_eq ▸ hF_mem)
          rw [hctr_minus_F] at hdir_mem
          have hzero := h_c_zero_of_mem _ hdir_mem
          have : k = 0 := by linarith
          exact hk_ne this
        have hssame : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center :=
          ⟨hwsame, h_mid_not_in_L, h_ctr_not_in_L⟩
        exact hss hssame
      · exact h_pos
    rw [h_u_eq, norm_smul, Real.norm_eq_abs, abs_of_pos h_k_pos, hm_norm, smul_smul]
    rw [show s.radius / (k * s.radius) * k = 1 from by field_simp]
    rw [one_smul]

/-- The measure-bisecting midpoint of a non-degenerate arc lies on the sphere. -/
theorem midpoint_mem (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∈ s := by
  rw [midpoint_eq_mid a hnd]
  exact a.mid_mem

/-- The measure-bisecting midpoint of a non-degenerate arc lies on the arc. -/
theorem midpoint_mem_arc (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∈ a := by
  rw [midpoint_eq_mid a hnd]
  exact mid_mem_arc a

/-- The measure-bisecting midpoint of a non-degenerate arc differs from the left endpoint. -/
theorem midpoint_ne_left (a : Arc s) (hnd : ¬a.IsDegenerate) : a.midpoint ≠ a.left := by
  rw [midpoint_eq_mid a hnd]
  exact not_isSinglePoint_of_left_ne_right a ((left_ne_right_iff_not_isDegenerate a).mpr hnd)

/-- The measure-bisecting midpoint of a non-degenerate arc differs from the right endpoint. -/
theorem midpoint_ne_right (a : Arc s) (hnd : ¬a.IsDegenerate) : a.midpoint ≠ a.right := by
  rw [midpoint_eq_mid a hnd]
  exact fun h =>
    ((left_ne_right_iff_not_isDegenerate a).mpr hnd) (left_eq_right_of_mid_eq_right a h)

/-- The measure-bisecting midpoint of a non-degenerate arc lies in its interior. -/
theorem midpoint_mem_interior (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∈ a.interior :=
  mem_interior_of_mem_of_ne_left_of_ne_right
    (midpoint_mem_arc a hnd) (midpoint_ne_left a hnd) (midpoint_ne_right a hnd)

/-- The measure-bisecting midpoint of a non-degenerate arc does not lie on the chord (or, in the
semicircle case, tangent) line `s.lineOrOrthRadius a.left a.right`. -/
theorem midpoint_not_mem_lineOrOrthRadius (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∉ s.lineOrOrthRadius a.left a.right := by
  have hLR := (left_ne_right_iff_not_isDegenerate a).mpr hnd
  rw [midpoint_eq_mid a hnd]
  exact mid_notMem_lineOrOrthRadius a hLR

/-- The measure-bisecting midpoint of a non-degenerate arc does not lie on the chord line
`line[a.left, a.right]` (the non-degenerate specialization of
`midpoint_not_mem_lineOrOrthRadius`). -/
theorem midpoint_not_mem_line (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∉ line[ℝ, a.left, a.right] := by
  rw [midpoint_eq_mid a hnd]
  exact a.mid_notMem_line ((left_ne_right_iff_not_isDegenerate a).mpr hnd)

open Classical in
/-- Each endpoint subtends the central angle `a.measure / 2` to the measure-bisecting midpoint. -/
theorem angle_center_midpoint_eq_half_measure (a : Arc s) (hnd : ¬a.IsDegenerate) :
    ∠ a.left s.center a.midpoint = a.measure / 2 ∧
      ∠ a.midpoint s.center a.right = a.measure / 2 := by
  classical
  rw [midpoint_eq_mid a hnd]
  have hLR : a.left ≠ a.right :=
    (left_ne_right_iff_not_isDegenerate a).mpr hnd
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne a.left_mem a.right_mem hLR
  have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr_ne
  set v : V := a.left -ᵥ s.center with hv_def
  set w : V := a.right -ᵥ s.center with hw_def
  set m : V := a.mid -ᵥ s.center with hm_def
  have hv_norm : ‖v‖ = s.radius := by rw [hv_def]; exact norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖w‖ = s.radius := by rw [hw_def]; exact norm_vsub_center_eq_radius a.right_mem
  have hm_norm : ‖m‖ = s.radius := by rw [hm_def]; exact norm_vsub_center_eq_radius a.mid_mem
  have hmm_eq : ⟪m, m⟫ = s.radius ^ 2 := by
    rw [real_inner_self_eq_norm_sq, hm_norm]
  have hr_sq_pos : (0 : ℝ) < s.radius ^ 2 := pow_pos hr_pos 2
  have h_chord_eq : (a.right -ᵥ a.left : V) = w - v := by
    show (a.right -ᵥ a.left : V) = (a.right -ᵥ s.center) - (a.left -ᵥ s.center)
    exact (vsub_sub_vsub_cancel_right _ _ _).symm
  have h_mid_perp : ⟪m, w - v⟫ = 0 := by
    rw [← h_chord_eq]; exact a.inner_mid_vsub_center_right_vsub_left
  have h_vm_eq_wm : ⟪v, m⟫ = ⟪w, m⟫ := by
    rw [inner_sub_right, sub_eq_zero] at h_mid_perp
    rw [show ⟪v, m⟫ = ⟪m, v⟫ from (real_inner_comm v m).symm]
    rw [show ⟪w, m⟫ = ⟪m, w⟫ from (real_inner_comm w m).symm]
    exact h_mid_perp.symm
  have h_angles_eq : ∠ a.left s.center a.mid = ∠ a.mid s.center a.right := by
    rw [angle_comm a.mid s.center a.right]
    refine Real.injOn_cos
      ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ ?_
    show Real.cos (InnerProductGeometry.angle v m) =
         Real.cos (InnerProductGeometry.angle w m)
    rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle,
        hv_norm, hw_norm, h_vm_eq_wm]
  suffices h : ∠ a.left s.center a.mid = a.measure / 2 by
    exact ⟨h, h_angles_eq ▸ h⟩
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (sum_left_right_vsub_center_mem_span_mid a)
  have h_u_eq : v + w = k • m := by
    rw [hv_def, hw_def, hm_def]
    exact hk.symm
  have hk_def_v : k = 2 * ⟪v, m⟫ / s.radius ^ 2 := by
    have h_inner := congrArg (fun x : V => ⟪x, m⟫) h_u_eq
    change ⟪v + w, m⟫ = ⟪k • m, m⟫ at h_inner
    rw [inner_add_left, real_inner_smul_left, h_vm_eq_wm, hmm_eq] at h_inner
    rw [eq_div_iff hr_sq_pos.ne']
    linarith
  have h_k_lt_2 : k < 2 := by
    have h_u_norm : ‖v + w‖ = |k| * s.radius := by
      rw [h_u_eq, norm_smul, Real.norm_eq_abs, hm_norm]
    have h_u_norm_le : ‖v + w‖ ≤ 2 * s.radius := by
      calc ‖v + w‖ ≤ ‖v‖ + ‖w‖ := norm_add_le _ _
        _ = 2 * s.radius := by rw [hv_norm, hw_norm]; ring
    have h_abs_le : |k| ≤ 2 := by
      have hh := h_u_norm ▸ h_u_norm_le
      nlinarith
    have h_lt : |k| < 2 := by
      rcases lt_or_eq_of_le h_abs_le with h_lt | h_eq
      · exact h_lt
      · exfalso
        have h_u_norm_eq : ‖v + w‖ = 2 * s.radius := by rw [h_u_norm, h_eq]
        have h_u_sq : ‖v + w‖ ^ 2 = (2 * s.radius) ^ 2 := by rw [h_u_norm_eq]
        have h_u_inner : ‖v + w‖ ^ 2 = 2 * s.radius ^ 2 + 2 * ⟪v, w⟫ := by
          rw [norm_add_sq_real, hv_norm, hw_norm]; ring
        have h_vw : ⟪v, w⟫ = s.radius ^ 2 := by nlinarith
        have h_vw_prod : ⟪v, w⟫ = ‖v‖ * ‖w‖ := by rw [h_vw, hv_norm, hw_norm]; ring
        have h_smul_eq : ‖w‖ • v = ‖v‖ • w := inner_eq_norm_mul_iff_real.mp h_vw_prod
        rw [hv_norm, hw_norm] at h_smul_eq
        have h_vw_eq : v = w := smul_right_injective V hr_ne h_smul_eq
        apply hLR
        have h1 : v +ᵥ s.center = w +ᵥ s.center := by rw [h_vw_eq]
        rwa [hv_def, hw_def, vsub_vadd, vsub_vadd] at h1
    exact (abs_lt.mp h_lt).2
  have h_one_sub_pos : (0 : ℝ) < 1 - k / 2 := by linarith
  have h_cos_AOM : Real.cos (∠ a.left s.center a.mid) = k / 2 := by
    show Real.cos (InnerProductGeometry.angle v m) = k / 2
    rw [InnerProductGeometry.cos_angle, hv_norm, hm_norm, hk_def_v]
    field_simp
  have h_inner_vw : ⟪v, w⟫ = (k ^ 2 / 2 - 1) * s.radius ^ 2 := by
    have h_sq : ‖v + w‖ ^ 2 = k ^ 2 * s.radius ^ 2 := by
      rw [h_u_eq, norm_smul, Real.norm_eq_abs, hm_norm, mul_pow, sq_abs]
    have h_sq' : ‖v + w‖ ^ 2 = 2 * s.radius ^ 2 + 2 * ⟪v, w⟫ := by
      rw [norm_add_sq_real, hv_norm, hw_norm]; ring
    linarith
  have h_cos_AOC : Real.cos (∠ a.left s.center a.right) = k ^ 2 / 2 - 1 := by
    show Real.cos (InnerProductGeometry.angle v w) = k ^ 2 / 2 - 1
    rw [InnerProductGeometry.cos_angle, hv_norm, hw_norm, h_inner_vw]
    field_simp
  have h_AOC_nn : 0 ≤ ∠ a.left s.center a.right :=
    angle_nonneg _ _ _
  have h_AOC_le_pi : ∠ a.left s.center a.right ≤ π :=
    angle_le_pi _ _ _
  have h_half_AOC_nn : 0 ≤ ∠ a.left s.center a.right / 2 := by linarith
  have h_half_AOC_le_pi_half : ∠ a.left s.center a.right / 2 ≤ π / 2 := by linarith
  have h_cos_half_AOC_nn :
      0 ≤ Real.cos (∠ a.left s.center a.right / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h_half_AOC_le_pi_half⟩
  have h_cos_half_AOC :
      Real.cos (∠ a.left s.center a.right / 2) = |k| / 2 := by
    have hπ_neg : -π ≤ ∠ a.left s.center a.right := by
      linarith [Real.pi_pos, h_AOC_nn]
    rw [Real.cos_half hπ_neg h_AOC_le_pi, h_cos_AOC,
        show (1 + (k ^ 2 / 2 - 1)) / 2 = (k / 2) ^ 2 from by ring,
        Real.sqrt_sq_eq_abs, abs_div]
    congr 1
    exact abs_of_pos (by norm_num : (0 : ℝ) < 2)
  set L : AffineSubspace ℝ P := s.lineOrOrthRadius a.left a.right with hL_def
  have hL_eq : L = line[ℝ, a.left, a.right] := lineOrOrthRadius_of_ne hLR
  set F : P := _root_.midpoint ℝ a.left a.right with hF_def
  have hF_mem : F ∈ L := by
    rw [hL_eq, hF_def]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hF_sub : F -ᵥ s.center = (k / 2) • m := by
    rw [hF_def, midpoint_vsub, ← hv_def, ← hw_def, ← smul_add, h_u_eq, smul_smul,
        invOf_eq_inv]
    congr 1; ring
  have hmid_minus_F : a.mid -ᵥ F = (1 - k / 2) • m := by
    have h1 : (a.mid -ᵥ F : V) = m - (F -ᵥ s.center) :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    rw [h1, hF_sub]; module
  have hctr_minus_F : s.center -ᵥ F = (-(k / 2)) • m := by
    rw [show (s.center -ᵥ F : V) = -(F -ᵥ s.center) from
          (neg_vsub_eq_vsub_rev _ _).symm,
        hF_sub, neg_smul]
  have hL_dir_chord : (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction =
      ℝ ∙ (w - v) := by
    rw [direction_affineSpan, vectorSpan_pair_rev, ← h_chord_eq]
  have h_c_zero_of_mem : ∀ c : ℝ,
      (c • m : V) ∈ (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction →
        c = 0 := by
    intro c hmem
    rw [hL_dir_chord] at hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hh := congrArg (fun x => ⟪x, m⟫) ht
    simp only at hh
    rw [real_inner_smul_left, real_inner_smul_left, hmm_eq] at hh
    have h_inner_zero : ⟪w - v, m⟫ = 0 := by
      rw [real_inner_comm, h_mid_perp]
    rw [h_inner_zero, mul_zero] at hh
    nlinarith [hr_sq_pos]
  have h_mid_not_in_L : a.mid ∉ L := by
    intro hmem
    rw [hL_eq] at hmem
    have hdir_mem : (a.mid -ᵥ F : V) ∈
        (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction :=
      AffineSubspace.vsub_mem_direction hmem
        (show F ∈ line[ℝ, a.left, a.right] from hL_eq ▸ hF_mem)
    rw [hmid_minus_F] at hdir_mem
    have h_zero := h_c_zero_of_mem _ hdir_mem
    linarith
  have h_ctr_not_in_L_of_k_ne : k ≠ 0 → s.center ∉ L := by
    intro hk_ne hctr
    rw [hL_eq] at hctr
    have hdir_mem : (s.center -ᵥ F : V) ∈
        (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction :=
      AffineSubspace.vsub_mem_direction hctr
        (show F ∈ line[ℝ, a.left, a.right] from hL_eq ▸ hF_mem)
    rw [hctr_minus_F] at hdir_mem
    have h_zero := h_c_zero_of_mem _ hdir_mem
    apply hk_ne
    linarith
  have h_aom_nn : 0 ≤ ∠ a.left s.center a.mid :=
    angle_nonneg _ _ _
  have h_aom_le_pi : ∠ a.left s.center a.mid ≤ π :=
    angle_le_pi _ _ _
  have h_meas_nn : 0 ≤ a.measure := measure_nonneg a
  have h_meas_le_2pi : a.measure ≤ 2 * π := measure_le_two_pi a
  have h_meas_half_nn : 0 ≤ a.measure / 2 := by linarith
  have h_meas_half_le_pi : a.measure / 2 ≤ π := by linarith [Real.pi_pos]
  refine Real.injOn_cos ⟨h_aom_nn, h_aom_le_pi⟩ ⟨h_meas_half_nn, h_meas_half_le_pi⟩ ?_
  rw [h_cos_AOM, measure, if_neg hr_ne]
  split_ifs with hss
  · have h_k_neg : k < 0 := by
      rcases lt_trichotomy k 0 with h_neg | h_zero | h_pos
      · exact h_neg
      · exfalso
        have h_uw_zero : v + w = 0 := by rw [h_u_eq, h_zero, zero_smul]
        have hF_eq_ctr : F = s.center := by
          have h_midpoint_sub : F -ᵥ s.center = (0 : V) := by
            rw [hF_def, midpoint_vsub, ← hv_def, ← hw_def, ← smul_add, h_uw_zero,
                smul_zero]
          have h1 : (F -ᵥ s.center) +ᵥ s.center = (0 : V) +ᵥ s.center := by
            rw [h_midpoint_sub]
          rwa [vsub_vadd, zero_vadd] at h1
        have hctr_in_L : s.center ∈ L := hF_eq_ctr ▸ hF_mem
        exact hss.2.2 hctr_in_L
      · exfalso
        have h_kh_pos : 0 < k / 2 := by linarith
        have hwopp : L.WOppSide a.mid s.center := by
          exact AffineSubspace.wOppSide_of_vsub_eq_smul
            (m := m) (c₁ := 1 - k / 2) (c₂ := -(k / 2))
            hF_mem hF_mem hmid_minus_F hctr_minus_F
            (mul_nonpos_of_nonneg_of_nonpos h_one_sub_pos.le (by linarith))
        have hctr_not_in_L : s.center ∉ L := h_ctr_not_in_L_of_k_ne h_pos.ne'
        have hsopp : L.SOppSide a.mid s.center :=
          ⟨hwopp, h_mid_not_in_L, hctr_not_in_L⟩
        exact hsopp.not_sSameSide hss
    rw [show (2 * π - ∠ a.left s.center a.right) / 2 =
          π - ∠ a.left s.center a.right / 2 from by ring,
        Real.cos_pi_sub, h_cos_half_AOC, abs_of_neg h_k_neg]
    ring
  · have h_k_nn : 0 ≤ k := by
      by_contra h_neg
      push Not at h_neg
      have h_kh_neg : -(k / 2) > 0 := by linarith
      have hwsame : L.WSameSide a.mid s.center := by
        exact AffineSubspace.wSameSide_of_vsub_eq_smul
          (m := m) (c₁ := 1 - k / 2) (c₂ := -(k / 2))
          hF_mem hF_mem hmid_minus_F hctr_minus_F
          (mul_nonneg h_one_sub_pos.le h_kh_neg.le)
      have hctr_not_in_L : s.center ∉ L := h_ctr_not_in_L_of_k_ne h_neg.ne
      have hssame : L.SSameSide a.mid s.center :=
        ⟨hwsame, h_mid_not_in_L, hctr_not_in_L⟩
      exact hss hssame
    rw [h_cos_half_AOC, abs_of_nonneg h_k_nn]

/-- The measure-bisecting midpoint lies on the perpendicular bisector of the chord. -/
theorem midpoint_mem_perpBisector (a : Arc s) (hnd : ¬a.IsDegenerate) :
    a.midpoint ∈ AffineSubspace.perpBisector a.left a.right := by
  rw [midpoint_eq_mid a hnd]
  exact a.line_center_mid_le_perpBisector (right_mem_affineSpan_pair ℝ s.center a.mid)

/-- For a minor arc, the measure-bisecting midpoint equals `minorMidpoint`. -/
theorem midpoint_minor_eq_minorMidpoint {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) (hne : A ≠ C) :
    (minor hA hC hND).midpoint = minorMidpoint s A C := by
  have hLR : (minor hA hC hND).left ≠ (minor hA hC hND).right := by
    simp only [minor_left, minor_right]; exact hne
  have hnd : ¬(minor hA hC hND).IsDegenerate := by
    rintro (hsp | hfc)
    · exact not_isSinglePoint_of_left_ne_right _ hLR hsp
    · exact not_isFullCircle_of_left_ne_right _ hLR hfc
  rw [midpoint_eq_mid _ hnd]
  rfl

/-- For a major arc, the measure-bisecting midpoint is the antipodal point of `minorMidpoint`. -/
theorem midpoint_major_eq_pointReflection_minorMidpoint
    {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) (hne : A ≠ C) :
    (major hA hC hND).midpoint =
      AffineEquiv.pointReflection ℝ s.center (minorMidpoint s A C) := by
  have hLR : (major hA hC hND).left ≠ (major hA hC hND).right := by
    simp only [major_left, major_right]; exact hne
  have hnd : ¬(major hA hC hND).IsDegenerate := by
    rintro (hsp | hfc)
    · exact not_isSinglePoint_of_left_ne_right _ hLR hsp
    · exact not_isFullCircle_of_left_ne_right _ hLR hfc
  rw [midpoint_eq_mid _ hnd, major_mid]
  rfl

end

/-! ### Inscribed angle and tangent-chord angle -/

section Inscribed

variable [Fact (Module.finrank ℝ V = 2)]

noncomputable section

/-- **Inscribed angle theorem**: if `B` lies in the interior of the opposite arc, the inscribed
angle `∠ a.left B a.right` equals `a.measure / 2`. -/
theorem inscribed_angle_eq_half_measure (a : Arc s)
    {B : P} (hB : B ∈ a.opposite.interior)
    (hBl : B ≠ a.left) (hBr : B ≠ a.right) :
    ∠ a.left B a.right = a.measure / 2 := by
  haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
  classical
  have hB_mem := mem_sphere_of_mem_interior hB
  have hB_ss := sSameSide_of_mem_interior hB
  rw [opposite_left, opposite_right] at hB_ss
  by_cases hLR : a.left = a.right
  · rcases isSinglePoint_or_isFullCircle_of_left_eq_right a hLR with h_sp | h_fc
    · have h_meas : a.measure = 0 := measure_eq_zero_of_isSinglePoint a h_sp
      have h_ang : ∠ a.left B a.right = 0 := by
        rw [show a.right = a.left from hLR.symm]
        exact angle_self_of_ne (Ne.symm hBl)
      rw [h_ang, h_meas]; ring
    · exfalso
      have h_opp_mid_eq : a.opposite.mid = a.left := by
        show AffineEquiv.pointReflection ℝ s.center a.mid = a.left
        rw [mid_eq_pointReflection_center_left_of_isFullCircle a h_fc]
        exact AffineEquiv.pointReflection_involutive ℝ s.center a.left
      have h_opp_mid_in : a.opposite.mid ∈ s.lineOrOrthRadius a.left a.right := by
        rw [h_opp_mid_eq]; exact left_mem_lineOrOrthRadius
      exact hB_ss.left_notMem h_opp_mid_in
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne a.left_mem a.right_mem hLR
  have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr_ne
  have hA_ne_O : a.left ≠ s.center := fun heq => by
    have h := mem_sphere.mp a.left_mem
    rw [heq, dist_self] at h; exact hr_ne h.symm
  have hC_ne_O : a.right ≠ s.center := fun heq => by
    have h := mem_sphere.mp a.right_mem
    rw [heq, dist_self] at h; exact hr_ne h.symm
  set v : V := a.left -ᵥ s.center with hv_def
  set w : V := a.right -ᵥ s.center with hw_def
  set b : V := B -ᵥ s.center with hb_def
  have hv_norm : ‖v‖ = s.radius := by rw [hv_def]; exact norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖w‖ = s.radius := by rw [hw_def]; exact norm_vsub_center_eq_radius a.right_mem
  have hb_norm : ‖b‖ = s.radius := by rw [hb_def]; exact norm_vsub_center_eq_radius hB_mem
  have hL_eq : s.lineOrOrthRadius a.left a.right = line[ℝ, a.left, a.right] :=
    lineOrOrthRadius_of_ne hLR
  rw [hL_eq] at hB_ss
  set L : AffineSubspace ℝ P := line[ℝ, a.left, a.right] with hL_def
  haveI : Module.Oriented ℝ V (Fin 2) :=
    ⟨Module.Basis.orientation
      (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩
  have h_oangle : ∡ a.left s.center a.right = (2 : ℤ) • ∡ a.left B a.right :=
    Sphere.oangle_center_eq_two_zsmul_oangle a.left_mem hB_mem a.right_mem
      (Ne.symm hBl.symm) (Ne.symm hBr.symm)
  set θ : ℝ := ∠ a.left s.center a.right with hθ_def
  set φ : ℝ := ∠ a.left B a.right with hφ_def
  have hθ_nn : 0 ≤ θ := angle_nonneg _ _ _
  have hθ_le_pi : θ ≤ π := angle_le_pi _ _ _
  have hφ_nn : 0 ≤ φ := angle_nonneg _ _ _
  have hφ_le_pi : φ ≤ π := angle_le_pi _ _ _
  have h_cos_θ_eq : Real.cos θ = 2 * Real.cos φ ^ 2 - 1 := by
    have h_cos_oAOC :
        Real.Angle.cos (∡ a.left s.center a.right) = Real.cos θ :=
      cos_oangle_eq_cos_angle hA_ne_O hC_ne_O
    have h_cos_oABC :
        Real.Angle.cos (∡ a.left B a.right) = Real.cos φ :=
      cos_oangle_eq_cos_angle hBl.symm hBr.symm
    have h_double :
        Real.Angle.cos ((2 : ℤ) • ∡ a.left B a.right) =
          2 * Real.Angle.cos (∡ a.left B a.right) ^ 2 - 1 := by
      rw [two_zsmul, Real.Angle.cos_add]
      have hsc := Real.Angle.cos_sq_add_sin_sq (∡ a.left B a.right)
      nlinarith
    calc Real.cos θ
        = Real.Angle.cos (∡ a.left s.center a.right) := h_cos_oAOC.symm
      _ = Real.Angle.cos ((2 : ℤ) • ∡ a.left B a.right) := by rw [h_oangle]
      _ = 2 * Real.Angle.cos (∡ a.left B a.right) ^ 2 - 1 := h_double
      _ = 2 * Real.cos φ ^ 2 - 1 := by rw [h_cos_oABC]
  set γ : ℝ := θ / 2 with hγ_def
  have hγ_nn : 0 ≤ γ := by show 0 ≤ θ / 2; linarith
  have hγ_le : γ ≤ π / 2 := by show θ / 2 ≤ π / 2; linarith
  have h_cos_γ_nn : 0 ≤ Real.cos γ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hγ_le⟩
  have h_cos_θ_eq_γ : Real.cos θ = 2 * Real.cos γ ^ 2 - 1 := by
    have h := Real.cos_two_mul γ
    rwa [show (2 : ℝ) * γ = θ from by show 2 * (θ / 2) = θ; ring] at h
  have h_cos_sq_eq : Real.cos φ ^ 2 = Real.cos γ ^ 2 := by
    have h := h_cos_θ_eq.symm.trans h_cos_θ_eq_γ
    linarith
  have hvb_ne : v - b ≠ 0 := by
    intro h
    exact hBl (vsub_left_cancel (sub_eq_zero.mp h)).symm
  have hwb_ne : w - b ≠ 0 := by
    intro h
    exact hBr (vsub_left_cancel (sub_eq_zero.mp h)).symm
  have h_vb_norm_pos : 0 < ‖v - b‖ := norm_pos_iff.mpr hvb_ne
  have h_wb_norm_pos : 0 < ‖w - b‖ := norm_pos_iff.mpr hwb_ne
  have h_denom_pos : 0 < ‖v - b‖ * ‖w - b‖ :=
    mul_pos h_vb_norm_pos h_wb_norm_pos
  have h_vw_inner : ⟪v, w⟫ = s.radius ^ 2 * Real.cos θ := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm v w
    have h_ang : InnerProductGeometry.angle v w = θ := rfl
    rw [h_ang, hv_norm, hw_norm] at h
    linarith
  have h_vb_wb_inner :
      ⟪v - b, w - b⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 - ⟪v + w, b⟫ := by
    have h_expand :
        ⟪v - b, w - b⟫ = ⟪v, w⟫ - ⟪v + w, b⟫ + ‖b‖ ^ 2 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_add_left,
          real_inner_self_eq_norm_sq, real_inner_comm w b, real_inner_comm b v]
      ring
    rw [h_expand, hb_norm, h_vw_inner, h_cos_θ_eq_γ]; ring
  have h_cos_φ_inner :
      Real.cos φ * (‖v - b‖ * ‖w - b‖) = ⟪v - b, w - b⟫ := by
    show Real.cos (InnerProductGeometry.angle (a.left -ᵥ B) (a.right -ᵥ B)) * _ = _
    rw [show (a.left -ᵥ B : V) = v - b from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        show (a.right -ᵥ B : V) = w - b from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        InnerProductGeometry.cos_angle]
    field_simp
  have h_inner_const_on_L : ∀ p ∈ L,
      ⟪p -ᵥ s.center, v + w⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by
    intro p hp
    rw [hL_def] at hp
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
    rw [AffineMap.lineMap_apply] at ht
    have hd_eq : (a.right -ᵥ a.left : V) = w - v :=
      (vsub_sub_vsub_cancel_right _ _ _).symm
    have h_p_sub : (p -ᵥ s.center : V) = v + t • (w - v) := by
      have h1 : (p -ᵥ s.center : V) = (p -ᵥ a.left) + (a.left -ᵥ s.center) :=
        (vsub_add_vsub_cancel _ _ _).symm
      have h2 : (p -ᵥ a.left : V) = t • (w - v) := by
        rw [← ht, vadd_vsub, hd_eq]
      rw [h1, h2, ← hv_def]; abel
    rw [h_p_sub]
    have h_perp : ⟪w - v, v + w⟫ = 0 := by
      rw [inner_sub_left, inner_add_right, inner_add_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          hv_norm, hw_norm, real_inner_comm v w]
      ring
    rw [inner_add_left, real_inner_smul_left, h_perp, mul_zero, add_zero,
        inner_add_right, real_inner_self_eq_norm_sq, hv_norm, h_vw_inner,
        h_cos_θ_eq_γ]
    ring
  have h_meas_half_nn : 0 ≤ a.measure / 2 := by
    have := measure_nonneg a; linarith
  have h_meas_half_le_pi : a.measure / 2 ≤ π := by
    have := measure_le_two_pi a; linarith [Real.pi_pos]
  by_cases h_ss : L.SSameSide a.mid s.center
  · have h_measure : a.measure = 2 * π - θ := by
      rw [measure, if_neg hr_ne]
      have h_ss' :
          (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
        rw [hL_eq]; exact h_ss
      rw [if_pos h_ss']
    have h_opp_sopp_center : L.SOppSide a.opposite.mid s.center := by
      have h1 : L.SOppSide a.mid a.opposite.mid := by
        have := sOppSide_mid_opposite_mid a hLR
        rwa [hL_eq] at this
      exact (h_ss.symm.trans_sOppSide h1).symm
    have h_B_sopp_center : L.SOppSide B s.center :=
      hB_ss.symm.trans_sOppSide h_opp_sopp_center
    have h_B_not_in_L : B ∉ L := h_B_sopp_center.2.1
    have h_center_not_in_L : s.center ∉ L := h_B_sopp_center.2.2
    obtain ⟨p₁, hp₁, p₂, hp₂, hsr⟩ := h_B_sopp_center.1
    have h_inner_p₁ :
        ⟪p₁ -ᵥ s.center, v + w⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 :=
      h_inner_const_on_L p₁ hp₁
    have h_inner_p₂ :
        ⟪p₂ -ᵥ s.center, v + w⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 :=
      h_inner_const_on_L p₂ hp₂
    have h_inner_B_p₁ :
        ⟪B -ᵥ p₁, v + w⟫ =
          ⟪v + w, b⟫ - 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by
      have h1 : (B -ᵥ p₁ : V) = b - (p₁ -ᵥ s.center) := by
        rw [hb_def]; exact (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, inner_sub_left, h_inner_p₁, real_inner_comm b (v + w)]
    rcases hsr with hl | hr0 | ⟨k₁, k₂, hk₁_pos, hk₂_pos, hk_eq⟩
    · exact absurd ((vsub_eq_zero_iff_eq.mp hl) ▸ hp₁) h_B_not_in_L
    · exact absurd ((vsub_eq_zero_iff_eq.mp hr0) ▸ hp₂) h_center_not_in_L
    · have h_ip :
          k₁ * ⟪B -ᵥ p₁, v + w⟫ = k₂ * ⟪p₂ -ᵥ s.center, v + w⟫ := by
        have hh := congrArg (fun x => ⟪x, v + w⟫) hk_eq
        simp only at hh
        rw [real_inner_smul_left, real_inner_smul_left] at hh
        exact hh
      rw [h_inner_B_p₁, h_inner_p₂] at h_ip
      have h_cos_γ_sq_nn : 0 ≤ Real.cos γ ^ 2 := sq_nonneg _
      have h_rad_sq_nn : 0 ≤ s.radius ^ 2 := sq_nonneg _
      have h_lhs_ge : ⟪v + w, b⟫ ≥ 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by
        by_contra h
        push Not at h
        have h_rhs_nn : 0 ≤ k₂ * (2 * s.radius ^ 2 * Real.cos γ ^ 2) := by
          apply mul_nonneg hk₂_pos.le
          positivity
        have h_lhs_neg :
            k₁ * (⟪v + w, b⟫ - 2 * s.radius ^ 2 * Real.cos γ ^ 2) < 0 :=
          mul_neg_of_pos_of_neg hk₁_pos (by linarith)
        linarith [h_ip]
      have h_inner_nonpos : ⟪v - b, w - b⟫ ≤ 0 := by
        rw [h_vb_wb_inner]; linarith
      have h_cos_φ_nonpos : Real.cos φ ≤ 0 := by
        nlinarith [h_cos_φ_inner, h_denom_pos]
      have h_cos_φ_eq : Real.cos φ = -Real.cos γ := by
        have hprod :
            (Real.cos φ - Real.cos γ) * (Real.cos φ + Real.cos γ) = 0 := by
          have heq :
              (Real.cos φ - Real.cos γ) * (Real.cos φ + Real.cos γ) =
                Real.cos φ ^ 2 - Real.cos γ ^ 2 := by ring
          rw [heq, h_cos_sq_eq, sub_self]
        rcases mul_eq_zero.mp hprod with h | h
        · have hγ_zero : Real.cos γ = 0 :=
            le_antisymm (by linarith) h_cos_γ_nn
          linarith
        · linarith
      have h_cos_meas : Real.cos (a.measure / 2) = -Real.cos γ := by
        rw [h_measure,
            show (2 * π - θ) / 2 = π - γ from by show _ = π - θ / 2; ring,
            Real.cos_pi_sub]
      exact Real.injOn_cos ⟨hφ_nn, hφ_le_pi⟩
        ⟨h_meas_half_nn, h_meas_half_le_pi⟩
        (by rw [h_cos_φ_eq, h_cos_meas])
  · have h_measure : a.measure = θ := by
      rw [measure, if_neg hr_ne]
      have h_ss' :
          ¬ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
        rw [hL_eq]; exact h_ss
      rw [if_neg h_ss']
    by_cases h_center_in_L : s.center ∈ L
    · have h_diam : s.IsDiameter a.left a.right :=
        (Sphere.center_mem_affineSpan_pair_iff_isDiameter a.left_mem a.right_mem hLR).mp
          (hL_def ▸ h_center_in_L)
      have h_θ_eq_pi : θ = π :=
        (angle_center_eq_pi_iff_isDiameter a.left_mem a.right_mem hr_ne).mpr h_diam
      have h_γ_eq : γ = π / 2 := by show θ / 2 = π / 2; rw [h_θ_eq_pi]
      have h_cos_γ_zero : Real.cos γ = 0 := by rw [h_γ_eq, Real.cos_pi_div_two]
      have h_cos_φ_zero : Real.cos φ = 0 := by
        have h_sq : Real.cos φ ^ 2 = 0 := by rw [h_cos_sq_eq, h_cos_γ_zero]; ring
        exact pow_eq_zero_iff two_ne_zero |>.mp h_sq
      have h_cos_meas : Real.cos (a.measure / 2) = 0 := by
        rw [h_measure, h_θ_eq_pi]; exact Real.cos_pi_div_two
      exact Real.injOn_cos ⟨hφ_nn, hφ_le_pi⟩
        ⟨h_meas_half_nn, h_meas_half_le_pi⟩
        (by rw [h_cos_φ_zero, h_cos_meas])
    · have h_opp_mid_ss_center : L.SSameSide a.opposite.mid s.center := by
        have h_notmem : s.center ∉ s.lineOrOrthRadius a.left a.right := by
          rw [hL_eq]; exact h_center_in_L
        rw [hL_eq, hL_def] at h_notmem
        have h := sSameSide_opposite_mid_iff a hLR h_notmem
        rw [hL_eq] at h
        exact h.mpr h_ss
      have h_B_ss_center : L.SSameSide B s.center :=
        hB_ss.symm.trans h_opp_mid_ss_center
      have h_B_not_in_L : B ∉ L := h_B_ss_center.2.1
      have h_center_not_in_L : s.center ∉ L := h_B_ss_center.2.2
      obtain ⟨p₁, hp₁, p₂, hp₂, hsr⟩ := h_B_ss_center.1
      have h_inner_p₁ :
          ⟪p₁ -ᵥ s.center, v + w⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 :=
        h_inner_const_on_L p₁ hp₁
      have h_inner_p₂ :
          ⟪p₂ -ᵥ s.center, v + w⟫ = 2 * s.radius ^ 2 * Real.cos γ ^ 2 :=
        h_inner_const_on_L p₂ hp₂
      have h_inner_B_p₁ :
          ⟪B -ᵥ p₁, v + w⟫ =
            ⟪v + w, b⟫ - 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by
        have h1 : (B -ᵥ p₁ : V) = b - (p₁ -ᵥ s.center) := by
          rw [hb_def]; exact (vsub_sub_vsub_cancel_right _ _ _).symm
        rw [h1, inner_sub_left, h_inner_p₁, real_inner_comm b (v + w)]
      have h_inner_center_p₂ :
          ⟪s.center -ᵥ p₂, v + w⟫ = -(2 * s.radius ^ 2 * Real.cos γ ^ 2) := by
        have h1 : (s.center -ᵥ p₂ : V) = -(p₂ -ᵥ s.center) :=
          (neg_vsub_eq_vsub_rev _ _).symm
        rw [h1, inner_neg_left, h_inner_p₂]
      rcases hsr with hl | hr0 | ⟨k₁, k₂, hk₁_pos, hk₂_pos, hk_eq⟩
      · exact absurd ((vsub_eq_zero_iff_eq.mp hl) ▸ hp₁) h_B_not_in_L
      · exact absurd ((vsub_eq_zero_iff_eq.mp hr0) ▸ hp₂) h_center_not_in_L
      · have h_ip :
            k₁ * ⟪B -ᵥ p₁, v + w⟫ = k₂ * ⟪s.center -ᵥ p₂, v + w⟫ := by
          have hh := congrArg (fun x => ⟪x, v + w⟫) hk_eq
          simp only at hh
          rw [real_inner_smul_left, real_inner_smul_left] at hh
          exact hh
        rw [h_inner_B_p₁, h_inner_center_p₂] at h_ip
        have h_cos_γ_pos : 0 < Real.cos γ := by
          refine lt_of_le_of_ne h_cos_γ_nn (Ne.symm ?_)
          intro h0
          have hγ_eq : γ = π / 2 := by
            by_contra h_ne
            have hγ_lt : γ < π / 2 := lt_of_le_of_ne hγ_le h_ne
            have : 0 < Real.cos γ :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hγ_lt⟩
            linarith
          have h_θ_eq_pi : θ = π := by
            have : θ / 2 = π / 2 := hγ_eq
            linarith
          have h_diam : s.IsDiameter a.left a.right :=
            (angle_center_eq_pi_iff_isDiameter a.left_mem a.right_mem hr_ne).mp h_θ_eq_pi
          have h_ctr_in : s.center ∈ L := by
            have := (Sphere.center_mem_affineSpan_pair_iff_isDiameter a.left_mem a.right_mem hLR).mpr h_diam
            rwa [hL_def]
          exact h_center_in_L h_ctr_in
        have h_cos_γ_sq_pos : 0 < Real.cos γ ^ 2 := pow_pos h_cos_γ_pos 2
        have h_2rsq_cs_pos : 0 < 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by positivity
        have h_rhs_le :
            ⟪v + w, b⟫ ≤ 2 * s.radius ^ 2 * Real.cos γ ^ 2 := by
          nlinarith [hk₁_pos, hk₂_pos]
        have h_inner_nonneg : 0 ≤ ⟪v - b, w - b⟫ := by
          rw [h_vb_wb_inner]; linarith
        have h_cos_φ_nonneg : 0 ≤ Real.cos φ := by
          rw [← h_cos_φ_inner] at h_inner_nonneg
          exact nonneg_of_mul_nonneg_left h_inner_nonneg h_denom_pos
        have h_cos_φ_eq : Real.cos φ = Real.cos γ := by
          have h_abs : |Real.cos φ| = |Real.cos γ| := by
            rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, h_cos_sq_eq]
          rwa [abs_of_nonneg h_cos_φ_nonneg, abs_of_nonneg h_cos_γ_nn] at h_abs
        have h_cos_meas : Real.cos (a.measure / 2) = Real.cos γ := by
          rw [h_measure]
        exact Real.injOn_cos ⟨hφ_nn, hφ_le_pi⟩
          ⟨h_meas_half_nn, h_meas_half_le_pi⟩
          (by rw [h_cos_φ_eq, h_cos_meas])

/-- If `Z` lies in the interior of the minor arc `XY`, the angle `∠ X Z Y` is at least
`π / 2`. -/
theorem angle_ge_pi_div_two_of_mem_minor_interior {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬ s.IsDiameter X Y)
    (hZ : Z ∈ (minor hX hY hND).interior) :
    π / 2 ≤ ∠ X Z Y := by
  have hZX : Z ≠ X := by have := ne_left_of_mem_interior hZ; rwa [minor_left] at this
  have hZY : Z ≠ Y := by have := ne_right_of_mem_interior hZ; rwa [minor_right] at this
  have hZ_oo : Z ∈ (minor hX hY hND).opposite.opposite.interior := by
    rw [opposite_opposite]; exact hZ
  have hangle : ∠ X Z Y = (minor hX hY hND).opposite.measure / 2 := by
    have h := inscribed_angle_eq_half_measure
      (minor hX hY hND).opposite hZ_oo
      (by rw [opposite_left, minor_left]; exact hZX)
      (by rw [opposite_right, minor_right]; exact hZY)
    rwa [opposite_left, opposite_right, minor_left, minor_right] at h
  have hmeas : π ≤ (minor hX hY hND).opposite.measure := by
    rw [minor_opposite_eq_major]; exact measure_major_ge_pi hX hY hND
  rw [hangle]; linarith

/-- If `Z` lies in the interior of the major arc `XY`, the angle `∠ X Z Y` is at most
`π / 2`. -/
theorem angle_le_pi_div_two_of_mem_major_interior {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬ s.IsDiameter X Y)
    (hZ : Z ∈ (major hX hY hND).interior) :
    ∠ X Z Y ≤ π / 2 := by
  have hZX : Z ≠ X := by have := ne_left_of_mem_interior hZ; rwa [major_left] at this
  have hZY : Z ≠ Y := by have := ne_right_of_mem_interior hZ; rwa [major_right] at this
  have hZ_maj : Z ∈ (minor hX hY hND).opposite.interior := by
    rw [minor_opposite_eq_major]; exact hZ
  have hangle : ∠ X Z Y = (minor hX hY hND).measure / 2 := by
    have h := inscribed_angle_eq_half_measure (minor hX hY hND) hZ_maj
      (by rw [minor_left]; exact hZX) (by rw [minor_right]; exact hZY)
    rwa [minor_left, minor_right] at h
  rw [hangle]; linarith [measure_minor_le_pi hX hY hND]

/-- If `Z` lies in the interior of the minor arc `XY`, then `π / 2 < ∠ X Z Y`. The extra
`X ≠ Y` hypothesis only supplies the nonzero radius needed for strictness; without it, the
possible single-point minor arc has empty interior. -/
theorem pi_div_two_lt_angle_of_mem_minor_interior {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y) (hXY : X ≠ Y)
    (hZ : Z ∈ (minor hX hY hND).interior) :
    π / 2 < ∠ X Z Y := by
  have hZX : Z ≠ X := by simpa only [minor_left] using ne_left_of_mem_interior hZ
  have hZY : Z ≠ Y := by simpa only [minor_right] using ne_right_of_mem_interior hZ
  have hangle : ∠ X Z Y = (major hX hY hND).measure / 2 := by
    have h := inscribed_angle_eq_half_measure (major hX hY hND)
      (by rwa [major_opposite_eq_minor])
      (by simpa only [major_left] using hZX) (by simpa only [major_right] using hZY)
    rwa [major_left, major_right] at h
  rw [hangle]
  linarith [pi_lt_measure_major hX hY hND hXY]

/-- If `Z` lies in the interior of the major arc `XY`, then `∠ X Z Y < π / 2`. The extra
`X ≠ Y` hypothesis only supplies the nonzero radius needed for strictness. -/
theorem angle_lt_pi_div_two_of_mem_major_interior {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y) (hXY : X ≠ Y)
    (hZ : Z ∈ (major hX hY hND).interior) :
    ∠ X Z Y < π / 2 := by
  have hZX : Z ≠ X := by simpa only [major_left] using ne_left_of_mem_interior hZ
  have hZY : Z ≠ Y := by simpa only [major_right] using ne_right_of_mem_interior hZ
  have hangle : ∠ X Z Y = (minor hX hY hND).measure / 2 := by
    have h := inscribed_angle_eq_half_measure (minor hX hY hND)
      (by rwa [minor_opposite_eq_major])
      (by simpa only [minor_left] using hZX) (by simpa only [minor_right] using hZY)
    rwa [minor_left, minor_right] at h
  rw [hangle]
  linarith [measure_minor_lt_pi hX hY hND hXY]

/-- A sphere point lies in the major arc's interior exactly when the chord subtends an acute
angle at that point. -/
theorem mem_major_interior_iff_angle_lt_pi_div_two {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y) (hXY : X ≠ Y)
    (hZ : Z ∈ s) :
    Z ∈ (major hX hY hND).interior ↔ ∠ X Z Y < π / 2 := by
  refine ⟨angle_lt_pi_div_two_of_mem_major_interior hX hY hND hXY, fun hacute => ?_⟩
  obtain ⟨hZX, hZY⟩ : Z ≠ X ∧ Z ≠ Y := by
    constructor <;> rintro rfl <;> simp at hacute
  exact (mem_minor_interior_or_mem_major_interior hX hY hND hZ hZX hZY).resolve_left
    fun h => absurd (angle_ge_pi_div_two_of_mem_minor_interior hX hY hND h)
      (not_le.mpr hacute)

/-- A sphere point lies in the minor arc's interior exactly when the chord subtends an angle
strictly greater than `π / 2` at that point. -/
theorem mem_minor_interior_iff_pi_div_two_lt_angle {X Y Z : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y) (hXY : X ≠ Y)
    (hZ : Z ∈ s) :
    Z ∈ (minor hX hY hND).interior ↔ π / 2 < ∠ X Z Y := by
  refine ⟨pi_div_two_lt_angle_of_mem_minor_interior hX hY hND hXY, fun hobtuse => ?_⟩
  obtain ⟨hZX, hZY⟩ : Z ≠ X ∧ Z ≠ Y := by
    constructor <;> rintro rfl <;> simp at hobtuse
  exact (mem_minor_interior_or_mem_major_interior hX hY hND hZ hZX hZY).resolve_right
    fun h => absurd (angle_le_pi_div_two_of_mem_major_interior hX hY hND h)
      (not_le.mpr hobtuse)

/-- If `C` lies in the interior of the opposite arc of the minor arc `XY`, the segment from `C`
to the minor arc's midpoint bisects the angle `∠ X C Y`. -/
theorem angle_bisect_of_mem_opposite {X Y C : P}
    (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬ s.IsDiameter X Y) (hXY : X ≠ Y)
    (hC_opp : C ∈ (minor hX hY hND).opposite.interior) :
    ∠ X C (minor hX hY hND).midpoint = ∠ (minor hX hY hND).midpoint C Y := by
  letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
  letI : Module.Oriented ℝ V (Fin 2) :=
    ⟨Module.Basis.orientation
      (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩
  have hCmem : C ∈ s := mem_sphere_of_mem_interior hC_opp
  have hnd : ¬ (minor hX hY hND).IsDegenerate := by
    rw [← left_ne_right_iff_not_isDegenerate, minor_left, minor_right]; exact hXY
  have hne : (minor hX hY hND).left ≠ (minor hX hY hND).right := by
    rw [minor_left, minor_right]; exact hXY
  set M := (minor hX hY hND).midpoint with hM_def
  have hMmem : M ∈ s := midpoint_mem _ hnd
  have hCX : C ≠ X := by
    have := ne_left_of_mem_interior hC_opp; rwa [opposite_left, minor_left] at this
  have hCY : C ≠ Y := by
    have := ne_right_of_mem_interior hC_opp; rwa [opposite_right, minor_right] at this
  have hM_int : M ∈ (minor hX hY hND).interior :=
    mem_interior_of_mem_of_ne_left_of_ne_right
      (midpoint_mem_arc _ hnd) (midpoint_ne_left _ hnd) (midpoint_ne_right _ hnd)
  have hCM : C ≠ M := fun h =>
    Set.disjoint_left.mp (interior_disjoint_opposite _ hne) hM_int (h ▸ hC_opp)
  have hXCY_eq : ∠ X C Y = (minor hX hY hND).measure / 2 := by
    have h := inscribed_angle_eq_half_measure (minor hX hY hND) hC_opp
      (by rw [minor_left]; exact hCX) (by rw [minor_right]; exact hCY)
    rwa [minor_left, minor_right] at h
  have hXCY_le : ∠ X C Y ≤ π / 2 := by
    rw [hXCY_eq]; linarith [measure_minor_le_pi hX hY hND]
  set L : AffineSubspace ℝ P := s.lineOrOrthRadius X Y with hL_def
  have hMC_opp : L.SOppSide M C := by
    have h := sOppSide_of_mem_interior_of_mem_opposite_interior
      (minor hX hY hND) hne hM_int hC_opp
    rwa [minor_left, minor_right, ← hL_def] at h
  obtain ⟨W, hW_mem, hW_sbtw⟩ := hMC_opp.exists_sbtw
  have hW_line : W ∈ line[ℝ, X, Y] := by rwa [hL_def, lineOrOrthRadius_of_ne hXY] at hW_mem
  have hW_lt : dist W s.center < s.radius := by
    have hlt := hW_sbtw.dist_lt_max_dist s.center
    rwa [mem_sphere.mp hMmem, mem_sphere.mp hCmem, max_self] at hlt
  have hcol : Collinear ℝ ({X, W, Y} : Set P) := by
    rw [show ({X, W, Y} : Set P) = ({W, X, Y} : Set P) by
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact (collinear_insert_iff_of_mem_affineSpan hW_line).2 (collinear_pair ℝ X Y)
  have hXWY : Sbtw ℝ X W Y := sbtw_of_collinear_of_dist_center_lt_radius hcol hX hW_lt hY hXY
  have hCWM : Sbtw ℝ C W M := hW_sbtw.symm
  have hsum : ∠ X C M + ∠ M C Y = ∠ X C Y := by
    rw [angle_comm M C Y]
    have hadd := angle_add_angle_eq_of_sbtw (p := C) hXWY
    rwa [hCWM.angle_eq_right X, angle_comm W C Y, hCWM.angle_eq_right Y] at hadd
  have hb1 : 2 * ∠ X C M ≤ π := by linarith [angle_nonneg M C Y]
  have hb2 : 2 * ∠ M C Y ≤ π := by linarith [angle_nonneg X C M]
  have hcenter : ∠ X s.center M = ∠ M s.center Y := by
    have hhalf := angle_center_midpoint_eq_half_measure (minor hX hY hND) hnd
    rw [minor_left, minor_right, ← hM_def] at hhalf
    exact hhalf.1.trans hhalf.2.symm
  have h1 := Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi
    hX hCmem hMmem hCX hCM hb1
  have h2 := Sphere.angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi
    hMmem hCmem hY hCM hCY hb2
  linarith

/-- Inscribed angles subtended from the interior of the opposite arc are equal. -/
theorem angle_eq_of_mem_opposite_interior (a : Arc s)
    {B₁ B₂ : P} (h₁ : B₁ ∈ a.opposite.interior) (h₂ : B₂ ∈ a.opposite.interior)
    (hB₁l : B₁ ≠ a.left) (hB₁r : B₁ ≠ a.right)
    (hB₂l : B₂ ≠ a.left) (hB₂r : B₂ ≠ a.right) :
    ∠ a.left B₁ a.right = ∠ a.left B₂ a.right := by
  rw [inscribed_angle_eq_half_measure a h₁ hB₁l hB₁r,
      inscribed_angle_eq_half_measure a h₂ hB₂l hB₂r]

/-- Inscribed angles subtended from opposite arcs to the same chord sum to `π`. -/
theorem angle_add_angle_opposite_eq_pi (a : Arc s)
    {B₁ B₂ : P} (h₁ : B₁ ∈ a.opposite.interior) (h₂ : B₂ ∈ a.interior)
    (hB₁l : B₁ ≠ a.left) (hB₁r : B₁ ≠ a.right)
    (hB₂l : B₂ ≠ a.left) (hB₂r : B₂ ≠ a.right) :
    ∠ a.left B₁ a.right + ∠ a.left B₂ a.right = π := by
  have h_B₁_mem : B₁ ∈ s := mem_sphere_of_mem_interior h₁
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne h_B₁_mem a.left_mem hB₁l
  have h_ang₁ : ∠ a.left B₁ a.right = a.measure / 2 :=
    inscribed_angle_eq_half_measure a h₁ hB₁l hB₁r
  have h₂' : B₂ ∈ a.opposite.opposite.interior := by
    rw [opposite_opposite]; exact h₂
  have hB₂l' : B₂ ≠ a.opposite.left := by rw [opposite_left]; exact hB₂l
  have hB₂r' : B₂ ≠ a.opposite.right := by rw [opposite_right]; exact hB₂r
  have h_ang₂' : ∠ a.opposite.left B₂ a.opposite.right = a.opposite.measure / 2 :=
    inscribed_angle_eq_half_measure a.opposite h₂' hB₂l' hB₂r'
  rw [opposite_left, opposite_right] at h_ang₂'
  rw [h_ang₁, h_ang₂', ← add_div,
      measure_add_measure_opposite a hr_ne]
  ring

omit [Fact (Module.finrank ℝ V = 2)]
/-- **Tangent-chord angle theorem**: for a minor arc, the angle between the radius
`a.left -ᵥ s.center` and the chord `a.right -ᵥ a.left` equals `π / 2 + a.measure / 2`. -/
theorem tangent_chord_angle_eq_pi_div_two_add_half_measure (a : Arc s)
    (hne : a.left ≠ a.right) (h_le : a.measure ≤ π) :
    InnerProductGeometry.angle
        (a.left -ᵥ s.center) (a.right -ᵥ a.left)
      = π / 2 + a.measure / 2 := by
  have hr_ne : s.radius ≠ 0 :=
    radius_ne_zero_of_mem_of_mem_of_ne a.left_mem a.right_mem hne
  have hr_pos : 0 < s.radius := radius_pos_of_mem a.left_mem hr_ne
  set v : V := a.left -ᵥ s.center with hv_def
  set w : V := a.right -ᵥ s.center with hw_def
  have hv_norm : ‖v‖ = s.radius := by rw [hv_def]; exact norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖w‖ = s.radius := by rw [hw_def]; exact norm_vsub_center_eq_radius a.right_mem
  have h_chord : (a.right -ᵥ a.left : V) = w - v :=
    (vsub_sub_vsub_cancel_right _ _ _).symm
  set θ : ℝ := ∠ a.left s.center a.right with hθ_def
  have hθ_nn : 0 ≤ θ := angle_nonneg _ _ _
  have hθ_le_pi : θ ≤ π := angle_le_pi _ _ _
  have hL_eq : s.lineOrOrthRadius a.left a.right = line[ℝ, a.left, a.right] :=
    lineOrOrthRadius_of_ne hne
  have h_measure : a.measure = θ := by
    by_cases hss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
    · exfalso
      have h_mes : a.measure = 2 * π - θ := by
        rw [measure, if_neg hr_ne, if_pos hss]
      rw [h_mes] at h_le
      have hθ_eq_pi : θ = π := le_antisymm hθ_le_pi (by linarith)
      have h_diam : s.IsDiameter a.left a.right :=
        (angle_center_eq_pi_iff_isDiameter a.left_mem a.right_mem hr_ne).mp hθ_eq_pi
      have h_center_in_chord : s.center ∈ line[ℝ, a.left, a.right] :=
        (Sphere.center_mem_affineSpan_pair_iff_isDiameter a.left_mem a.right_mem hne).mpr h_diam
      have h_center_in_LOR : s.center ∈ s.lineOrOrthRadius a.left a.right := by
        rw [hL_eq]; exact h_center_in_chord
      exact hss.2.2 h_center_in_LOR
    · rw [measure, if_neg hr_ne, if_neg hss]
  have h_vw_inner : ⟪v, w⟫ = s.radius ^ 2 * Real.cos θ := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm v w
    have h_ang : InnerProductGeometry.angle v w = θ := rfl
    rw [h_ang, hv_norm, hw_norm] at h
    linarith
  have h_wv_inner : ⟪w, v⟫ = s.radius ^ 2 * Real.cos θ := by
    rw [real_inner_comm]; exact h_vw_inner
  have hθ_pos : 0 < θ := by
    have hθ_ne : θ ≠ 0 := by
      intro hθ_zero
      exact hne ((angle_center_eq_zero_iff_eq a.left_mem a.right_mem hr_ne).mp
        (by simpa [hθ_def] using hθ_zero))
    exact hθ_nn.lt_of_ne' hθ_ne
  have h_half_id : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    have h_2half : 2 * (θ / 2) = θ := by ring
    rw [h_2half] at h
    have h_pyth := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have h_sin_half_pos : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h_wv_norm_sq : ‖w - v‖ ^ 2 = (2 * s.radius * Real.sin (θ / 2)) ^ 2 := by
    rw [@norm_sub_sq_real, hv_norm, hw_norm, h_wv_inner,
        show Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 from by linarith]
    ring
  have h_wv_norm : ‖w - v‖ = 2 * s.radius * Real.sin (θ / 2) := by
    have h_lhs_nn : 0 ≤ ‖w - v‖ := norm_nonneg _
    have h_rhs_nn : 0 ≤ 2 * s.radius * Real.sin (θ / 2) := by positivity
    have h := congrArg Real.sqrt h_wv_norm_sq
    rwa [Real.sqrt_sq h_lhs_nn, Real.sqrt_sq h_rhs_nn] at h
  have h_inner_v_wv :
      ⟪v, w - v⟫ = -(2 * s.radius ^ 2 * Real.sin (θ / 2) ^ 2) := by
    rw [inner_sub_right, h_vw_inner, real_inner_self_eq_norm_sq, hv_norm,
        show Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 from by linarith]
    ring
  have h_cos_angle :
      Real.cos (InnerProductGeometry.angle v (w - v)) = -Real.sin (θ / 2) := by
    rw [InnerProductGeometry.cos_angle, hv_norm, h_wv_norm, h_inner_v_wv]
    field_simp
  have h_target_cos : Real.cos (π / 2 + θ / 2) = -Real.sin (θ / 2) := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  rw [h_chord, h_measure]
  refine Real.injOn_cos
    ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
    ⟨by linarith [Real.pi_pos], by linarith⟩ ?_
  rw [h_cos_angle, h_target_cos]

end

end Inscribed

end Arc

end Sphere

end EuclideanGeometry
