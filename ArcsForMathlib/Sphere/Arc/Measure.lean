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
# Arc measure

This file defines the measure and midpoint of an arc on a sphere. It relates arc measure to
opposite arcs, the minor and major constructors, chord length, and central angles, and proves
the inscribed angle theorem in two dimensions.

## Main definitions

* `EuclideanGeometry.Sphere.Arc.measure`: the measure of an arc in radians, in `[0, 2π]`.
* `EuclideanGeometry.Sphere.Arc.midpoint`: the arc midpoint, defined to be the structural anchor.

## Main results

* `EuclideanGeometry.Sphere.Arc.measure_add_measure_opposite`: on a sphere of nonzero radius,
  the measures of an arc and its opposite sum to `2π`.
* `EuclideanGeometry.Sphere.Arc.measure_minor`, `EuclideanGeometry.Sphere.Arc.measure_major`:
  for non-diametral endpoints, the minor arc has measure equal to the central angle, and the
  major arc has measure `2π` minus that angle.
* `EuclideanGeometry.Sphere.Arc.sSameSide_iff_pi_lt_measure`: on a sphere of nonzero radius,
  the anchor lies strictly on the center's side of the separating subspace exactly when the
  measure exceeds `π`.
* `EuclideanGeometry.Sphere.Arc.mid_eq_minorMidpoint`,
  `EuclideanGeometry.Sphere.Arc.mid_eq_pointReflection_minorMidpoint`: below and above measure
  `π`, the anchor is the normalized endpoint sum and its antipode, respectively.
* `EuclideanGeometry.Sphere.Arc.sum_vsub_center_eq_two_mul_cos_half_measure_smul`: the sum
  of the endpoint radius vectors is `2 * Real.cos (a.measure / 2)` times the anchor radius vector.
* `EuclideanGeometry.Sphere.Arc.dist_left_right_eq_two_mul_radius_mul_sin_measure`: the chord
  length is `2 * s.radius * Real.sin (a.measure / 2)`.
* `EuclideanGeometry.Sphere.Arc.angle_center_midpoint_eq_half_measure`: on a sphere of nonzero
  radius, the central angle from either endpoint to the midpoint equals half the arc measure.
* `EuclideanGeometry.Sphere.Arc.inscribed_angle_eq_half_measure`: in two dimensions, the angle
  subtended by the endpoints at a point in the opposite arc's interior equals half the arc measure.

## Implementation notes

Measure is defined using the central angle and the side of the chord containing the anchor.
On a sphere of radius zero it is defined to be zero. On a sphere of nonzero radius, single-point
and full-circle arcs have measures `0` and `2π`, respectively.

The midpoint is definitionally equal to `mid`. Its geometric characterization by half the arc
measure is proved from the endpoint-sum identity, including for single-point and full-circle arcs.
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

/-- An arc on a sphere of radius zero has measure zero. -/
theorem measure_eq_zero_of_radius_eq_zero (a : Arc s) (hr : s.radius = 0) :
    a.measure = 0 := by rw [measure, if_pos hr]

/-- When the anchor is strictly on the center's side, the measure is the reflex central angle. -/
theorem measure_eq_two_pi_sub_angle_of_sSameSide (a : Arc s) (hr : s.radius ≠ 0)
    (hss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center) :
    a.measure = 2 * π - ∠ a.left s.center a.right := by
  rw [measure, if_neg hr, if_pos hss]

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
  · exact absurd (by rw [h]; exact left_mem_lineOrOrthRadius) hss.left_notMem
  · rw [← left_eq_right_of_isSinglePoint a h]
    refine angle_self_of_ne fun heq => hr ?_
    have h2 := mem_sphere.mp a.left_mem
    rw [heq, dist_self] at h2
    exact h2.symm

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
  have hmid_not_L : a.mid ∉ s.lineOrOrthRadius a.left a.right :=
    a.mid_notMem_lineOrOrthRadius h.2
  have hSS : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
    refine AffineSubspace.sSameSide_of_vsub_eq_smul
      (m := s.center -ᵥ a.left) (c₁ := 2) (c₂ := 1)
      left_mem_lineOrOrthRadius left_mem_lineOrOrthRadius h_mid_sub ?_ ?_
      hmid_not_L hcenter_not_L
    · rw [one_smul]
    · norm_num
  rw [a.measure_eq_two_pi_sub_angle_of_sSameSide hr hSS, ← h_lr,
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

/-! ### Central angles and half-measure cosine -/

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

/-- On a sphere of nonzero radius, an arc has measure `π` if and only if
its endpoints are diametrically opposite. -/
theorem measure_eq_pi_iff_isDiameter (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = π ↔ s.IsDiameter a.left a.right := by
  rw [← angle_center_eq_pi_iff_isDiameter a.left_mem a.right_mem hr, measure, if_neg hr]
  split_ifs with hss
  · constructor <;> intro h <;> linarith
  · rfl

/-- On a sphere of nonzero radius, the half-measure cosine vanishes exactly for diametral arcs. -/
theorem cos_half_measure_eq_zero_iff_isDiameter (a : Arc s) (hr : s.radius ≠ 0) :
    Real.cos (a.measure / 2) = 0 ↔ s.IsDiameter a.left a.right := by
  rw [← measure_eq_pi_iff_isDiameter a hr]
  refine ⟨fun h => ?_, fun h => by rw [h]; exact Real.cos_pi_div_two⟩
  have heq := Real.injOn_cos
    ⟨by linarith [a.measure_nonneg], by linarith [a.measure_le_two_pi]⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
    (show Real.cos (a.measure / 2) = Real.cos (π / 2) by rw [h, Real.cos_pi_div_two])
  linarith

/-- On a sphere of nonzero radius, the anchor is strictly on the center's side of the
separating subspace exactly when the measure exceeds `π`. -/
theorem sSameSide_iff_pi_lt_measure (a : Arc s) (hr : s.radius ≠ 0) :
    (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center ↔ π < a.measure := by
  constructor
  · intro hss
    have hθ : ∠ a.left s.center a.right < π :=
      (angle_le_pi _ _ _).lt_of_ne fun hπ =>
        (measure_eq_angle_iff_not_sSameSide a hr).mp
          (by rw [a.measure_eq_two_pi_sub_angle_of_sSameSide hr hss, hπ]; ring) hss
    rw [a.measure_eq_two_pi_sub_angle_of_sSameSide hr hss]
    linarith
  · intro h
    by_contra hss
    rw [(measure_eq_angle_iff_not_sSameSide a hr).mpr hss] at h
    exact (not_lt_of_ge (angle_le_pi _ _ _)) h

/-- On a sphere of nonzero radius, the measure equals the central angle exactly when it is
at most `π`. -/
theorem measure_eq_angle_iff_le_pi (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure = ∠ a.left s.center a.right ↔ a.measure ≤ π := by
  rw [a.measure_eq_angle_iff_not_sSameSide hr, a.sSameSide_iff_pi_lt_measure hr, not_lt]

/-- On a sphere of nonzero radius, the anchor is strictly on the center's side of the chord
exactly when the half-measure cosine is negative. -/
theorem sSameSide_iff_cos_half_measure_neg (a : Arc s) (hr : s.radius ≠ 0) :
    (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center ↔
      Real.cos (a.measure / 2) < 0 := by
  rw [a.sSameSide_iff_pi_lt_measure hr]
  constructor
  · intro h
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
      (by linarith [a.measure_le_two_pi, Real.pi_pos])
  · intro h
    by_contra hle
    exact (not_lt_of_ge (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [a.measure_nonneg, Real.pi_pos], by linarith⟩)) h

/-! ### Endpoint-sum identity -/

/-- The endpoint radius sum is a scalar multiple of the anchor radius, with coefficient
`2 * cos (measure / 2)`. This also holds for single-point, full-circle,
and zero-radius arcs. -/
theorem sum_vsub_center_eq_two_mul_cos_half_measure_smul (a : Arc s) :
    (a.left -ᵥ s.center) + (a.right -ᵥ s.center) =
      (2 * Real.cos (a.measure / 2)) • (a.mid -ᵥ s.center) := by
  rcases eq_or_ne s.radius 0 with hr0 | hr_ne
  · have hl := dist_eq_zero.mp ((mem_sphere.mp a.left_mem).trans hr0)
    have hm := dist_eq_zero.mp ((mem_sphere.mp a.mid_mem).trans hr0)
    have hright := dist_eq_zero.mp ((mem_sphere.mp a.right_mem).trans hr0)
    simp [hl, hm, hright]
  by_cases hLR : a.left = a.right
  · rcases isSinglePoint_or_isFullCircle_of_left_eq_right a hLR with hsp | hfc
    · rw [measure_eq_zero_of_isSinglePoint a hsp, hsp, ← hLR]
      simp [two_smul]
    · rw [measure_eq_two_pi_of_isFullCircle a hr_ne hfc,
        mid_eq_pointReflection_center_left_of_isFullCircle a hfc, ← hLR,
        AffineEquiv.pointReflection_apply, vadd_vsub, ← neg_vsub_eq_vsub_rev]
      simp [two_smul]
  set v : V := a.left -ᵥ s.center with hv_def
  set w : V := a.right -ᵥ s.center with hw_def
  set m : V := a.mid -ᵥ s.center with hm_def
  have hv_norm : ‖v‖ = s.radius := by rw [hv_def]; exact norm_vsub_center_eq_radius a.left_mem
  have hw_norm : ‖w‖ = s.radius := by rw [hw_def]; exact norm_vsub_center_eq_radius a.right_mem
  have hm_norm : ‖m‖ = s.radius := by rw [hm_def]; exact norm_vsub_center_eq_radius a.mid_mem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp
    (sum_vsub_center_mem_span_mid a)
  have h_u_eq : v + w = k • m := by
    rw [hv_def, hw_def, hm_def]
    exact hk.symm
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
  have h_mid_not_in_L : a.mid ∉ L :=
    a.mid_notMem_lineOrOrthRadius (a.mid_ne_left_of_left_ne_right hLR)
  have h_k_le_2 : k ≤ 2 :=
    (le_abs_self k).trans (by
      linarith [Real.cos_le_one (∠ a.left s.center a.right / 2), h_cos_half_AOC])
  have h_k_lt_2 : k < 2 := lt_of_le_of_ne h_k_le_2 fun hk => by
    have hmF : a.mid = F := vsub_eq_zero_iff_eq.mp (by rw [hmid_minus_F, hk]; simp)
    exact h_mid_not_in_L (by rw [hmF]; exact hF_mem)
  have h_one_sub_pos : (0 : ℝ) < 1 - k / 2 := by linarith
  have hm_ne : m ≠ 0 := by rw [← norm_ne_zero_iff, hm_norm]; exact hr_ne
  have h_ctr_not_in_L_of_k_ne : k ≠ 0 → s.center ∉ L := by
    intro hk hctr
    have hdiam := (Sphere.center_mem_affineSpan_pair_iff_isDiameter
      a.left_mem a.right_mem hLR).mp (hL_eq ▸ hctr)
    have h0 : (k / 2) • m = 0 := by
      rw [← hF_sub, hF_def, hdiam.midpoint_eq_center, vsub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact hk (by linarith)
    · exact hm_ne h
  have hiff : L.SSameSide a.mid s.center ↔ k < 0 := by
    constructor
    · intro hss
      by_contra hk
      have hk_nonneg : 0 ≤ k := le_of_not_gt hk
      by_cases hk_zero : k = 0
      · have hF_eq : F = s.center := vsub_eq_zero_iff_eq.mp (by
          rw [hF_sub, hk_zero, zero_div, zero_smul])
        exact hss.right_notMem (hF_eq ▸ hF_mem)
      · have hwopp : L.WOppSide a.mid s.center :=
          AffineSubspace.wOppSide_of_vsub_eq_smul hF_mem hF_mem
            hmid_minus_F hctr_minus_F
            (mul_nonpos_of_nonneg_of_nonpos h_one_sub_pos.le (by linarith))
        exact (show L.SOppSide a.mid s.center from
          ⟨hwopp, h_mid_not_in_L, h_ctr_not_in_L_of_k_ne hk_zero⟩).not_sSameSide hss
    · intro hk
      exact ⟨AffineSubspace.wSameSide_of_vsub_eq_smul hF_mem hF_mem
        hmid_minus_F hctr_minus_F
        (mul_nonneg h_one_sub_pos.le (by linarith)),
        h_mid_not_in_L, h_ctr_not_in_L_of_k_ne hk.ne⟩
  suffices hk : k / 2 = Real.cos (a.measure / 2) by
    change v + w = _ • m
    rw [h_u_eq, show k = 2 * Real.cos (a.measure / 2) by linarith]
  by_cases hss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
  · rw [a.measure_eq_two_pi_sub_angle_of_sSameSide hr_ne hss,
      show (2 * π - ∠ a.left s.center a.right) / 2 =
      π - ∠ a.left s.center a.right / 2 from by ring,
      Real.cos_pi_sub, h_cos_half_AOC, abs_of_neg (hiff.mp hss)]
    ring
  · rw [(a.measure_eq_angle_iff_not_sSameSide hr_ne).mpr hss,
      h_cos_half_AOC, abs_of_nonneg (not_lt.mp (fun hk => hss (hiff.mpr hk)))]

/-! ### Measure of opposite arcs -/

/-- On a sphere of nonzero radius, the opposite arc has measure `2π` minus the arc's measure.
No dimension hypothesis is required. -/
theorem measure_opposite (a : Arc s) (hr : s.radius ≠ 0) :
    a.opposite.measure = 2 * π - a.measure := by
  have hm_ne : (a.mid -ᵥ s.center : V) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_vsub_center_eq_radius a.mid_mem]
    exact hr
  have hsum := a.opposite.sum_vsub_center_eq_two_mul_cos_half_measure_smul
  simp only [opposite_left, opposite_right, opposite_mid_vsub_center,
    smul_neg, ← neg_smul] at hsum
  have hcos : -(2 * Real.cos (a.opposite.measure / 2)) = 2 * Real.cos (a.measure / 2) :=
    smul_left_injective ℝ hm_ne
      (hsum.symm.trans a.sum_vsub_center_eq_two_mul_cos_half_measure_smul)
  have hhalf := Real.injOn_cos
    ⟨by linarith [a.opposite.measure_nonneg], by linarith [a.opposite.measure_le_two_pi]⟩
    ⟨by linarith [a.measure_le_two_pi], by linarith [a.measure_nonneg, Real.pi_pos]⟩
    (show Real.cos (a.opposite.measure / 2) = Real.cos (π - a.measure / 2) by
      rw [Real.cos_pi_sub]; linarith)
  linarith

/-- An arc and its opposite have measures summing to `2π`. -/
theorem measure_add_measure_opposite (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure + a.opposite.measure = 2 * π := by
  rw [measure_opposite a hr]; ring

/-! ### Measure on minor and major arcs -/

/-- The measure of a minor arc equals the central angle `∠ A s.center C`. -/
@[simp]
theorem measure_minor {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C) :
    (minor hA hC hND).measure = ∠ A s.center C := by
  have hr := radius_ne_zero_of_not_isDiameter hA hC hND
  have hu := sum_vsub_center_ne_zero_of_not_isDiameter hA hND
  have hscale : 0 < s.radius / ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖ :=
    div_pos (radius_pos_of_mem hA hr) (norm_pos_iff.mpr hu)
  have hid := (minor hA hC hND).sum_vsub_center_eq_two_mul_cos_half_measure_smul
  rw [minor_left, minor_right, minor_mid, vadd_vsub, smul_smul] at hid
  have hcoeff : 2 * Real.cos ((minor hA hC hND).measure / 2) *
      (s.radius / ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖) = 1 :=
    smul_left_injective ℝ hu (hid.symm.trans (one_smul ℝ _).symm)
  have hcos : 0 < Real.cos ((minor hA hC hND).measure / 2) := by
    nlinarith [hcoeff, hscale]
  have hss : ¬(s.lineOrOrthRadius (minor hA hC hND).left
      (minor hA hC hND).right).SSameSide (minor hA hC hND).mid s.center :=
    fun h => (not_lt.mpr hcos.le)
      (((minor hA hC hND).sSameSide_iff_cos_half_measure_neg hr).mp h)
  simpa only [minor_left, minor_right] using
    (measure_eq_angle_iff_not_sSameSide (minor hA hC hND) hr).mpr hss

/-- The measure of a major arc equals `2π` minus the central angle `∠ A s.center C`. -/
@[simp]
theorem measure_major {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hND : ¬s.IsDiameter A C) :
    (major hA hC hND).measure = 2 * π - ∠ A s.center C := by
  rw [← minor_opposite_eq_major hA hC hND,
    measure_opposite _ (radius_ne_zero_of_not_isDiameter hA hC hND),
    measure_minor hA hC hND]

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
  set F : P := _root_.midpoint ℝ A C with hF_def
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
  have hr : 0 ≤ s.radius := radius_nonneg_of_mem a.left_mem
  have hsin : 0 ≤ Real.sin (∠ a.left s.center a.right / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [angle_nonneg a.left s.center a.right])
      (by linarith [angle_le_pi a.left s.center a.right, Real.pi_pos])
  apply (sq_eq_sq₀ dist_nonneg (by positivity)).mp
  have hchord := law_cos a.left s.center a.right
  rw [mem_sphere.mp a.left_mem, mem_sphere.mp a.right_mem] at hchord
  have hcos := Real.cos_two_mul (∠ a.left s.center a.right / 2)
  rw [show 2 * (∠ a.left s.center a.right / 2) = ∠ a.left s.center a.right by ring] at hcos
  nlinarith [Real.sin_sq_add_cos_sq (∠ a.left s.center a.right / 2)]

/-- The chord of an arc has length `2 * s.radius * Real.sin (a.measure / 2)`. -/
theorem dist_left_right_eq_two_mul_radius_mul_sin_measure (a : Arc s) :
    dist a.left a.right = 2 * s.radius * Real.sin (a.measure / 2) := by
  rw [a.dist_left_right_eq_two_mul_radius_mul_sin]
  by_cases hr : s.radius = 0
  · simp [hr]
  by_cases hss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center
  · rw [a.measure_eq_two_pi_sub_angle_of_sSameSide hr hss,
      show (2 * π - ∠ a.left s.center a.right) / 2 =
        π - ∠ a.left s.center a.right / 2 by ring, Real.sin_pi_sub]
  · rw [(a.measure_eq_angle_iff_not_sSameSide hr).mpr hss]

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
  · rw [a.measure_eq_zero_of_radius_eq_zero hr, b.measure_eq_zero_of_radius_eq_zero hr]
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

/-! ### The arc midpoint -/

private theorem minorMidpoint_eq_sign_smul_mid (a : Arc s)
    (hND : ¬s.IsDiameter a.left a.right) :
    minorMidpoint s a.left a.right =
      (Real.cos (a.measure / 2) / |Real.cos (a.measure / 2)|) •
        (a.mid -ᵥ s.center) +ᵥ s.center := by
  have hr := radius_ne_zero_of_not_isDiameter a.left_mem a.right_mem hND
  have hc : Real.cos (a.measure / 2) ≠ 0 :=
    fun h => hND ((a.cos_half_measure_eq_zero_iff_isDiameter hr).mp h)
  rw [minorMidpoint, a.sum_vsub_center_eq_two_mul_cos_half_measure_smul,
    norm_smul, Real.norm_eq_abs, norm_vsub_center_eq_radius a.mid_mem, smul_smul]
  congr 2
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  field_simp

/-- Below measure `π`, the anchor is the normalized endpoint sum, including at radius zero. -/
theorem mid_eq_minorMidpoint (a : Arc s) (h : a.measure < π) :
    a.mid = minorMidpoint s a.left a.right := by
  by_cases hr : s.radius = 0
  · have hm := dist_eq_zero.mp ((mem_sphere.mp a.mid_mem).trans hr)
    simp [minorMidpoint, hr, hm]
  have hND : ¬s.IsDiameter a.left a.right :=
    fun hd => h.ne ((a.measure_eq_pi_iff_isDiameter hr).mpr hd)
  have hc : 0 < Real.cos (a.measure / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [a.measure_nonneg, Real.pi_pos], by linarith⟩
  rw [minorMidpoint_eq_sign_smul_mid a hND, abs_of_pos hc, div_self hc.ne',
    one_smul, vsub_vadd]

/-- Above measure `π`, the anchor is the antipode of the normalized endpoint sum. -/
theorem mid_eq_pointReflection_minorMidpoint (a : Arc s) (h : π < a.measure) :
    a.mid = AffineEquiv.pointReflection ℝ s.center (minorMidpoint s a.left a.right) := by
  have hr : s.radius ≠ 0 := by
    intro hr
    rw [a.measure_eq_zero_of_radius_eq_zero hr] at h
    linarith [Real.pi_pos]
  have hND : ¬s.IsDiameter a.left a.right :=
    fun hd => h.ne' ((a.measure_eq_pi_iff_isDiameter hr).mpr hd)
  have hc := (a.sSameSide_iff_cos_half_measure_neg hr).mp
    ((a.sSameSide_iff_pi_lt_measure hr).mpr h)
  rw [minorMidpoint_eq_sign_smul_mid a hND, abs_of_neg hc, div_neg, div_self hc.ne,
    neg_one_smul, AffineEquiv.pointReflection_apply, ← neg_vsub_eq_vsub_rev,
    vadd_vsub, neg_neg, vsub_vadd]

/-- The public geometric name for the midpoint, definitionally equal to the stored anchor.
`mid` is the simp normal form. The geometric content is `angle_center_midpoint_eq_half_measure`;
bisection is proved rather than required as a structure invariant. -/
def midpoint (a : Arc s) : P := a.mid

@[simp]
theorem midpoint_eq_mid (a : Arc s) : a.midpoint = a.mid := rfl

/-- The midpoint of every arc lies on the sphere. -/
theorem midpoint_mem (a : Arc s) : a.midpoint ∈ s := a.mid_mem

/-- The midpoint of every arc lies on the arc. -/
theorem midpoint_mem_arc (a : Arc s) : a.midpoint ∈ a := mid_mem_arc a

/-- Unless the arc is a single point, its midpoint differs from the left endpoint. -/
theorem midpoint_ne_left (a : Arc s) (h : ¬a.IsSinglePoint) : a.midpoint ≠ a.left := h

/-- Unless the arc is a single point, its midpoint differs from the right endpoint. -/
theorem midpoint_ne_right (a : Arc s) (h : ¬a.IsSinglePoint) : a.midpoint ≠ a.right :=
  a.mid_ne_right h

/-- Unless the arc is a single point, its midpoint lies in its interior,
including for full circles. -/
theorem midpoint_mem_interior (a : Arc s) (h : ¬a.IsSinglePoint) :
    a.midpoint ∈ a.interior := a.mid_mem_interior h

/-- Unless the arc is a single point, its midpoint does not lie on the separating subspace. -/
theorem midpoint_notMem_lineOrOrthRadius (a : Arc s) (h : ¬a.IsSinglePoint) :
    a.midpoint ∉ s.lineOrOrthRadius a.left a.right := a.mid_notMem_lineOrOrthRadius h

/-- Unless the arc is a single point, its midpoint does not lie on the chord's affine span. -/
theorem midpoint_notMem_line (a : Arc s) (h : ¬a.IsSinglePoint) :
    a.midpoint ∉ line[ℝ, a.left, a.right] := a.mid_notMem_line h

/-- Reflection symmetry gives equal central angles to the anchor, even at radius zero. -/
theorem angle_center_mid_eq_angle_mid_center_right (a : Arc s) :
    ∠ a.left s.center a.mid = ∠ a.mid s.center a.right := by
  have h := a.inner_mid_vsub_center_right_vsub_left
  rw [← vsub_sub_vsub_cancel_right a.right a.left s.center, inner_sub_right, sub_eq_zero] at h
  apply Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
  change Real.cos (InnerProductGeometry.angle _ _) = Real.cos (InnerProductGeometry.angle _ _)
  simp only [InnerProductGeometry.cos_angle]
  rw [norm_vsub_center_eq_radius a.left_mem, norm_vsub_center_eq_radius a.right_mem, h,
    real_inner_comm (a.left -ᵥ s.center) (a.mid -ᵥ s.center),
    mul_comm s.radius ‖a.mid -ᵥ s.center‖]

/-- On a sphere of nonzero radius, each endpoint subtends the central angle `a.measure / 2` to
the arc midpoint. This includes single-point and full-circle arcs. -/
theorem angle_center_midpoint_eq_half_measure (a : Arc s) (hr : s.radius ≠ 0) :
    ∠ a.left s.center a.midpoint = a.measure / 2 ∧
      ∠ a.midpoint s.center a.right = a.measure / 2 := by
  have hvm : ⟪a.left -ᵥ s.center, a.mid -ᵥ s.center⟫
      = Real.cos (a.measure / 2) * s.radius ^ 2 := by
    have hip := congrArg (fun x : V => ⟪x, a.mid -ᵥ s.center⟫)
      a.sum_vsub_center_eq_two_mul_cos_half_measure_smul
    have heq : ⟪a.right -ᵥ s.center, a.mid -ᵥ s.center⟫
        = ⟪a.left -ᵥ s.center, a.mid -ᵥ s.center⟫ := by
      have h := a.inner_mid_vsub_center_right_vsub_left
      rw [← vsub_sub_vsub_cancel_right a.right a.left s.center,
        inner_sub_right, sub_eq_zero] at h
      simpa only [real_inner_comm] using h
    simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_vsub_center_eq_radius a.mid_mem] at hip
    rw [heq] at hip; linarith
  have hleft : ∠ a.left s.center a.mid = a.measure / 2 := by
    apply Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨by linarith [a.measure_nonneg], by linarith [a.measure_le_two_pi]⟩
    change Real.cos (InnerProductGeometry.angle _ _) = _
    rw [InnerProductGeometry.cos_angle, norm_vsub_center_eq_radius a.left_mem,
      norm_vsub_center_eq_radius a.mid_mem, hvm, div_eq_iff (mul_ne_zero hr hr)]; ring
  exact ⟨hleft, a.angle_center_mid_eq_angle_mid_center_right ▸ hleft⟩

/-- The midpoint of every arc lies on the perpendicular bisector of its endpoints. -/
theorem midpoint_mem_perpBisector (a : Arc s) :
    a.midpoint ∈ AffineSubspace.perpBisector a.left a.right := by
  rw [midpoint_eq_mid a]
  exact a.line_center_mid_le_perpBisector (right_mem_affineSpan_pair ℝ s.center a.mid)

/-- For a minor arc, the midpoint equals `minorMidpoint`. -/
theorem midpoint_minor_eq_minorMidpoint {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    (minor hA hC hND).midpoint = minorMidpoint s A C := rfl

/-- For a major arc, the midpoint is the antipodal point of `minorMidpoint`. -/
theorem midpoint_major_eq_pointReflection_minorMidpoint
    {A C : P} (hA : A ∈ s) (hC : C ∈ s)
    (hND : ¬s.IsDiameter A C) :
    (major hA hC hND).midpoint =
      AffineEquiv.pointReflection ℝ s.center (minorMidpoint s A C) := rfl

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
      have h_ss' :
          (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
        rw [hL_eq]; exact h_ss
      exact a.measure_eq_two_pi_sub_angle_of_sSameSide hr_ne h_ss'
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
      have h_ss' :
          ¬ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid s.center := by
        rw [hL_eq]; exact h_ss
      exact (a.measure_eq_angle_iff_not_sSameSide hr_ne).mpr h_ss'
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
            have := (Sphere.center_mem_affineSpan_pair_iff_isDiameter
              a.left_mem a.right_mem hLR).mpr h_diam
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
  have hne : (minor hX hY hND).left ≠ (minor hX hY hND).right := by
    rw [minor_left, minor_right]; exact hXY
  set M := (minor hX hY hND).midpoint with hM_def
  have hMmem : M ∈ s := midpoint_mem _
  have hCX : C ≠ X := by
    have := ne_left_of_mem_interior hC_opp; rwa [opposite_left, minor_left] at this
  have hCY : C ≠ Y := by
    have := ne_right_of_mem_interior hC_opp; rwa [opposite_right, minor_right] at this
  have hM_int : M ∈ (minor hX hY hND).interior :=
    midpoint_mem_interior _ (not_isSinglePoint_of_left_ne_right _ hne)
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
    have hr := radius_ne_zero_of_mem_of_mem_of_ne hX hY hXY
    have hhalf := angle_center_midpoint_eq_half_measure (minor hX hY hND) hr
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
  have h_measure : a.measure = θ :=
    (a.measure_eq_angle_iff_le_pi hr_ne).mpr h_le
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
