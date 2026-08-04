/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import ArcsForMathlib.Sphere.Arc.Basic

/-!
# Structural Theorems on Arcs

This file proves structural and topological theorems about arcs on spheres:
membership, interiors, and the relationship between different arc constructors.

## Main results

* `EuclideanGeometry.Sphere.Arc.mem_arc_or_mem_opposite`: in two dimensions,
  every sphere point lies in an arc or its opposite.
* `EuclideanGeometry.Sphere.Arc.interior_disjoint_opposite`: in two dimensions,
  the interiors of an arc and its opposite are disjoint when the endpoints
  differ.
* `EuclideanGeometry.Sphere.Arc.sOppSide_of_mem_interior_of_mem_opposite_interior`: in two
  dimensions, interior points of an arc and its opposite lie on strictly opposite sides of the
  chord.
* `EuclideanGeometry.Sphere.Arc.mem_and_mem_opposite_iff_eq_left_or_eq_right`: a sphere point
  lies in both an arc and its opposite iff it equals one of the two endpoints.
* `EuclideanGeometry.Sphere.Arc.ne_left_of_mem_interior` /
  `ne_right_of_mem_interior`: an interior point is not an endpoint.
* `EuclideanGeometry.Sphere.Arc.mem_interior_of_mem_of_ne_endpoints_of_left_ne_right`:
  a sphere point in an arc with distinct endpoints that is itself distinct from
  both endpoints lies in the arc's interior.
* `EuclideanGeometry.Sphere.Arc.mid_mem_interior`: the mid point of an arc with distinct endpoints
  lies in its interior.
* `EuclideanGeometry.Sphere.Arc.mem_through_iff_mem_minor_of_mem_minor_interior` /
  `mem_through_iff_mem_major_of_mem_major_interior`: `through A B C` has the same points as the
  minor (respectively major) arc when `B` lies in that arc's interior.
* `EuclideanGeometry.Sphere.Arc.center_minorMidpoint_chord_midpoint_collinear`: the
  center, the mid of the minor arc, and the chord midpoint are collinear.
-/

@[expose] public section

namespace EuclideanGeometry

namespace Sphere

namespace Arc

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable {s : Sphere P}

noncomputable section

/-! ## Structural properties -/

/-- In two dimensions, every point on the sphere lies in the arc or its opposite arc. -/
theorem mem_arc_or_mem_opposite [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) {Q : P} (hQ : Q ∈ s) :
    Q ∈ a ∨ Q ∈ a.opposite := by
  by_cases hLR : a.left = a.right
  · by_cases hQl : Q = a.left
    · exact Or.inl (hQl ▸ left_mem_arc a)
    · by_cases hMA : a.mid = a.left
      · have hleft_ne_center : a.left ≠ s.center :=
          ne_center_of_mem_of_mem_of_ne a.left_mem hQ (Ne.symm hQl)
        have hom_ne : a.opposite.mid ≠ a.left := by
          show AffineEquiv.pointReflection ℝ s.center a.mid ≠ a.left
          rw [hMA]
          intro hfix
          rw [AffineEquiv.pointReflection_fixed_iff_of_module] at hfix
          exact hleft_ne_center hfix
        refine Or.inr (mem_iff.mpr ⟨hQ, Or.inr (Or.inr ?_)⟩)
        rw [opposite_left, opposite_right, lineOrOrthRadius_of_eq hLR]
        exact sSameSide_orthRadius_of_mem a.left_mem a.opposite.mid_mem hQ hom_ne.symm
          (Ne.symm hQl)
      · refine Or.inl (mem_iff.mpr ⟨hQ, Or.inr (Or.inr ?_)⟩)
        rw [lineOrOrthRadius_of_eq hLR]
        exact sSameSide_orthRadius_of_mem a.left_mem a.mid_mem hQ (Ne.symm hMA) (Ne.symm hQl)
  · haveI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 1
    have hL_opp_eq :
        s.lineOrOrthRadius a.opposite.left a.opposite.right =
        s.lineOrOrthRadius a.left a.right := by
      rw [opposite_left, opposite_right]
    set L : AffineSubspace ℝ P := s.lineOrOrthRadius a.left a.right with hL_def
    have hAL : a.left ∈ L := left_mem_lineOrOrthRadius
    suffices h : L.WSameSide a.mid Q ∨ L.WSameSide a.opposite.mid Q by
      rcases h with hM | hOM
      · exact Or.inl ((mem_iff_wSameSide hLR).mpr ⟨hQ, hL_def ▸ hM⟩)
      · have hLR_opp : a.opposite.left ≠ a.opposite.right := by simpa using hLR
        refine Or.inr ((mem_iff_wSameSide hLR_opp).mpr ⟨hQ, ?_⟩)
        rw [hL_opp_eq]
        exact hL_def ▸ hOM
    by_cases hQL : Q ∈ L
    · exact Or.inl (AffineSubspace.wSameSide_of_right_mem _ hQL)
    have hQ_ne_left : Q ≠ a.left := fun h => hQL (h ▸ hAL)
    have hr_ne : s.radius ≠ 0 :=
      radius_ne_zero_of_mem_of_mem_of_ne a.left_mem hQ (Ne.symm hQ_ne_left)
    set m : V := a.mid -ᵥ s.center with hm_def
    set q : V := Q -ᵥ s.center with hq_def
    have hm_norm : ‖m‖ = s.radius := by rw [hm_def]; exact norm_vsub_center_eq_radius a.mid_mem
    have hm_ne : m ≠ 0 := by rw [← norm_ne_zero_iff, hm_norm]; exact hr_ne
    have hOM_sub : a.opposite.mid -ᵥ s.center = -m := by
      show AffineEquiv.pointReflection ℝ s.center a.mid -ᵥ s.center = -m
      rw [AffineEquiv.pointReflection_apply, vadd_vsub, ← neg_vsub_eq_vsub_rev, ← hm_def]
    have hL_eq : L = line[ℝ, a.left, a.right] := by
      rw [hL_def]; exact lineOrOrthRadius_of_ne hLR
    set d : V := a.right -ᵥ a.left with hd_def
    set F : P := midpoint ℝ a.left a.right with hF_def
    have hd_ne : d ≠ 0 := vsub_ne_zero.mpr (Ne.symm hLR)
    have hm_perp_d : ⟪m, d⟫ = 0 := a.inner_mid_vsub_center_right_vsub_left
    have hd_inner_m : ⟪d, m⟫ = 0 := by rw [real_inner_comm]; exact hm_perp_d
    have hF_mem : F ∈ L := by
      rw [hL_eq, hF_def]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hFc_perp : ⟪F -ᵥ s.center, d⟫ = 0 := by
      rw [hF_def, hd_def, ← neg_vsub_eq_vsub_rev, inner_neg_left,
          Sphere.inner_vsub_center_midpoint_vsub a.left_mem a.right_mem, neg_zero]
    have hd_inner_Fc : ⟪d, F -ᵥ s.center⟫ = 0 := by
      rw [real_inner_comm]; exact hFc_perp
    have hFc_in_span : (F -ᵥ s.center : V) ∈ Submodule.span ℝ ({m} : Set V) :=
      Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
        hd_ne hm_ne hd_inner_Fc hd_inner_m
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp hFc_in_span
    have hδ_abs : |δ| < 1 := by
      have h_dist : dist s.center F < s.radius :=
        Sphere.dist_center_midpoint_lt_radius a.left_mem a.right_mem hLR
      have h_norm : ‖s.center -ᵥ F‖ = |δ| * s.radius := by
        rw [show (s.center -ᵥ F : V) = -(F -ᵥ s.center) from
              (neg_vsub_eq_vsub_rev _ _).symm,
            norm_neg, ← hδ, norm_smul, Real.norm_eq_abs, hm_norm]
      rw [dist_eq_norm_vsub V, h_norm] at h_dist
      have hr_pos : 0 < s.radius :=
        lt_of_le_of_ne (Sphere.radius_nonneg_of_mem a.left_mem) (Ne.symm hr_ne)
      nlinarith [abs_nonneg δ]
    have ham_sub : a.mid -ᵥ F = (1 - δ) • m := by
      have h1 : (a.mid -ᵥ F : V) = (a.mid -ᵥ s.center) - (F -ᵥ s.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, ← hm_def, ← hδ]; module
    have haom_sub : a.opposite.mid -ᵥ F = (-(1 + δ)) • m := by
      have h1 : (a.opposite.mid -ᵥ F : V) =
          (a.opposite.mid -ᵥ s.center) - (F -ᵥ s.center) :=
        (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, hOM_sub, ← hδ]; module
    set α : ℝ := ⟪q, m⟫ / ⟪m, m⟫ with hα_def
    set β : ℝ := ⟪q, d⟫ / ⟪d, d⟫ with hβ_def
    have h_orth_eq : (Submodule.span ℝ ({m} : Set V))ᗮ = Submodule.span ℝ ({d} : Set V) := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hm_perp_d)
      · rw [Submodule.finrank_orthogonal_span_singleton (n := 1) hm_ne,
            finrank_span_singleton hd_ne]
    have h_q_dec : q = α • m + β • d := by
      have hsum := Submodule.starProjection_add_starProjection_orthogonal
        (K := Submodule.span ℝ ({m} : Set V)) q
      simp only [h_orth_eq] at hsum
      rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton] at hsum
      rw [hα_def, hβ_def, real_inner_comm m q, real_inner_comm d q,
          real_inner_self_eq_norm_sq m, real_inner_self_eq_norm_sq d]
      exact_mod_cast hsum.symm
    have hQF_sub : (Q -ᵥ F : V) = (α - δ) • m + β • d := by
      have h1 : (Q -ᵥ F : V) = q - (F -ᵥ s.center) := by
        rw [hq_def]; exact (vsub_sub_vsub_cancel_right _ _ _).symm
      rw [h1, h_q_dec, ← hδ]; module
    have hd_dir : d ∈ (line[ℝ, a.left, a.right] : AffineSubspace ℝ P).direction := by
      rw [direction_affineSpan, vectorSpan_pair, hd_def,
          show a.right -ᵥ a.left = -(a.left -ᵥ a.right) from
            (neg_vsub_eq_vsub_rev _ _).symm]
      exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
    have hβd_mem : (β • d : V) +ᵥ F ∈ L := by
      rw [hL_eq]
      exact AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ _ hd_dir) (hL_eq ▸ hF_mem)
    have hQ_minus_p : Q -ᵥ ((β • d : V) +ᵥ F) = (α - δ) • m := by
      rw [show Q -ᵥ ((β • d : V) +ᵥ F) = (Q -ᵥ F) - β • d from by
        rw [vsub_vadd_eq_vsub_sub], hQF_sub]
      module
    rcases le_or_gt δ α with hαδ | hαδ
    · exact Or.inl (AffineSubspace.wSameSide_of_vsub_eq_smul hF_mem hβd_mem ham_sub hQ_minus_p
        (mul_nonneg (by linarith [(abs_lt.mp hδ_abs).2]) (by linarith)))
    · refine Or.inr (AffineSubspace.wSameSide_of_vsub_eq_smul hF_mem hβd_mem haom_sub hQ_minus_p
        ?_)
      have h := abs_lt.mp hδ_abs
      nlinarith [mul_pos (show (0:ℝ) < 1 + δ by linarith [h.1]) (show (0:ℝ) < δ - α by linarith)]

/-- A sphere point that belongs to an arc with distinct endpoints and is itself distinct
from both endpoints lies in the arc's interior. -/
theorem mem_interior_of_mem_of_ne_endpoints_of_left_ne_right
    (a : Arc s) {B : P} (hB : B ∈ a) (hBl : B ≠ a.left) (hBr : B ≠ a.right)
    (hne : a.left ≠ a.right) :
    B ∈ a.interior := by
  rcases (mem_iff.mp hB) with ⟨hBs, hleft | hright | hss⟩
  · exact False.elim (hBl hleft)
  · exact False.elim (hBr hright)
  · exact ⟨hBs, hss.1, mid_not_mem_lineOrOrthRadius a hne, hss.2.2⟩

/-- In two dimensions, the interiors of an arc and its opposite are disjoint when the
endpoints differ. -/
theorem interior_disjoint_opposite [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right) :
    Disjoint (a.interior : Set P) a.opposite.interior := by
  rw [Set.disjoint_left]
  intro p hp hp_opp
  have h_ss : (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p := hp.2
  have h_ss_opp : (s.lineOrOrthRadius a.left a.right).SSameSide a.opposite.mid p := by
    simpa only [opposite_left, opposite_right] using hp_opp.2
  have h_opp : (s.lineOrOrthRadius a.left a.right).SOppSide a.mid a.opposite.mid :=
    sOppSide_mid_opposite_mid a hne
  exact (h_opp.trans_sSameSide h_ss_opp).not_sSameSide h_ss

/-- A sphere point distinct from both endpoints lies in the interior of the arc or of its
opposite. With `interior_disjoint_opposite`, exactly one of the two holds. -/
theorem mem_interior_or_mem_opposite_interior [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hne : a.left ≠ a.right) {Z : P} (hZ : Z ∈ s)
    (hZl : Z ≠ a.left) (hZr : Z ≠ a.right) :
    Z ∈ a.interior ∨ Z ∈ a.opposite.interior :=
  (mem_arc_or_mem_opposite a hZ).imp
    (mem_interior_of_mem_of_ne_endpoints_of_left_ne_right a · hZl hZr hne)
    (mem_interior_of_mem_of_ne_endpoints_of_left_ne_right a.opposite ·
      (by rwa [opposite_left]) (by rwa [opposite_right])
      (by simpa only [opposite_left, opposite_right] using hne))

/-- Interior points of an arc and its opposite lie on strictly opposite sides of the chord. -/
theorem sOppSide_of_mem_interior_of_mem_opposite_interior [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) {X Y : P} (hne : a.left ≠ a.right)
    (hX : X ∈ a.interior) (hY : Y ∈ a.opposite.interior) :
    (s.lineOrOrthRadius a.left a.right).SOppSide X Y := by
  have hYss : (s.lineOrOrthRadius a.left a.right).SSameSide a.opposite.mid Y := by
    have h := hY.2
    rwa [opposite_left, opposite_right] at h
  exact (hX.2.symm.trans_sOppSide (sOppSide_mid_opposite_mid a hne)).trans_sSameSide hYss

/-- A sphere point lies in both an arc and its opposite if and only if it equals one of the
two endpoints. -/
theorem mem_and_mem_opposite_iff_eq_left_or_eq_right [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) {Q : P} (hQ : Q ∈ s) (hne : a.left ≠ a.right) :
    (Q ∈ a ∧ Q ∈ a.opposite) ↔ (Q = a.left ∨ Q = a.right) := by
  refine ⟨fun ⟨hQa, hQopp⟩ => ?_, ?_⟩
  · have h_aQ := ((mem_iff_wSameSide hne).mp hQa).2
    have hne_opp : a.opposite.left ≠ a.opposite.right := by simpa using hne
    have h_oQ := ((mem_iff_wSameSide hne_opp).mp hQopp).2
    rw [opposite_left, opposite_right] at h_oQ
    by_contra h_not_endpoint
    push Not at h_not_endpoint
    obtain ⟨hQ_ne_left, hQ_ne_right⟩ := h_not_endpoint
    have hQ_not_L : Q ∉ s.lineOrOrthRadius a.left a.right :=
      not_mem_lineOrOrthRadius_of_mem_sphere a.left_mem hQ a.right_mem
        hQ_ne_left hQ_ne_right
    have h_opp := sOppSide_mid_opposite_mid a hne
    have h_mid_not_L : a.mid ∉ s.lineOrOrthRadius a.left a.right := h_opp.2.1
    have h_aQ_strict :
        (s.lineOrOrthRadius a.left a.right).SSameSide a.mid Q :=
      ⟨h_aQ, h_mid_not_L, hQ_not_L⟩
    exact (h_opp.symm.trans_sSameSide h_aQ_strict).not_wSameSide h_oQ
  · rintro (rfl | rfl)
    · refine ⟨left_mem_arc a, ?_⟩
      have := left_mem_arc a.opposite
      rwa [opposite_left] at this
    · refine ⟨right_mem_arc a, ?_⟩
      have := right_mem_arc a.opposite
      rwa [opposite_right] at this

/-- An interior point of an arc is not the left endpoint. -/
theorem ne_left_of_mem_interior (a : Arc s) {B : P} (hB : B ∈ a.interior) :
    B ≠ a.left :=
  fun h => hB.2.2.2 (h ▸ left_mem_lineOrOrthRadius)

/-- An interior point of an arc is not the right endpoint. -/
theorem ne_right_of_mem_interior (a : Arc s) {B : P} (hB : B ∈ a.interior) :
    B ≠ a.right :=
  fun h => hB.2.2.2 (h ▸ right_mem_lineOrOrthRadius)

/-- The mid point of an arc with distinct endpoints lies in its interior. -/
theorem mid_mem_interior (a : Arc s) (hne : a.left ≠ a.right) :
    a.mid ∈ a.interior := by
  have h_mid_not : a.mid ∉ s.lineOrOrthRadius a.left a.right :=
    mid_not_mem_lineOrOrthRadius a hne
  exact ⟨a.mid_mem, AffineSubspace.sSameSide_self_iff.mpr
    ⟨⟨a.left, left_mem_lineOrOrthRadius⟩, h_mid_not⟩⟩

/-! ## Interaction between `through` and `minor` / `major` -/

/-- A sphere point distinct from the endpoints of a non-diametral chord lies in the interior
of either its minor arc or its major arc. -/
theorem mem_minor_interior_or_mem_major_interior [Fact (Module.finrank ℝ V = 2)]
    {X Y Z : P} (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y) (hXY : X ≠ Y)
    (hZ : Z ∈ s) (hZX : Z ≠ X) (hZY : Z ≠ Y) :
    Z ∈ (minor hX hY hND).interior ∨ Z ∈ (major hX hY hND).interior :=
  mem_interior_or_mem_opposite_interior _ (by simpa only [minor_left, minor_right] using hXY)
    hZ (by simpa only [minor_left] using hZX) (by simpa only [minor_right] using hZY)

/-- If `Q` lies on the sphere and is strictly on the same side of the chord `AC` as the
through-point `B`, then `Q` lies in the interior of `Sphere.Arc.through A B C`. -/
theorem mem_interior_through_of_sSameSide [Fact (Module.finrank ℝ V = 2)] {s : Sphere P}
    {A B C Q : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hQ : Q ∈ s) (hss : (s.lineOrOrthRadius A C).SSameSide B Q) :
    Q ∈ (through hA hB hC hBA hBC).interior := by
  refine ⟨hQ, ?_⟩
  have hmid := (mem_interior_through hA hB hC hBA hBC).2
  simp only [through_left, through_right hA hB hC hBA hBC] at hmid ⊢
  exact hmid.trans hss

/-- Two interior points of `Sphere.Arc.through A B C` are strictly on the same side of the
chord `AC`. -/
theorem sSameSide_of_mem_interior_through [Fact (Module.finrank ℝ V = 2)] {s : Sphere P}
    {A B C P₁ P₂ : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hP₁ : P₁ ∈ (through hA hB hC hBA hBC).interior)
    (hP₂ : P₂ ∈ (through hA hB hC hBA hBC).interior) :
    (s.lineOrOrthRadius A C).SSameSide P₁ P₂ := by
  have h := hP₁.2.symm.trans hP₂.2
  simp only [through_left, through_right hA hB hC hBA hBC] at h
  exact h

/-- If `B` lies in the minor arc's interior, then `through A B C` has the same points
as the minor arc. -/
theorem mem_through_iff_mem_minor_of_mem_minor_interior [Fact (Module.finrank ℝ V = 2)]
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hNotDiam).interior) :
    ∀ Q : P, Q ∈ through hA hB hC hBA hBC ↔ Q ∈ minor hA hC hNotDiam := by
  have hB_through : B ∈ (through hA hB hC hBA hBC).interior :=
    mem_interior_through hA hB hC hBA hBC
  have h_t_ss := hB_through.2
  have h_m_ss := hB_minor.2
  simp only [through_left, through_right hA hB hC hBA hBC,
             minor_left, minor_right] at h_t_ss h_m_ss
  have h_mid_ss : (s.lineOrOrthRadius A C).SSameSide
      (through hA hB hC hBA hBC).mid (minor hA hC hNotDiam).mid :=
    h_t_ss.trans h_m_ss.symm
  intro Q
  rw [mem_iff, mem_iff, through_left, through_right hA hB hC hBA hBC,
    minor_left, minor_right]
  exact and_congr_right fun _ =>
    or_congr_right <| or_congr_right ⟨(h_mid_ss.symm.trans ·), (h_mid_ss.trans ·)⟩

/-- If `B` lies in the major arc's interior, then `through A B C` has the same points
as the major arc. -/
theorem mem_through_iff_mem_major_of_mem_major_interior [Fact (Module.finrank ℝ V = 2)]
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_major : B ∈ (major hA hC hNotDiam).interior) :
    ∀ Q : P, Q ∈ through hA hB hC hBA hBC ↔ Q ∈ major hA hC hNotDiam := by
  have hB_through : B ∈ (through hA hB hC hBA hBC).interior :=
    mem_interior_through hA hB hC hBA hBC
  have h_t_ss := hB_through.2
  have h_m_ss := hB_major.2
  simp only [through_left, through_right hA hB hC hBA hBC,
             major_left, major_right] at h_t_ss h_m_ss
  have h_mid_ss : (s.lineOrOrthRadius A C).SSameSide
      (through hA hB hC hBA hBC).mid (major hA hC hNotDiam).mid :=
    h_t_ss.trans h_m_ss.symm
  intro Q
  rw [mem_iff, mem_iff, through_left, through_right hA hB hC hBA hBC,
    major_left, major_right]
  exact and_congr_right fun _ =>
    or_congr_right <| or_congr_right ⟨(h_mid_ss.symm.trans ·), (h_mid_ss.trans ·)⟩

/-! ## Geometric landmarks on `minor` -/

/-- The center, the mid of the minor arc, and the midpoint of the chord are collinear. -/
theorem center_minorMidpoint_chord_midpoint_collinear
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hNotDiam : ¬s.IsDiameter A C) :
    Collinear ℝ ({s.center, (minor hA hC hNotDiam).mid, midpoint ℝ A C} : Set P) := by
  rw [collinear_iff_of_mem (Set.mem_insert _ _)]
  refine ⟨(A -ᵥ s.center) + (C -ᵥ s.center), ?_⟩
  intro p hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨s.radius / ‖(A -ᵥ s.center) + (C -ᵥ s.center)‖, ?_⟩
    rw [minor_mid]
  · refine ⟨(⅟2 : ℝ), ?_⟩
    rw [eq_vadd_iff_vsub_eq, midpoint_vsub, smul_add]

end

end Arc

end Sphere

end EuclideanGeometry
