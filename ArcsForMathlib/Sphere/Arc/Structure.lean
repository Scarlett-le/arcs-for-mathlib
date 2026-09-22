/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import ArcsForMathlib.Sphere.Arc.Basic

/-!
# Structure of arcs: complementation and canonicity

In two dimensions a chord separates the sphere. This file draws the two consequences: an arc and
its opposite complement each other, and an arc is pinned down by its ordered endpoints together
with a single interior point. The second makes `through A B C` canonical, which identifies it
with `minor`, with `major`, and with any other arc carrying the same data.

## Main results

* `EuclideanGeometry.Sphere.Arc.mem_arc_or_mem_opposite`,
  `EuclideanGeometry.Sphere.Arc.interior_disjoint_opposite` and
  `EuclideanGeometry.Sphere.Arc.mem_and_mem_opposite_iff_eq_left_or_eq_right`: the two interiors
  and the endpoint pair partition the sphere.
* `EuclideanGeometry.Sphere.Arc.eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior`: the
  ordered endpoints and one shared interior point determine an arc.
* `EuclideanGeometry.Sphere.Arc.eq_of_left_eq_of_right_eq_of_coe_eq`: the ordered endpoints and
  the underlying point set determine the same `Arc` object, including coincident endpoints.
* `EuclideanGeometry.Sphere.Arc.through_eq_of_mem_interior` and
  `EuclideanGeometry.Sphere.Arc.avoiding_eq_of_mem_opposite_interior`: `through` and `avoiding`
  are the arcs on `A`, `C` singled out by the position of `B`.
* `EuclideanGeometry.Sphere.Arc.through_eq_through_of_sSameSide` and
  `EuclideanGeometry.Sphere.Arc.avoiding_eq_avoiding_of_sSameSide`: the through-point enters only
  through the side of `AC` it lies on.
* `EuclideanGeometry.Sphere.Arc.through_eq_avoiding_of_sOppSide` and
  `EuclideanGeometry.Sphere.Arc.avoiding_eq_through_of_sOppSide`: through-points on opposite sides
  of `AC` select complementary arcs.
* `EuclideanGeometry.Sphere.Arc.through_eq_minor_of_mem_minor_interior` and
  `EuclideanGeometry.Sphere.Arc.through_eq_major_of_mem_major_interior`: `through` coincides with
  `minor` and with `major` as `Arc` objects, not merely as point sets.

## Implementation notes

Most equality results in this file carry no `left ≠ right` hypothesis. When the endpoints
coincide, an arc is either the single-point representation (`mid = left`) or has its mid forced to
the point reflection of the endpoint through the center. The representation-level lemma
`EuclideanGeometry.Sphere.Arc.coe_eq_singleton_iff_mid_eq_left` handles the first case directly in
`Basic`, so `Structure` remains independent of `Arc.Degenerate`. This is what lets both the
interior-point and point-set uniqueness results cover coincident endpoints without adding an
import edge.
-/

@[expose] public section

namespace EuclideanGeometry

namespace Sphere

namespace Arc

open scoped EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable {s : Sphere P}
variable [Fact (Module.finrank ℝ V = 2)]

/-! ## Structural properties -/

/-- In two dimensions, every point on the sphere lies in the arc or its opposite arc. -/
theorem mem_arc_or_mem_opposite (a : Arc s) {Q : P} (hQ : Q ∈ s) :
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
  · haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
    set L : AffineSubspace ℝ P := s.lineOrOrthRadius a.left a.right with hL_def
    have hAL : a.left ∈ L := left_mem_lineOrOrthRadius
    suffices h : L.WSameSide a.mid Q ∨ L.WSameSide a.opposite.mid Q by
      rcases h with hM | hOM
      · exact Or.inl ((mem_iff_wSameSide hLR).mpr ⟨hQ, hL_def ▸ hM⟩)
      · have hLR' : a.opposite.left ≠ a.opposite.right := by simpa using hLR
        refine Or.inr ((mem_iff_wSameSide hLR').mpr ⟨hQ, ?_⟩)
        rw [opposite_left, opposite_right]
        exact hL_def ▸ hOM
    by_cases hQL : Q ∈ L
    · exact Or.inl (AffineSubspace.wSameSide_of_right_mem _ hQL)
    have hr_ne : s.radius ≠ 0 :=
      radius_ne_zero_of_mem_of_mem_of_ne a.left_mem hQ (fun h => hQL (h ▸ hAL))
    set m : V := a.mid -ᵥ s.center with hm_def
    set d : V := a.right -ᵥ a.left with hd_def
    set F : P := midpoint ℝ a.left a.right with hF_def
    have hL_eq : L = line[ℝ, a.left, a.right] := lineOrOrthRadius_of_ne hLR
    have hF_mem : F ∈ L := by
      rw [hL_eq, hF_def]; exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hd_ne : d ≠ 0 := vsub_ne_zero.mpr (Ne.symm hLR)
    have hm_ne : m ≠ 0 := by
      rw [hm_def, ← norm_ne_zero_iff, norm_vsub_center_eq_radius a.mid_mem]; exact hr_ne
    have hm_perp_d : ⟪m, d⟫ = 0 := a.inner_mid_vsub_center_right_vsub_left
    have hd_dir : d ∈ L.direction := by
      rw [hL_eq, direction_affineSpan, vectorSpan_pair, hd_def,
          show a.right -ᵥ a.left = -(a.left -ᵥ a.right) from (neg_vsub_eq_vsub_rev _ _).symm]
      exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
    have h_orth_eq : (Submodule.span ℝ ({m} : Set V))ᗮ = Submodule.span ℝ ({d} : Set V) := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hm_perp_d)
      · rw [Submodule.finrank_orthogonal_span_singleton (n := 1) hm_ne,
            finrank_span_singleton hd_ne]
    obtain ⟨t, ⟨ht0, ht1⟩, htF⟩ := (sbtw_mid_midpoint_opposite_mid a hLR).mem_image_Ioo
    have hopp_sub : (a.opposite.mid -ᵥ a.mid : V) = (-2 : ℝ) • m := by
      rw [show (a.opposite.mid -ᵥ a.mid : V) =
            (a.opposite.mid -ᵥ s.center) - (a.mid -ᵥ s.center) from
              (vsub_sub_vsub_cancel_right _ _ _).symm,
          opposite_mid_vsub_center, ← hm_def]
      module
    have hFm : (F -ᵥ a.mid : V) = (-2 * t) • m := by
      rw [hF_def, ← htF, AffineMap.lineMap_apply, vadd_vsub, hopp_sub, smul_smul]
      module
    set δ : ℝ := 1 - 2 * t with hδ_def
    have hδ_abs : |δ| < 1 := by rw [hδ_def, abs_lt]; constructor <;> linarith
    have ham_sub : (a.mid -ᵥ F : V) = (1 - δ) • m := by
      rw [show (a.mid -ᵥ F : V) = -(F -ᵥ a.mid) from (neg_vsub_eq_vsub_rev _ _).symm, hFm, hδ_def]
      module
    have haom_sub : (a.opposite.mid -ᵥ F : V) = (-(1 + δ)) • m := by
      rw [show (a.opposite.mid -ᵥ F : V) = (a.opposite.mid -ᵥ a.mid) + (a.mid -ᵥ F) from
            (vsub_add_vsub_cancel _ _ _).symm,
          hopp_sub, ham_sub, hδ_def]
      module
    set γ : ℝ := ⟪Q -ᵥ F, m⟫ / ⟪m, m⟫ with hγ_def
    set p : P := ((Q -ᵥ F) - γ • m) +ᵥ F with hp_def
    have hp_mem : p ∈ L := by
      have hvdir : (Q -ᵥ F) - γ • m ∈ L.direction := by
        have hperp : (Q -ᵥ F) - γ • m ∈ (Submodule.span ℝ ({m} : Set V))ᗮ := by
          rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
              real_inner_smul_right, hγ_def, div_mul_cancel₀ _ (inner_self_ne_zero.mpr hm_ne),
              real_inner_comm m (Q -ᵥ F), sub_self]
        rw [h_orth_eq] at hperp
        exact (Submodule.span_singleton_le_iff_mem _ _).mpr hd_dir hperp
      rw [hp_def]
      exact AffineSubspace.vadd_mem_of_mem_direction hvdir hF_mem
    have hQp : (Q -ᵥ p : V) = γ • m := by rw [hp_def, vsub_vadd_eq_vsub_sub]; module
    rcases le_or_gt 0 γ with hγ | hγ
    · exact Or.inl (AffineSubspace.wSameSide_of_vsub_eq_smul hF_mem hp_mem ham_sub hQp
        (mul_nonneg (by linarith [(abs_lt.mp hδ_abs).2]) hγ))
    · exact Or.inr (AffineSubspace.wSameSide_of_vsub_eq_smul hF_mem hp_mem haom_sub hQp
        (mul_nonneg_of_nonpos_of_nonpos (by linarith [(abs_lt.mp hδ_abs).1]) hγ.le))

/-- A sphere point distinct from both endpoints lies in the interior of the arc or of its
opposite. With `interior_disjoint_opposite`, exactly one of the two holds. -/
theorem mem_interior_or_mem_opposite_interior (a : Arc s) {Z : P} (hZ : Z ∈ s)
    (hZl : Z ≠ a.left) (hZr : Z ≠ a.right) :
    Z ∈ a.interior ∨ Z ∈ a.opposite.interior :=
  (mem_arc_or_mem_opposite a hZ).imp
    (mem_interior_of_mem_of_ne_left_of_ne_right · hZl hZr)
    (mem_interior_of_mem_of_ne_left_of_ne_right ·
      (by rwa [opposite_left]) (by rwa [opposite_right]))

/-- Interior points of an arc and its opposite lie on strictly opposite sides of the chord. -/
theorem sOppSide_of_mem_interior_of_mem_opposite_interior
    (a : Arc s) {X Y : P} (hne : a.left ≠ a.right)
    (hX : X ∈ a.interior) (hY : Y ∈ a.opposite.interior) :
    (s.lineOrOrthRadius a.left a.right).SOppSide X Y := by
  have hYss : (s.lineOrOrthRadius a.left a.right).SSameSide a.opposite.mid Y := by
    have h := sSameSide_of_mem_interior hY
    rwa [opposite_left, opposite_right] at h
  exact ((sSameSide_of_mem_interior hX).symm.trans_sOppSide
    (sOppSide_mid_opposite_mid a hne)).trans_sSameSide hYss

/-- In two dimensions, the interiors of an arc and its opposite are disjoint when the
endpoints differ. -/
theorem interior_disjoint_opposite (a : Arc s) (hne : a.left ≠ a.right) :
    Disjoint a.interior a.opposite.interior :=
  Set.disjoint_left.mpr fun _ hp hp' =>
    have h := sOppSide_of_mem_interior_of_mem_opposite_interior a hne hp hp'
    h.left_notMem (AffineSubspace.wOppSide_self_iff.mp h.wOppSide)

/-- A point lies in both an arc and its opposite if and only if it equals one of the
two endpoints. -/
theorem mem_and_mem_opposite_iff_eq_left_or_eq_right
    (a : Arc s) {Q : P} (hne : a.left ≠ a.right) :
    (Q ∈ a ∧ Q ∈ a.opposite) ↔ (Q = a.left ∨ Q = a.right) := by
  constructor
  · rintro ⟨hQa, hQo⟩
    by_contra h_not_endpoint
    push Not at h_not_endpoint
    exact Set.disjoint_left.mp (interior_disjoint_opposite a hne)
      (mem_interior_of_mem_of_ne_left_of_ne_right hQa h_not_endpoint.1 h_not_endpoint.2)
      (mem_interior_of_mem_of_ne_left_of_ne_right hQo
        (by simpa only [opposite_left] using h_not_endpoint.1)
        (by simpa only [opposite_right] using h_not_endpoint.2))
  · rintro (rfl | rfl)
    · exact ⟨left_mem_arc a, left_mem_arc a.opposite⟩
    · exact ⟨right_mem_arc a, by simpa using right_mem_arc a.opposite⟩

/-- Two arcs with the same ordered endpoints sharing an interior point are equal, including when
the endpoints coincide. -/
theorem eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior
    {a b : Arc s} {p : P}
    (hl : a.left = b.left) (hr : a.right = b.right)
    (hpa : p ∈ a.interior) (hpb : p ∈ b.interior) : a = b := by
  by_cases hlr : a.left = a.right
  · have hbne : b.left = b.right := by rw [← hl, ← hr]; exact hlr
    have hma : a.mid ≠ a.left := fun h =>
      (sSameSide_of_mem_interior hpa).left_notMem (h ▸ left_mem_lineOrOrthRadius)
    have hmb : b.mid ≠ b.left := fun h =>
      (sSameSide_of_mem_interior hpb).left_notMem (h ▸ left_mem_lineOrOrthRadius)
    refine Arc.ext hl ?_
    rw [mid_eq_pointReflection_center_left_of_left_eq_right_of_mid_ne_left a hlr hma,
        mid_eq_pointReflection_center_left_of_left_eq_right_of_mid_ne_left b hbne hmb, hl]
  · refine eq_of_left_eq_of_right_eq_of_sSameSide_mid hl hr hlr ?_
    have hb := sSameSide_of_mem_interior hpb
    rw [← hl, ← hr] at hb
    exact (sSameSide_of_mem_interior hpa).trans hb.symm

/-- Two arcs with the same ordered endpoints and the same point set are equal as `Arc`
objects. -/
theorem eq_of_left_eq_of_right_eq_of_coe_eq
    {a b : Arc s} (hl : a.left = b.left) (hr : a.right = b.right)
    (hset : (a : Set P) = (b : Set P)) :
    a = b := by
  by_cases hlr : a.left = a.right
  · -- Inline the degenerate dichotomy to keep this file independent of `Arc.Degenerate`.
    have hiff : a.mid = a.left ↔ b.mid = b.left := by
      rw [← coe_eq_singleton_iff_mid_eq_left a, ← coe_eq_singleton_iff_mid_eq_left b,
        hset, hl]
    refine Arc.ext hl ?_
    by_cases hma : a.mid = a.left
    · rw [hma, hiff.mp hma, hl]
    · rw [mid_eq_pointReflection_center_left_of_left_eq_right_of_mid_ne_left a hlr hma,
        mid_eq_pointReflection_center_left_of_left_eq_right_of_mid_ne_left b
          (by rw [← hl, ← hr]; exact hlr) (hiff.not.mp hma), hl]
  · have hmid : a.mid ∈ a.interior := mid_mem_interior a (a.mid_ne_left_of_left_ne_right hlr)
    refine eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior hl hr hmid ?_
    exact mem_interior_of_mem_of_ne_left_of_ne_right
      (show a.mid ∈ (b : Set P) from
        hset ▸ (show a.mid ∈ (a : Set P) from mid_mem_arc a))
      (fun h => ne_left_of_mem_interior hmid (h.trans hl.symm))
      (fun h => ne_right_of_mem_interior hmid (h.trans hr.symm))

/-! ## Canonicity of `through` and interaction with `minor` / `major` -/

/-- A sphere point distinct from the endpoints of a non-diametral chord lies in the interior
of either its minor arc or its major arc. -/
theorem mem_minor_interior_or_mem_major_interior
    {X Y Z : P} (hX : X ∈ s) (hY : Y ∈ s) (hND : ¬s.IsDiameter X Y)
    (hZ : Z ∈ s) (hZX : Z ≠ X) (hZY : Z ≠ Y) :
    Z ∈ (minor hX hY hND).interior ∨ Z ∈ (major hX hY hND).interior :=
  mem_interior_or_mem_opposite_interior _ hZ
    (by simpa only [minor_left] using hZX) (by simpa only [minor_right] using hZY)

/-- A point lies in the interior of `through A B C` if and only if it lies on the sphere and is
strictly on the same side of the chord `AC` as the through-point `B`. -/
theorem mem_interior_through_iff
    {A B C Q : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C) :
    Q ∈ (through hA hB hC hBA hBC).interior ↔
      Q ∈ s ∧ (s.lineOrOrthRadius A C).SSameSide B Q := by
  have hmid : (s.lineOrOrthRadius A C).SSameSide (through hA hB hC hBA hBC).mid B := by
    simpa only [through_left, through_right hA hB hC hBA hBC] using
      sSameSide_of_mem_interior (mem_interior_through hA hB hC hBA hBC)
  rw [mem_interior_iff, through_left, through_right hA hB hC hBA hBC]
  exact and_congr_right fun _ => ⟨(hmid.symm.trans ·), (hmid.trans ·)⟩

/-- If `Q` lies on the sphere and is strictly on the same side of the chord `AC` as the
through-point `B`, then `Q` lies in the interior of `Sphere.Arc.through A B C`. -/
theorem mem_interior_through_of_sSameSide
    {A B C Q : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hQ : Q ∈ s) (hss : (s.lineOrOrthRadius A C).SSameSide B Q) :
    Q ∈ (through hA hB hC hBA hBC).interior :=
  (mem_interior_through_iff hA hB hC hBA hBC).mpr ⟨hQ, hss⟩

/-- Two interior points of `Sphere.Arc.through A B C` are strictly on the same side of the
chord `AC`. -/
theorem sSameSide_of_mem_interior_through
    {A B C X Y : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    (hX : X ∈ (through hA hB hC hBA hBC).interior)
    (hY : Y ∈ (through hA hB hC hBA hBC).interior) :
    (s.lineOrOrthRadius A C).SSameSide X Y :=
  ((mem_interior_through_iff hA hB hC hBA hBC).mp hX).2.symm.trans
    ((mem_interior_through_iff hA hB hC hBA hBC).mp hY).2

/-- `through A B C` is the unique arc with endpoints `A`, `C` having `B` in its interior. -/
theorem through_eq_of_mem_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    {b : Arc s} (hbl : b.left = A) (hbr : b.right = C) (hBb : B ∈ b.interior) :
    through hA hB hC hBA hBC = b :=
  eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior
    (by rw [through_left, hbl]) (by rw [through_right hA hB hC hBA hBC, hbr])
    (mem_interior_through hA hB hC hBA hBC) hBb

/-- `avoiding A B C` is the unique arc with endpoints `A`, `C` having `B` in the interior of
its opposite. -/
theorem avoiding_eq_of_mem_opposite_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C)
    {b : Arc s} (hbl : b.left = A) (hbr : b.right = C)
    (hBb : B ∈ b.opposite.interior) :
    avoiding hA hB hC hBA hBC = b := by
  rw [← through_opposite hA hB hC hBA hBC,
    through_eq_of_mem_interior hA hB hC hBA hBC
    (by rwa [opposite_left]) (by rwa [opposite_right]) hBb, opposite_opposite]

/-! ### Independence of the through-point -/

/-- Two through-points strictly on the same side of `AC` determine the same `through` arc. This
also holds when the endpoints coincide. -/
theorem through_eq_through_of_sSameSide
    {A B C D : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hD : D ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hDA : D ≠ A) (hDC : D ≠ C)
    (hss : (s.lineOrOrthRadius A C).SSameSide B D) :
    through hA hB hC hBA hBC = through hA hD hC hDA hDC :=
  through_eq_of_mem_interior hA hB hC hBA hBC
    (through_left hA hD hC hDA hDC) (through_right hA hD hC hDA hDC)
    (mem_interior_through_of_sSameSide hA hD hC hDA hDC hB hss.symm)

/-- Two through-points strictly on the same side of `AC` determine the same `avoiding` arc. -/
theorem avoiding_eq_avoiding_of_sSameSide
    {A B C D : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hD : D ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hDA : D ≠ A) (hDC : D ≠ C)
    (hss : (s.lineOrOrthRadius A C).SSameSide B D) :
    avoiding hA hB hC hBA hBC = avoiding hA hD hC hDA hDC :=
  congrArg Arc.opposite
    (through_eq_through_of_sSameSide hA hB hC hD hBA hBC hDA hDC hss)

/-! ### Complementary branches -/

/-- Through-points strictly on opposite sides of `AC` select complementary arcs: the arc through
`B` is the arc avoiding `D`. When `A = C`, no two sphere points can lie strictly on opposite sides
of `s.lineOrOrthRadius A C`, so the hypothesis rules out that case on its own. -/
theorem through_eq_avoiding_of_sOppSide
    {A B C D : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hD : D ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hDA : D ≠ A) (hDC : D ≠ C)
    (hopp : (s.lineOrOrthRadius A C).SOppSide B D) :
    through hA hB hC hBA hBC = avoiding hA hD hC hDA hDC := by
  refine through_eq_of_mem_interior hA hB hC hBA hBC
    (avoiding_left hA hD hC hDA hDC) (avoiding_right hA hD hC hDA hDC) ?_
  rcases mem_interior_or_mem_opposite_interior (through hA hD hC hDA hDC) hB
    (by simpa only [through_left] using hBA)
    (by simpa only [through_right hA hD hC hDA hDC] using hBC) with h | h
  · exact absurd
      (sSameSide_of_mem_interior_through hA hD hC hDA hDC h
        (mem_interior_through hA hD hC hDA hDC))
      hopp.not_sSameSide
  · rwa [through_opposite] at h

/-- Through-points strictly on opposite sides of `AC` select complementary arcs: the arc avoiding
`B` is the arc through `D`. -/
theorem avoiding_eq_through_of_sOppSide
    {A B C D : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hD : D ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hDA : D ≠ A) (hDC : D ≠ C)
    (hopp : (s.lineOrOrthRadius A C).SOppSide B D) :
    avoiding hA hB hC hBA hBC = through hA hD hC hDA hDC :=
  (through_eq_avoiding_of_sOppSide hA hD hC hB hDA hDC hBA hBC hopp.symm).symm

/-! ### Object-level identification -/

/-- If `B` lies in the minor arc's interior, then `through A B C` is the minor arc as an
`Arc` object. -/
theorem through_eq_minor_of_mem_minor_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hNotDiam).interior) :
    through hA hB hC hBA hBC = minor hA hC hNotDiam :=
  through_eq_of_mem_interior hA hB hC hBA hBC
    (minor_left hA hC hNotDiam) (minor_right hA hC hNotDiam) hB_minor

/-- If `B` lies in the major arc's interior, then `through A B C` is the major arc as an
`Arc` object. -/
theorem through_eq_major_of_mem_major_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_major : B ∈ (major hA hC hNotDiam).interior) :
    through hA hB hC hBA hBC = major hA hC hNotDiam :=
  through_eq_of_mem_interior hA hB hC hBA hBC
    (major_left hA hC hNotDiam) (major_right hA hC hNotDiam) hB_major

end Arc

end Sphere

end EuclideanGeometry
