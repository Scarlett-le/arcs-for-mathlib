/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import ArcsForMathlib.Sphere.Arc.Basic

/-!
# Structure of arcs: complementation and canonicity

In two dimensions a chord separates the sphere, and this file develops the two consequences of
that fact. First, an arc and its opposite cover the sphere and meet exactly at the two endpoints,
so their interiors partition the sphere minus the endpoints. Second, an arc with distinct
endpoints is determined by its ordered endpoints together with any one of its interior points;
this makes `through A B C` canonical and yields object-level identifications of `through` with
`minor` and `major`.

## Main results

* `EuclideanGeometry.Sphere.Arc.mem_arc_or_mem_opposite` and
  `EuclideanGeometry.Sphere.Arc.mem_interior_or_mem_opposite_interior`: every point of the sphere
  lies in an arc or in its opposite, and a point distinct from both endpoints lies in one of the
  two interiors.
* `EuclideanGeometry.Sphere.Arc.interior_disjoint_opposite` and
  `EuclideanGeometry.Sphere.Arc.mem_and_mem_opposite_iff_eq_left_or_eq_right`: the two interiors
  are disjoint, and the two arcs meet exactly at the endpoints.
* `EuclideanGeometry.Sphere.Arc.eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior` and
  `EuclideanGeometry.Sphere.Arc.eq_of_coe_eq_of_left_eq_of_right_eq`: distinct ordered endpoints
  together with one shared interior point — or with equal point sets — determine the same `Arc`
  object.
* `EuclideanGeometry.Sphere.Arc.mem_interior_through_iff`: the interior of `through A B C` is
  exactly the set of sphere points strictly on the same side of `AC` as `B`.
* `EuclideanGeometry.Sphere.Arc.through_eq_minor_of_mem_minor_interior` and
  `EuclideanGeometry.Sphere.Arc.through_eq_major_of_mem_major_interior`: `through` coincides with
  `minor` and with `major` as `Arc` objects, not merely as point sets.

## Implementation notes

`through_eq_minor_of_mem_minor_interior` re-proves, in the special case it needs, that a
single-point arc has empty interior; the general statement is `interior_eq_empty_of_isSinglePoint`
in `Arc.Degenerate`. This is deliberate, so that the two files stay independent and can be read in
either order.
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

/-- Two arcs with the same distinct ordered endpoints sharing an interior point are equal. -/
theorem eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior
    {a b : Arc s} {p : P}
    (hl : a.left = b.left) (hr : a.right = b.right) (hne : a.left ≠ a.right)
    (hpa : p ∈ a.interior) (hpb : p ∈ b.interior) :
    a = b := by
  refine eq_of_left_eq_of_right_eq_of_sSameSide_mid hl hr hne ?_
  have hb := sSameSide_of_mem_interior hpb
  rw [← hl, ← hr] at hb
  exact (sSameSide_of_mem_interior hpa).trans hb.symm

/-- Two arcs with the same distinct ordered endpoints and the same point set are equal as `Arc`
objects. -/
theorem eq_of_coe_eq_of_left_eq_of_right_eq
    {a b : Arc s} (hl : a.left = b.left) (hr : a.right = b.right)
    (hne : a.left ≠ a.right) (hset : (a : Set P) = (b : Set P)) :
    a = b := by
  have hmid : a.mid ∈ a.interior := mid_mem_interior a hne
  refine eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior hl hr hne hmid ?_
  exact mem_interior_of_mem_of_ne_left_of_ne_right
    (show a.mid ∈ (b : Set P) from
      hset ▸ (show a.mid ∈ (a : Set P) from mid_mem_arc a))
    (fun h => ne_left_of_mem_interior hmid (h.trans hl.symm))
    (fun h => ne_right_of_mem_interior hmid (h.trans hr.symm))

/-! ## Interaction between `through` and `minor` / `major` -/

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
    {b : Arc s} (hbl : b.left = A) (hbr : b.right = C) (hAC : A ≠ C)
    (hBb : B ∈ b.interior) :
    through hA hB hC hBA hBC = b :=
  eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior
    (by rw [through_left, hbl]) (by rw [through_right hA hB hC hBA hBC, hbr])
    (by rw [through_left, through_right hA hB hC hBA hBC]; exact hAC)
    (mem_interior_through hA hB hC hBA hBC) hBb

/-! ### Object-level identification -/

/-- If `B` lies in the minor arc's interior, then `through A B C` is the minor arc as an
`Arc` object. -/
theorem through_eq_minor_of_mem_minor_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hNotDiam).interior) :
    through hA hB hC hBA hBC = minor hA hC hNotDiam := by
  have hAC : A ≠ C := by
    rintro rfl
    refine (sSameSide_of_mem_interior hB_minor).left_notMem ?_
    have hmid : (minor hA hC hNotDiam).mid = (minor hA hC hNotDiam).left := by
      rw [minor_left]
      exact minorMidpoint_self hA (radius_ne_zero_of_mem_of_mem_of_ne hA hB hBA.symm)
    rw [hmid]
    exact left_mem_lineOrOrthRadius
  exact through_eq_of_mem_interior hA hB hC hBA hBC
    (minor_left hA hC hNotDiam) (minor_right hA hC hNotDiam) hAC hB_minor

/-- If `B` lies in the major arc's interior, then `through A B C` is the major arc as an
`Arc` object. -/
theorem through_eq_major_of_mem_major_interior
    {A B C : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_major : B ∈ (major hA hC hNotDiam).interior) :
    through hA hB hC hBA hBC = major hA hC hNotDiam := by
  by_cases hAC : A = C
  · subst C
    exact through_self_eq_major_self hA hB hBA hNotDiam
  · exact through_eq_of_mem_interior hA hB hC hBA hBC
      (major_left hA hC hNotDiam) (major_right hA hC hNotDiam) hAC hB_major

/-! ### Membership-level consequences -/

/-- If `B` lies in the minor arc's interior, then `through A B C` and the minor arc have the
same points. This is the membership-level consequence of
`through_eq_minor_of_mem_minor_interior`. -/
theorem mem_through_iff_mem_minor_of_mem_minor_interior
    {A B C Q : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_minor : B ∈ (minor hA hC hNotDiam).interior) :
    Q ∈ through hA hB hC hBA hBC ↔ Q ∈ minor hA hC hNotDiam := by
  rw [through_eq_minor_of_mem_minor_interior hA hB hC hBA hBC hNotDiam hB_minor]

/-- If `B` lies in the major arc's interior, then `through A B C` and the major arc have the
same points. This is the membership-level consequence of
`through_eq_major_of_mem_major_interior`. -/
theorem mem_through_iff_mem_major_of_mem_major_interior
    {A B C Q : P} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hBA : B ≠ A) (hBC : B ≠ C) (hNotDiam : ¬s.IsDiameter A C)
    (hB_major : B ∈ (major hA hC hNotDiam).interior) :
    Q ∈ through hA hB hC hBA hBC ↔ Q ∈ major hA hC hNotDiam := by
  rw [through_eq_major_of_mem_major_interior hA hB hC hBA hBC hNotDiam hB_major]

end Arc

end Sphere

end EuclideanGeometry
