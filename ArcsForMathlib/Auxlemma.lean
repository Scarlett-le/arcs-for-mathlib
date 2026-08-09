/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius
public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.SignedDist
public import Mathlib.Geometry.Euclidean.Triangle

@[expose] public section

noncomputable section

open scoped EuclideanGeometry InnerProductSpace

/-! ## Side / `SameRay` helpers

These package the recurring "displacement is a scalar multiple of a fixed vector"
witnesses for `WSameSide` / `WOppSide` (and their strict forms), so that call sites no
longer build `SameRay` proofs by hand. They live over any real module + torsor; no inner
product is needed. -/

section Side

variable {V : Type*} {P : Type*}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Two scalar multiples of a common vector whose coefficients have the same sign
(or one of which is zero) lie on a common ray. -/
theorem sameRay_smul_smul_of_mul_nonneg {m : V} {c₁ c₂ : ℝ} (h : 0 ≤ c₁ * c₂) :
    SameRay ℝ (c₁ • m) (c₂ • m) := by
  rcases eq_or_ne c₁ 0 with hc₁ | hc₁
  · rw [hc₁, zero_smul]; exact SameRay.zero_left _
  rcases eq_or_ne c₂ 0 with hc₂ | hc₂
  · rw [hc₂, zero_smul]; exact SameRay.zero_right _
  have hpos : 0 < c₁ * c₂ := h.lt_of_ne (Ne.symm (mul_ne_zero hc₁ hc₂))
  rcases mul_pos_iff.mp hpos with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr (Or.inr ⟨c₂, c₁, h₂, h₁, by rw [smul_smul, smul_smul]; congr 1; ring⟩)
  · exact Or.inr (Or.inr ⟨-c₂, -c₁, neg_pos.mpr h₂, neg_pos.mpr h₁, by
      rw [smul_smul, smul_smul]; congr 1; ring⟩)

namespace AffineSubspace

/-- If `x` and `y` are displaced from points of `s` by same-signed multiples of a common
vector, they are weakly on the same side of `s`. -/
theorem wSameSide_of_vsub_eq_smul {s : AffineSubspace ℝ P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : ℝ}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m) (hc : 0 ≤ c₁ * c₂) :
    s.WSameSide x y :=
  ⟨p₁, hp₁, p₂, hp₂, by rw [h₁, h₂]; exact sameRay_smul_smul_of_mul_nonneg hc⟩

/-- If `x` and `y` are displaced from points of `s` by opposite-signed multiples of a common
vector, they are weakly on opposite sides of `s`. -/
theorem wOppSide_of_vsub_eq_smul {s : AffineSubspace ℝ P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : ℝ}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m) (hc : c₁ * c₂ ≤ 0) :
    s.WOppSide x y :=
  ⟨p₁, hp₁, p₂, hp₂, by
    rw [h₁, show p₂ -ᵥ y = (-c₂) • m from by rw [← neg_vsub_eq_vsub_rev, h₂, neg_smul]]
    exact sameRay_smul_smul_of_mul_nonneg (by rw [mul_neg]; linarith)⟩

/-- Strict same-side version of `wSameSide_of_vsub_eq_smul`. -/
theorem sSameSide_of_vsub_eq_smul {s : AffineSubspace ℝ P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : ℝ}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m) (hc : 0 ≤ c₁ * c₂)
    (hx : x ∉ s) (hy : y ∉ s) :
    s.SSameSide x y :=
  ⟨wSameSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

/-- Strict opposite-side version of `wOppSide_of_vsub_eq_smul`. -/
theorem sOppSide_of_vsub_eq_smul {s : AffineSubspace ℝ P} {x y p₁ p₂ : P} {m : V} {c₁ c₂ : ℝ}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (h₁ : x -ᵥ p₁ = c₁ • m) (h₂ : y -ᵥ p₂ = c₂ • m) (hc : c₁ * c₂ ≤ 0)
    (hx : x ∉ s) (hy : y ∉ s) :
    s.SOppSide x y :=
  ⟨wOppSide_of_vsub_eq_smul hp₁ hp₂ h₁ h₂ hc, hx, hy⟩

end AffineSubspace

end Side

/-! ## ChineseMO 2010 P1 backported angle helpers -/

namespace Real

/-- ChineseMO 2010 P1 auxiliary lemma. -/
@[simp]
theorem pi_div_two_le_arccos {x : ℝ} : π / 2 ≤ arccos x ↔ x ≤ 0 := by
  simp [arccos]

/-- ChineseMO 2010 P1 auxiliary lemma. -/
@[simp]
theorem pi_div_two_lt_arccos {x : ℝ} : π / 2 < arccos x ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arccos_le_pi_div_two

end Real

namespace InnerProductGeometry

open RealInnerProductSpace
open scoped RealInnerProductSpace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- ChineseMO 2010 P1 auxiliary lemma.

The inner product of two vectors is nonpositive if and only if the angle between them is
at least `π / 2`. -/
theorem inner_nonpos_iff_pi_div_two_le_angle {x y : V} :
    ⟪x, y⟫ ≤ 0 ↔ π / 2 ≤ angle x y := by
  rw [angle, Real.pi_div_two_le_arccos]
  refine ⟨fun h => div_nonpos_of_nonpos_of_nonneg h (by positivity), fun h => ?_⟩
  by_contra hpos
  push Not at hpos
  exact absurd h (not_le.2 (div_pos hpos (hpos.trans_le (real_inner_le_norm x y))))

/-- ChineseMO 2010 P1 auxiliary lemma.

The inner product of two vectors is negative if and only if the angle between them exceeds
`π / 2`. -/
theorem inner_neg_iff_pi_div_two_lt_angle {x y : V} :
    ⟪x, y⟫ < 0 ↔ π / 2 < angle x y := by
  rw [angle, Real.pi_div_two_lt_arccos]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have hy : y ≠ 0 := by rintro rfl; simp at h
    exact div_neg_of_neg_of_pos h (mul_pos (norm_pos_iff.2 hx) (norm_pos_iff.2 hy))
  · by_contra hnonneg
    push Not at hnonneg
    exact absurd h (not_lt.2 (div_nonneg hnonneg (by positivity)))

end InnerProductGeometry

/-! ## Angle helpers

These angle-addition lemmas have already been submitted upstream to Mathlib. -/

namespace EuclideanGeometry

open InnerProductGeometry
open scoped EuclideanGeometry RealInnerProductSpace Real

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

/-- ChineseMO 2010 P1 auxiliary lemma.
The angle at `p₂` is at least `π / 2` if and only if the square of the opposite side is at
least the sum of the squares of the other two sides. -/
theorem dist_sq_add_dist_sq_le_dist_sq_iff_pi_div_two_le_angle {p₁ p₂ p₃ : P} :
    dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ≤ dist p₁ p₃ * dist p₁ p₃ ↔
      π / 2 ≤ ∠ p₁ p₂ p₃ := by
  rw [angle, ← InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle,
    dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂,
    show (p₁ -ᵥ p₃ : V) = (p₁ -ᵥ p₂) - (p₃ -ᵥ p₂) from
      (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm,
    norm_sub_mul_self_real]
  constructor <;> intro h <;> linarith

/-- If `X` lies strictly between `A` and `C`, then `∠ A P X + ∠ X P C = ∠ A P C`,
with no nondegeneracy assumption on the point `P`. -/
lemma angle_add_angle_eq_of_sbtw {a c p x : P} (hx : Sbtw ℝ a x c) :
    ∠ a p x + ∠ x p c = ∠ a p c := by
  by_cases hpa : p = a
  · subst p; simp [(hx.angle_eq_right x).symm.trans (angle_self_of_ne hx.ne_left)]
  by_cases hpc : p = c
  · subst p; simp [(hx.symm.angle_eq_right a).trans (angle_self_of_ne hx.left_ne_right)]
  exact angle_add_of_ne_of_ne hpa hpc hx.wbtw

/-- If `B` lies on the same ray from `P` as a point `X` strictly between `A` and `C`,
then `∠ A P B + ∠ B P C = ∠ A P C`. -/
theorem angle_add_angle_eq_of_sbtw_of_sameRay {a b c p x : P}
    (hx : Sbtw ℝ a x c) (hxb : SameRay ℝ (x -ᵥ p) (b -ᵥ p)) (hb : b ≠ p) :
    ∠ a p b + ∠ b p c = ∠ a p c := by
  by_cases hxp : x = p
  · subst x
    have hpi : ∠ a p c = π := hx.angle₁₂₃_eq_pi
    rw [hpi, angle_comm a p b]
    exact angle_add_angle_eq_pi_of_angle_eq_pi b hpi
  obtain ⟨r, hr, hrb⟩ :=
    (exists_pos_left_iff_sameRay (vsub_ne_zero.2 hxp) (vsub_ne_zero.2 hb)).2 hxb
  have hab : ∠ a p b = ∠ a p x := by
    unfold EuclideanGeometry.angle; rw [← hrb]; exact angle_smul_right_of_pos _ _ hr
  have hbc : ∠ b p c = ∠ x p c := by
    unfold EuclideanGeometry.angle; rw [← hrb]; exact angle_smul_left_of_pos _ _ hr
  rw [hab, hbc]
  exact angle_add_angle_eq_of_sbtw hx

end EuclideanGeometry

/-! ## From `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`

The theorem `mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero` is placed in the
`Submodule` namespace with `open Module` to bring `finrank` into scope, matching
the original file structure.
-/

namespace Submodule

open Module

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

/-- If two nonzero vectors `w` and `u` are both orthogonal to the same nonzero vector `v`
in a two-dimensional inner product space, then `u` lies in the span of `w`. -/
theorem mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Fact (finrank 𝕜 E = 2)] {u v w : E}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪v, u⟫_𝕜 = 0) (hwv : ⟪v, w⟫_𝕜 = 0) :
    u ∈ Submodule.span 𝕜 {w} := by
  haveI : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ 1
  have heq : 𝕜 ∙ w = (𝕜 ∙ v)ᗮ :=
      Submodule.eq_of_le_of_finrank_le
        ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hwv))
        (by rw [finrank_orthogonal_span_singleton (n := 1) hv, finrank_span_singleton hw])
  rwa [heq, Submodule.mem_orthogonal_singleton_iff_inner_right]

end Submodule

/-! ## From `Mathlib.Analysis.InnerProductSpace.Basic`

Helper lemmas `inner_eq_zero_of_left` / `inner_eq_zero_of_right` may also be from the
same PR. If they already exist in your Mathlib, remove them to avoid duplicates.
-/

section InnerProductBasicHelpers

variable {𝕜' E' : Type*} [RCLike 𝕜'] [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜' E']

end InnerProductBasicHelpers

namespace EuclideanGeometry

open RealInnerProductSpace

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-! ## From `Mathlib.Geometry.Euclidean.Sphere.OrthRadius`

If your Mathlib does NOT yet have the OrthRadius file at all, you will need to uncomment
the `orthRadius` block below. If it already exists, just keep the `lineOrOrthRadius` section.
-/

namespace Sphere

open AffineSubspace RealInnerProductSpace
open scoped Affine

variable {s : Sphere P} {p q : P}

/-- A sphere lies strictly on one side of the affine subspace orthogonal to a radius at one of
its points: any two sphere points other than the point of tangency are strictly on the same side.
This result is dimension-independent. -/
theorem sSameSide_orthRadius_of_mem {q₁ q₂ : P} (hp : p ∈ s) (hq₁ : q₁ ∈ s)
    (hq₂ : q₂ ∈ s) (hpq₁ : p ≠ q₁) (hpq₂ : p ≠ q₂) :
    (s.orthRadius p).SSameSide q₁ q₂ := by
  have hpc : p ≠ s.center := by
    rintro rfl
    exact hpq₁ (dist_eq_zero.mp (by rw [mem_sphere.mp hq₁, ← mem_sphere.mp hp, dist_self])).symm
  have hmm : (0 : ℝ) < ⟪p -ᵥ s.center, p -ᵥ s.center⟫ :=
    real_inner_self_pos.2 (vsub_ne_zero.2 hpc)
  have hsign : ∀ {q : P}, q ∈ s → p ≠ q → ⟪q -ᵥ p, p -ᵥ s.center⟫ < 0 := by
    intro q hq hpq
    have h := inner_vsub_center_vsub_pos hp hq hpq
    rwa [← neg_vsub_eq_vsub_rev p s.center, inner_neg_right, neg_pos] at h
  have hnot : ∀ {q : P}, q ∈ s → p ≠ q → q ∉ s.orthRadius p := by
    intro q hq hpq hmem
    exact (hsign hq hpq).ne (mem_orthRadius_iff_inner_left.mp hmem)
  have key : ∀ q : P, ∃ f ∈ s.orthRadius p, q -ᵥ f =
      (⟪q -ᵥ p, p -ᵥ s.center⟫ / ⟪p -ᵥ s.center, p -ᵥ s.center⟫) • (p -ᵥ s.center) := by
    intro q
    refine ⟨(-(⟪q -ᵥ p, p -ᵥ s.center⟫ / ⟪p -ᵥ s.center, p -ᵥ s.center⟫)) •
        (p -ᵥ s.center) +ᵥ q, ?_, ?_⟩
    · rw [mem_orthRadius_iff_inner_left, vadd_vsub_assoc, inner_add_left,
        real_inner_smul_left]
      field_simp [hmm.ne']
      ring
    · rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_smul, neg_neg]
  obtain ⟨f₁, hf₁, hv₁⟩ := key q₁
  obtain ⟨f₂, hf₂, hv₂⟩ := key q₂
  exact AffineSubspace.sSameSide_of_vsub_eq_smul hf₁ hf₂ hv₁ hv₂
    (mul_nonneg_of_nonpos_of_nonpos (div_neg_of_neg_of_pos (hsign hq₁ hpq₁) hmm).le
      (div_neg_of_neg_of_pos (hsign hq₂ hpq₂) hmm).le) (hnot hq₁ hpq₁) (hnot hq₂ hpq₂)

open Classical in
/-- The line through two points on a sphere, or the orthogonal radius (tangent) at that point
when they coincide. -/
noncomputable def lineOrOrthRadius (s : Sphere P) (p q : P) : AffineSubspace ℝ P :=
  if p = q then s.orthRadius p else line[ℝ, p, q]

@[simp]
lemma lineOrOrthRadius_of_eq (h : p = q) : s.lineOrOrthRadius p q = s.orthRadius p := by
  rw [lineOrOrthRadius, if_pos h]

@[simp]
lemma lineOrOrthRadius_of_ne (h : p ≠ q) : s.lineOrOrthRadius p q = line[ℝ, p, q] := by
  rw [lineOrOrthRadius, if_neg h]

lemma left_mem_lineOrOrthRadius : p ∈ s.lineOrOrthRadius p q := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, self_mem_orthRadius, left_mem_affineSpan_pair]

lemma right_mem_lineOrOrthRadius : q ∈ s.lineOrOrthRadius p q := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, self_mem_orthRadius, right_mem_affineSpan_pair]

lemma lineOrOrthRadius_comm : s.lineOrOrthRadius p q = s.lineOrOrthRadius q p := by
  by_cases h : p = q <;> simp [lineOrOrthRadius, h, Ne.symm, affineSpan_pair_comm]

/-- A point on the sphere, distinct from both endpoints,
    cannot lie on the lineOrOrthRadius between them. -/
lemma notMem_lineOrOrthRadius_of_mem_sphere {A B C : P}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hBA : B ≠ A) (hBC : B ≠ C) :
    B ∉ s.lineOrOrthRadius A C := by
  by_cases hAC : A = C
  · subst hAC
    simp only [lineOrOrthRadius_of_eq, mem_orthRadius_iff_inner_left]
    intro h
    have := inner_pos_or_eq_of_dist_le_radius hA (mem_sphere.mp hB).le
    rw [← neg_vsub_eq_vsub_rev, inner_neg_left, h, neg_zero, lt_self_iff_false, false_or] at this
    exact hBA this.symm
  · simp only [lineOrOrthRadius_of_ne hAC]
    intro hB_mem
    have hB_eq := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA hB_mem).mpr hB
    have hC_eq := (s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hA
      (right_mem_affineSpan_pair ℝ A C)).mpr hC
    rcases hB_eq, hC_eq with ⟨rfl | hB', rfl | hC'⟩
    · exact hBA rfl
    · exact hBA rfl
    · exact hAC rfl
    · exact hBC (hB'.trans hC'.symm)

/-- The intersection of lineOrOrthRadius with the sphere is exactly the endpoints. -/
lemma mem_lineOrOrthRadius_inter_sphere_iff {A B C : P}
    (hA : A ∈ s) (hC : C ∈ s) (hB : B ∈ s) :
    B ∈ s.lineOrOrthRadius A C ↔ B = A ∨ B = C := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact notMem_lineOrOrthRadius_of_mem_sphere hA hB hC hne.1 hne.2 h
  · rintro (rfl | rfl)
    · exact left_mem_lineOrOrthRadius
    · exact right_mem_lineOrOrthRadius


end Sphere

end EuclideanGeometry

end

/-! ## Sphere-chord auxiliary lemmas

The following lemmas concern the relationship between a sphere, its center,
a chord, and diametric configurations.  They were previously stated at
the end of `Arc.lean` but are more naturally placed here, since they are
pure facts about spheres and chords (not involving the `Arc` structure
itself), and are used from multiple downstream files (`Arc/Structure.lean`,
`Arc/Measure.lean`). -/

namespace EuclideanGeometry

namespace Sphere

open scoped EuclideanGeometry RealInnerProductSpace Real

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- A sphere containing a point and having nonzero radius has positive radius. -/
theorem radius_pos_of_mem {s : Sphere P} {p : P} (hp : p ∈ s) (hr : s.radius ≠ 0) :
    0 < s.radius :=
  (radius_nonneg_of_mem hp).lt_of_ne' hr

/-- If a sphere contains two distinct points, then its radius is nonzero. -/
theorem radius_ne_zero_of_mem_of_mem_of_ne {s : Sphere P} {p q : P}
    (hp : p ∈ s) (hq : q ∈ s) (hne : p ≠ q) : s.radius ≠ 0 := by
  intro hr
  apply hne
  exact (dist_eq_zero.mp ((mem_sphere.mp hp).trans hr)).trans
    (dist_eq_zero.mp ((mem_sphere.mp hq).trans hr)).symm

/-- A point of a sphere that differs from some other point of the sphere is not its center. -/
lemma ne_center_of_mem_of_mem_of_ne {s : Sphere P} {p q : P}
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) : p ≠ s.center := by
  rintro rfl
  rw [center_mem_iff] at hp
  exact hpq (dist_eq_zero.mp (by rw [mem_sphere.mp hq, hp])).symm

omit [InnerProductSpace ℝ V] in
/-- For a point on a sphere, the norm of its displacement from the center equals the radius. -/
theorem norm_vsub_center_eq_radius {s : Sphere P} {p : P} (hp : p ∈ s) :
    ‖p -ᵥ s.center‖ = s.radius := by
  rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp

/-- Point reflection through the center of a sphere preserves membership in the sphere. -/
lemma pointReflection_center_mem {s : Sphere P} {m : P} (hm : m ∈ s) :
    AffineEquiv.pointReflection ℝ s.center m ∈ s := by
  rw [mem_sphere] at hm ⊢
  rw [AffineEquiv.pointReflection_apply, dist_vadd_left, ← dist_eq_norm_vsub', ← hm]

/-- The center lies on the chord between two distinct points of a sphere iff
those points are diametrically opposite. -/
theorem center_mem_affineSpan_pair_iff_isDiameter {s : Sphere P}
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hne : A ≠ C) :
    s.center ∈ line[ℝ, A, C] ↔ s.IsDiameter A C := by
  rw [isDiameter_iff_mem_and_mem_and_wbtw]
  refine ⟨fun h => ⟨hA, hC, ?_⟩, fun h => h.2.2.mem_affineSpan⟩
  have hcol : Collinear ℝ ({A, s.center, C} : Set P) := by
    have h' := collinear_insert_of_mem_affineSpan_pair h
    rwa [Set.insert_comm] at h'
  refine wbtw_of_collinear_of_dist_center_le_radius hcol hA ?_ hC hne
  simpa using radius_nonneg_of_mem hA

/-- On a sphere of nonzero radius, the central angle `∠ A center C` equals `π` iff
`A` and `C` are diametrically opposite. -/
theorem angle_center_eq_pi_iff_isDiameter {s : Sphere P}
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hr : s.radius ≠ 0) :
    ∠ A s.center C = π ↔ s.IsDiameter A C := by
  rw [angle_eq_pi_iff_sbtw]
  exact ⟨fun h => isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨hA, hC, h.wbtw⟩, fun h => h.sbtw hr⟩

/-- On a sphere of nonzero radius, the central angle `∠ A center C` equals zero iff
`A = C`. -/
theorem angle_center_eq_zero_iff_eq {s : Sphere P}
    {A C : P} (hA : A ∈ s) (hC : C ∈ s) (hr : s.radius ≠ 0) :
    ∠ A s.center C = 0 ↔ A = C := by
  constructor
  · intro hangle
    exact vsub_left_cancel <|
      InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq
        (by simpa [angle] using hangle)
        (by rw [norm_vsub_center_eq_radius hA, norm_vsub_center_eq_radius hC])
  · intro h
    subst h
    exact angle_self_of_ne fun heq => hr (Sphere.center_mem_iff.mp (heq ▸ hC))

/-! ## Power of a point

These lemmas are signed-power counterparts and converses to the power-of-a-point API in
`Mathlib.Geometry.Euclidean.Sphere.Power`.  The signed invariant is the inner product
`⟪a -ᵥ p, b -ᵥ p⟫`, which avoids splitting the chord and secant cases by hand. -/

/-- Signed power of a point on a secant line: if `a` and `b` lie on `s` and `p` lies on the
line `ab`, then `⟪a -ᵥ p, b -ᵥ p⟫` is exactly the power of `p` with respect to `s`. -/
theorem inner_vsub_vsub_eq_power {s : Sphere P} {a b p : P}
    (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ line[ℝ, a, b]) :
    ⟪a -ᵥ p, b -ᵥ p⟫ = s.power p := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  set A : V := a -ᵥ s.center with hA
  set B : V := b -ᵥ s.center with hB
  have ha' : ⟪A, A⟫ = s.radius ^ 2 := by
    rw [hA, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp ha]
  have hb' : ⟪B, B⟫ = s.radius ^ 2 := by
    rw [hB, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp hb]
  have hap : (a -ᵥ AffineMap.lineMap a b t : V) = t • (A - B) := by
    rw [AffineMap.left_vsub_lineMap, hA, hB, vsub_sub_vsub_cancel_right]
  have hbp : (b -ᵥ AffineMap.lineMap a b t : V) = (1 - t) • (B - A) := by
    rw [AffineMap.right_vsub_lineMap, hA, hB, vsub_sub_vsub_cancel_right]
  have hpc : (AffineMap.lineMap a b t -ᵥ s.center : V) = A + t • (B - A) := by
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b t) a s.center,
      AffineMap.lineMap_vsub_left, hA, hB, vsub_sub_vsub_cancel_right, add_comm]
  rw [Sphere.power, dist_eq_norm_vsub V, ← real_inner_self_eq_norm_sq, hap, hbp, hpc]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  linear_combination (t - 1) * ha' - t * hb'

/-- A one-secant converse to signed power.  If `a ∈ s`, `x` lies on the line `pa`, and the
signed product `⟪a -ᵥ p, x -ᵥ p⟫` equals the power of `p`, then `x ∈ s`. -/
theorem mem_of_inner_vsub_vsub_eq_power_of_mem_line {s : Sphere P} {a p x : P}
    (ha : a ∈ s) (hx : x ∈ line[ℝ, p, a])
    (hpow : ⟪a -ᵥ p, x -ᵥ p⟫ = s.power p) :
    x ∈ s := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  set A : V := a -ᵥ s.center with hA
  set y : V := p -ᵥ s.center with hy
  have ha' : ⟪A, A⟫ = s.radius ^ 2 := by
    rw [hA, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp ha]
  have hap : (a -ᵥ p : V) = A - y := by rw [hA, hy, vsub_sub_vsub_cancel_right]
  have hxp : (AffineMap.lineMap p a t -ᵥ p : V) = t • (A - y) := by
    rw [AffineMap.lineMap_vsub_left, hap]
  have hxc : (AffineMap.lineMap p a t -ᵥ s.center : V) = y + t • (A - y) := by
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap p a t) p s.center, hxp, ← hy]; abel
  rw [hap, hxp, Sphere.power, dist_eq_norm_vsub V, ← real_inner_self_eq_norm_sq, ← hy] at hpow
  rw [mem_sphere, dist_eq_norm_vsub V,
    ← pow_left_inj₀ (norm_nonneg _) (radius_nonneg_of_mem ha) two_ne_zero,
    ← real_inner_self_eq_norm_sq, hxc]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right] at hpow ⊢
  linear_combination t * ha' + (t - 1) * hpow

end Sphere

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

open scoped EuclideanGeometry RealInnerProductSpace Real

/-! ## Second intersections along a common direction (`#42308`) -/

/-- The difference between the second intersections of two spheres along a common direction. -/
theorem Sphere.secondInter_vsub_secondInter (s₁ s₂ : Sphere P) (p : P) (v : V) :
    s₁.secondInter p v -ᵥ s₂.secondInter p v = (2 * ⟪v, s₁.center -ᵥ s₂.center⟫ / ⟪v, v⟫) • v := by
  rw [Sphere.secondInter, Sphere.secondInter, vadd_vsub_vadd_cancel_right, ← sub_smul,
    ← vsub_sub_vsub_cancel_left s₁.center s₂.center p, inner_sub_right]
  congr 1
  ring

/-- The difference between the second intersections of two spheres along a common unit direction. -/
theorem Sphere.secondInter_vsub_secondInter_of_norm_eq_one (s₁ s₂ : Sphere P) (p : P) {v : V}
    (hv : ‖v‖ = 1) :
    s₁.secondInter p v -ᵥ s₂.secondInter p v = (2 * ⟪v, s₁.center -ᵥ s₂.center⟫) • v := by
  have hvv : ⟪v, v⟫ = (1 : ℝ) := by simp [hv]
  rw [secondInter_vsub_secondInter, hvv, div_one]

/-- The distance between the second intersections of two spheres along a common direction. -/
theorem Sphere.dist_secondInter_secondInter (s₁ s₂ : Sphere P) (p : P) (v : V) :
    dist (s₁.secondInter p v) (s₂.secondInter p v) = 2 * |⟪v, s₁.center -ᵥ s₂.center⟫| / ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  rw [dist_eq_norm_vsub V, secondInter_vsub_secondInter, norm_smul, Real.norm_eq_abs,
    abs_div, abs_mul, abs_two, real_inner_self_eq_norm_sq,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2)]
  field_simp

/-- The distance between the second intersections of two spheres along a common unit direction. -/
theorem Sphere.dist_secondInter_secondInter_of_norm_eq_one (s₁ s₂ : Sphere P) (p : P) {v : V}
    (hv : ‖v‖ = 1) :
    dist (s₁.secondInter p v) (s₂.secondInter p v) = 2 * |⟪v, s₁.center -ᵥ s₂.center⟫| := by
  rw [dist_secondInter_secondInter, hv, div_one]

/-! ### Converse direction: equal products imply cospherical -/

/-- A dimension-free converse to power of a point in signed form.  If `p` lies on both lines
`p₁p₂` and `p₃p₄`, and the two signed power products are equal, then the four endpoints are
cospherical. -/
theorem cospherical_of_inner_vsub_eq_inner_vsub {p₁ p₂ p₃ p₄ p : P}
    (h₁₂ : p ∈ line[ℝ, p₁, p₂]) (h₃₄ : p ∈ line[ℝ, p₃, p₄])
    (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P))
    (hpow : ⟪p₁ -ᵥ p, p₂ -ᵥ p⟫ = ⟪p₃ -ᵥ p, p₄ -ᵥ p⟫) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hpp₃ : p ≠ p₃ := by
    rintro rfl; exact hn (by simpa using collinear_pair ℝ p₁ p)
  have hp₁p₃ : p₁ ≠ p₃ := by
    rintro rfl; exact hn (by simpa using collinear_pair ℝ p p₁)
  have hp₁p₂ : p₁ ≠ p₂ := by
    rintro rfl
    have hpeq : p = p₁ := by simpa using h₁₂
    exact hn (by rw [hpeq]; simpa using collinear_pair ℝ p₁ p₃)
  have hn₁₂₃ : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
    intro hcol
    apply hn
    have hp₂_mem : p₂ ∈ line[ℝ, p₁, p₃] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₁p₃
    have hp_mem : p ∈ line[ℝ, p₁, p₃] := by
      rwa [affineSpan_pair_eq_of_right_mem_of_ne hp₂_mem hp₁p₂.symm] at h₁₂
    simpa [Set.insert_comm] using collinear_insert_of_mem_affineSpan_pair hp_mem
  let t : Affine.Triangle ℝ P :=
    ⟨![p₁, p₂, p₃], affineIndependent_iff_not_collinear_set.mpr hn₁₂₃⟩
  have hp₁_mem : p₁ ∈ t.circumsphere := t.mem_circumsphere 0
  have hp₂_mem : p₂ ∈ t.circumsphere := t.mem_circumsphere 1
  have hp₃_mem : p₃ ∈ t.circumsphere := t.mem_circumsphere 2
  have hleft : ⟪p₁ -ᵥ p, p₂ -ᵥ p⟫ = t.circumsphere.power p :=
    Sphere.inner_vsub_vsub_eq_power hp₁_mem hp₂_mem h₁₂
  have hp₄_line : p₄ ∈ line[ℝ, p, p₃] :=
    (collinear_insert_of_mem_affineSpan_pair h₃₄).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hpp₃
  have hp₄_mem : p₄ ∈ t.circumsphere :=
    Sphere.mem_of_inner_vsub_vsub_eq_power_of_mem_line hp₃_mem hp₄_line
      (hpow.symm.trans hleft)
  rw [cospherical_iff_exists_sphere]
  refine ⟨t.circumsphere, ?_⟩
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp₁_mem, hp₂_mem, hp₃_mem, hp₄_mem⟩

-- The `∠ = π` chord converse from the same PR is already available upstream as
-- `EuclideanGeometry.cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi`.

/-- **Converse of the Intersecting Secants Theorem**.  If
`dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`, and `p₁, p₂` lie on a common ray from `p`
(`∠ p₁ p p₂ = 0`) and `p₃, p₄` on another, with `{p₁, p, p₃}` not collinear, then
`p₁, p₂, p₃, p₄` are cospherical.  As in Mathlib's forward secant theorem, `p₁ ≠ p₂` and
`p₃ ≠ p₄` are required: unlike `∠ = π`, the condition `∠ = 0` does not force the endpoints to
be distinct. -/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_zero {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (h₁₂ : p₁ ≠ p₂) (h₃₄ : p₃ ≠ p₄)
    (hp₁p₂ : ∠ p₁ p p₂ = 0) (hp₃p₄ : ∠ p₃ p p₄ = 0)
    (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  refine cospherical_of_inner_vsub_eq_inner_vsub
    ((collinear_of_angle_eq_zero hp₁p₂).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) h₁₂)
    ((collinear_of_angle_eq_zero hp₃p₄).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) h₃₄) hn ?_
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm,
    ← InnerProductGeometry.cos_angle_mul_norm_mul_norm,
    ← EuclideanGeometry.angle, ← EuclideanGeometry.angle, hp₁p₂, hp₃p₄,
    ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V, ← dist_eq_norm_vsub V,
    ← dist_eq_norm_vsub V, h]

namespace Sphere

section OrientedPlane

variable [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-! ## BMO 2018 P4 auxiliary Sphere lemmas-/

/-- BMO auxiliary lemma. Unoriented central-angle theorem with an explicit branch condition.

The angle at the center of a circle equals twice the angle at the circumference, unoriented
angle version, provided twice the angle at the circumference is at most `π`. -/
theorem angle_center_eq_two_mul_angle_of_two_mul_angle_le_pi {s : Sphere P} {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (h : 2 * ∠ p₁ p₂ p₃ ≤ π) : ∠ p₁ s.center p₃ = 2 * ∠ p₁ p₂ p₃ := by
  have key : ∀ {x : P}, x ∈ s → p₂ ≠ x → x ≠ s.center := by
    rintro x hx hne rfl
    rw [center_mem_iff] at hx
    exact hne (dist_eq_zero.mp (by rw [mem_sphere.mp hp₂, hx]))
  have hp₁c := key hp₁ hp₂p₁
  have hp₃c := key hp₃ hp₂p₃
  refine Real.injOn_cos ⟨angle_nonneg p₁ s.center p₃, angle_le_pi p₁ s.center p₃⟩
    ⟨mul_nonneg zero_le_two (angle_nonneg p₁ p₂ p₃), h⟩ ?_
  rw [← cos_oangle_eq_cos_angle hp₁c hp₃c,
    oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃, Real.cos_two_mul,
    ← cos_oangle_eq_cos_angle hp₂p₁.symm hp₂p₃.symm, two_zsmul, Real.Angle.cos_add]
  nlinarith [Real.Angle.cos_sq_add_sin_sq (∡ p₁ p₂ p₃)]

/-- The angle at the center of a circle is `2 * π` minus twice the angle at the circumference,
unoriented angle version, provided twice the angle at the circumference is at least `π`. -/
theorem angle_center_eq_two_pi_sub_two_mul_angle_of_pi_le_two_mul_angle {s : Sphere P}
    {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁)
    (hp₂p₃ : p₂ ≠ p₃) (h : π ≤ 2 * ∠ p₁ p₂ p₃) :
    ∠ p₁ s.center p₃ = 2 * π - 2 * ∠ p₁ p₂ p₃ := by
  have hp₁c : p₁ ≠ s.center := by
    rintro rfl; rw [center_mem_iff] at hp₁
    exact hp₂p₁ (dist_eq_zero.mp (by rw [mem_sphere.mp hp₂, hp₁]))
  have hp₃c : p₃ ≠ s.center := by
    rintro rfl; rw [center_mem_iff] at hp₃
    exact hp₂p₃ (dist_eq_zero.mp (by rw [mem_sphere.mp hp₂, hp₃]))
  refine Real.injOn_cos ⟨angle_nonneg p₁ s.center p₃, angle_le_pi p₁ s.center p₃⟩
    ⟨by linarith [angle_le_pi p₁ p₂ p₃], by linarith⟩ ?_
  rw [show (2 : ℝ) * π - 2 * ∠ p₁ p₂ p₃ = -(2 * ∠ p₁ p₂ p₃) + 2 * π by ring,
    Real.cos_add_two_pi, Real.cos_neg, ← cos_oangle_eq_cos_angle hp₁c hp₃c,
    oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃, Real.cos_two_mul,
    ← cos_oangle_eq_cos_angle hp₂p₁.symm hp₂p₃.symm, two_zsmul, Real.Angle.cos_add]
  nlinarith [Real.Angle.cos_sq_add_sin_sq (∡ p₁ p₂ p₃)]

/-- For a tangent line to a sphere, twice the oriented angle between the line and the radius at the
tangent point equals `π`. -/
theorem IsTangentAt.two_zsmul_oangle_eq_pi {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hq : q ∈ as) (hqp : q ≠ p) (hcp : s.center ≠ p) :
    (2 : ℤ) • ∡ q p s.center = π := by
  rw [Real.Angle.two_zsmul_eq_pi_iff, ← Real.Angle.abs_toReal_eq_pi_div_two_iff,
    ← angle_eq_abs_oangle_toReal hqp hcp]
  exact h.angle_eq_pi_div_two hq

/-- **Alternate segment theorem**: Oriented angle version of "the angle between a tangent and
a chord equals the inscribed angle subtending that chord", for oriented angles mod π,
represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_tangent_eq {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (htan : s.IsTangentAt p₁ line[ℝ, p₁, p₄]) (hp₄p₁ : p₄ ≠ p₁) (hp₃p₁ : p₃ ≠ p₁)
    (hp₃p₂ : p₃ ≠ p₂) (hp₂p₁ : p₂ ≠ p₁) :
    (2 : ℤ) • ∡ p₄ p₁ p₂ = (2 : ℤ) • ∡ p₁ p₃ p₂ := by
  have hcenter : s.center ≠ p₁ := (ne_center_of_mem_of_mem_of_ne hp₁ hp₃ hp₃p₁.symm).symm
  have htan_chord : (2 : ℤ) • ∡ p₄ p₁ p₂ = π + (2 : ℤ) • ∡ s.center p₁ p₂ := by
    have hright : (2 : ℤ) • ∡ p₄ p₁ s.center = π :=
      htan.two_zsmul_oangle_eq_pi (right_mem_affineSpan_pair ℝ p₁ p₄) hp₄p₁ hcenter
    rw [← oangle_add hp₄p₁ hcenter hp₂p₁, smul_add, hright]
  have hinscribed : (2 : ℤ) • ∡ p₁ p₃ p₂ = π + (2 : ℤ) • ∡ s.center p₁ p₂ := by
    have h := two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₃ hp₂ hp₃p₁ hp₃p₂ hp₂p₁.symm
    rw [oangle_rev, smul_neg] at h
    rw [← h]; abel
  exact htan_chord.trans hinscribed.symm

end OrientedPlane

end Sphere

end EuclideanGeometry

/-!
# Sides of an orthogonal hyperplane and the sign of the signed distance

`AffineSubspace.mk' A (ℝ ∙ n)ᗮ` is the affine hyperplane through `A` orthogonal to `n`, and
`signedDist n A` is a functional vanishing exactly on it.  This file relates the sign of that
functional to `AffineSubspace.WSameSide`, `SSameSide`, `WOppSide` and `SOppSide`.

## Implementation notes

No nondegeneracy hypothesis on `n` is needed: for `n = 0` we have `(ℝ ∙ n)ᗮ = ⊤` and
`signedDist n = 0`, so the weak statements become trivially true and the strict ones trivially
false, matching the conditions on the product.

The hyperplane is presented as `AffineSubspace.mk' A (ℝ ∙ n)ᗮ`; `AffineSubspace.mk'_eq` puts
any `s` with `A ∈ s` and `s.direction = (ℝ ∙ n)ᗮ` into that form.  Nothing below needs
completeness or `Submodule.HasOrthogonalProjection`, as the foot of the perpendicular is
written down explicitly.
-/

open NormedSpace
open scoped RealInnerProductSpace

section SignedDist

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The inner product with `n` is the signed distance in the direction `n`, scaled by `‖n‖`. -/
theorem inner_vsub_eq_norm_mul_signedDist (n : V) (A X : P) :
    ⟪n, X -ᵥ A⟫ = ‖n‖ * signedDist n A X := by
  rw [signedDist_apply_apply, ← real_inner_smul_left, norm_smul_normalize]

end SignedDist

namespace AffineSubspace

section SignedDistSide

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- A point lies on the affine hyperplane through `A` orthogonal to `n` exactly when its signed
distance from `A` in the direction `n` vanishes. -/
theorem mem_mk'_orthogonal_iff_signedDist_eq_zero (n : V) (A X : P) :
    X ∈ mk' A (ℝ ∙ n)ᗮ ↔ signedDist n A X = 0 := by
  rw [mem_mk', Submodule.mem_orthogonal_singleton_iff_inner_right,
    inner_vsub_eq_norm_mul_signedDist]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, mul_zero]⟩
  rcases mul_eq_zero.1 h with h | h
  · rw [norm_eq_zero] at h
    subst h
    simp
  · exact h

private theorem notMem_mk'_orthogonal_of_signedDist_ne_zero {n : V} {A X : P}
    (h : signedDist n A X ≠ 0) : X ∉ mk' A (ℝ ∙ n)ᗮ :=
  fun hX ↦ h ((mem_mk'_orthogonal_iff_signedDist_eq_zero n A X).1 hX)

private theorem exists_mem_mk'_orthogonal_vsub_eq (n : V) (A X : P) :
    ∃ p ∈ mk' A (ℝ ∙ n)ᗮ, X -ᵥ p = signedDist n A X • normalize n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨X, (mem_mk'_orthogonal_iff_signedDist_eq_zero 0 A X).2 (by simp), by simp⟩
  refine ⟨(-signedDist n A X) • normalize n +ᵥ X, ?_, ?_⟩
  · rw [mem_mk'_orthogonal_iff_signedDist_eq_zero, signedDist_vadd_right,
      real_inner_smul_right, real_inner_self_eq_norm_mul_norm, norm_normalize hn]
    ring
  · rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, neg_smul, neg_neg]

private theorem wSameSide_of_signedDist_mul_nonneg {n : V} {A X Y : P}
    (h : 0 ≤ signedDist n A X * signedDist n A Y) :
    (mk' A (ℝ ∙ n)ᗮ).WSameSide X Y := by
  obtain ⟨pX, hpX, hXpX⟩ := exists_mem_mk'_orthogonal_vsub_eq n A X
  obtain ⟨pY, hpY, hYpY⟩ := exists_mem_mk'_orthogonal_vsub_eq n A Y
  exact wSameSide_of_vsub_eq_smul hpX hpY hXpX hYpY h

private theorem wOppSide_of_signedDist_mul_nonpos {n : V} {A X Y : P}
    (h : signedDist n A X * signedDist n A Y ≤ 0) :
    (mk' A (ℝ ∙ n)ᗮ).WOppSide X Y := by
  obtain ⟨pX, hpX, hXpX⟩ := exists_mem_mk'_orthogonal_vsub_eq n A X
  obtain ⟨pY, hpY, hYpY⟩ := exists_mem_mk'_orthogonal_vsub_eq n A Y
  exact wOppSide_of_vsub_eq_smul hpX hpY hXpX hYpY h

private theorem sSameSide_of_signedDist_mul_pos {n : V} {A X Y : P}
    (h : 0 < signedDist n A X * signedDist n A Y) :
    (mk' A (ℝ ∙ n)ᗮ).SSameSide X Y :=
  ⟨wSameSide_of_signedDist_mul_nonneg h.le,
    notMem_mk'_orthogonal_of_signedDist_ne_zero (left_ne_zero_of_mul h.ne'),
    notMem_mk'_orthogonal_of_signedDist_ne_zero (right_ne_zero_of_mul h.ne')⟩

private theorem sOppSide_of_signedDist_mul_neg {n : V} {A X Y : P}
    (h : signedDist n A X * signedDist n A Y < 0) :
    (mk' A (ℝ ∙ n)ᗮ).SOppSide X Y :=
  ⟨wOppSide_of_signedDist_mul_nonpos h.le,
    notMem_mk'_orthogonal_of_signedDist_ne_zero (left_ne_zero_of_mul h.ne),
    notMem_mk'_orthogonal_of_signedDist_ne_zero (right_ne_zero_of_mul h.ne)⟩

/-- Two points lie weakly on the same side of the affine hyperplane through `A` orthogonal to
`n` exactly when their signed distances from it have nonnegative product. -/
theorem wSameSide_mk'_orthogonal_iff_signedDist_mul_nonneg {n : V} {A X Y : P} :
    (mk' A (ℝ ∙ n)ᗮ).WSameSide X Y ↔ 0 ≤ signedDist n A X * signedDist n A Y :=
  ⟨fun h ↦ not_lt.1 fun hlt ↦ h.not_sOppSide (sOppSide_of_signedDist_mul_neg hlt),
    wSameSide_of_signedDist_mul_nonneg⟩

/-- Two points lie weakly on opposite sides of the affine hyperplane through `A` orthogonal to
`n` exactly when their signed distances from it have nonpositive product. -/
theorem wOppSide_mk'_orthogonal_iff_signedDist_mul_nonpos {n : V} {A X Y : P} :
    (mk' A (ℝ ∙ n)ᗮ).WOppSide X Y ↔ signedDist n A X * signedDist n A Y ≤ 0 :=
  ⟨fun h ↦ not_lt.1 fun hlt ↦ h.not_sSameSide (sSameSide_of_signedDist_mul_pos hlt),
    wOppSide_of_signedDist_mul_nonpos⟩

/-- Two points lie strictly on the same side of the affine hyperplane through `A` orthogonal to
`n` exactly when their signed distances from it have positive product. -/
theorem sSameSide_mk'_orthogonal_iff_signedDist_mul_pos {n : V} {A X Y : P} :
    (mk' A (ℝ ∙ n)ᗮ).SSameSide X Y ↔ 0 < signedDist n A X * signedDist n A Y := by
  refine ⟨fun h ↦ ?_, sSameSide_of_signedDist_mul_pos⟩
  obtain ⟨hw, hX, hY⟩ := h
  rw [mem_mk'_orthogonal_iff_signedDist_eq_zero] at hX hY
  exact (wSameSide_mk'_orthogonal_iff_signedDist_mul_nonneg.1 hw).lt_of_ne'
    (mul_ne_zero hX hY)

/-- Two points lie strictly on opposite sides of the affine hyperplane through `A` orthogonal to
`n` exactly when their signed distances from it have negative product. -/
theorem sOppSide_mk'_orthogonal_iff_signedDist_mul_neg {n : V} {A X Y : P} :
    (mk' A (ℝ ∙ n)ᗮ).SOppSide X Y ↔ signedDist n A X * signedDist n A Y < 0 := by
  refine ⟨fun h ↦ ?_, sOppSide_of_signedDist_mul_neg⟩
  obtain ⟨hw, hX, hY⟩ := h
  rw [mem_mk'_orthogonal_iff_signedDist_eq_zero] at hX hY
  exact (wOppSide_mk'_orthogonal_iff_signedDist_mul_nonpos.1 hw).lt_of_ne
    (mul_ne_zero hX hY)

/-- In a two-dimensional space, the line through `A` and `B` is the hyperplane through `A`
orthogonal to any nonzero `n` orthogonal to `B -ᵥ A`. -/
theorem line_eq_mk'_orthogonal [Fact (Module.finrank ℝ V = 2)] {A B : P} {n : V}
    (hAB : A ≠ B) (hn : n ≠ 0) (horth : ⟪n, B -ᵥ A⟫ = 0) :
    line[ℝ, A, B] = AffineSubspace.mk' A (ℝ ∙ n)ᗮ := by
  have h2 : Module.finrank ℝ V = 2 := Fact.out
  have : FiniteDimensional ℝ V := .of_finrank_pos (by omega)
  have hBA : B -ᵥ A ≠ 0 := vsub_ne_zero.2 hAB.symm
  have hdir : (line[ℝ, A, B] : AffineSubspace ℝ P).direction = (ℝ ∙ n)ᗮ := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
    refine Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2
        (Submodule.mem_orthogonal_singleton_iff_inner_right.2 horth)) ?_
    have hsum := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ n : Submodule ℝ V))
    rw [finrank_span_singleton hn, h2] at hsum
    rw [finrank_span_singleton hBA]
    omega
  rw [← hdir, AffineSubspace.mk'_eq (left_mem_affineSpan_pair ℝ A B)]

end SignedDistSide

end AffineSubspace
