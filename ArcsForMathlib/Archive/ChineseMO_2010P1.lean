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
# Chinese MO 2010, Problem 1

## Reference

Chinese Mathematical Society, *China Mathematical Olympiad 2010, Problem 1*;
25th China Mathematical Olympiad (National High School Mathematics Winter Camp),
Chongqing, January 2010. Official problems and solutions in *Zouxiang IMO: Shuxue
Aolinpike Shiti Jijin (2010)*, East China Normal University Press, 2010 (in Chinese).
-/

open scoped Affine Congruent EuclideanGeometry Real RealInnerProductSpace
open Affine EuclideanGeometry Module Sphere

namespace ChinaMO2010P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

noncomputable section

/-! ## Shared geometric helpers -/

/-- If two points lie on a sphere and the first of them lies strictly between an external
point and the second, then the external point has positive power. -/
theorem Sphere.power_pos_of_sbtw {s : Sphere Pt} {X Y Z : Pt}
    (hY : Y ∈ s) (hZ : Z ∈ s) (h : Sbtw ℝ X Y Z) :
    0 < s.power X := by
  refine (Sphere.power_pos_iff_radius_lt_dist_center (Sphere.radius_nonneg_of_mem hY)).2 ?_
  by_contra hnot
  exact h.not_swap_left (wbtw_of_collinear_of_dist_center_le_radius
    (by simpa only [Set.insert_comm] using h.wbtw.collinear) hY (not_lt.1 hnot) hZ h.ne_right)

/-- A point strictly between two points of a sphere has negative power. -/
theorem Sphere.power_neg_of_sbtw {s : Sphere Pt} {X Y Z : Pt}
    (hY : Y ∈ s) (hZ : Z ∈ s) (h : Sbtw ℝ Y X Z) :
    s.power X < 0 :=
  (Sphere.power_neg_iff_dist_center_lt_radius (Sphere.radius_nonneg_of_mem hY)).2
    (by simpa [dist_comm] using Sphere.dist_center_lt_radius_of_sbtw hY hZ h)

/-- A point of positive power differs from every point on the sphere. -/
private theorem Sphere.ne_of_power_pos_of_mem {s : Sphere Pt} {X B : Pt}
    (hB : B ∈ s) (hX : 0 < s.power X) : X ≠ B := by
  rintro rfl
  exact hX.ne' ((Sphere.power_eq_zero_iff_mem_sphere (Sphere.radius_nonneg_of_mem hB)).2 hB)

/-- For two spheres through `A`, their signed-power difference is the affine-linear functional
whose normal vector joins the two centers. -/
theorem Sphere.power_sub_power_eq {s₁ s₂ : Sphere Pt} {A : Pt}
    (h₁ : A ∈ s₁) (h₂ : A ∈ s₂) (X : Pt) :
    s₁.power X - s₂.power X =
      2 * ⟪(X -ᵥ A : V), (s₂.center -ᵥ s₁.center : V)⟫ := by
  have key : ∀ s : Sphere Pt, A ∈ s →
      s.power X = ‖(X -ᵥ A : V)‖ ^ 2 + 2 * ⟪(X -ᵥ A : V), (A -ᵥ s.center : V)⟫ := by
    intro s hs
    rw [Sphere.power, ← mem_sphere.mp hs, dist_eq_norm_vsub V, dist_eq_norm_vsub V,
      ← vsub_add_vsub_cancel X A s.center, norm_add_sq_real]
    ring
  rw [key s₁ h₁, key s₂ h₂, ← vsub_sub_vsub_cancel_left s₂.center s₁.center A, inner_sub_right]
  ring

/-- For a point of `s₁`, its power with respect to `s₂` is (twice) the signed distance to the
radical axis, measured along the line of centers. -/
theorem Sphere.power_eq_neg_two_inner_of_mem {s₁ s₂ : Sphere Pt} {A X : Pt}
    (h₁A : A ∈ s₁) (h₂A : A ∈ s₂) (hX : X ∈ s₁) :
    s₂.power X = -2 * ⟪(X -ᵥ A : V), (s₂.center -ᵥ s₁.center : V)⟫ := by
  have h := Sphere.power_sub_power_eq h₁A h₂A X
  rw [(Sphere.power_eq_zero_iff_mem_sphere (Sphere.radius_nonneg_of_mem h₁A)).2 hX] at h
  linarith

/-- On a sphere through the common chord `AB`, strict same-side points have powers of the
same sign with respect to the other sphere. -/
theorem Sphere.power_pos_of_mem_of_sSameSide {s₁ s₂ : Sphere Pt} {A B X Y : Pt}
    (h₁A : A ∈ s₁) (h₂A : A ∈ s₂) (h₁B : B ∈ s₁) (h₂B : B ∈ s₂)
    (hX : X ∈ s₁) (hY : Y ∈ s₁)
    (hs : (line[ℝ, A, B] : AffineSubspace ℝ Pt).SSameSide X Y)
    (hpos : 0 < s₂.power X) :
    0 < s₂.power Y := by
  let n : V := s₂.center -ᵥ s₁.center
  have horth : ⟪n, B -ᵥ A⟫ = 0 :=
    inner_vsub_vsub_of_mem_sphere_of_mem_sphere h₁A h₁B h₂A h₂B
  have hline_zero : ∀ p ∈ line[ℝ, A, B], ⟪p -ᵥ A, n⟫ = 0 := by
    intro p hp
    obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
    rw [AffineMap.lineMap_vsub_left, real_inner_smul_left, real_inner_comm, horth, mul_zero]
  have hshift : ∀ Z p, p ∈ line[ℝ, A, B] → ⟪Z -ᵥ p, n⟫ = ⟪Z -ᵥ A, n⟫ := fun Z p hp => by
    rw [show (Z -ᵥ p : V) = (Z -ᵥ A) - (p -ᵥ A) from (vsub_sub_vsub_cancel_right Z p A).symm,
      inner_sub_left, hline_zero p hp, sub_zero]
  have hkey : ∀ P ∈ s₁, s₂.power P = -2 * ⟪P -ᵥ A, n⟫ := fun P hP =>
    Sphere.power_eq_neg_two_inner_of_mem h₁A h₂A hP
  have hinnerX : ⟪X -ᵥ A, n⟫ < 0 := by have := hkey X hX; linarith
  rcases hs.1 with ⟨p₁, hp₁, p₂, hp₂, hray⟩
  have hXp₁ : X ≠ p₁ := fun h => hs.left_notMem (h ▸ hp₁)
  have hYp₂ : Y ≠ p₂ := fun h => hs.right_notMem (h ▸ hp₂)
  obtain ⟨r, hr, hscale⟩ :=
    hray.exists_pos_left (vsub_ne_zero.mpr hXp₁) (vsub_ne_zero.mpr hYp₂)
  have hinnerY : ⟪Y -ᵥ A, n⟫ < 0 := by
    rw [← hshift Y p₂ hp₂, ← hscale, real_inner_smul_left, hshift X p₁ hp₁]
    exact mul_neg_of_pos_of_neg hr hinnerX
  have := hkey Y hY; linarith

/-- Pythagoras in the orthogonal basis formed by two nonzero vectors in a plane. -/
theorem inner_sq_mul_norm_sq_add_inner_sq_mul_norm_sq
    [Fact (finrank ℝ V = 2)] {a n u : V}
    (ha : a ≠ 0) (hn : n ≠ 0) (han : ⟪a, n⟫ = 0) :
    ⟪a, u⟫ ^ 2 * ‖n‖ ^ 2 + ⟪n, u⟫ ^ 2 * ‖a‖ ^ 2 =
      ‖u‖ ^ 2 * ‖a‖ ^ 2 * ‖n‖ ^ 2 := by
  let x : ℝ := ⟪a, u⟫ / ‖a‖ ^ 2
  let y : ℝ := ⟪n, u⟫ / ‖n‖ ^ 2
  let r : V := u - (x • a + y • n)
  have ha_sq : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  have hn_sq : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hna : ⟪n, a⟫ = 0 := by rwa [real_inner_comm]
  have har : ⟪a, r⟫ = 0 := by
    simp only [r, inner_sub_right, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, han, mul_zero, add_zero, x]
    field_simp
    ring
  have hnr : ⟪n, r⟫ = 0 := by
    simp only [r, inner_sub_right, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hna, mul_zero, zero_add, y]
    field_simp
    ring
  have hr0 : r = 0 := by
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp
      (Submodule.mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero ha hn har han)
    rw [← hz, inner_smul_right, real_inner_self_eq_norm_sq] at hnr
    rw [← hz, (mul_eq_zero.mp hnr).resolve_right hn_sq, zero_smul]
  have hu : u = x • a + y • n := by simpa [r] using sub_eq_zero.mp hr0
  rw [← real_inner_self_eq_norm_sq a, ← real_inner_self_eq_norm_sq n,
    ← real_inner_self_eq_norm_sq u, hu]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    han, hna]
  ring

/-- Opposite signs of a normal affine functional put two points strictly on opposite sides
of the line through `A` and `B`. -/
theorem AffineSubspace.sOppSide_line_of_inner_neg_of_pos
    [Fact (finrank ℝ V = 2)] {A B X Y : Pt} {n : V}
    (hAB : A ≠ B) (horth : ⟪n, B -ᵥ A⟫ = 0)
    (hX : ⟪X -ᵥ A, n⟫ < 0) (hY : 0 < ⟪Y -ᵥ A, n⟫) :
    (line[ℝ, A, B] : AffineSubspace ℝ Pt).SOppSide X Y := by
  have hn : n ≠ 0 := by rintro rfl; simp at hX
  have hnorm : (0 : ℝ) < ‖n‖ := norm_pos_iff.2 hn
  have key : ∀ Z : Pt, ⟪Z -ᵥ A, n⟫ = ‖n‖ * signedDist n A Z := fun Z ↦ by
    rw [real_inner_comm, inner_vsub_eq_norm_mul_signedDist]
  rw [key] at hX hY
  have hdX : signedDist n A X < 0 := by nlinarith
  have hdY : 0 < signedDist n A Y := by nlinarith
  rw [AffineSubspace.line_eq_mk'_orthogonal hAB hn horth,
    AffineSubspace.sOppSide_mk'_orthogonal_iff_signedDist_mul_neg]
  exact mul_neg_of_neg_of_pos hdX hdY

/-- A non-base point of a sphere on a secant line is the second intersection in that
line's direction. -/
private theorem Sphere.secondInter_eq_of_mem_line {s : Sphere Pt} {B X Y : Pt}
    (hB : B ∈ (s : Set Pt)) (hX : X ∈ (s : Set Pt)) (hX_ne : X ≠ B)
    (hX_line : X ∈ line[ℝ, B, Y]) : X = s.secondInter B (Y -ᵥ B) :=
  ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hB hX_line).mpr hX).resolve_left hX_ne

/-- A non-base point on a secant line is the second intersection in the normalized secant
direction. -/
private theorem Sphere.secondInter_eq_of_mem_line_normalize {s : Sphere Pt} {B X Y : Pt}
    (hB : B ∈ (s : Set Pt)) (hX : X ∈ (s : Set Pt)) (hX_ne : X ≠ B)
    (hX_line : X ∈ line[ℝ, B, Y]) (hY_ne : Y ≠ B) :
    X = s.secondInter B (NormedSpace.normalize (Y -ᵥ B)) := by
  rw [NormedSpace.normalize, Sphere.secondInter_smul _ _ _
    (inv_ne_zero (norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hY_ne)))]
  exact Sphere.secondInter_eq_of_mem_line hB hX hX_ne hX_line

private theorem Sphere.Arc.ne_of_mem_interior_of_mem_opposite_interior
    [Fact (finrank ℝ V = 2)] {s : Sphere Pt} (a : Sphere.Arc s)
    (h : ¬a.IsDegenerate) {X Y : Pt} (hX : X ∈ a.interior)
    (hY : Y ∈ a.opposite.interior) : X ≠ Y := by
  intro hXY
  exact Set.disjoint_left.mp
    (Sphere.Arc.interior_disjoint_opposite a
      ((Sphere.Arc.left_ne_right_iff_not_isDegenerate a).mpr h)) hX (hXY ▸ hY)

/-- A strict-between point makes the two adjacent angles on its line supplementary. -/
theorem _root_.Sbtw.angle_add_angle_eq_pi {A C B D : Pt} (h : Sbtw ℝ C B D) :
    ∠ C B A + ∠ A B D = π := by
  simpa [angle_comm A B C] using
    EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi (V := V) (P := Pt)
      (p₁ := A) (p₂ := C) (p₃ := B) (p₄ := D) h.angle₁₂₃_eq_pi

/-! ### Reusable oriented-angle bisector lemmas -/

section OrientedAngleBisectors

variable [Fact (finrank ℝ V = 2)]

local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

/-- In a nondegenerate angle, an unoriented angle-bisector equality is the internal oriented
bisector, not one of the weak-between degeneracies. -/
theorem oangle_bisector_of_angle_eq {A B C X : Pt}
    (hncol : ¬Collinear ℝ ({A, B, C} : Set Pt))
    (h : ∠ A B X = ∠ X B C) :
    ∡ A B X = ∡ X B C := by
  have hAB : A ≠ B := by rintro rfl; exact hncol (by simp [collinear_pair])
  have hCB : C ≠ B := by rintro rfl; exact hncol (by simp [collinear_pair])
  refine ((angle_eq_iff_oangle_eq_or_wbtw hAB hCB).mp h).resolve_right ?_
  rintro (hW | hW) <;>
    exact hncol (hW.collinear.subset (by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      tauto))

theorem collinear_of_oangle_bisectors {A B C X Y : Pt}
    (hAB : A ≠ B) (hCB : C ≠ B) (hXB : X ≠ B) (hYB : Y ≠ B)
    (hX : ∡ A B X = ∡ X B C) (hY : ∡ A B Y = ∡ Y B C) :
    Collinear ℝ ({X, B, Y} : Set Pt) := by
  rw [← oangle_eq_zero_or_eq_pi_iff_collinear, ← Real.Angle.two_zsmul_eq_zero_iff, two_zsmul]
  have h1 : ∡ X B C + ∡ X B Y = ∡ Y B C := by rw [← hX, ← hY]; exact oangle_add hAB hXB hYB
  have h2 : ∡ X B Y + ∡ Y B C = ∡ X B C := oangle_add hXB hYB hCB
  calc ∡ X B Y + ∡ X B Y
      = (∡ X B C + ∡ X B Y) + (∡ X B Y + ∡ Y B C) - ∡ X B C - ∡ Y B C := by abel
    _ = ∡ Y B C + ∡ X B C - ∡ X B C - ∡ Y B C := by rw [h1, h2]
    _ = 0 := by abel

end OrientedAngleBisectors

/-! ## Common configuration -/

/-- Data shared by the branch-independent proof and the through-arc branch. -/
structure CfgCore (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
    [NormedAddTorsor V Pt] where
  (A B C D E F P Q : Pt)
  (Γ₁ Γ₂ : Sphere Pt)
  A_mem_Γ₁ : A ∈ (Γ₁ : Set Pt)
  A_mem_Γ₂ : A ∈ (Γ₂ : Set Pt)
  B_mem_Γ₁ : B ∈ (Γ₁ : Set Pt)
  B_mem_Γ₂ : B ∈ (Γ₂ : Set Pt)
  A_ne_B : A ≠ B
  C_mem_Γ₁ : C ∈ (Γ₁ : Set Pt)
  D_mem_Γ₂ : D ∈ (Γ₂ : Set Pt)
  sbtw_C_B_D : Sbtw ℝ C B D
  E_mem_Γ₁ : E ∈ (Γ₁ : Set Pt)
  F_eq : F = Γ₂.secondInter B (E -ᵥ B)
  E_not_mem_line_CD : E ∉ line[ℝ, C, D]
  P_eq : P = Γ₁.secondInter C (F -ᵥ C)
  sbtw_C_P_F : Sbtw ℝ C P F
  Q_eq : Q = Γ₂.secondInter F (C -ᵥ F)
  sbtw_C_Q_F : Sbtw ℝ C Q F
  P_mem_Γ₁ : P ∈ (Γ₁ : Set Pt)
  PB_not_diam : ¬Γ₁.IsDiameter P B
  Q_mem_Γ₂ : Q ∈ (Γ₂ : Set Pt)
  QB_not_diam : ¬Γ₂.IsDiameter Q B
  CD_eq_EF : dist C D = dist E F

namespace CfgCore

variable (cfg : CfgCore V Pt)

theorem C_ne_B : cfg.C ≠ cfg.B := cfg.sbtw_C_B_D.ne_left.symm

theorem B_ne_D : cfg.B ≠ cfg.D := cfg.sbtw_C_B_D.ne_right

theorem C_ne_D : cfg.C ≠ cfg.D := cfg.sbtw_C_B_D.left_ne_right

theorem C_ne_F : cfg.C ≠ cfg.F := cfg.sbtw_C_P_F.left_ne_right

theorem P_ne_C : cfg.P ≠ cfg.C := cfg.sbtw_C_P_F.ne_left

theorem Q_ne_F : cfg.Q ≠ cfg.F := cfg.sbtw_C_Q_F.ne_right

theorem F_mem_Γ₂ : cfg.F ∈ (cfg.Γ₂ : Set Pt) := by
  rw [cfg.F_eq]
  exact (Sphere.secondInter_mem _).2 cfg.B_mem_Γ₂

theorem power_Γ₂_C_pos : 0 < cfg.Γ₂.power cfg.C :=
  Sphere.power_pos_of_sbtw cfg.B_mem_Γ₂ cfg.D_mem_Γ₂ cfg.sbtw_C_B_D

theorem power_Γ₁_F_pos : 0 < cfg.Γ₁.power cfg.F :=
  Sphere.power_pos_of_sbtw cfg.P_mem_Γ₁ cfg.C_mem_Γ₁ cfg.sbtw_C_P_F.symm

theorem F_ne_B : cfg.F ≠ cfg.B :=
  Sphere.ne_of_power_pos_of_mem cfg.B_mem_Γ₁ cfg.power_Γ₁_F_pos

/-- The second secant cannot start with `E = B`: that would collapse both `F` and `P`
to `B`, contradicting the strict order `C-P-F`. -/
theorem E_ne_B : cfg.E ≠ cfg.B := fun hEB =>
  cfg.F_ne_B (by rw [cfg.F_eq, hEB, vsub_self, Sphere.secondInter_zero])

theorem F_mem_line_BE : cfg.F ∈ line[ℝ, cfg.B, cfg.E] := by
  rw [cfg.F_eq]
  exact Sphere.secondInter_vsub_mem_affineSpan _ _ _

/-- `F` lies on the secant `BE`, so that secant *is* the line `BF`, which therefore carries `E`. -/
theorem E_mem_line_BF : cfg.E ∈ line[ℝ, cfg.B, cfg.F] := by
  rw [affineSpan_pair_eq_of_right_mem_of_ne cfg.F_mem_line_BE cfg.F_ne_B]
  exact right_mem_affineSpan_pair ℝ _ _

/-- The triangle `BCF` is nondegenerate: otherwise the line `BF`, which carries `E`,
would be the line `CD`. -/
theorem not_collinear_BCF : ¬Collinear ℝ ({cfg.B, cfg.C, cfg.F} : Set Pt) := by
  intro hcol
  apply cfg.E_not_mem_line_CD
  have hF_BC : cfg.F ∈ line[ℝ, cfg.B, cfg.C] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.C_ne_B.symm
  have hBC_eq_CD : line[ℝ, cfg.B, cfg.C] = line[ℝ, cfg.C, cfg.D] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne cfg.sbtw_C_B_D.wbtw.mem_affineSpan
      (left_mem_affineSpan_pair ℝ _ _) cfg.C_ne_B.symm
  have hE_BF := cfg.E_mem_line_BF
  rwa [affineSpan_pair_eq_of_right_mem_of_ne hF_BC cfg.F_ne_B, hBC_eq_CD] at hE_BF

/-- `D = F` would make `C`, `B`, `F` collinear. -/
theorem D_ne_F : cfg.D ≠ cfg.F := fun hDF =>
  cfg.not_collinear_BCF (hDF ▸ Set.insert_comm .. ▸ cfg.sbtw_C_B_D.wbtw.collinear)

theorem P_mem_line_CF : cfg.P ∈ line[ℝ, cfg.C, cfg.F] := by
  rw [cfg.P_eq]
  exact Sphere.secondInter_vsub_mem_affineSpan _ _ _

theorem Q_mem_line_FC : cfg.Q ∈ line[ℝ, cfg.F, cfg.C] := by
  rw [cfg.Q_eq]
  exact Sphere.secondInter_vsub_mem_affineSpan _ _ _

theorem P_ne_B : cfg.P ≠ cfg.B := by
  intro hPB
  exact cfg.not_collinear_BCF <| (collinear_insert_iff_of_mem_affineSpan
    (by simpa [hPB] using cfg.P_mem_line_CF)).2 (collinear_pair ℝ _ _)

theorem Q_ne_B : cfg.Q ≠ cfg.B := by
  intro hQB
  exact cfg.not_collinear_BCF <| (collinear_insert_iff_of_mem_affineSpan (by
    rw [AffineSubspace.affineSpan_pair_comm]
    simpa [hQB] using cfg.Q_mem_line_FC)).2 (collinear_pair ℝ _ _)

/-- The minor arc `PB` on `Γ₁`. -/
def arcPB : Sphere.Arc cfg.Γ₁ :=
  Sphere.Arc.minor cfg.P_mem_Γ₁ cfg.B_mem_Γ₁ cfg.PB_not_diam

/-- The minor arc `QB` on `Γ₂`. -/
def arcQB : Sphere.Arc cfg.Γ₂ :=
  Sphere.Arc.minor cfg.Q_mem_Γ₂ cfg.B_mem_Γ₂ cfg.QB_not_diam

theorem arcPB_not_isDegenerate : ¬cfg.arcPB.IsDegenerate := by
  rw [← Sphere.Arc.left_ne_right_iff_not_isDegenerate]
  simpa [arcPB] using cfg.P_ne_B

theorem arcQB_not_isDegenerate : ¬cfg.arcQB.IsDegenerate := by
  rw [← Sphere.Arc.left_ne_right_iff_not_isDegenerate]
  simpa [arcQB] using cfg.Q_ne_B

section Plane

variable [Fact (finrank ℝ V = 2)]

local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

/-- The signed radical-axis functional puts `C` and `F` on opposite sides of the common
chord `AB`, independently of the order of `E`, `B`, and `F`. -/
theorem sOppSide_AB_C_F :
    (line[ℝ, cfg.A, cfg.B] : AffineSubspace ℝ Pt).SOppSide cfg.C cfg.F := by
  have hC : ⟪(cfg.C -ᵥ cfg.A : V), (cfg.Γ₂.center -ᵥ cfg.Γ₁.center : V)⟫ < 0 := by
    have h := Sphere.power_eq_neg_two_inner_of_mem cfg.A_mem_Γ₁ cfg.A_mem_Γ₂ cfg.C_mem_Γ₁
    linarith [cfg.power_Γ₂_C_pos]
  have hF : 0 < ⟪(cfg.F -ᵥ cfg.A : V), (cfg.Γ₂.center -ᵥ cfg.Γ₁.center : V)⟫ := by
    have h := Sphere.power_eq_neg_two_inner_of_mem cfg.A_mem_Γ₂ cfg.A_mem_Γ₁ cfg.F_mem_Γ₂
    rw [← neg_vsub_eq_vsub_rev cfg.Γ₂.center, inner_neg_right] at h
    linarith [cfg.power_Γ₁_F_pos]
  exact AffineSubspace.sOppSide_line_of_inner_neg_of_pos cfg.A_ne_B
    (inner_vsub_vsub_of_mem_sphere_of_mem_sphere cfg.A_mem_Γ₁ cfg.B_mem_Γ₁
      cfg.A_mem_Γ₂ cfg.B_mem_Γ₂) hC hF

theorem sSameSide_AB_D_F :
    (line[ℝ, cfg.A, cfg.B] : AffineSubspace ℝ Pt).SSameSide cfg.D cfg.F := by
  have hB : cfg.B ∈ line[ℝ, cfg.A, cfg.B] := right_mem_affineSpan_pair ℝ _ _
  have hCD : (line[ℝ, cfg.A, cfg.B] : AffineSubspace ℝ Pt).SOppSide cfg.C cfg.D :=
    cfg.sbtw_C_B_D.sOppSide_of_notMem_of_mem cfg.sOppSide_AB_C_F.left_notMem hB
  exact hCD.symm.trans cfg.sOppSide_AB_C_F

/-- Equal cross-circle chords determine the two secant directions up to reflection in `AB`.
The same-side fact for `D` and `F` rules out the supplementary branch. -/
theorem angle_CBA_eq_angle_FBA : ∠ cfg.C cfg.B cfg.A = ∠ cfg.F cfg.B cfg.A := by
  let uC : V := NormedSpace.normalize (cfg.C -ᵥ cfg.B)
  let uF : V := NormedSpace.normalize (cfg.F -ᵥ cfg.B)
  let a : V := NormedSpace.normalize (cfg.A -ᵥ cfg.B)
  let n : V := cfg.Γ₁.center -ᵥ cfg.Γ₂.center
  have hCB0 : cfg.C -ᵥ cfg.B ≠ 0 := vsub_ne_zero.mpr cfg.C_ne_B
  have hFB0 : cfg.F -ᵥ cfg.B ≠ 0 := vsub_ne_zero.mpr cfg.F_ne_B
  have hAB0 : cfg.A -ᵥ cfg.B ≠ 0 := vsub_ne_zero.mpr cfg.A_ne_B
  have huC : ‖uC‖ = 1 := by simpa [uC] using NormedSpace.norm_normalize hCB0
  have huF : ‖uF‖ = 1 := by simpa [uF] using NormedSpace.norm_normalize hFB0
  have huA : ‖a‖ = 1 := by simpa [a] using NormedSpace.norm_normalize hAB0
  have hD_BC : cfg.D ∈ line[ℝ, cfg.B, cfg.C] := by
    simpa [AffineSubspace.affineSpan_pair_comm] using cfg.sbtw_C_B_D.right_mem_affineSpan
  have hC_second : cfg.C = cfg.Γ₁.secondInter cfg.B uC := by
    simpa [uC] using Sphere.secondInter_eq_of_mem_line_normalize cfg.B_mem_Γ₁ cfg.C_mem_Γ₁
      cfg.C_ne_B (right_mem_affineSpan_pair ℝ _ _) cfg.C_ne_B
  have hD_second : cfg.D = cfg.Γ₂.secondInter cfg.B uC := by
    simpa [uC] using Sphere.secondInter_eq_of_mem_line_normalize cfg.B_mem_Γ₂ cfg.D_mem_Γ₂
      cfg.B_ne_D.symm hD_BC cfg.C_ne_B
  have hE_second : cfg.E = cfg.Γ₁.secondInter cfg.B uF := by
    simpa [uF] using Sphere.secondInter_eq_of_mem_line_normalize cfg.B_mem_Γ₁ cfg.E_mem_Γ₁
      cfg.E_ne_B cfg.E_mem_line_BF cfg.F_ne_B
  have hF_second : cfg.F = cfg.Γ₂.secondInter cfg.B uF := by
    simpa [uF] using Sphere.secondInter_eq_of_mem_line_normalize cfg.B_mem_Γ₂ cfg.F_mem_Γ₂
      cfg.F_ne_B (right_mem_affineSpan_pair ℝ _ _) cfg.F_ne_B
  have hdistCD : dist cfg.C cfg.D = 2 * |⟪n, uC⟫| := by
    rw [hC_second, hD_second]
    simpa [n, real_inner_comm] using
      Sphere.dist_secondInter_secondInter_of_norm_eq_one cfg.Γ₁ cfg.Γ₂ cfg.B huC
  have hdistEF : dist cfg.E cfg.F = 2 * |⟪n, uF⟫| := by
    rw [hE_second, hF_second]
    simpa [n, real_inner_comm] using
      Sphere.dist_secondInter_secondInter_of_norm_eq_one cfg.Γ₁ cfg.Γ₂ cfg.B huF
  have habs : |⟪n, uC⟫| = |⟪n, uF⟫| := by
    linarith [cfg.CD_eq_EF, hdistCD, hdistEF]
  have hnproj : ⟪n, uC⟫ ^ 2 = ⟪n, uF⟫ ^ 2 := by rw [← sq_abs, habs, sq_abs]
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [huA]; norm_num)
  have hn0 : n ≠ 0 := by
    intro hn0
    have hzero : dist cfg.C cfg.D = 0 := by simp [hdistCD, hn0]
    exact cfg.C_ne_D (dist_eq_zero.mp hzero)
  have horth_raw : ⟪cfg.A -ᵥ cfg.B, n⟫ = 0 := by
    have h := inner_vsub_vsub_of_mem_sphere_of_mem_sphere cfg.A_mem_Γ₁ cfg.B_mem_Γ₁
      cfg.A_mem_Γ₂ cfg.B_mem_Γ₂
    change ⟪cfg.Γ₂.center -ᵥ cfg.Γ₁.center, cfg.B -ᵥ cfg.A⟫ = 0 at h
    calc
      ⟪cfg.A -ᵥ cfg.B, n⟫ =
          ⟪-(cfg.B -ᵥ cfg.A), -(cfg.Γ₂.center -ᵥ cfg.Γ₁.center)⟫ := by
        rw [neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
      _ = ⟪cfg.B -ᵥ cfg.A, cfg.Γ₂.center -ᵥ cfg.Γ₁.center⟫ := by
        rw [inner_neg_left, inner_neg_right, neg_neg]
      _ = 0 := by rwa [real_inner_comm]
  have horth : ⟪a, n⟫ = 0 := by
    dsimp [a]
    rw [NormedSpace.normalize, real_inner_smul_left, horth_raw, mul_zero]
  have haproj : ⟪a, uC⟫ ^ 2 = ⟪a, uF⟫ ^ 2 := by
    have hgramC := inner_sq_mul_norm_sq_add_inner_sq_mul_norm_sq
      (u := uC) ha0 hn0 horth
    have hgramF := inner_sq_mul_norm_sq_add_inner_sq_mul_norm_sq
      (u := uF) ha0 hn0 horth
    rw [huC, huA, one_pow] at hgramC
    rw [huF, huA, one_pow] at hgramF
    nlinarith [hgramC, hgramF, hnproj, sq_pos_of_pos (norm_pos_iff.mpr hn0)]
  have hinnerC : ⟪a, uC⟫ = Real.cos (∠ cfg.C cfg.B cfg.A) := by
    calc
      ⟪a, uC⟫ = ⟪uC, a⟫ := real_inner_comm _ _
      _ = Real.cos (∠ cfg.C cfg.B cfg.A) := by
        simpa [a, uC, EuclideanGeometry.angle] using
          InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one huC huA
  have hinnerF : ⟪a, uF⟫ = Real.cos (∠ cfg.F cfg.B cfg.A) := by
    calc
      ⟪a, uF⟫ = ⟪uF, a⟫ := real_inner_comm _ _
      _ = Real.cos (∠ cfg.F cfg.B cfg.A) := by
        simpa [a, uF, EuclideanGeometry.angle] using
          InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one huF huA
  have hcosSq : Real.cos (∠ cfg.C cfg.B cfg.A) ^ 2 =
      Real.cos (∠ cfg.F cfg.B cfg.A) ^ 2 := by
    rw [hinnerC, hinnerF] at haproj
    exact haproj
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hcosSq with hcos | hcos
  · exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
      ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ hcos
  · have hsum : ∠ cfg.C cfg.B cfg.A + ∠ cfg.F cfg.B cfg.A = π := by
      have hcos' : Real.cos (∠ cfg.C cfg.B cfg.A) =
          Real.cos (π - ∠ cfg.F cfg.B cfg.A) := by
        rw [Real.cos_pi_sub]
        exact hcos
      have heq : ∠ cfg.C cfg.B cfg.A = π - ∠ cfg.F cfg.B cfg.A :=
        Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
          ⟨sub_nonneg.mpr (angle_le_pi _ _ _), sub_le_self π (angle_nonneg _ _ _)⟩ hcos'
      linarith
    have hCAD := cfg.sbtw_C_B_D.angle_add_angle_eq_pi (A := cfg.A)
    have hangle : ∠ cfg.D cfg.B cfg.A = ∠ cfg.A cfg.B cfg.F := by
      rw [angle_comm cfg.D cfg.B cfg.A, angle_comm cfg.A cfg.B cfg.F]
      linarith
    rcases (angle_eq_iff_oangle_eq_or_wbtw cfg.B_ne_D.symm cfg.F_ne_B).mp hangle with
      ho | hbetween
    · have hsign_same := cfg.sSameSide_AB_D_F.oangle_sign_eq
        (left_mem_affineSpan_pair ℝ cfg.A cfg.B) (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
      have hsign_swap := EuclideanGeometry.oangle_swap₂₃_sign cfg.A cfg.B cfg.F
      exfalso
      have hzero : (∡ cfg.A cfg.B cfg.F).sign = 0 := by
        have hs1 : (∡ cfg.D cfg.B cfg.A).sign = (∡ cfg.A cfg.B cfg.F).sign :=
          congrArg Real.Angle.sign ho
        have hs2 : (∡ cfg.D cfg.B cfg.A).sign = -(∡ cfg.A cfg.B cfg.F).sign := by
          calc
            (∡ cfg.D cfg.B cfg.A).sign = (∡ cfg.A cfg.D cfg.B).sign :=
              EuclideanGeometry.oangle_rotate_sign cfg.A cfg.D cfg.B
            _ = (∡ cfg.A cfg.F cfg.B).sign := hsign_same.symm
            _ = -(∡ cfg.A cfg.B cfg.F).sign := hsign_swap.symm
        exact SignType.self_eq_neg_iff.mp (hs1.symm.trans hs2)
      have hcol : Collinear ℝ ({cfg.A, cfg.B, cfg.F} : Set Pt) := by
        rwa [EuclideanGeometry.oangle_sign_eq_zero_iff_collinear] at hzero
      exact cfg.sSameSide_AB_D_F.right_notMem
        (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)
    · exfalso
      have hcol : Collinear ℝ ({cfg.B, cfg.D, cfg.F} : Set Pt) := by
        rcases hbetween with hBDF | hBFD
        · exact hBDF.collinear
        · simpa only [Set.pair_comm] using hBFD.collinear
      have hF_BD : cfg.F ∈ line[ℝ, cfg.B, cfg.D] :=
        hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.B_ne_D
      have hF_eq : cfg.F = cfg.Γ₂.secondInter cfg.B (cfg.D -ᵥ cfg.B) :=
        Sphere.secondInter_eq_of_mem_line cfg.B_mem_Γ₂ cfg.F_mem_Γ₂ cfg.F_ne_B hF_BD
      have hD_eq : cfg.D = cfg.Γ₂.secondInter cfg.B (cfg.D -ᵥ cfg.B) :=
        Sphere.secondInter_eq_of_mem_line cfg.B_mem_Γ₂ cfg.D_mem_Γ₂ cfg.B_ne_D.symm
          (right_mem_affineSpan_pair ℝ _ _)
      exact cfg.D_ne_F (hD_eq.trans hF_eq.symm)

end Plane

end CfgCore

/-! ## The through-arc branch -/

/-- The branch selected by the two through-arc seeds.

This structure contains only the data needed to derive the two opposite-arc position seeds used
by `Cfg`; the arc midpoints `M` and `N` belong only to the branch-independent configuration. -/
structure CfgArcACB (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
    [NormedAddTorsor V Pt] extends CfgCore V Pt where
  -- Type-level tax: derivable from the core data, but needed to state the through arc.
  C_ne_A : C ≠ A
  E_mem_arcACB_Γ₁ :
    E ∈ (Sphere.Arc.through A_mem_Γ₁ C_mem_Γ₁ B_mem_Γ₁
      C_ne_A sbtw_C_B_D.ne_left.symm).interior
  F_mem_arcABD_Γ₂ :
    F ∈ (Sphere.Arc.through A_mem_Γ₂ B_mem_Γ₂ D_mem_Γ₂
      A_ne_B.symm sbtw_C_B_D.ne_right).interior

namespace CfgArcACB

variable [Fact (finrank ℝ V = 2)] (cfg : CfgArcACB V Pt)

local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

/-! ### Branch setup: incidence, secant order, and arc positions -/

omit [Fact (finrank ℝ V = 2)] in
/-- `C` cannot lie on the line `AB`: it would then be the second intersection of `Γ₁`
with that line, hence equal to `B`. -/
theorem C_not_mem_line_AB : cfg.C ∉ line[ℝ, cfg.A, cfg.B] := fun hC_AB =>
  cfg.C_ne_B <|
    (Sphere.secondInter_eq_of_mem_line cfg.A_mem_Γ₁ cfg.C_mem_Γ₁ cfg.C_ne_A hC_AB).trans
      (Sphere.secondInter_eq_of_mem_line cfg.A_mem_Γ₁ cfg.B_mem_Γ₁ cfg.A_ne_B.symm
        (right_mem_affineSpan_pair ℝ _ _)).symm

omit [Fact (finrank ℝ V = 2)] in
theorem D_ne_A : cfg.D ≠ cfg.A := fun hDA =>
  cfg.C_not_mem_line_AB (by simpa [hDA] using cfg.sbtw_C_B_D.left_mem_affineSpan)

/-- The arc on `Γ₂` from `A` to `B` passing through `D`. -/
def arcADB_Γ₂ : Sphere.Arc cfg.Γ₂ :=
  Sphere.Arc.through cfg.A_mem_Γ₂ cfg.D_mem_Γ₂ cfg.B_mem_Γ₂
    cfg.D_ne_A cfg.sbtw_C_B_D.ne_right.symm

/-- The arc on `Γ₂` from `A` to `D` passing through `B`. -/
def arcABD_Γ₂ : Sphere.Arc cfg.Γ₂ :=
  Sphere.Arc.through cfg.A_mem_Γ₂ cfg.B_mem_Γ₂ cfg.D_mem_Γ₂
    cfg.A_ne_B.symm cfg.sbtw_C_B_D.ne_right

/-- The arc on `Γ₂` from `A` to `F` passing through `D`. -/
def arcADF_Γ₂ : Sphere.Arc cfg.Γ₂ :=
  Sphere.Arc.through cfg.A_mem_Γ₂ cfg.D_mem_Γ₂ cfg.F_mem_Γ₂
    cfg.D_ne_A cfg.D_ne_F

/-- The arc on `Γ₁` from `A` to `B` passing through `C`. -/
def arcACB_Γ₁ : Sphere.Arc cfg.Γ₁ :=
  Sphere.Arc.through cfg.A_mem_Γ₁ cfg.C_mem_Γ₁ cfg.B_mem_Γ₁
    cfg.C_ne_A cfg.sbtw_C_B_D.ne_left.symm

theorem D_mem_arcADB_Γ₂_interior : cfg.D ∈ cfg.arcADB_Γ₂.interior := by
  simpa [arcADB_Γ₂] using
    Sphere.Arc.mem_interior_through cfg.A_mem_Γ₂ cfg.D_mem_Γ₂ cfg.B_mem_Γ₂
      cfg.D_ne_A cfg.sbtw_C_B_D.ne_right.symm

theorem B_mem_arcABD_Γ₂_interior : cfg.B ∈ cfg.arcABD_Γ₂.interior := by
  simpa [arcABD_Γ₂] using
    Sphere.Arc.mem_interior_through cfg.A_mem_Γ₂ cfg.B_mem_Γ₂ cfg.D_mem_Γ₂
      cfg.A_ne_B.symm cfg.sbtw_C_B_D.ne_right

theorem D_mem_arcADF_Γ₂_interior : cfg.D ∈ cfg.arcADF_Γ₂.interior := by
  simpa [arcADF_Γ₂] using
    Sphere.Arc.mem_interior_through cfg.A_mem_Γ₂ cfg.D_mem_Γ₂ cfg.F_mem_Γ₂
      cfg.D_ne_A cfg.D_ne_F

theorem C_mem_arcACB_Γ₁_interior : cfg.C ∈ cfg.arcACB_Γ₁.interior := by
  simpa [arcACB_Γ₁] using
    Sphere.Arc.mem_interior_through cfg.A_mem_Γ₁ cfg.C_mem_Γ₁ cfg.B_mem_Γ₁
      cfg.C_ne_A cfg.sbtw_C_B_D.ne_left.symm

omit [Fact (finrank ℝ V = 2)] in
theorem E_ne_A : cfg.E ≠ cfg.A :=
  Sphere.Arc.ne_left_of_mem_interior cfg.E_mem_arcACB_Γ₁

theorem sSameSide_AB_C_E :
    (line[ℝ, cfg.A, cfg.B] : AffineSubspace ℝ Pt).SSameSide cfg.C cfg.E := by
  have h := Sphere.Arc.sSameSide_of_mem_interior_through cfg.A_mem_Γ₁ cfg.C_mem_Γ₁
    cfg.B_mem_Γ₁ cfg.C_ne_A cfg.sbtw_C_B_D.ne_left.symm
    cfg.C_mem_arcACB_Γ₁_interior cfg.E_mem_arcACB_Γ₁
  rwa [lineOrOrthRadius_of_ne cfg.A_ne_B] at h

theorem power_Γ₂_E_pos : 0 < cfg.Γ₂.power cfg.E :=
  Sphere.power_pos_of_mem_of_sSameSide cfg.A_mem_Γ₁ cfg.A_mem_Γ₂ cfg.B_mem_Γ₁
    cfg.B_mem_Γ₂ cfg.C_mem_Γ₁ cfg.E_mem_Γ₁ cfg.sSameSide_AB_C_E
    cfg.power_Γ₂_C_pos

/-- The order `E-B-F` is forced by the two positive signed powers: the other two possible
orders would put `E` inside `Γ₂` or `F` inside `Γ₁`. -/
theorem sbtw_E_B_F : Sbtw ℝ cfg.E cfg.B cfg.F := by
  have hcol : Collinear ℝ ({cfg.E, cfg.B, cfg.F} : Set Pt) := by
    rw [show ({cfg.E, cfg.B, cfg.F} : Set Pt) = {cfg.B, cfg.E, cfg.F} by
      simp only [Set.insert_comm], cfg.F_eq]
    exact Sphere.secondInter_collinear cfg.Γ₂ cfg.B cfg.E
  have hE_ne_F : cfg.E ≠ cfg.F :=
    Sphere.ne_of_power_pos_of_mem cfg.F_mem_Γ₂ cfg.power_Γ₂_E_pos
  rcases hcol.wbtw_or_wbtw_or_wbtw with hEBF | hBFE | hFEB
  · exact ⟨hEBF, cfg.E_ne_B.symm, cfg.F_ne_B.symm⟩
  · linarith [cfg.power_Γ₁_F_pos,
      Sphere.power_neg_of_sbtw cfg.B_mem_Γ₁ cfg.E_mem_Γ₁
        (⟨hBFE, cfg.F_ne_B, hE_ne_F.symm⟩ : Sbtw ℝ cfg.B cfg.F cfg.E)]
  · linarith [cfg.power_Γ₂_E_pos,
      Sphere.power_neg_of_sbtw cfg.F_mem_Γ₂ cfg.B_mem_Γ₂
        (⟨hFEB, hE_ne_F, cfg.E_ne_B⟩ : Sbtw ℝ cfg.F cfg.E cfg.B)]

omit [Fact (finrank ℝ V = 2)] in
theorem F_ne_A : cfg.F ≠ cfg.A :=
  Sphere.Arc.ne_left_of_mem_interior cfg.F_mem_arcABD_Γ₂

/-- The seed `E_mem_arcACB_Γ₁` says that the second secant meets `Γ₁` on the same side
of chord `AB` as `C`.  The derived order `E-B-F` then transfers this to the statement that
`F` is on the same side of chord `AB` as `D` on `Γ₂`, which is exactly membership in the
interior of arc `ADB`. -/
theorem F_mem_arcADB_Γ₂ : cfg.F ∈ cfg.arcADB_Γ₂.interior := by
  have hss : (cfg.Γ₂.lineOrOrthRadius cfg.A cfg.B).SSameSide cfg.D cfg.F := by
    rw [lineOrOrthRadius_of_ne cfg.A_ne_B]
    exact cfg.sSameSide_AB_D_F
  simpa [arcADB_Γ₂] using
    Sphere.Arc.mem_interior_through_of_sSameSide cfg.A_mem_Γ₂ cfg.D_mem_Γ₂ cfg.B_mem_Γ₂
      cfg.D_ne_A cfg.sbtw_C_B_D.ne_right.symm cfg.F_mem_Γ₂ hss

/-- The seed `F_mem_arcABD_Γ₂` fixes `F` on the same side of chord `AD` as `B`.
Together with `cfg.F_mem_arcADB_Γ₂`, this determines the cyclic order on `Γ₂`; if `B`
were on the `D`-side arc of `ADF`, the corresponding oriented-angle signs would force
`sign (∡ A B D) = -sign (∡ A B D)`, contradicting noncollinearity of `A`, `B`, `D`.
Thus `B` lies in the opposite arc of `ADF`. -/
theorem B_mem_arcADF_Γ₂_opposite :
    cfg.B ∈ cfg.arcADF_Γ₂.opposite.interior := by
  have hABD_ne : (∡ cfg.A cfg.B cfg.D).sign ≠ 0 := by
    rw [Ne, EuclideanGeometry.oangle_sign_eq_zero_iff_collinear]
    exact fun hcol => cfg.sSameSide_AB_D_F.left_notMem
      (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)
  have hB_ne_left : cfg.B ≠ cfg.arcADF_Γ₂.left := by
    simpa [arcADF_Γ₂] using cfg.A_ne_B.symm
  have hB_ne_right : cfg.B ≠ cfg.arcADF_Γ₂.right := by
    simpa [arcADF_Γ₂] using cfg.F_ne_B.symm
  have hBF_seed : (line[ℝ, cfg.A, cfg.D] : AffineSubspace ℝ Pt).SSameSide cfg.B cfg.F :=
    by
      simpa [lineOrOrthRadius_of_ne cfg.D_ne_A.symm] using
        Sphere.Arc.sSameSide_of_mem_interior_through cfg.A_mem_Γ₂ cfg.B_mem_Γ₂
          cfg.D_mem_Γ₂ cfg.A_ne_B.symm cfg.sbtw_C_B_D.ne_right
          cfg.B_mem_arcABD_Γ₂_interior cfg.F_mem_arcABD_Γ₂
  have hα : (∡ cfg.A cfg.F cfg.B).sign = (∡ cfg.A cfg.D cfg.B).sign :=
    cfg.sSameSide_AB_D_F.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.B) (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
  have hβ : (∡ cfg.A cfg.F cfg.D).sign = (∡ cfg.A cfg.B cfg.D).sign :=
    hBF_seed.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.D) (right_mem_affineSpan_pair ℝ cfg.A cfg.D)
  rcases Sphere.Arc.mem_arc_or_mem_opposite cfg.arcADF_Γ₂ cfg.B_mem_Γ₂ with hB_arc | hB_opp
  · exfalso
    have hDB : (line[ℝ, cfg.A, cfg.F] : AffineSubspace ℝ Pt).SSameSide cfg.D cfg.B := by
      have hB_int : cfg.B ∈ cfg.arcADF_Γ₂.interior :=
        Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right hB_arc
          hB_ne_left hB_ne_right
      simpa [lineOrOrthRadius_of_ne cfg.F_ne_A.symm] using
        Sphere.Arc.sSameSide_of_mem_interior_through cfg.A_mem_Γ₂ cfg.D_mem_Γ₂
          cfg.F_mem_Γ₂ cfg.D_ne_A cfg.D_ne_F cfg.D_mem_arcADF_Γ₂_interior hB_int
    have hbad : (∡ cfg.A cfg.B cfg.F).sign = (∡ cfg.A cfg.D cfg.F).sign :=
      hDB.oangle_sign_eq
        (left_mem_affineSpan_pair ℝ cfg.A cfg.F) (right_mem_affineSpan_pair ℝ cfg.A cfg.F)
    have s1 := EuclideanGeometry.oangle_swap₂₃_sign cfg.A cfg.F cfg.B
    have s2 := EuclideanGeometry.oangle_swap₂₃_sign cfg.A cfg.D cfg.B
    have s3 := EuclideanGeometry.oangle_swap₂₃_sign cfg.A cfg.F cfg.D
    have key : (∡ cfg.A cfg.B cfg.D).sign = -(∡ cfg.A cfg.B cfg.D).sign :=
      calc (∡ cfg.A cfg.B cfg.D).sign
          = -(∡ cfg.A cfg.D cfg.B).sign := s2.symm
        _ = -(∡ cfg.A cfg.F cfg.B).sign := by rw [hα]
        _ = (∡ cfg.A cfg.B cfg.F).sign := s1
        _ = (∡ cfg.A cfg.D cfg.F).sign := hbad
        _ = -(∡ cfg.A cfg.F cfg.D).sign := s3.symm
        _ = -(∡ cfg.A cfg.B cfg.D).sign := by rw [hβ]
    exact hABD_ne (SignType.self_eq_neg_iff.mp key)
  · exact Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right hB_opp
      (by simpa using hB_ne_left) (by simpa using hB_ne_right)

omit [Fact (finrank ℝ V = 2)] in
/-- Points `A`, `D`, and `C` are noncollinear.  Otherwise `C` and `B` would be the same
second intersection of `Γ₁` with line `AB`, contradicting strict betweenness. -/
theorem not_collinear_ADC : ¬Collinear ℝ ({cfg.A, cfg.D, cfg.C} : Set Pt) := by
  intro hcol
  have hA_CD : cfg.A ∈ line[ℝ, cfg.C, cfg.D] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.C_ne_D
  refine cfg.C_not_mem_line_AB ?_
  rw [affineSpan_pair_eq_of_mem_of_mem_of_ne hA_CD
    cfg.sbtw_C_B_D.wbtw.mem_affineSpan cfg.A_ne_B]
  exact left_mem_affineSpan_pair ℝ _ _

/-! ### Step 1: the congruence `△ACD ≅ △AEF` -/

/-- On `Γ₂`, the inscribed angles subtending chord `AB` are equal. -/
theorem angle_ADB_eq_angle_AFB :
    ∠ cfg.A cfg.D cfg.B = ∠ cfg.A cfg.F cfg.B := by
  have h := Sphere.Arc.angle_eq_of_mem_opposite_interior cfg.arcADB_Γ₂.opposite
    (B₁ := cfg.D) (B₂ := cfg.F)
    (by simpa [arcADB_Γ₂] using cfg.D_mem_arcADB_Γ₂_interior)
    (by simpa [arcADB_Γ₂] using cfg.F_mem_arcADB_Γ₂)
    (by simpa [arcADB_Γ₂] using cfg.D_ne_A)
    (by simpa [arcADB_Γ₂] using cfg.sbtw_C_B_D.ne_right.symm)
    (by simpa [arcADB_Γ₂] using cfg.F_ne_A)
    (by simpa [arcADB_Γ₂] using cfg.F_ne_B)
  simpa [arcADB_Γ₂] using h

/-- On `Γ₁`, the inscribed angles subtending chord `AB`, with `E, B, F` collinear. -/
theorem angle_ACB_eq_angle_AEF :
    ∠ cfg.A cfg.C cfg.B = ∠ cfg.A cfg.E cfg.F := by
  have h := Sphere.Arc.angle_eq_of_mem_opposite_interior cfg.arcACB_Γ₁.opposite
    (B₁ := cfg.C) (B₂ := cfg.E)
    (by simpa [arcACB_Γ₁] using cfg.C_mem_arcACB_Γ₁_interior)
    (by simpa [arcACB_Γ₁] using cfg.E_mem_arcACB_Γ₁)
    (by simpa [arcACB_Γ₁] using cfg.C_ne_A)
    (by simpa [arcACB_Γ₁] using cfg.sbtw_C_B_D.ne_left.symm)
    (by simpa [arcACB_Γ₁] using cfg.E_ne_A)
    (by simpa [arcACB_Γ₁] using cfg.E_ne_B)
  have hAEB : ∠ cfg.A cfg.C cfg.B = ∠ cfg.A cfg.E cfg.B := by
    simpa [arcACB_Γ₁] using h
  calc
    ∠ cfg.A cfg.C cfg.B = ∠ cfg.A cfg.E cfg.B := hAEB
    _ = ∠ cfg.A cfg.E cfg.F := cfg.sbtw_E_B_F.angle_eq_right cfg.A

/-- The ASA congruence `△ADC ≅ △AFE`. -/
theorem congr_ADC_AFE :
    ![cfg.A, cfg.D, cfg.C] ≅ ![cfg.A, cfg.F, cfg.E] := by
  have hADC_AFE : ∠ cfg.A cfg.D cfg.C = ∠ cfg.A cfg.F cfg.E := by
    calc
      ∠ cfg.A cfg.D cfg.C = ∠ cfg.A cfg.D cfg.B :=
        (cfg.sbtw_C_B_D.symm.angle_eq_right cfg.A).symm
      _ = ∠ cfg.A cfg.F cfg.B := cfg.angle_ADB_eq_angle_AFB
      _ = ∠ cfg.A cfg.F cfg.E := cfg.sbtw_E_B_F.symm.angle_eq_right cfg.A
  have hDCA_FEA : ∠ cfg.D cfg.C cfg.A = ∠ cfg.F cfg.E cfg.A := by
    have hACD_AEF : ∠ cfg.A cfg.C cfg.D = ∠ cfg.A cfg.E cfg.F := by
      calc
        ∠ cfg.A cfg.C cfg.D = ∠ cfg.A cfg.C cfg.B :=
          (cfg.sbtw_C_B_D.angle_eq_right cfg.A).symm
        _ = ∠ cfg.A cfg.E cfg.F := cfg.angle_ACB_eq_angle_AEF
    simpa [angle_comm] using hACD_AEF
  have hCD_EF : dist cfg.D cfg.C = dist cfg.F cfg.E := by
    simpa [dist_comm] using cfg.CD_eq_EF
  exact angle_side_angle cfg.not_collinear_ADC hADC_AFE hCD_EF hDCA_FEA

/-- The ASA congruence gives the corresponding side `AD = AF`. -/
theorem dist_AD_eq_dist_AF :
    dist cfg.A cfg.D = dist cfg.A cfg.F := by
  simpa using cfg.congr_ADC_AFE.dist_eq 0 1

/-! ### Step 2: the isosceles triangle `ADF` -/

theorem angle_ADF_eq_angle_AFD :
    ∠ cfg.A cfg.D cfg.F = ∠ cfg.A cfg.F cfg.D :=
  angle_eq_angle_of_dist_eq cfg.dist_AD_eq_dist_AF

omit [Fact (finrank ℝ V = 2)] in
theorem not_collinear_ADF : ¬Collinear ℝ ({cfg.A, cfg.D, cfg.F} : Set Pt) := by
  intro hcol
  have hA_DF : cfg.A ∈ line[ℝ, cfg.D, cfg.F] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.D_ne_F
  have hA_lor : cfg.A ∈ cfg.Γ₂.lineOrOrthRadius cfg.D cfg.F := by
    rwa [lineOrOrthRadius_of_ne cfg.D_ne_F]
  have hA_eq :=
    (Sphere.mem_lineOrOrthRadius_inter_sphere_iff cfg.D_mem_Γ₂ cfg.F_mem_Γ₂
      cfg.A_mem_Γ₂).mp hA_lor
  rcases hA_eq with hAD | hAF
  · exact cfg.D_ne_A hAD.symm
  · exact cfg.F_ne_A hAF.symm

theorem angle_ADF_lt_pi_div_two :
    ∠ cfg.A cfg.D cfg.F < π / 2 := by
  have hsum : ∠ cfg.A cfg.D cfg.F + ∠ cfg.D cfg.F cfg.A + ∠ cfg.F cfg.A cfg.D = π :=
    EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.F cfg.D_ne_A
  have hapex_pos : 0 < ∠ cfg.F cfg.A cfg.D :=
    angle_pos_of_not_collinear fun h =>
      cfg.not_collinear_ADF (by rw [Set.insert_comm, Set.pair_comm] at h; exact h)
  rw [angle_comm cfg.D cfg.F cfg.A, cfg.angle_ADF_eq_angle_AFD.symm] at hsum
  linarith

theorem angle_ABF_add_ADF :
    ∠ cfg.A cfg.B cfg.F + ∠ cfg.A cfg.D cfg.F = π := by
  have h := Sphere.Arc.angle_add_angle_opposite_eq_pi cfg.arcADF_Γ₂
    (B₁ := cfg.B) (B₂ := cfg.D)
    (by simpa [arcADF_Γ₂] using cfg.B_mem_arcADF_Γ₂_opposite)
    (by simpa [arcADF_Γ₂] using cfg.D_mem_arcADF_Γ₂_interior)
    (by simpa [arcADF_Γ₂] using cfg.A_ne_B.symm)
    (by simpa [arcADF_Γ₂] using cfg.F_ne_B.symm)
    (by simpa [arcADF_Γ₂] using cfg.D_ne_A)
    (by simpa [arcADF_Γ₂] using cfg.D_ne_F)
  simpa [arcADF_Γ₂] using h

theorem pi_div_two_lt_angle_ABF : π / 2 < ∠ cfg.A cfg.B cfg.F := by
  linarith [cfg.angle_ABF_add_ADF, cfg.angle_ADF_lt_pi_div_two]

/-! ### Step 3: `AB` is the angle bisector at `B` of triangle `BCF` -/

theorem angle_ABD_add_ABF :
    ∠ cfg.A cfg.B cfg.D + ∠ cfg.A cfg.B cfg.F = π := by
  have hCBA_eq_ABF : ∠ cfg.C cfg.B cfg.A = ∠ cfg.A cfg.B cfg.F := by
    rw [cfg.angle_CBA_eq_angle_FBA, angle_comm cfg.F cfg.B cfg.A]
  linarith [cfg.sbtw_C_B_D.angle_add_angle_eq_pi (A := cfg.A)]

theorem dist_BF_lt_dist_BD : dist cfg.B cfg.F < dist cfg.B cfg.D := by
  have hABD_eq : ∠ cfg.A cfg.B cfg.D = π - ∠ cfg.A cfg.B cfg.F := by
    linarith [cfg.angle_ABD_add_ABF]
  have hcosABD : Real.cos (∠ cfg.A cfg.B cfg.D) = -Real.cos (∠ cfg.A cfg.B cfg.F) := by
    rw [hABD_eq, Real.cos_pi_sub]
  have hcos_neg : Real.cos (∠ cfg.A cfg.B cfg.F) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt cfg.pi_div_two_lt_angle_ABF
      (by linarith [angle_le_pi cfg.A cfg.B cfg.F, Real.pi_pos])
  have hAD := EuclideanGeometry.law_cos cfg.A cfg.B cfg.D
  have hAF := EuclideanGeometry.law_cos cfg.A cfg.B cfg.F
  have hsq : dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.D cfg.B * dist cfg.D cfg.B -
        2 * dist cfg.A cfg.B * dist cfg.D cfg.B * Real.cos (∠ cfg.A cfg.B cfg.D) =
      dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.F cfg.B * dist cfg.F cfg.B -
        2 * dist cfg.A cfg.B * dist cfg.F cfg.B * Real.cos (∠ cfg.A cfg.B cfg.F) := by
    calc
      dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.D cfg.B * dist cfg.D cfg.B -
          2 * dist cfg.A cfg.B * dist cfg.D cfg.B * Real.cos (∠ cfg.A cfg.B cfg.D)
          = dist cfg.A cfg.D * dist cfg.A cfg.D := hAD.symm
      _ = dist cfg.A cfg.F * dist cfg.A cfg.F := by rw [cfg.dist_AD_eq_dist_AF]
      _ = dist cfg.A cfg.B * dist cfg.A cfg.B + dist cfg.F cfg.B * dist cfg.F cfg.B -
          2 * dist cfg.A cfg.B * dist cfg.F cfg.B * Real.cos (∠ cfg.A cfg.B cfg.F) := hAF
  rw [hcosABD] at hsq
  have hAB_pos : 0 < dist cfg.A cfg.B := dist_pos.mpr cfg.A_ne_B
  have hD_pos : 0 < dist cfg.D cfg.B := dist_pos.mpr cfg.B_ne_D.symm
  have hF_nonneg : 0 ≤ dist cfg.F cfg.B := dist_nonneg
  have hcoef_pos :
      0 < -2 * dist cfg.A cfg.B * Real.cos (∠ cfg.A cfg.B cfg.F) :=
    mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by norm_num) hAB_pos) hcos_neg
  have hsum_pos : 0 < dist cfg.D cfg.B + dist cfg.F cfg.B := by linarith
  have hprod_pos := mul_pos hcoef_pos hsum_pos
  have : dist cfg.F cfg.B < dist cfg.D cfg.B := by nlinarith [hsq, hprod_pos]
  simpa [dist_comm] using this

theorem dist_BC_lt_dist_BE : dist cfg.B cfg.C < dist cfg.B cfg.E := by
  have hCD : dist cfg.B cfg.C + dist cfg.B cfg.D = dist cfg.C cfg.D := by
    simpa [dist_comm, add_comm] using cfg.sbtw_C_B_D.wbtw.dist_add_dist
  have hEF : dist cfg.B cfg.E + dist cfg.B cfg.F = dist cfg.E cfg.F := by
    simpa [dist_comm] using cfg.sbtw_E_B_F.wbtw.dist_add_dist
  linarith [cfg.CD_eq_EF, hCD, hEF, cfg.dist_BF_lt_dist_BD]

omit [Fact (finrank ℝ V = 2)] in
theorem dist_BF_mul_CD_lt_CF_sq :
    dist cfg.B cfg.F * dist cfg.C cfg.D < dist cfg.C cfg.F ^ 2 := by
  have hF_CP : cfg.F ∈ line[ℝ, cfg.C, cfg.P] := cfg.sbtw_C_P_F.right_mem_affineSpan
  have hF_EB : cfg.F ∈ line[ℝ, cfg.E, cfg.B] := by
    rw [AffineSubspace.affineSpan_pair_comm, cfg.F_eq]
    exact Sphere.secondInter_vsub_mem_affineSpan cfg.Γ₂ cfg.B cfg.E
  have hpow_CP := cfg.Γ₁.mul_dist_eq_abs_power hF_CP cfg.C_mem_Γ₁ cfg.P_mem_Γ₁
  have hpow_EB := cfg.Γ₁.mul_dist_eq_abs_power hF_EB cfg.E_mem_Γ₁ cfg.B_mem_Γ₁
  have hprod : dist cfg.F cfg.C * dist cfg.F cfg.P = dist cfg.F cfg.E * dist cfg.F cfg.B := by
    rw [hpow_CP, hpow_EB]
  have hCP_add_PF : dist cfg.C cfg.P + dist cfg.P cfg.F = dist cfg.C cfg.F :=
    cfg.sbtw_C_P_F.wbtw.dist_add_dist
  have hCP_pos : 0 < dist cfg.C cfg.P := dist_pos.mpr cfg.P_ne_C.symm
  have hPF_lt_CF : dist cfg.P cfg.F < dist cfg.C cfg.F := by linarith
  have hFP_lt_FC : dist cfg.F cfg.P < dist cfg.F cfg.C := by
    simpa [dist_comm] using hPF_lt_CF
  have hFC_pos : 0 < dist cfg.F cfg.C := dist_pos.mpr cfg.C_ne_F.symm
  have hlt : dist cfg.F cfg.E * dist cfg.F cfg.B < dist cfg.F cfg.C * dist cfg.F cfg.C := by
    rw [← hprod]
    exact mul_lt_mul_of_pos_left hFP_lt_FC hFC_pos
  simpa [pow_two, dist_comm, cfg.CD_eq_EF, mul_comm, mul_left_comm, mul_assoc] using hlt

omit [Fact (finrank ℝ V = 2)] in
theorem dist_BC_mul_CD_lt_CF_sq :
    dist cfg.B cfg.C * dist cfg.C cfg.D < dist cfg.C cfg.F ^ 2 := by
  have hC_DB : cfg.C ∈ line[ℝ, cfg.D, cfg.B] := cfg.sbtw_C_B_D.left_mem_affineSpan
  have hC_FQ : cfg.C ∈ line[ℝ, cfg.F, cfg.Q] := cfg.sbtw_C_Q_F.left_mem_affineSpan
  have hpow_DB := cfg.Γ₂.mul_dist_eq_abs_power hC_DB cfg.D_mem_Γ₂ cfg.B_mem_Γ₂
  have hpow_FQ := cfg.Γ₂.mul_dist_eq_abs_power hC_FQ cfg.F_mem_Γ₂ cfg.Q_mem_Γ₂
  have hprod : dist cfg.C cfg.D * dist cfg.C cfg.B = dist cfg.C cfg.F * dist cfg.C cfg.Q := by
    rw [hpow_DB, hpow_FQ]
  have hCQ_add_QF : dist cfg.C cfg.Q + dist cfg.Q cfg.F = dist cfg.C cfg.F :=
    cfg.sbtw_C_Q_F.wbtw.dist_add_dist
  have hQF_pos : 0 < dist cfg.Q cfg.F := dist_pos.mpr cfg.Q_ne_F
  have hCQ_lt_CF : dist cfg.C cfg.Q < dist cfg.C cfg.F := by linarith
  have hCF_pos : 0 < dist cfg.C cfg.F := dist_pos.mpr cfg.C_ne_F
  have hlt : dist cfg.C cfg.D * dist cfg.C cfg.B < dist cfg.C cfg.F * dist cfg.C cfg.F := by
    rw [hprod]
    exact mul_lt_mul_of_pos_left hCQ_lt_CF hCF_pos
  simpa [pow_two, dist_comm, mul_comm, mul_left_comm, mul_assoc] using hlt

/-! ### Major-arc side conditions

The midpoint-bisector bridge requires `C` and `F` to lie on the major arcs
`PB` and `QB`; otherwise the resulting bisectors may be external. We prove
this by first showing `π / 2 ≤ ∠ CBF`. The metric argument derives
`BF < BD`, then `BC + BF < CD`, followed by
`BF * CD < CF ^ 2` and `BC * CD < CF ^ 2`; hence
`BC ^ 2 + BF ^ 2 < CF ^ 2`, which gives the required angle bound. -/

/-- The angle at `B` in triangle `BCF` is non-acute. -/
theorem pi_div_two_le_angle_CBF : π / 2 ≤ ∠ cfg.C cfg.B cfg.F := by
  have hEF : dist cfg.B cfg.E + dist cfg.B cfg.F = dist cfg.E cfg.F := by
    simpa [dist_comm] using cfg.sbtw_E_B_F.wbtw.dist_add_dist
  have hCD_eq : dist cfg.C cfg.D = dist cfg.B cfg.E + dist cfg.B cfg.F :=
    cfg.CD_eq_EF.trans hEF.symm
  have hCD_gt : dist cfg.B cfg.C + dist cfg.B cfg.F < dist cfg.C cfg.D := by
    linarith [hCD_eq, cfg.dist_BC_lt_dist_BE]
  have hBC_pos : 0 < dist cfg.B cfg.C := dist_pos.mpr cfg.C_ne_B.symm
  have hBF_pos : 0 < dist cfg.B cfg.F := dist_pos.mpr cfg.F_ne_B.symm
  have hsq :
      dist cfg.B cfg.C ^ 2 + dist cfg.B cfg.F ^ 2 < dist cfg.C cfg.F ^ 2 := by
    by_cases hle : dist cfg.B cfg.C ≤ dist cfg.B cfg.F
    · have hprod : dist cfg.B cfg.C ^ 2 + dist cfg.B cfg.F ^ 2 <
          dist cfg.B cfg.F * dist cfg.C cfg.D := by
        nlinarith
      nlinarith [hprod, cfg.dist_BF_mul_CD_lt_CF_sq]
    · have hlt : dist cfg.B cfg.F < dist cfg.B cfg.C := lt_of_not_ge hle
      have hprod : dist cfg.B cfg.C ^ 2 + dist cfg.B cfg.F ^ 2 <
          dist cfg.B cfg.C * dist cfg.C cfg.D := by
        nlinarith
      nlinarith [hprod, cfg.dist_BC_mul_CD_lt_CF_sq]
  exact (dist_sq_add_dist_sq_le_dist_sq_iff_pi_div_two_le_angle
    (p₁ := cfg.C) (p₂ := cfg.B) (p₃ := cfg.F)).mp (by
    simpa [pow_two, dist_comm] using hsq.le)

/-- `C` lies on the major arc `PB` of `Γ₁` (the interior of the arc opposite the minor arc, i.e. the
arc not containing the minor-arc midpoint `M`).  If instead `C` were on the *minor* arc `PB`, it
would subtend `PB` (hence `∠BCF`, as `P` is between `C` and `F`) at `≥ π/2`; together with the
non-acute angle at `B` this would force `∠BFC ≤ 0`, contradicting nondegeneracy of `△BCF`. -/
theorem C_mem_arcPB_opposite : cfg.C ∈ cfg.arcPB.opposite.interior := by
  have hBFC_pos : 0 < ∠ cfg.B cfg.F cfg.C :=
    angle_pos_of_not_collinear (by simpa only [Set.pair_comm] using cfg.not_collinear_BCF)
  have hPCB_lt : ∠ cfg.P cfg.C cfg.B < π / 2 := by
    rw [angle_comm, cfg.sbtw_C_P_F.angle_eq_right cfg.B]
    have hsum : ∠ cfg.C cfg.B cfg.F + ∠ cfg.B cfg.F cfg.C + ∠ cfg.F cfg.C cfg.B = π :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.F cfg.C_ne_B.symm
    rw [angle_comm cfg.F cfg.C cfg.B] at hsum
    linarith [cfg.pi_div_two_le_angle_CBF]
  simpa [CfgCore.arcPB] using
    (Sphere.Arc.mem_major_interior_iff_angle_lt_pi_div_two
      cfg.P_mem_Γ₁ cfg.B_mem_Γ₁ cfg.PB_not_diam cfg.P_ne_B cfg.C_mem_Γ₁).2 hPCB_lt

/-- `F` lies on the major arc `QB` of `Γ₂`.  Symmetric to `C_mem_arcPB_opposite`. -/
theorem F_mem_arcQB_opposite : cfg.F ∈ cfg.arcQB.opposite.interior := by
  have hFCB_pos : 0 < ∠ cfg.F cfg.C cfg.B := by
    rw [angle_comm]
    exact angle_pos_of_not_collinear cfg.not_collinear_BCF
  have hQFB_lt : ∠ cfg.Q cfg.F cfg.B < π / 2 := by
    rw [angle_comm, cfg.sbtw_C_Q_F.symm.angle_eq_right cfg.B]
    have hsum : ∠ cfg.C cfg.B cfg.F + ∠ cfg.B cfg.F cfg.C + ∠ cfg.F cfg.C cfg.B = π :=
      EuclideanGeometry.angle_add_angle_add_angle_eq_pi cfg.F cfg.C_ne_B.symm
    linarith [cfg.pi_div_two_le_angle_CBF]
  simpa [CfgCore.arcQB] using
    (Sphere.Arc.mem_major_interior_iff_angle_lt_pi_div_two
      cfg.Q_mem_Γ₂ cfg.B_mem_Γ₂ cfg.QB_not_diam cfg.Q_ne_B cfg.F_mem_Γ₂).2 hQFB_lt
end CfgArcACB

/-! ## Branch-independent configuration and proof

The original text does not choose an order for `E`, `B`, and `F`.  The two `opposite`
memberships below record exactly the extra cyclic-order information needed by the minor-arc
reading of `M` and `N`; neither secant order is built into this structure. -/

structure Cfg (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
    [NormedAddTorsor V Pt] extends CfgCore V Pt where
  (M N : Pt)
  M_eq : M = (Sphere.Arc.minor P_mem_Γ₁ B_mem_Γ₁ PB_not_diam).midpoint
  -- root: `C` is on the arc opposite the minor arc whose midpoint is `M`.
  C_mem_arcPB_opposite :
    C ∈ (Sphere.Arc.minor P_mem_Γ₁ B_mem_Γ₁ PB_not_diam).opposite.interior
  N_eq : N = (Sphere.Arc.minor Q_mem_Γ₂ B_mem_Γ₂ QB_not_diam).midpoint
  -- root: `F` is on the arc opposite the minor arc whose midpoint is `N`.
  F_mem_arcQB_opposite :
    F ∈ (Sphere.Arc.minor Q_mem_Γ₂ B_mem_Γ₂ QB_not_diam).opposite.interior

namespace Cfg

variable [Fact (finrank ℝ V = 2)] (cfg : Cfg V Pt)

local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

/-! ### Minor arcs and the triangle `BCF` -/

omit [Fact (finrank ℝ V = 2)] in
theorem M_mem_Γ₁ : cfg.M ∈ (cfg.Γ₁ : Set Pt) := by
  rw [cfg.M_eq]
  exact Sphere.Arc.midpoint_mem cfg.arcPB

omit [Fact (finrank ℝ V = 2)] in
theorem N_mem_Γ₂ : cfg.N ∈ (cfg.Γ₂ : Set Pt) := by
  rw [cfg.N_eq]
  exact Sphere.Arc.midpoint_mem cfg.arcQB

omit [Fact (finrank ℝ V = 2)] in
theorem affineIndependent_BCF : AffineIndependent ℝ ![cfg.B, cfg.C, cfg.F] :=
  affineIndependent_iff_not_collinear_set.mpr cfg.not_collinear_BCF

omit [Fact (finrank ℝ V = 2)] in
def triangleBCF : Triangle ℝ Pt := ⟨_, cfg.affineIndependent_BCF⟩

omit [Fact (finrank ℝ V = 2)] in
theorem M_mem_arcPB_interior : cfg.M ∈ cfg.arcPB.interior := by
  rw [cfg.M_eq]
  exact Sphere.Arc.midpoint_mem_interior cfg.arcPB (fun h => cfg.arcPB_not_isDegenerate (Or.inl h))

omit [Fact (finrank ℝ V = 2)] in
theorem N_mem_arcQB_interior : cfg.N ∈ cfg.arcQB.interior := by
  rw [cfg.N_eq]
  exact Sphere.Arc.midpoint_mem_interior cfg.arcQB (fun h => cfg.arcQB_not_isDegenerate (Or.inl h))

theorem M_ne_C : cfg.M ≠ cfg.C :=
  Sphere.Arc.ne_of_mem_interior_of_mem_opposite_interior cfg.arcPB
    cfg.arcPB_not_isDegenerate cfg.M_mem_arcPB_interior cfg.C_mem_arcPB_opposite

theorem N_ne_F : cfg.N ≠ cfg.F :=
  Sphere.Arc.ne_of_mem_interior_of_mem_opposite_interior cfg.arcQB
    cfg.arcQB_not_isDegenerate cfg.N_mem_arcQB_interior cfg.F_mem_arcQB_opposite

/-! ### Steps 4 and 5: the two minor-arc midpoints give internal angle bisectors -/

omit [Fact (finrank ℝ V = 2)] in
theorem angle_DCM_eq_angle_BCM : ∠ cfg.D cfg.C cfg.M = ∠ cfg.B cfg.C cfg.M := by
  rw [angle_comm cfg.D cfg.C cfg.M, angle_comm cfg.B cfg.C cfg.M]
  exact (cfg.sbtw_C_B_D.angle_eq_right cfg.M).symm

theorem angle_PCM_eq_angle_BCM : ∠ cfg.P cfg.C cfg.M = ∠ cfg.B cfg.C cfg.M := by
  have h := Sphere.Arc.angle_bisect_of_mem_opposite cfg.P_mem_Γ₁ cfg.B_mem_Γ₁
    cfg.PB_not_diam cfg.P_ne_B cfg.C_mem_arcPB_opposite
  rw [← cfg.M_eq] at h
  rw [h, angle_comm cfg.M cfg.C cfg.B]

theorem angle_DCM_eq_angle_FCM : ∠ cfg.D cfg.C cfg.M = ∠ cfg.F cfg.C cfg.M := by
  have hFP : ∠ cfg.F cfg.C cfg.M = ∠ cfg.P cfg.C cfg.M := by
    rw [angle_comm cfg.F cfg.C cfg.M, angle_comm cfg.P cfg.C cfg.M]
    exact (cfg.sbtw_C_P_F.angle_eq_right cfg.M).symm
  rw [cfg.angle_DCM_eq_angle_BCM, ← cfg.angle_PCM_eq_angle_BCM, hFP]

theorem angle_QFN_eq_angle_BFN : ∠ cfg.Q cfg.F cfg.N = ∠ cfg.B cfg.F cfg.N := by
  have h := Sphere.Arc.angle_bisect_of_mem_opposite cfg.Q_mem_Γ₂ cfg.B_mem_Γ₂
    cfg.QB_not_diam cfg.Q_ne_B cfg.F_mem_arcQB_opposite
  rw [← cfg.N_eq] at h
  rw [h, angle_comm cfg.N cfg.F cfg.B]

theorem angle_CFN_eq_angle_BFN : ∠ cfg.C cfg.F cfg.N = ∠ cfg.B cfg.F cfg.N := by
  have hCQ : ∠ cfg.C cfg.F cfg.N = ∠ cfg.Q cfg.F cfg.N := by
    rw [angle_comm cfg.C cfg.F cfg.N, angle_comm cfg.Q cfg.F cfg.N]
    exact (cfg.sbtw_C_Q_F.symm.angle_eq_right cfg.N).symm
  rw [hCQ, cfg.angle_QFN_eq_angle_BFN]

/-! ### Step 6: the three branch-independent angle bisectors concur -/

theorem exists_incenter :
    ∃ I : Pt,
      I ∈ line[ℝ, cfg.A, cfg.B] ∧
        I ∈ line[ℝ, cfg.C, cfg.M] ∧
          I ∈ line[ℝ, cfg.F, cfg.N] ∧ ¬Collinear ℝ ({cfg.C, I, cfg.F} : Set Pt) := by
  let I := cfg.triangleBCF.incenter
  have hI_ne_B : I ≠ cfg.B := by simpa [I, triangleBCF] using cfg.triangleBCF.incenter_ne_point 0
  have hI_ne_C : I ≠ cfg.C := by simpa [I, triangleBCF] using cfg.triangleBCF.incenter_ne_point 1
  have hI_ne_F : I ≠ cfg.F := by simpa [I, triangleBCF] using cfg.triangleBCF.incenter_ne_point 2
  have hncol_CBF : ¬Collinear ℝ ({cfg.C, cfg.B, cfg.F} : Set Pt) := by
    simpa only [Set.insert_comm] using cfg.not_collinear_BCF
  have hncol_BFC : ¬Collinear ℝ ({cfg.B, cfg.F, cfg.C} : Set Pt) := by
    simpa only [Set.pair_comm] using cfg.not_collinear_BCF
  have hA_bis : ∡ cfg.C cfg.B cfg.A = ∡ cfg.A cfg.B cfg.F := by
    refine oangle_bisector_of_angle_eq hncol_CBF ?_
    simpa [angle_comm cfg.F cfg.B cfg.A] using cfg.angle_CBA_eq_angle_FBA
  have hI_bis_B : ∡ cfg.C cfg.B I = ∡ I cfg.B cfg.F := by
    simpa [I, triangleBCF] using cfg.triangleBCF.oangle_incenter_eq
      (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
      (show (1 : Fin 3) ≠ 2 by decide)
  have hM_bis : ∡ cfg.B cfg.C cfg.M = ∡ cfg.M cfg.C cfg.F := by
    refine oangle_bisector_of_angle_eq cfg.not_collinear_BCF ?_
    calc
      ∠ cfg.B cfg.C cfg.M = ∠ cfg.D cfg.C cfg.M := cfg.angle_DCM_eq_angle_BCM.symm
      _ = ∠ cfg.F cfg.C cfg.M := cfg.angle_DCM_eq_angle_FCM
      _ = ∠ cfg.M cfg.C cfg.F := angle_comm cfg.F cfg.C cfg.M
  have hI_bis_C : ∡ cfg.B cfg.C I = ∡ I cfg.C cfg.F := by
    simpa [I, triangleBCF] using cfg.triangleBCF.oangle_incenter_eq
      (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide)
  have hN_bis : ∡ cfg.B cfg.F cfg.N = ∡ cfg.N cfg.F cfg.C := by
    refine oangle_bisector_of_angle_eq hncol_BFC ?_
    calc
      ∠ cfg.B cfg.F cfg.N = ∠ cfg.C cfg.F cfg.N := cfg.angle_CFN_eq_angle_BFN.symm
      _ = ∠ cfg.N cfg.F cfg.C := angle_comm cfg.C cfg.F cfg.N
  have hI_bis_F : ∡ cfg.B cfg.F I = ∡ I cfg.F cfg.C := by
    simpa [I, triangleBCF] using cfg.triangleBCF.oangle_incenter_eq
      (show (2 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 1 by decide)
  have hcol_ABI : Collinear ℝ ({cfg.A, cfg.B, I} : Set Pt) :=
    collinear_of_oangle_bisectors cfg.C_ne_B cfg.F_ne_B cfg.A_ne_B hI_ne_B hA_bis hI_bis_B
  have hcol_CMI : Collinear ℝ ({cfg.M, cfg.C, I} : Set Pt) :=
    collinear_of_oangle_bisectors cfg.C_ne_B.symm cfg.C_ne_F.symm cfg.M_ne_C hI_ne_C
      hM_bis hI_bis_C
  have hcol_FNI : Collinear ℝ ({cfg.N, cfg.F, I} : Set Pt) :=
    collinear_of_oangle_bisectors cfg.F_ne_B.symm cfg.C_ne_F cfg.N_ne_F hI_ne_F
      hN_bis hI_bis_F
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · exact hcol_ABI.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B
  · exact hcol_CMI.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.M_ne_C.symm
  · exact hcol_FNI.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.N_ne_F.symm
  · have hnot : I ∉ line[ℝ, cfg.C, cfg.F] := by
      simpa [I, triangleBCF] using cfg.triangleBCF.incenter_notMem_affineSpan_pair 1 2
    intro hcol
    exact hnot (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.C_ne_F)

/-! ### Step 7: equal powers give the desired concyclicity -/

theorem result_cfg : Cospherical ({cfg.C, cfg.F, cfg.M, cfg.N} : Set Pt) := by
  obtain ⟨I, hI_AB, hI_CM, hI_FN, hCIF⟩ := cfg.exists_incenter
  have hpow : ⟪cfg.C -ᵥ I, cfg.M -ᵥ I⟫ = ⟪cfg.F -ᵥ I, cfg.N -ᵥ I⟫ := by
    calc
      _ = cfg.Γ₁.power I :=
        Sphere.inner_vsub_vsub_eq_power cfg.C_mem_Γ₁ cfg.M_mem_Γ₁ hI_CM
      _ = ⟪cfg.A -ᵥ I, cfg.B -ᵥ I⟫ :=
        (Sphere.inner_vsub_vsub_eq_power cfg.A_mem_Γ₁ cfg.B_mem_Γ₁ hI_AB).symm
      _ = cfg.Γ₂.power I :=
        Sphere.inner_vsub_vsub_eq_power cfg.A_mem_Γ₂ cfg.B_mem_Γ₂ hI_AB
      _ = ⟪cfg.F -ᵥ I, cfg.N -ᵥ I⟫ :=
        (Sphere.inner_vsub_vsub_eq_power cfg.F_mem_Γ₂ cfg.N_mem_Γ₂ hI_FN).symm
  simpa [Set.insert_comm cfg.M cfg.F] using
    EuclideanGeometry.cospherical_of_inner_vsub_eq_inner_vsub hI_CM hI_FN hCIF hpow

end Cfg

/-! ## Public theorems -/

/-- China MO 2010 Problem 1.

Circles `Γ₁`, `Γ₂` meet at `A`, `B`. A line through `B` meets `Γ₁` at `C` and `Γ₂`
at `D`, with `B` between `C` and `D`; another line through `B` meets `Γ₁` at `E` and
`Γ₂` at `F`. Line segment `CF` meets `Γ₁` at `P` and `Γ₂` at `Q`. The points `M`, `N`
are the midpoints of minor arcs `PB` and `QB`. If `CD = EF`, then `C`, `F`, `M`, `N`
are concyclic.

No order is imposed on `E`, `B`, and `F`, so this statement covers both secant-order
branches.  The two explicit `opposite` hypotheses are essential for the chosen minor arcs:
without them the corresponding statement is false in one of the branches. -/
theorem result [Fact (finrank ℝ V = 2)]
    {A B C D E F P Q M N : Pt} {Γ₁ Γ₂ : Sphere Pt}
    (A_mem_Γ₁ : A ∈ (Γ₁ : Set Pt)) (A_mem_Γ₂ : A ∈ (Γ₂ : Set Pt))
    (B_mem_Γ₁ : B ∈ (Γ₁ : Set Pt)) (B_mem_Γ₂ : B ∈ (Γ₂ : Set Pt))
    (A_ne_B : A ≠ B)
    (C_mem_Γ₁ : C ∈ (Γ₁ : Set Pt)) (D_mem_Γ₂ : D ∈ (Γ₂ : Set Pt))
    (sbtw_C_B_D : Sbtw ℝ C B D)
    (E_mem_Γ₁ : E ∈ (Γ₁ : Set Pt))
    (F_eq : F = Γ₂.secondInter B (E -ᵥ B))
    -- root: the two secants through `B` are distinct.
    (E_not_mem_line_CD : E ∉ line[ℝ, C, D])
    (P_eq : P = Γ₁.secondInter C (F -ᵥ C))
    (sbtw_C_P_F : Sbtw ℝ C P F)
    (Q_eq : Q = Γ₂.secondInter F (C -ᵥ F))
    (sbtw_C_Q_F : Sbtw ℝ C Q F)
    -- tax: needed to state the minor arc `PB` used in `M_eq`.
    (P_mem_Γ₁ : P ∈ (Γ₁ : Set Pt))
    -- tax: needed to make the chosen minor arc `PB` non-diametral.
    (PB_not_diam : ¬Γ₁.IsDiameter P B)
    (M_eq : M = (Sphere.Arc.minor P_mem_Γ₁ B_mem_Γ₁ PB_not_diam).midpoint)
    -- root: needed because `minor PB` need not be the arc avoiding `C` in both branches.
    (C_mem_arcPB_opposite :
      C ∈ (Sphere.Arc.minor P_mem_Γ₁ B_mem_Γ₁ PB_not_diam).opposite.interior)
    -- tax: needed to state the minor arc `QB` used in `N_eq`.
    (Q_mem_Γ₂ : Q ∈ (Γ₂ : Set Pt))
    -- tax: needed to make the chosen minor arc `QB` non-diametral.
    (QB_not_diam : ¬Γ₂.IsDiameter Q B)
    (N_eq : N = (Sphere.Arc.minor Q_mem_Γ₂ B_mem_Γ₂ QB_not_diam).midpoint)
    -- root: the symmetric position seed for `minor QB`.
    (F_mem_arcQB_opposite :
      F ∈ (Sphere.Arc.minor Q_mem_Γ₂ B_mem_Γ₂ QB_not_diam).opposite.interior)
    (CD_eq_EF : dist C D = dist E F) :
    Cospherical ({C, F, M, N} : Set Pt) :=
  ({ A, B, C, D, E, F, P, Q, M, N, Γ₁, Γ₂, A_mem_Γ₁, A_mem_Γ₂,
     B_mem_Γ₁, B_mem_Γ₂, A_ne_B, C_mem_Γ₁, D_mem_Γ₂, sbtw_C_B_D,
     E_mem_Γ₁, F_eq, E_not_mem_line_CD, P_eq, sbtw_C_P_F, Q_eq, sbtw_C_Q_F,
     P_mem_Γ₁, PB_not_diam, Q_mem_Γ₂, QB_not_diam, CD_eq_EF, M_eq,
     C_mem_arcPB_opposite, N_eq, F_mem_arcQB_opposite } : Cfg V Pt).result_cfg

/-- In the branch selected by the two through-arc seeds, the position seeds required by
`result` are theorems rather than hypotheses: `CD = EF` together with power-of-a-point
arguments forces both apex points onto the arcs opposite the chosen minor arcs. -/
theorem mem_arcPB_opposite_and_mem_arcQB_opposite_of_arc_seeds
    [Fact (finrank ℝ V = 2)]
    {A B C D E F P Q : Pt} {Γ₁ Γ₂ : Sphere Pt}
    (A_mem_Γ₁ : A ∈ (Γ₁ : Set Pt)) (A_mem_Γ₂ : A ∈ (Γ₂ : Set Pt))
    (B_mem_Γ₁ : B ∈ (Γ₁ : Set Pt)) (B_mem_Γ₂ : B ∈ (Γ₂ : Set Pt))
    (A_ne_B : A ≠ B)
    (C_mem_Γ₁ : C ∈ (Γ₁ : Set Pt)) (D_mem_Γ₂ : D ∈ (Γ₂ : Set Pt))
    (sbtw_C_B_D : Sbtw ℝ C B D)
    (C_ne_A : C ≠ A)
    (F_eq : F = Γ₂.secondInter B (E -ᵥ B))
    (E_not_mem_line_CD : E ∉ line[ℝ, C, D])
    (E_mem_arcACB_Γ₁ : E ∈ (Sphere.Arc.through A_mem_Γ₁ C_mem_Γ₁ B_mem_Γ₁
        C_ne_A sbtw_C_B_D.ne_left.symm).interior)
    (F_mem_arcABD_Γ₂ : F ∈ (Sphere.Arc.through A_mem_Γ₂ B_mem_Γ₂ D_mem_Γ₂
        A_ne_B.symm sbtw_C_B_D.ne_right).interior)
    (P_eq : P = Γ₁.secondInter C (F -ᵥ C))
    (sbtw_C_P_F : Sbtw ℝ C P F)
    (Q_eq : Q = Γ₂.secondInter F (C -ᵥ F))
    (sbtw_C_Q_F : Sbtw ℝ C Q F)
    (P_mem_Γ₁ : P ∈ (Γ₁ : Set Pt))
    (PB_not_diam : ¬Γ₁.IsDiameter P B)
    (Q_mem_Γ₂ : Q ∈ (Γ₂ : Set Pt))
    (QB_not_diam : ¬Γ₂.IsDiameter Q B)
    (CD_eq_EF : dist C D = dist E F) :
    C ∈ (Sphere.Arc.minor P_mem_Γ₁ B_mem_Γ₁ PB_not_diam).opposite.interior ∧
      F ∈ (Sphere.Arc.minor Q_mem_Γ₂ B_mem_Γ₂ QB_not_diam).opposite.interior := by
  let cfg : CfgArcACB V Pt :=
    { A, B, C, D, E, F, P, Q, Γ₁, Γ₂, A_mem_Γ₁, A_mem_Γ₂, B_mem_Γ₁, B_mem_Γ₂,
      A_ne_B, C_mem_Γ₁, D_mem_Γ₂, sbtw_C_B_D, E_mem_Γ₁ := E_mem_arcACB_Γ₁.1,
      F_eq, E_not_mem_line_CD, P_eq, sbtw_C_P_F, Q_eq, sbtw_C_Q_F, P_mem_Γ₁,
      PB_not_diam, Q_mem_Γ₂, QB_not_diam, CD_eq_EF, C_ne_A, E_mem_arcACB_Γ₁,
      F_mem_arcABD_Γ₂ }
  exact ⟨by simpa [CfgCore.arcPB] using cfg.C_mem_arcPB_opposite,
    by simpa [CfgCore.arcQB] using cfg.F_mem_arcQB_opposite⟩

end

end ChinaMO2010P1
