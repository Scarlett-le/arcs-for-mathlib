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
# Chinese MO 2012, Problem 1

## Reference

Chinese Mathematical Society, *China Mathematical Olympiad 2012, Problem 1*;
27th China Mathematical Olympiad (National High School Mathematics Winter Camp),
Xi'an, January 2012. Official problems and solutions in *Zouxiang IMO: Shuxue
Aolinpike Shiti Jijin (2012)*, East China Normal University Press, 2012 (in Chinese).
-/

open scoped Real EuclideanGeometry RealInnerProductSpace
open Affine EuclideanGeometry Module Sphere

namespace ChinaMO2012P1

variable {V Pt : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

noncomputable section

/-! ## Shared geometric helpers -/

section PlaneHelpers

variable [Fact (finrank ℝ V = 2)]

local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V Fact.out)⟩

/-- A tangent line to a circle puts any two non-tangent points of the circle on the same
strict side of that line.

This is the two-dimensional specialization of `Sphere.sSameSide_orthRadius_of_mem`. -/
theorem sSameSide_of_tangent_sphere {O : Sphere Pt} {A X U W : Pt}
    (hA : A ∈ (O : Set Pt)) (hU : U ∈ (O : Set Pt)) (hW : W ∈ (O : Set Pt))
    (htan : O.IsTangentAt A line[ℝ, A, X]) (hradius : O.radius ≠ 0)
    (hAX : A ≠ X) (hAU : A ≠ U) (hAW : A ≠ W) :
    (line[ℝ, A, X]).SSameSide U W := by
  have hfr : finrank ℝ (line[ℝ, A, X]).direction + 1 = finrank ℝ V := by
    rw [direction_affineSpan, vectorSpan_pair_rev,
      finrank_span_singleton (vsub_ne_zero.mpr hAX.symm), (Fact.out : finrank ℝ V = 2)]
  rw [htan.eq_orthRadius_of_finrank_add_one_eq hradius hfr]
  exact Sphere.sSameSide_orthRadius_of_mem hA hU hW hAU hAW

/-! ### Local oriented-angle helpers

These are problem-local scaffolding lemmas for branch and sign bookkeeping, not library
candidates.
-/

private lemma abs_add_sub_self {a c : ℝ}
    (hsign : (0 < a ∧ 0 < c) ∨ (a < 0 ∧ c < 0)) (hle : |a| ≤ |c|) :
    |a| + |c - a| = |c| := by
  rcases hsign with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · rw [abs_of_pos ha, abs_of_pos hc] at hle ⊢
    rw [abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_neg ha, abs_of_neg hc] at hle ⊢
    rw [abs_of_nonpos (by linarith)]
    ring

private lemma abs_toReal_add_abs_toReal_of_sign_eq {θ δ : Real.Angle}
    (h : θ.sign = (θ + δ).sign) (h0 : θ.sign ≠ 0)
    (hle_abs : |θ.toReal| ≤ |(θ + δ).toReal|) :
    |θ.toReal| + |δ.toReal| = |(θ + δ).toReal| := by
  have hθ_ne_pi : θ ≠ π := (Real.Angle.sign_ne_zero_iff.mp h0).2
  have hδ_ne_pi : δ ≠ π := by
    rintro rfl
    rw [Real.Angle.sign_add_pi] at h
    exact h0 (by simpa [SignType.self_eq_neg_iff] using h)
  have hto : (θ + δ).toReal = θ.toReal + δ.toReal :=
    Real.Angle.toReal_add_eq_toReal_add_toReal hθ_ne_pi hδ_ne_pi (.inr h)
  have hδeq : δ.toReal = (θ + δ).toReal - θ.toReal := by
    rw [hto]
    ring
  rw [hδeq]
  refine abs_add_sub_self ?_ hle_abs
  have hs_cases : θ.sign = 1 ∨ θ.sign = -1 := by
    revert h0
    generalize θ.sign = s
    decide +revert
  rcases hs_cases with hp | hn
  · exact Or.inl ⟨(Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr hp).1,
      (Real.Angle.toReal_mem_Ioo_iff_sign_pos.mpr (h ▸ hp)).1⟩
  · exact Or.inr ⟨Real.Angle.toReal_neg_iff_sign_neg.mpr hn,
      Real.Angle.toReal_neg_iff_sign_neg.mpr (h ▸ hn)⟩

/-- If two oriented angles from the same initial ray have the same nonzero sign and the first
unoriented angle is no larger than the second, then the intermediate ray splits the larger
unoriented angle. -/
theorem angle_add_of_oangle_sign_eq_of_angle_le {O X Y Z : Pt}
    (hs_ne : (∡ X O Y).sign ≠ 0)
    (hs : (∡ X O Y).sign = (∡ X O Z).sign)
    (hle : ∠ X O Y ≤ ∠ X O Z) :
    ∠ X O Y + ∠ Y O Z = ∠ X O Z := by
  have hXY_ne : ∡ X O Y ≠ 0 := (Real.Angle.sign_ne_zero_iff.mp hs_ne).1
  have hXZ_ne : ∡ X O Z ≠ 0 := (Real.Angle.sign_ne_zero_iff.mp (hs ▸ hs_ne)).1
  have hX : X ≠ O := left_ne_of_oangle_ne_zero hXY_ne
  have hY : Y ≠ O := right_ne_of_oangle_ne_zero hXY_ne
  have hZ : Z ≠ O := right_ne_of_oangle_ne_zero hXZ_ne
  rw [angle_eq_abs_oangle_toReal hX hY, angle_eq_abs_oangle_toReal hY hZ,
    angle_eq_abs_oangle_toReal hX hZ, ← oangle_add hX hY hZ]
  refine abs_toReal_add_abs_toReal_of_sign_eq ?_ hs_ne ?_
  · rw [oangle_add hX hY hZ]
    exact hs
  · rw [oangle_add hX hY hZ, ← angle_eq_abs_oangle_toReal hX hY,
      ← angle_eq_abs_oangle_toReal hX hZ]
    exact hle

/-- Same-sign rays split one of the two unoriented angles, without preselecting which one is
larger. -/
theorem angle_add_or_add_of_oangle_sign_eq {O X Y Z : Pt}
    (hs_ne : (∡ X O Y).sign ≠ 0)
    (hs : (∡ X O Y).sign = (∡ X O Z).sign) :
    ∠ X O Y + ∠ Y O Z = ∠ X O Z ∨
      ∠ X O Z + ∠ Z O Y = ∠ X O Y := by
  rcases le_total (∠ X O Y) (∠ X O Z) with hle | hle
  · exact Or.inl (angle_add_of_oangle_sign_eq_of_angle_le hs_ne hs hle)
  · exact Or.inr (angle_add_of_oangle_sign_eq_of_angle_le (hs ▸ hs_ne) hs.symm hle)

theorem sin_angle_eq_abs_sin_oangle {O X Y : Pt} (hX : X ≠ O) (hY : Y ≠ O) :
    Real.sin (∠ X O Y) = |Real.Angle.sin (∡ X O Y)| := by
  rw [angle_eq_abs_oangle_toReal hX hY,
    ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
    Real.Angle.sin_toReal]

end PlaneHelpers

/-- A bundled configuration for China MO 2012 P1.

This follows the `IMO 2019 Q2` / `jsm` style used elsewhere in the repository: the theorem
statement is first repackaged as a structure, and the proof is developed as named lemmas on that
structure.  This keeps the main angle chase readable and makes the remaining gaps local. -/
structure Cfg (V Pt : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
    [NormedAddTorsor V Pt] where
  (A B C D E P : Pt)
  (ω O₁ O₂ : Sphere Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  circumsphere_ABC_eq_ω :
    (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere = ω
  angle_A_gt_B : ∠ A B C < ∠ B A C
  angle_A_gt_C : ∠ A C B < ∠ B A C
  A_mem_ω : A ∈ (ω : Set Pt)
  B_mem_ω : B ∈ (ω : Set Pt)
  C_mem_ω : C ∈ (ω : Set Pt)
  A_ne_B : A ≠ B
  A_ne_C : A ≠ C
  B_ne_C : B ≠ C
  D_eq : D = (Sphere.Arc.through A_mem_ω B_mem_ω C_mem_ω A_ne_B.symm B_ne_C).midpoint
  E_eq : E = (Sphere.Arc.through A_mem_ω C_mem_ω B_mem_ω A_ne_C.symm B_ne_C.symm).midpoint
  D_on_arc_BC : D ∈ Sphere.Arc.avoiding B_mem_ω A_mem_ω C_mem_ω A_ne_B A_ne_C
  E_on_arc_BC : E ∈ Sphere.Arc.avoiding B_mem_ω A_mem_ω C_mem_ω A_ne_B A_ne_C
  A_mem_O₁ : A ∈ (O₁ : Set Pt)
  B_mem_O₁ : B ∈ (O₁ : Set Pt)
  O₁_tangent_AC : O₁.IsTangentAt A line[ℝ, A, C]
  A_mem_O₂ : A ∈ (O₂ : Set Pt)
  E_mem_O₂ : E ∈ (O₂ : Set Pt)
  O₂_tangent_AD : O₂.IsTangentAt A line[ℝ, A, D]
  P_mem_O₁ : P ∈ (O₁ : Set Pt)
  P_mem_O₂ : P ∈ (O₂ : Set Pt)
  P_ne_A : P ≠ A

namespace Cfg

variable (cfg : Cfg V Pt)

/-! ### Basic derived objects and nondegeneracy -/

/-- The arc `ABC`, from `A` to `C` through `B`.  Its midpoint is `D`. -/
def arcABC : Sphere.Arc cfg.ω :=
  Sphere.Arc.through cfg.A_mem_ω cfg.B_mem_ω cfg.C_mem_ω cfg.A_ne_B.symm cfg.B_ne_C

/-- The arc `ACB`, from `A` to `B` through `C`.  Its midpoint is `E`. -/
def arcACB : Sphere.Arc cfg.ω :=
  Sphere.Arc.through cfg.A_mem_ω cfg.C_mem_ω cfg.B_mem_ω cfg.A_ne_C.symm cfg.B_ne_C.symm

/-- The arc `BC` not containing `A`. -/
def arcBC : Sphere.Arc cfg.ω :=
  Sphere.Arc.avoiding cfg.B_mem_ω cfg.A_mem_ω cfg.C_mem_ω cfg.A_ne_B cfg.A_ne_C

section DimensionFree

theorem not_collinear_ABC : ¬ Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.mp cfg.affineIndependent_ABC

/-- The vertex `B` is not on the side line `AC`. -/
theorem B_not_mem_line_AC : cfg.B ∉ line[ℝ, cfg.A, cfg.C] := by
  intro hB
  have hcolBAC : Collinear ℝ ({cfg.B, cfg.A, cfg.C} : Set Pt) :=
    collinear_insert_of_mem_affineSpan_pair hB
  exact cfg.not_collinear_ABC (by
    simpa [Set.insert_comm] using hcolBAC)

@[simp] theorem arcABC_left : cfg.arcABC.left = cfg.A := rfl

@[simp] theorem arcACB_left : cfg.arcACB.left = cfg.A := rfl

@[simp] theorem arcBC_left : cfg.arcBC.left = cfg.B := rfl

theorem O₁_radius_ne_zero : cfg.O₁.radius ≠ 0 :=
  Sphere.radius_ne_zero_of_mem_of_mem_of_ne cfg.A_mem_O₁ cfg.B_mem_O₁ cfg.A_ne_B

/-- The vertex `C` is not on the side line `AB`. -/
theorem C_not_mem_line_AB : cfg.C ∉ line[ℝ, cfg.A, cfg.B] := by
  intro hC
  have hcolCAB : Collinear ℝ ({cfg.C, cfg.A, cfg.B} : Set Pt) :=
    collinear_insert_of_mem_affineSpan_pair hC
  have hcolACB : Collinear ℝ ({cfg.A, cfg.C, cfg.B} : Set Pt) := by
    rwa [Set.insert_comm cfg.C cfg.A ({cfg.B} : Set Pt)] at hcolCAB
  exact cfg.not_collinear_ABC (by simpa [Set.pair_comm cfg.C cfg.B] using hcolACB)

/-- The point `P` is not on the tangent line `AC` to `O₁`. -/
theorem P_not_mem_line_AC : cfg.P ∉ line[ℝ, cfg.A, cfg.C] := by
  intro hPline
  have hP_eq_A := cfg.O₁_tangent_AC.eq_of_mem_of_mem cfg.P_mem_O₁ hPline
  exact cfg.P_ne_A hP_eq_A

/-- The point `P` is not on the tangent line `AD` to `O₂`. -/
theorem P_not_mem_line_AD : cfg.P ∉ line[ℝ, cfg.A, cfg.D] := by
  intro hPline
  have hP_eq_A := cfg.O₂_tangent_AD.eq_of_mem_of_mem cfg.P_mem_O₂ hPline
  exact cfg.P_ne_A hP_eq_A

/-- A segment from `A` to a point on the opposite side of `BC` crosses the open chord `BC`. -/
theorem cross_BC {Z : Pt} (hZ : Z ∈ cfg.ω)
    (hopp : (line[ℝ, cfg.B, cfg.C]).SOppSide cfg.A Z) :
    ∃ X, Sbtw ℝ cfg.B X cfg.C ∧ Sbtw ℝ cfg.A X Z := by
  obtain ⟨X, hXline, hAXZ⟩ := hopp.exists_sbtw
  have hXin : dist cfg.ω.center X < cfg.ω.radius :=
    cfg.ω.dist_center_lt_radius_of_sbtw cfg.A_mem_ω hZ hAXZ
  have hcolBXC : Collinear ℝ ({cfg.B, X, cfg.C} : Set Pt) := by
    simpa [Set.insert_comm] using collinear_insert_of_mem_affineSpan_pair hXline
  exact ⟨X, sbtw_of_collinear_of_dist_center_lt_radius hcolBXC cfg.B_mem_ω
    (by rwa [dist_comm] at hXin) cfg.C_mem_ω cfg.B_ne_C, hAXZ⟩

/-- Crossing `BC` from `A` to `Z` puts `Z` on the same strict side of `AB` as `C`. -/
theorem sSameSide_AB_of_cross {Z X : Pt} (hZ_notAB : Z ∉ line[ℝ, cfg.A, cfg.B])
    (hBXC : Sbtw ℝ cfg.B X cfg.C) (hAXZ : Sbtw ℝ cfg.A X Z) :
    (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.C Z := by
  have hA_mem : cfg.A ∈ line[ℝ, cfg.A, cfg.B] :=
    left_mem_affineSpan_pair ℝ cfg.A cfg.B
  have hB_mem : cfg.B ∈ line[ℝ, cfg.A, cfg.B] :=
    right_mem_affineSpan_pair ℝ cfg.A cfg.B
  have hX_not : X ∉ line[ℝ, cfg.A, cfg.B] := by
    intro hX
    apply cfg.C_not_mem_line_AB
    have hC_BX : cfg.C ∈ line[ℝ, cfg.B, X] := hBXC.right_mem_affineSpan
    rwa [affineSpan_pair_eq_of_mem_of_mem_of_ne hB_mem hX hBXC.ne_left.symm] at hC_BX
  have hXC : (line[ℝ, cfg.A, cfg.B]).SSameSide X cfg.C :=
    ⟨hBXC.wbtw.wSameSide₂₃ hB_mem, hX_not, cfg.C_not_mem_line_AB⟩
  have hXZ : (line[ℝ, cfg.A, cfg.B]).SSameSide X Z :=
    ⟨hAXZ.wbtw.wSameSide₂₃ hA_mem, hX_not, hZ_notAB⟩
  exact hXC.symm.trans hXZ

end DimensionFree

section Plane

variable [Fact (finrank ℝ V = 2)]

local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation (Module.finBasisOfFinrankEq ℝ V Fact.out)⟩

@[simp] theorem arcABC_right : cfg.arcABC.right = cfg.C := by
  exact Sphere.Arc.through_right cfg.A_mem_ω cfg.B_mem_ω cfg.C_mem_ω
    cfg.A_ne_B.symm cfg.B_ne_C

@[simp] theorem arcACB_right : cfg.arcACB.right = cfg.B := by
  exact Sphere.Arc.through_right cfg.A_mem_ω cfg.C_mem_ω cfg.B_mem_ω
    cfg.A_ne_C.symm cfg.B_ne_C.symm

@[simp] theorem arcBC_right : cfg.arcBC.right = cfg.C := by
  exact Sphere.Arc.avoiding_right cfg.B_mem_ω cfg.A_mem_ω cfg.C_mem_ω
    cfg.A_ne_B cfg.A_ne_C

theorem arcABC_not_isDegenerate : ¬ cfg.arcABC.IsDegenerate := by
  rw [← Sphere.Arc.left_ne_right_iff_not_isDegenerate]
  simpa using cfg.A_ne_C

theorem arcACB_not_isDegenerate : ¬ cfg.arcACB.IsDegenerate := by
  rw [← Sphere.Arc.left_ne_right_iff_not_isDegenerate]
  simpa using cfg.A_ne_B

theorem D_mem_ω' : cfg.D ∈ cfg.ω := by
  rw [cfg.D_eq]
  exact Sphere.Arc.midpoint_mem cfg.arcABC cfg.arcABC_not_isDegenerate

theorem E_mem_ω' : cfg.E ∈ cfg.ω := by
  rw [cfg.E_eq]
  exact Sphere.Arc.midpoint_mem cfg.arcACB cfg.arcACB_not_isDegenerate

theorem D_ne_A : cfg.D ≠ cfg.A := by
  rw [cfg.D_eq]
  simpa using
    Sphere.Arc.midpoint_ne_left cfg.arcABC cfg.arcABC_not_isDegenerate

theorem D_ne_C : cfg.D ≠ cfg.C := by
  rw [cfg.D_eq]
  simpa using
    Sphere.Arc.midpoint_ne_right cfg.arcABC cfg.arcABC_not_isDegenerate

theorem E_ne_A : cfg.E ≠ cfg.A := by
  rw [cfg.E_eq]
  simpa using
    Sphere.Arc.midpoint_ne_left cfg.arcACB cfg.arcACB_not_isDegenerate

theorem E_ne_B : cfg.E ≠ cfg.B := by
  rw [cfg.E_eq]
  simpa using
    Sphere.Arc.midpoint_ne_right cfg.arcACB cfg.arcACB_not_isDegenerate

theorem O₂_radius_ne_zero : cfg.O₂.radius ≠ 0 :=
  Sphere.radius_ne_zero_of_mem_of_mem_of_ne cfg.A_mem_O₂ cfg.E_mem_O₂ cfg.E_ne_A.symm

/-- The point `B` is not on `O₂`; otherwise `O₂ = ω`, contradicting the tangency at `A` to `AD`
because `D` is another point of `ω` on that tangent line. -/
theorem B_not_mem_O₂ : cfg.B ∉ (cfg.O₂ : Set Pt) := by
  intro hB
  have hO₂_eq_ω : cfg.O₂ = cfg.ω := by
    by_contra hne
    haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
    have h :=
      eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
        (Fact.out : finrank ℝ V = 2) (s₁ := cfg.O₂) (s₂ := cfg.ω)
        (p₁ := cfg.A) (p₂ := cfg.E) (p := cfg.B)
        hne cfg.E_ne_A.symm cfg.A_mem_O₂ cfg.E_mem_O₂ hB
        cfg.A_mem_ω cfg.E_mem_ω' cfg.B_mem_ω
    rcases h with hBA | hBE
    · exact cfg.A_ne_B hBA.symm
    · exact cfg.E_ne_B hBE.symm
  have hD_eq_A : cfg.D = cfg.A := by
    refine cfg.O₂_tangent_AD.eq_of_mem_of_mem ?_ ?_
    · simpa [hO₂_eq_ω] using cfg.D_mem_ω'
    · exact right_mem_affineSpan_pair ℝ cfg.A cfg.D
  exact cfg.D_ne_A hD_eq_A

/-- The point `E` is not on `O₁`; otherwise `O₁ = ω`, contradicting the tangency at `A` to `AC`
because `C` is another point of `ω` on that tangent line. -/
theorem E_not_mem_O₁ : cfg.E ∉ (cfg.O₁ : Set Pt) := by
  intro hE
  have hO₁_eq_ω : cfg.O₁ = cfg.ω := by
    by_contra hne
    haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
    have h :=
      eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
        (Fact.out : finrank ℝ V = 2) (s₁ := cfg.O₁) (s₂ := cfg.ω)
        (p₁ := cfg.A) (p₂ := cfg.B) (p := cfg.E)
        hne cfg.A_ne_B cfg.A_mem_O₁ cfg.B_mem_O₁ hE
        cfg.A_mem_ω cfg.B_mem_ω cfg.E_mem_ω'
    rcases h with hEA | hEB
    · exact cfg.E_ne_A hEA
    · exact cfg.E_ne_B hEB
  have hC_eq_A : cfg.C = cfg.A := by
    refine cfg.O₁_tangent_AC.eq_of_mem_of_mem ?_ ?_
    · simpa [hO₁_eq_ω] using cfg.C_mem_ω
    · exact right_mem_affineSpan_pair ℝ cfg.A cfg.C
  exact cfg.A_ne_C hC_eq_A.symm

/-- The second intersection point cannot coincide with `B`. -/
theorem P_ne_B : cfg.P ≠ cfg.B := by
  intro h
  exact cfg.B_not_mem_O₂ (by simpa [h] using cfg.P_mem_O₂)

/-- The second intersection point cannot coincide with `E`. -/
theorem P_ne_E : cfg.P ≠ cfg.E := by
  intro h
  exact cfg.E_not_mem_O₁ (by simpa [h] using cfg.P_mem_O₁)

/-- The arc midpoint `E` is not on the chord line `AB`. -/
theorem E_not_mem_line_AB : cfg.E ∉ line[ℝ, cfg.A, cfg.B] := by
  rw [cfg.E_eq]
  simpa using
    Sphere.Arc.midpoint_not_mem_line cfg.arcACB cfg.arcACB_not_isDegenerate

/-- The arc midpoint `D` is not on the chord line `AC`. -/
theorem D_not_mem_line_AC : cfg.D ∉ line[ℝ, cfg.A, cfg.C] := by
  rw [cfg.D_eq]
  simpa using
    Sphere.Arc.midpoint_not_mem_line cfg.arcABC cfg.arcABC_not_isDegenerate

/-- The vertex `C` is not on the tangent line `AD`. -/
theorem C_not_mem_line_AD : cfg.C ∉ line[ℝ, cfg.A, cfg.D] := by
  intro hC
  apply cfg.D_not_mem_line_AC
  have hAC_eq_AD : line[ℝ, cfg.A, cfg.C] = line[ℝ, cfg.A, cfg.D] :=
    affineSpan_pair_eq_of_right_mem_of_ne hC cfg.A_ne_C.symm
  rw [hAC_eq_AD]
  exact right_mem_affineSpan_pair ℝ cfg.A cfg.D

/-- The point `P` is not on the chord line `AB` of `O₁`. -/
theorem P_not_mem_line_AB : cfg.P ∉ line[ℝ, cfg.A, cfg.B] := by
  intro hPline
  have hP_lor : cfg.P ∈ cfg.O₁.lineOrOrthRadius cfg.A cfg.B := by
    rwa [Sphere.lineOrOrthRadius_of_ne cfg.A_ne_B]
  have hP_eq :=
    (Sphere.mem_lineOrOrthRadius_inter_sphere_iff cfg.A_mem_O₁ cfg.B_mem_O₁
      cfg.P_mem_O₁).mp hP_lor
  rcases hP_eq with hPA | hPB
  · exact cfg.P_ne_A hPA
  · exact cfg.P_ne_B hPB

/-- The circle `O₁` is tangent to `AC` at `A`, so all non-`A` points of `O₁`
lie on one strict side of `AC`; in particular `P` and `B` do. -/
theorem P_sSameSide_AC_B : (line[ℝ, cfg.A, cfg.C]).SSameSide cfg.P cfg.B := by
  exact sSameSide_of_tangent_sphere cfg.A_mem_O₁ cfg.P_mem_O₁ cfg.B_mem_O₁
    cfg.O₁_tangent_AC cfg.O₁_radius_ne_zero cfg.A_ne_C cfg.P_ne_A.symm cfg.A_ne_B

/-- The point `E` is not on the tangent line `AD` to `O₂`. -/
theorem E_not_mem_line_AD : cfg.E ∉ line[ℝ, cfg.A, cfg.D] := by
  intro hEline
  have hE_eq_A := cfg.O₂_tangent_AD.eq_of_mem_of_mem cfg.E_mem_O₂ hEline
  exact cfg.E_ne_A hE_eq_A

/-- The circle `O₂` is tangent to `AD` at `A`, so `P` and `E` lie on the same
strict side of `AD`. -/
theorem P_sSameSide_AD_E : (line[ℝ, cfg.A, cfg.D]).SSameSide cfg.P cfg.E := by
  exact sSameSide_of_tangent_sphere cfg.A_mem_O₂ cfg.P_mem_O₂ cfg.E_mem_O₂
    cfg.O₂_tangent_AD cfg.O₂_radius_ne_zero cfg.D_ne_A.symm cfg.P_ne_A.symm
    cfg.E_ne_A.symm

/-- The points `A,B,E` are non-collinear. -/
theorem not_collinear_ABE : ¬ Collinear ℝ ({cfg.A, cfg.B, cfg.E} : Set Pt) := by
  intro hcol
  exact cfg.E_not_mem_line_AB
    (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)

/-- The points `A,B,P` are non-collinear. -/
theorem not_collinear_ABP : ¬ Collinear ℝ ({cfg.A, cfg.B, cfg.P} : Set Pt) := by
  intro hcol
  exact cfg.P_not_mem_line_AB
    (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)

/-- The oriented angle `ABP` is nondegenerate. -/
theorem oangle_ABP_sign_ne_zero : (∡ cfg.A cfg.B cfg.P).sign ≠ 0 := by
  simpa [oangle_sign_eq_zero_iff_collinear] using cfg.not_collinear_ABP

/-- The oriented angle `ABE` is nondegenerate. -/
theorem oangle_ABE_sign_ne_zero : (∡ cfg.A cfg.B cfg.E).sign ≠ 0 := by
  simpa [oangle_sign_eq_zero_iff_collinear] using cfg.not_collinear_ABE

/-! ### Arc-midpoint metric data

The old directed-angle midpoint lemmas have deliberately been removed. They were only
`oangle_add` decompositions and did not use the midpoint hypotheses. The load-bearing arc facts
are the metric ones below: each midpoint lies on the perpendicular bisector of its chord, exactly
as in `ARC/IncenterArcMidpoint.lean`.
-/

/-- `D`, the midpoint of the arc from `A` to `C` through `B`, is equidistant from `A` and `C`. -/
theorem dist_D_A_eq_dist_D_C : dist cfg.D cfg.A = dist cfg.D cfg.C := by
  have hmem := Sphere.Arc.midpoint_mem_perpBisector cfg.arcABC cfg.arcABC_not_isDegenerate
  have hdist := AffineSubspace.mem_perpBisector_iff_dist_eq.mp hmem
  simpa [cfg.D_eq] using hdist

/-- `E`, the midpoint of the arc from `A` to `B` through `C`, is equidistant from `A` and `B`. -/
theorem dist_E_A_eq_dist_E_B : dist cfg.E cfg.A = dist cfg.E cfg.B := by
  have hmem := Sphere.Arc.midpoint_mem_perpBisector cfg.arcACB cfg.arcACB_not_isDegenerate
  have hdist := AffineSubspace.mem_perpBisector_iff_dist_eq.mp hmem
  simpa [cfg.E_eq] using hdist

/-- The maximality of `∠A` keeps the arc-midpoint `D` away from the endpoint `B`. -/
theorem D_ne_B : cfg.D ≠ cfg.B := by
  intro h
  have hBA : dist cfg.B cfg.A = dist cfg.B cfg.C := by
    have hd := cfg.dist_D_A_eq_dist_D_C
    rwa [h] at hd
  have hang : ∠ cfg.B cfg.A cfg.C = ∠ cfg.B cfg.C cfg.A :=
    angle_eq_angle_of_dist_eq hBA
  rw [angle_comm cfg.B cfg.C cfg.A] at hang
  exact (ne_of_lt cfg.angle_A_gt_C) hang.symm

/-- The arc midpoint `D` is not on the chord line `AB`. -/
theorem D_not_mem_line_AB : cfg.D ∉ line[ℝ, cfg.A, cfg.B] := by
  rw [← Sphere.lineOrOrthRadius_of_ne (s := cfg.ω) cfg.A_ne_B]
  exact Sphere.notMem_lineOrOrthRadius_of_mem_sphere cfg.A_mem_ω cfg.D_mem_ω'
    cfg.B_mem_ω cfg.D_ne_A cfg.D_ne_B

/-- The maximality of `∠A` keeps the arc-midpoint `E` away from the endpoint `C`. -/
theorem E_ne_C : cfg.E ≠ cfg.C := by
  intro h
  have hCA : dist cfg.C cfg.A = dist cfg.C cfg.B := by
    have he := cfg.dist_E_A_eq_dist_E_B
    rwa [h] at he
  have hang : ∠ cfg.C cfg.A cfg.B = ∠ cfg.C cfg.B cfg.A :=
    angle_eq_angle_of_dist_eq hCA
  rw [angle_comm cfg.C cfg.A cfg.B, angle_comm cfg.C cfg.B cfg.A] at hang
  exact (ne_of_lt cfg.angle_A_gt_B) hang.symm

/-! ### Isosceles and arc-angle consequences

The first two lemmas are direct pons-asinorum consequences of the metric midpoint facts. The
next two are the official solution's arc-angle values; they still need the configuration/arc
bookkeeping connecting equal chords with the relevant inscribed angles on `ω`.
-/

/-- Base angles in the isosceles triangle `ADC`. -/
theorem angle_CAD_eq_ACD : ∠ cfg.C cfg.A cfg.D = ∠ cfg.A cfg.C cfg.D := by
  have h := angle_eq_angle_of_dist_eq cfg.dist_D_A_eq_dist_D_C
  simpa [angle_comm cfg.D cfg.A cfg.C, angle_comm cfg.D cfg.C cfg.A] using h

/-- Base angles in the isosceles triangle `AEB`. -/
theorem angle_BAE_eq_ABE : ∠ cfg.B cfg.A cfg.E = ∠ cfg.A cfg.B cfg.E := by
  have h := angle_eq_angle_of_dist_eq cfg.dist_E_A_eq_dist_E_B
  simpa [angle_comm cfg.E cfg.A cfg.B, angle_comm cfg.E cfg.B cfg.A] using h

/-- The specified point `C` is in the interior of the arc `ACB`. -/
theorem C_mem_arcACB_interior : cfg.C ∈ cfg.arcACB.interior := by
  exact Sphere.Arc.mem_interior_through cfg.A_mem_ω cfg.C_mem_ω cfg.B_mem_ω
    cfg.A_ne_C.symm cfg.B_ne_C.symm

/-- The midpoint `E` is an interior point of the nondegenerate arc `ACB`. -/
theorem E_mem_arcACB_interior : cfg.E ∈ cfg.arcACB.interior := by
  have hmem : cfg.E ∈ cfg.arcACB := by
    rw [cfg.E_eq]
    exact Sphere.Arc.midpoint_mem_arc cfg.arcACB cfg.arcACB_not_isDegenerate
  refine Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right
    hmem ?_ ?_
  · simpa using cfg.E_ne_A
  · simpa using cfg.E_ne_B

/-- The specified point `A` is in the interior of the arc opposite `arcBC`. -/
theorem A_mem_arcBC_opposite_interior : cfg.A ∈ cfg.arcBC.opposite.interior := by
  dsimp [arcBC]
  rw [Sphere.Arc.avoiding, Sphere.Arc.opposite_opposite]
  exact Sphere.Arc.mem_interior_through cfg.B_mem_ω cfg.A_mem_ω cfg.C_mem_ω
    cfg.A_ne_B cfg.A_ne_C

/-- The midpoint `D` is an interior point of the arc `BC` not containing `A`. -/
theorem D_mem_arcBC_interior : cfg.D ∈ cfg.arcBC.interior := by
  refine Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right
    cfg.D_on_arc_BC ?_ ?_
  · simpa using cfg.D_ne_B
  · simpa using cfg.D_ne_C

/-- The midpoint `E` is an interior point of the arc `BC` not containing `A`. -/
theorem E_mem_arcBC_interior : cfg.E ∈ cfg.arcBC.interior := by
  refine Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right
    cfg.E_on_arc_BC ?_ ?_
  · simpa using cfg.E_ne_B
  · simpa using cfg.E_ne_C

/-- Points `A` and `D` lie on opposite strict sides of the chord line `BC`. -/
theorem sOppSide_BC_A_D : (line[ℝ, cfg.B, cfg.C]).SOppSide cfg.A cfg.D := by
  have h := Sphere.Arc.sOppSide_of_mem_interior_of_mem_opposite_interior cfg.arcBC
    (by simpa using cfg.B_ne_C)
    cfg.D_mem_arcBC_interior cfg.A_mem_arcBC_opposite_interior
  simpa [Sphere.lineOrOrthRadius_of_ne cfg.B_ne_C] using h.symm

/-- Points `A` and `E` lie on opposite strict sides of the chord line `BC`. -/
theorem sOppSide_BC_A_E : (line[ℝ, cfg.B, cfg.C]).SOppSide cfg.A cfg.E := by
  have h := Sphere.Arc.sOppSide_of_mem_interior_of_mem_opposite_interior cfg.arcBC
    (by simpa using cfg.B_ne_C)
    cfg.E_mem_arcBC_interior cfg.A_mem_arcBC_opposite_interior
  simpa [Sphere.lineOrOrthRadius_of_ne cfg.B_ne_C] using h.symm

/-- The segment `AD` crosses the open chord `BC`. -/
theorem cross_BC_D : ∃ X, Sbtw ℝ cfg.B X cfg.C ∧ Sbtw ℝ cfg.A X cfg.D :=
  cfg.cross_BC cfg.D_mem_ω' cfg.sOppSide_BC_A_D

/-- The segment `AE` crosses the open chord `BC`. -/
theorem cross_BC_E : ∃ X, Sbtw ℝ cfg.B X cfg.C ∧ Sbtw ℝ cfg.A X cfg.E :=
  cfg.cross_BC cfg.E_mem_ω' cfg.sOppSide_BC_A_E

/-- The arc midpoint `D` lies on the same strict side of `AB` as `C`. -/
theorem C_sSameSide_AB_D : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.C cfg.D := by
  obtain ⟨X, hBXC, hAXD⟩ := cfg.cross_BC_D
  exact cfg.sSameSide_AB_of_cross cfg.D_not_mem_line_AB hBXC hAXD

/-- The arc midpoint `E` lies on the same strict side of `AB` as `C`. -/
theorem C_sSameSide_AB_E : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.C cfg.E := by
  obtain ⟨X, hBXC, hAXE⟩ := cfg.cross_BC_E
  exact cfg.sSameSide_AB_of_cross cfg.E_not_mem_line_AB hBXC hAXE

/-- The two arc midpoints are on the same strict side of `AB`. -/
theorem D_sSameSide_AB_E : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.D cfg.E :=
  cfg.C_sSameSide_AB_D.symm.trans cfg.C_sSameSide_AB_E

/-- The directed angles from `AB` to `AD` and `AE` have the same orientation. -/
theorem oangle_BAD_sign_eq_BAE :
    (∡ cfg.B cfg.A cfg.D).sign = (∡ cfg.B cfg.A cfg.E).sign := by
  have h := cfg.D_sSameSide_AB_E.oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
    (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
  simpa [oangle_rotate_sign cfg.B cfg.A cfg.D, oangle_rotate_sign cfg.B cfg.A cfg.E] using h.symm

/-- The directed angle from `AB` to `AD` is nondegenerate. -/
theorem oangle_BAD_sign_ne_zero : (∡ cfg.B cfg.A cfg.D).sign ≠ 0 := by
  intro hzero
  rw [oangle_sign_eq_zero_iff_collinear] at hzero
  exact cfg.D_not_mem_line_AB
    (hzero.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)

/-- The ray `AD` lies inside `∠BAC`. -/
theorem angle_BAD_add_DAC_eq_BAC :
    ∠ cfg.B cfg.A cfg.D + ∠ cfg.D cfg.A cfg.C = ∠ cfg.B cfg.A cfg.C := by
  obtain ⟨X, hBXC, hAXD⟩ := cfg.cross_BC_D
  have hsame : SameRay ℝ (X -ᵥ cfg.A) (cfg.D -ᵥ cfg.A) :=
    hAXD.wbtw.sameRay_vsub_left
  exact angle_add_angle_eq_of_sbtw_of_sameRay hBXC hsame cfg.D_ne_A

/-- The ray `AE` lies inside `∠BAC`. -/
theorem angle_BAE_add_EAC_eq_BAC :
    ∠ cfg.B cfg.A cfg.E + ∠ cfg.E cfg.A cfg.C = ∠ cfg.B cfg.A cfg.C := by
  obtain ⟨X, hBXC, hAXE⟩ := cfg.cross_BC_E
  have hsame : SameRay ℝ (X -ᵥ cfg.A) (cfg.E -ᵥ cfg.A) :=
    hAXE.wbtw.sameRay_vsub_left
  exact angle_add_angle_eq_of_sbtw_of_sameRay hBXC hsame cfg.E_ne_A

/-- The specified point `B` is in the interior of the arc `ABC`. -/
theorem B_mem_arcABC_interior : cfg.B ∈ cfg.arcABC.interior := by
  exact Sphere.Arc.mem_interior_through cfg.A_mem_ω cfg.B_mem_ω cfg.C_mem_ω
    cfg.A_ne_B.symm cfg.B_ne_C

/-- The midpoint `D` is an interior point of the nondegenerate arc `ABC`. -/
theorem D_mem_arcABC_interior : cfg.D ∈ cfg.arcABC.interior := by
  have hmem : cfg.D ∈ cfg.arcABC := by
    rw [cfg.D_eq]
    exact Sphere.Arc.midpoint_mem_arc cfg.arcABC cfg.arcABC_not_isDegenerate
  refine Sphere.Arc.mem_interior_of_mem_of_ne_left_of_ne_right
    hmem ?_ ?_
  · simpa using cfg.D_ne_A
  · simpa using cfg.D_ne_C

/-- The point `D` lies on the same strict side of the chord `AC` as `B`. -/
theorem B_sSameSide_AC_D : (line[ℝ, cfg.A, cfg.C]).SSameSide cfg.B cfg.D := by
  have hBss : (line[ℝ, cfg.A, cfg.C]).SSameSide cfg.arcABC.mid cfg.B := by
    have h := cfg.B_mem_arcABC_interior.2
    simpa [Sphere.lineOrOrthRadius_of_ne cfg.A_ne_C] using h
  have hDss : (line[ℝ, cfg.A, cfg.C]).SSameSide cfg.arcABC.mid cfg.D := by
    have h := cfg.D_mem_arcABC_interior.2
    simpa [Sphere.lineOrOrthRadius_of_ne cfg.A_ne_C] using h
  exact hBss.symm.trans hDss

/-- The sign of the oriented angle `ABC` is opposite to that of `DAC`. -/
theorem oangle_ABC_sign_eq_neg_DAC :
    (∡ cfg.A cfg.B cfg.C).sign = -(∡ cfg.D cfg.A cfg.C).sign := by
  have h := cfg.B_sSameSide_AC_D.oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.A cfg.C)
    (right_mem_affineSpan_pair ℝ cfg.A cfg.C)
  calc
    (∡ cfg.A cfg.B cfg.C).sign = (∡ cfg.A cfg.D cfg.C).sign := h.symm
    _ = (∡ cfg.C cfg.A cfg.D).sign := oangle_rotate_sign cfg.C cfg.A cfg.D
    _ = -(∡ cfg.D cfg.A cfg.C).sign := (oangle_swap₁₃_sign cfg.D cfg.A cfg.C).symm

/-- The directed angle `DAC` is nondegenerate. -/
theorem oangle_DAC_sign_ne_zero : (∡ cfg.D cfg.A cfg.C).sign ≠ 0 := by
  intro hzero
  rw [oangle_sign_eq_zero_iff_collinear] at hzero
  exact cfg.D_not_mem_line_AC
    (hzero.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_C)

/-- The angles `∠AEB` and `∠ACB` subtend the same chord `AB` on `ω`. -/
theorem angle_AEB_eq_ACB : ∠ cfg.A cfg.E cfg.B = ∠ cfg.A cfg.C cfg.B := by
  have h := Sphere.Arc.angle_eq_of_mem_opposite_interior cfg.arcACB.opposite
    (B₁ := cfg.E) (B₂ := cfg.C)
    (by simpa using cfg.E_mem_arcACB_interior)
    (by simpa using cfg.C_mem_arcACB_interior)
    (by simpa using cfg.E_ne_A)
    (by simpa using cfg.E_ne_B)
    (by simpa using cfg.A_ne_C.symm)
    (by simpa using cfg.B_ne_C.symm)
  simpa using h

/-- The angles `∠ADC` and `∠ABC` subtend the same chord `AC` on `ω`. -/
theorem angle_ADC_eq_ABC : ∠ cfg.A cfg.D cfg.C = ∠ cfg.A cfg.B cfg.C := by
  have h := Sphere.Arc.angle_eq_of_mem_opposite_interior cfg.arcABC.opposite
    (B₁ := cfg.D) (B₂ := cfg.B)
    (by simpa using cfg.D_mem_arcABC_interior)
    (by simpa using cfg.B_mem_arcABC_interior)
    (by simpa using cfg.D_ne_A)
    (by simpa using cfg.D_ne_C)
    (by simpa using cfg.A_ne_B.symm)
    (by simpa using cfg.B_ne_C)
  simpa using h

/-- Official step ② for `E`: `AE = EB` plus the inscribed angle on `ω`.

This is no longer a directed-angle midpoint statement. The missing work is to prove
`∠AEB = ∠ACB` from the common circumcircle and then use the triangle sum in isosceles `AEB`. -/
theorem angle_BAE :
    ∠ cfg.B cfg.A cfg.E = π / 2 - ∠ cfg.A cfg.C cfg.B / 2 := by
  have hsum :=
    angle_add_angle_add_angle_eq_pi (p₁ := cfg.B) (p₂ := cfg.A) cfg.E cfg.A_ne_B
  rw [angle_comm cfg.E cfg.B cfg.A, ← cfg.angle_BAE_eq_ABE, cfg.angle_AEB_eq_ACB] at hsum
  linarith

/-- Official step ② for `D`: `AD = DC` plus the inscribed angle on `ω`.

The missing work is the symmetric one: prove `∠ADC = ∠ABC` on the original circumcircle and use
the triangle sum in isosceles `ADC`. -/
theorem angle_CAD :
    ∠ cfg.C cfg.A cfg.D = π / 2 - ∠ cfg.A cfg.B cfg.C / 2 := by
  have hsum :=
    angle_add_angle_add_angle_eq_pi (p₁ := cfg.C) (p₂ := cfg.A) cfg.D cfg.A_ne_C
  rw [angle_comm cfg.D cfg.C cfg.A, ← cfg.angle_CAD_eq_ACD, cfg.angle_ADC_eq_ABC] at hsum
  linarith

theorem angle_BAD :
    ∠ cfg.B cfg.A cfg.D =
      ∠ cfg.B cfg.A cfg.C - (π / 2 - ∠ cfg.A cfg.B cfg.C / 2) := by
  have hsplit := cfg.angle_BAD_add_DAC_eq_BAC
  rw [angle_comm cfg.D cfg.A cfg.C, cfg.angle_CAD] at hsplit
  linarith

/-- Along the interior of `∠BAC`, the ray `AD` occurs before `AE`. -/
theorem angle_BAD_lt_BAE : ∠ cfg.B cfg.A cfg.D < ∠ cfg.B cfg.A cfg.E := by
  have hsum :=
    angle_add_angle_add_angle_eq_pi (p₁ := cfg.B) (p₂ := cfg.A) cfg.C cfg.A_ne_B
  rw [angle_comm cfg.C cfg.B cfg.A] at hsum
  have hBpos : 0 < ∠ cfg.A cfg.B cfg.C :=
    angle_pos_of_not_collinear cfg.not_collinear_ABC
  have hCpos : 0 < ∠ cfg.A cfg.C cfg.B :=
    angle_pos_of_not_collinear (by
      simpa [Set.pair_comm cfg.B cfg.C] using cfg.not_collinear_ABC)
  rw [cfg.angle_BAD, cfg.angle_BAE]
  linarith

/-- The ray `AD` lies between `AB` and `AE`. -/
theorem angle_BAD_add_DAE_eq_BAE :
    ∠ cfg.B cfg.A cfg.D + ∠ cfg.D cfg.A cfg.E = ∠ cfg.B cfg.A cfg.E :=
  angle_add_of_oangle_sign_eq_of_angle_le
    cfg.oangle_BAD_sign_ne_zero cfg.oangle_BAD_sign_eq_BAE
    (le_of_lt cfg.angle_BAD_lt_BAE)

/-- The ray `AE` lies between `AD` and `AC`. -/
theorem angle_DAE_add_EAC_eq_DAC :
    ∠ cfg.D cfg.A cfg.E + ∠ cfg.E cfg.A cfg.C = ∠ cfg.D cfg.A cfg.C := by
  have h₁ := cfg.angle_BAD_add_DAE_eq_BAE
  have h₂ := cfg.angle_BAE_add_EAC_eq_BAC
  have h₃ := cfg.angle_BAD_add_DAC_eq_BAC
  linarith

/-- The points `C` and `E` lie on the same strict side of `AD`. -/
theorem C_sSameSide_AD_E : (line[ℝ, cfg.A, cfg.D]).SSameSide cfg.C cfg.E := by
  have hsplit := cfg.angle_DAE_add_EAC_eq_DAC
  have hvec :
      InnerProductGeometry.angle (cfg.D -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) =
        InnerProductGeometry.angle (cfg.D -ᵥ cfg.A : V) (cfg.E -ᵥ cfg.A) +
          InnerProductGeometry.angle (cfg.E -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) := by
    simpa [EuclideanGeometry.angle] using hsplit.symm
  have hcone_or :=
    (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (y := cfg.E -ᵥ cfg.A)
      (x := cfg.D -ᵥ cfg.A)
      (z := cfg.C -ᵥ cfg.A)
      (vsub_ne_zero.mpr cfg.E_ne_A)).mp hvec
  have hnot_pi :
      InnerProductGeometry.angle (cfg.D -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) ≠ π := by
    have hnot : ¬ Collinear ℝ ({cfg.D, cfg.A, cfg.C} : Set Pt) := by
      intro hcol
      exact cfg.D_not_mem_line_AC
        (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_C)
    have h := angle_ne_pi_of_not_collinear hnot
    simpa [EuclideanGeometry.angle] using h
  rcases hcone_or with hpi | hcone
  · exact False.elim (hnot_pi hpi)
  rw [Submodule.mem_span_pair] at hcone
  obtain ⟨kD, kC, hk⟩ := hcone
  let Q : Pt := (kD : ℝ) • (cfg.D -ᵥ cfg.A : V) +ᵥ cfg.A
  have hQ_mem : Q ∈ line[ℝ, cfg.A, cfg.D] := by
    dsimp [Q]
    rw [vadd_left_mem_affineSpan_pair]
    exact ⟨(kD : ℝ), rfl⟩
  have hEvec : cfg.E -ᵥ Q = (kC : ℝ) • (cfg.C -ᵥ cfg.A : V) := by
    have hk' :
        (cfg.E -ᵥ cfg.A : V) =
          (kD : ℝ) • (cfg.D -ᵥ cfg.A : V) + (kC : ℝ) • (cfg.C -ᵥ cfg.A : V) := by
      simpa [NNReal.smul_def, add_comm] using hk.symm
    dsimp [Q]
    rw [vsub_vadd_eq_vsub_sub, hk']
    abel
  have hCvec : cfg.C -ᵥ cfg.A = (1 : ℝ) • (cfg.C -ᵥ cfg.A : V) := by
    rw [one_smul]
  have hEC : (line[ℝ, cfg.A, cfg.D]).SSameSide cfg.E cfg.C :=
    AffineSubspace.sSameSide_of_vsub_eq_smul hQ_mem
      (left_mem_affineSpan_pair ℝ cfg.A cfg.D)
      hEvec hCvec (by positivity) cfg.E_not_mem_line_AD cfg.C_not_mem_line_AD
  exact hEC.symm

/-- The second intersection point `P` lies on the same side of `AD` as `C`. -/
theorem P_sSameSide_AD_C : (line[ℝ, cfg.A, cfg.D]).SSameSide cfg.P cfg.C :=
  cfg.P_sSameSide_AD_E.trans cfg.C_sSameSide_AD_E.symm

theorem oangle_DAC_sign_eq_BAC :
    (∡ cfg.D cfg.A cfg.C).sign = (∡ cfg.B cfg.A cfg.C).sign := by
  have hABC_neg_BAC :
      (∡ cfg.A cfg.B cfg.C).sign = -(∡ cfg.B cfg.A cfg.C).sign := by
    calc
      (∡ cfg.A cfg.B cfg.C).sign = (∡ cfg.B cfg.C cfg.A).sign :=
        (oangle_rotate_sign cfg.A cfg.B cfg.C).symm
      _ = (∡ cfg.C cfg.A cfg.B).sign :=
        (oangle_rotate_sign cfg.B cfg.C cfg.A).symm
      _ = -(∡ cfg.B cfg.A cfg.C).sign :=
        (oangle_swap₁₃_sign cfg.B cfg.A cfg.C).symm
  have h := cfg.oangle_ABC_sign_eq_neg_DAC
  rw [hABC_neg_BAC] at h
  have h' := congrArg Neg.neg h
  simpa [neg_neg] using h'.symm

theorem oangle_DAE_sign_eq_BAC :
    (∡ cfg.D cfg.A cfg.E).sign = (∡ cfg.B cfg.A cfg.C).sign := by
  have hside := cfg.C_sSameSide_AD_E.oangle_sign_eq
    (left_mem_affineSpan_pair ℝ cfg.A cfg.D)
    (right_mem_affineSpan_pair ℝ cfg.A cfg.D)
  calc
    (∡ cfg.D cfg.A cfg.E).sign = (∡ cfg.A cfg.E cfg.D).sign :=
      (oangle_rotate_sign cfg.D cfg.A cfg.E).symm
    _ = (∡ cfg.A cfg.C cfg.D).sign := hside
    _ = (∡ cfg.D cfg.A cfg.C).sign := oangle_rotate_sign cfg.D cfg.A cfg.C
    _ = (∡ cfg.B cfg.A cfg.C).sign := cfg.oangle_DAC_sign_eq_BAC

/-! The following coordinate lemmas package the remaining side bookkeeping around `P`.  We use
the non-collinear pair `(AD, AC)` as a temporary basis: `AD` lies in the positive cone generated
by `AB` and `AC`, while the two tangent-circle side facts put `P` in the positive cone generated
by `AD` and `AC`. -/

theorem span_DA_CA_eq_top :
    Submodule.span ℝ ({cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V) = ⊤ := by
  have hLI :
      LinearIndependent ℝ ![cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A] := by
    have hind : AffineIndependent ℝ ![cfg.A, cfg.D, cfg.C] := by
      refine affineIndependent_iff_not_collinear_set.mpr ?_
      intro hcol
      exact cfg.D_not_mem_line_AC
        (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_C)
    have hLI' := (affineIndependent_iff_linearIndependent_vsub ℝ ![cfg.A, cfg.D, cfg.C] 0).mp hind
    have hLI'' := hLI'.comp (finSuccAboveEquiv (0 : Fin 3)) (finSuccAboveEquiv (0 : Fin 3)).injective
    convert hLI'' using 2
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv_apply, Fin.zero_succAbove]
  have hspan_finrank :
      Module.finrank ℝ (Submodule.span ℝ ({cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V)) = 2 := by
    have hrange :
        Set.range ![cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A] =
          ({cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V) := by
      ext x
      constructor <;> intro h <;> simpa [or_comm] using h
    have hcard := linearIndependent_iff_card_eq_finrank_span.mp hLI
    rw [← Set.finrank, ← hrange]
    simpa using hcard.symm
  haveI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  exact Submodule.eq_top_of_finrank_eq (by
    rw [hspan_finrank, (Fact.out : Module.finrank ℝ V = 2)])

theorem P_vsub_A_mem_span_DA_CA :
    cfg.P -ᵥ cfg.A ∈ Submodule.span ℝ ({cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V) := by
  rw [cfg.span_DA_CA_eq_top]
  exact Submodule.mem_top

/-- The ray `AD` lies in the positive cone generated by `AB` and `AC`. -/
theorem D_pos_coords_BA_CA :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      cfg.D -ᵥ cfg.A = r • (cfg.B -ᵥ cfg.A : V) + s • (cfg.C -ᵥ cfg.A : V) := by
  have hvec :
      InnerProductGeometry.angle (cfg.B -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) =
        InnerProductGeometry.angle (cfg.B -ᵥ cfg.A : V) (cfg.D -ᵥ cfg.A) +
          InnerProductGeometry.angle (cfg.D -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) := by
    simpa [EuclideanGeometry.angle] using cfg.angle_BAD_add_DAC_eq_BAC.symm
  have hcone_or :=
    (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (y := cfg.D -ᵥ cfg.A)
      (x := cfg.B -ᵥ cfg.A)
      (z := cfg.C -ᵥ cfg.A)
      (vsub_ne_zero.mpr cfg.D_ne_A)).mp hvec
  have hnot_pi :
      InnerProductGeometry.angle (cfg.B -ᵥ cfg.A : V) (cfg.C -ᵥ cfg.A) ≠ π := by
    have hnot : ¬ Collinear ℝ ({cfg.B, cfg.A, cfg.C} : Set Pt) := by
      intro hcol
      exact cfg.B_not_mem_line_AC
        (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_C)
    have h := angle_ne_pi_of_not_collinear hnot
    simpa [EuclideanGeometry.angle] using h
  rcases hcone_or with hpi | hcone
  · exact False.elim (hnot_pi hpi)
  rw [Submodule.mem_span_pair] at hcone
  obtain ⟨r, s, hrs⟩ := hcone
  have hD :
      cfg.D -ᵥ cfg.A =
        (r : ℝ) • (cfg.B -ᵥ cfg.A : V) + (s : ℝ) • (cfg.C -ᵥ cfg.A : V) := by
    simpa [NNReal.smul_def, add_comm] using hrs.symm
  have hr_ne : (r : ℝ) ≠ 0 := by
    intro hr0
    apply cfg.D_not_mem_line_AC
    rw [← vsub_vadd cfg.D cfg.A, vadd_left_mem_affineSpan_pair]
    refine ⟨(s : ℝ), ?_⟩
    rw [hD, hr0, zero_smul, zero_add]
  have hs_ne : (s : ℝ) ≠ 0 := by
    intro hs0
    apply cfg.D_not_mem_line_AB
    rw [← vsub_vadd cfg.D cfg.A, vadd_left_mem_affineSpan_pair]
    refine ⟨(r : ℝ), ?_⟩
    rw [hD, hs0, zero_smul, add_zero]
  have hr_pos : 0 < (r : ℝ) := lt_of_le_of_ne r.2 (Ne.symm hr_ne)
  have hs_pos : 0 < (s : ℝ) := lt_of_le_of_ne s.2 (Ne.symm hs_ne)
  exact ⟨(r : ℝ), (s : ℝ), hr_pos, hs_pos, hD⟩

/-- In the basis formed by the rays `AD` and `AC`, the point `P` has positive coordinates. -/
theorem P_pos_coords_DA_CA :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      cfg.P -ᵥ cfg.A = u • (cfg.D -ᵥ cfg.A : V) + v • (cfg.C -ᵥ cfg.A : V) := by
  obtain ⟨u, v, huv⟩ := (Submodule.mem_span_pair.mp cfg.P_vsub_A_mem_span_DA_CA)
  let d : V := cfg.D -ᵥ cfg.A
  let c : V := cfg.C -ᵥ cfg.A
  have hP : cfg.P -ᵥ cfg.A = u • d + v • c := by
    dsimp [d, c]
    exact huv.symm
  have hAP : cfg.A -ᵥ cfg.P = (-u) • d + (-v) • c := by
    rw [← neg_vsub_eq_vsub_rev cfg.P cfg.A, hP, neg_add, neg_smul, neg_smul]
  have hDP : cfg.D -ᵥ cfg.P = (1 - u) • d + (-v) • c := by
    rw [← vsub_sub_vsub_cancel_right cfg.D cfg.P cfg.A, hP]
    dsimp [d, c]
    module
  have hCP : cfg.C -ᵥ cfg.P = (-u) • d + (1 - v) • c := by
    rw [← vsub_sub_vsub_cancel_right cfg.C cfg.P cfg.A, hP]
    dsimp [d, c]
    module
  have hAPD_sign :
      (∡ cfg.A cfg.P cfg.D).sign = SignType.sign v * (∡ cfg.D cfg.A cfg.C).sign := by
    rw [EuclideanGeometry.oangle]
    change (o.oangle (cfg.A -ᵥ cfg.P) (cfg.D -ᵥ cfg.P)).sign =
      SignType.sign v * (o.oangle d c).sign
    rw [hAP, hDP, o.oangle_sign_smul_add_smul_smul_add_smul]
    congr 1
    ring_nf
  have hAPC_sign :
      (∡ cfg.A cfg.P cfg.C).sign = -SignType.sign u * (∡ cfg.D cfg.A cfg.C).sign := by
    rw [EuclideanGeometry.oangle]
    change (o.oangle (cfg.A -ᵥ cfg.P) (cfg.C -ᵥ cfg.P)).sign =
      -SignType.sign u * (o.oangle d c).sign
    rw [hAP, hCP, o.oangle_sign_smul_add_smul_smul_add_smul]
    rw [show (-u) * (1 - v) - (-v) * (-u) = -u by ring_nf, Left.sign_neg]
  have hv_sign : SignType.sign v = 1 := by
    have hside := cfg.P_sSameSide_AD_C.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.D)
      (right_mem_affineSpan_pair ℝ cfg.A cfg.D)
    have hrot : (∡ cfg.A cfg.C cfg.D).sign = (∡ cfg.D cfg.A cfg.C).sign := by
      exact oangle_rotate_sign cfg.D cfg.A cfg.C
    rw [hrot, hAPD_sign] at hside
    have hb_ne := cfg.oangle_DAC_sign_ne_zero
    revert hside hb_ne
    generalize SignType.sign v = sv
    generalize (∡ cfg.D cfg.A cfg.C).sign = sb
    decide +revert
  have hu_sign : SignType.sign u = 1 := by
    have hside := cfg.P_sSameSide_AC_B.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.C)
      (right_mem_affineSpan_pair ℝ cfg.A cfg.C)
    rw [cfg.oangle_ABC_sign_eq_neg_DAC, hAPC_sign] at hside
    have hb_ne := cfg.oangle_DAC_sign_ne_zero
    revert hside hb_ne
    generalize SignType.sign u = su
    generalize (∡ cfg.D cfg.A cfg.C).sign = sb
    decide +revert
  have hu_pos : 0 < u := sign_eq_one_iff.mp hu_sign
  have hv_pos : 0 < v := sign_eq_one_iff.mp hv_sign
  exact ⟨u, v, hu_pos, hv_pos, hP⟩

theorem angle_DAP_add_PAC_eq_DAC :
    ∠ cfg.D cfg.A cfg.P + ∠ cfg.P cfg.A cfg.C = ∠ cfg.D cfg.A cfg.C := by
  obtain ⟨u, v, hu, hv, hP⟩ := cfg.P_pos_coords_DA_CA
  have hcone :
      (cfg.P -ᵥ cfg.A : V) ∈
        Submodule.span NNReal ({cfg.D -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨u, le_of_lt hu⟩, ⟨v, le_of_lt hv⟩, ?_⟩
    simpa [NNReal.smul_def] using hP.symm
  have hvec :=
    (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (y := cfg.P -ᵥ cfg.A)
      (x := cfg.D -ᵥ cfg.A)
      (z := cfg.C -ᵥ cfg.A)
      (vsub_ne_zero.mpr cfg.P_ne_A)).mpr (Or.inr hcone)
  simpa [EuclideanGeometry.angle] using hvec.symm

/-- In the basis formed by the sides `AB` and `AC`, the point `P` has positive coordinates. -/
theorem P_pos_coords_BA_CA :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      cfg.P -ᵥ cfg.A = α • (cfg.B -ᵥ cfg.A : V) + β • (cfg.C -ᵥ cfg.A : V) := by
  obtain ⟨r, s, hr, hs, hD⟩ := cfg.D_pos_coords_BA_CA
  obtain ⟨u, v, hu, hv, hP_D⟩ := cfg.P_pos_coords_DA_CA
  refine ⟨u * r, u * s + v, mul_pos hu hr, add_pos (mul_pos hu hs) hv, ?_⟩
  rw [hP_D, hD]
  module

theorem P_sSameSide_AB_C : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.P cfg.C := by
  obtain ⟨α, β, hα, hβ, hP⟩ := cfg.P_pos_coords_BA_CA
  let Q : Pt := α • (cfg.B -ᵥ cfg.A : V) +ᵥ cfg.A
  have hQ_mem : Q ∈ line[ℝ, cfg.A, cfg.B] := by
    dsimp [Q]
    rw [vadd_left_mem_affineSpan_pair]
    exact ⟨α, rfl⟩
  have hPvec : cfg.P -ᵥ Q = β • (cfg.C -ᵥ cfg.A : V) := by
    dsimp [Q]
    rw [vsub_vadd_eq_vsub_sub, hP]
    module
  have hCvec : cfg.C -ᵥ cfg.A = (1 : ℝ) • (cfg.C -ᵥ cfg.A : V) := by
    rw [one_smul]
  exact AffineSubspace.sSameSide_of_vsub_eq_smul hQ_mem
    (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
    hPvec hCvec (by positivity) cfg.P_not_mem_line_AB cfg.C_not_mem_line_AB

theorem P_sSameSide_AB_E : (line[ℝ, cfg.A, cfg.B]).SSameSide cfg.P cfg.E :=
  cfg.P_sSameSide_AB_C.trans cfg.C_sSameSide_AB_E

theorem angle_BAP_add_PAC_eq_BAC :
    ∠ cfg.B cfg.A cfg.P + ∠ cfg.P cfg.A cfg.C = ∠ cfg.B cfg.A cfg.C := by
  obtain ⟨α, β, hα, hβ, hP⟩ := cfg.P_pos_coords_BA_CA
  have hcone :
      (cfg.P -ᵥ cfg.A : V) ∈
        Submodule.span NNReal ({cfg.B -ᵥ cfg.A, cfg.C -ᵥ cfg.A} : Set V) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨α, le_of_lt hα⟩, ⟨β, le_of_lt hβ⟩, ?_⟩
    simpa [NNReal.smul_def] using hP.symm
  have hvec :=
    (InnerProductGeometry.angle_eq_angle_add_angle_iff
      (y := cfg.P -ᵥ cfg.A)
      (x := cfg.B -ᵥ cfg.A)
      (z := cfg.C -ᵥ cfg.A)
      (vsub_ne_zero.mpr cfg.P_ne_A)).mpr (Or.inr hcone)
  simpa [EuclideanGeometry.angle] using hvec.symm

/-- The directed angle `BAC` is nondegenerate. -/
theorem oangle_BAC_sign_ne_zero : (∡ cfg.B cfg.A cfg.C).sign ≠ 0 := by
  intro hzero
  rw [oangle_sign_eq_zero_iff_collinear] at hzero
  exact cfg.B_not_mem_line_AC
    (hzero.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_C)

/-- The angle `APB` has the same orientation as `BAC`. -/
theorem oangle_APB_sign_eq_BAC :
    (∡ cfg.A cfg.P cfg.B).sign = (∡ cfg.B cfg.A cfg.C).sign := by
  obtain ⟨α, β, hα, hβ, hP⟩ := cfg.P_pos_coords_BA_CA
  let b : V := cfg.B -ᵥ cfg.A
  let c : V := cfg.C -ᵥ cfg.A
  have hAP : cfg.A -ᵥ cfg.P = (-α) • b + (-β) • c := by
    rw [← neg_vsub_eq_vsub_rev cfg.P cfg.A, hP]
    dsimp [b, c]
    module
  have hBP : cfg.B -ᵥ cfg.P = (1 - α) • b + (-β) • c := by
    rw [← vsub_sub_vsub_cancel_right cfg.B cfg.P cfg.A, hP]
    dsimp [b, c]
    module
  rw [EuclideanGeometry.oangle]
  change (o.oangle (cfg.A -ᵥ cfg.P) (cfg.B -ᵥ cfg.P)).sign = (o.oangle b c).sign
  rw [hAP, hBP, o.oangle_sign_smul_add_smul_smul_add_smul]
  rw [show (-α) * (-β) - (-β) * (1 - α) = β by ring_nf,
    sign_eq_one_iff.mpr hβ]
  simp

/-- The tangent-chord equality for chord `AP` is on the same-sign branch. -/
theorem oangle_ABP_sign_eq_CAP :
    (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.C cfg.A cfg.P).sign := by
  obtain ⟨r, s, hr, hs, hD⟩ := cfg.D_pos_coords_BA_CA
  obtain ⟨u, v, hu, hv, hP_D⟩ := cfg.P_pos_coords_DA_CA
  let b : V := cfg.B -ᵥ cfg.A
  let c : V := cfg.C -ᵥ cfg.A
  let α : ℝ := u * r
  let β : ℝ := u * s + v
  have hα_pos : 0 < α := by
    dsimp [α]
    exact mul_pos hu hr
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact add_pos (mul_pos hu hs) hv
  have hP :
      cfg.P -ᵥ cfg.A = α • b + β • c := by
    dsimp [α, β, b, c]
    rw [hP_D, hD]
    module
  have hPB :
      cfg.P -ᵥ cfg.B = (α - 1) • b + β • c := by
    rw [← vsub_sub_vsub_cancel_right cfg.P cfg.B cfg.A, hP]
    dsimp [b, c]
    module
  have hABP : (∡ cfg.A cfg.B cfg.P).sign = -(∡ cfg.B cfg.A cfg.C).sign := by
    rw [EuclideanGeometry.oangle]
    change (o.oangle (cfg.A -ᵥ cfg.B) (cfg.P -ᵥ cfg.B)).sign =
      -(o.oangle b c).sign
    rw [hPB]
    rw [show cfg.A -ᵥ cfg.B = (-1 : ℝ) • b + (0 : ℝ) • c by
      dsimp [b]
      rw [← neg_vsub_eq_vsub_rev cfg.B cfg.A]
      module]
    rw [o.oangle_sign_smul_add_smul_smul_add_smul]
    rw [show (-1 : ℝ) * β - 0 * (α - 1) = -β by ring_nf, Left.sign_neg,
      sign_eq_one_iff.mpr hβ_pos]
    simp
  have hCAP : (∡ cfg.C cfg.A cfg.P).sign = -(∡ cfg.B cfg.A cfg.C).sign := by
    have hP' : cfg.P -ᵥ cfg.A = β • c + α • b := by
      rw [hP]
      module
    rw [EuclideanGeometry.oangle]
    change (o.oangle c (cfg.P -ᵥ cfg.A)).sign = -(o.oangle b c).sign
    rw [hP', o.oangle_sign_smul_add_smul_right]
    rw [sign_eq_one_iff.mpr hα_pos, one_mul, o.oangle_rev, Real.Angle.sign_neg]
  rw [hABP, hCAP]

/-- `O₁`, chord `AB`: the directed core behind `angle_APB`. -/
theorem tangent_chord_O₁_AB_directed :
    (2 : ℤ) • ∡ cfg.C cfg.A cfg.B = (2 : ℤ) • ∡ cfg.A cfg.P cfg.B := by
  exact Sphere.two_zsmul_oangle_tangent_eq cfg.A_mem_O₁ cfg.B_mem_O₁ cfg.P_mem_O₁
    cfg.O₁_tangent_AC cfg.A_ne_C.symm cfg.P_ne_A cfg.P_ne_B cfg.A_ne_B.symm

/-- `O₁`, chord `AP`: the directed core behind `angle_ABP_eq_CAP`. -/
theorem tangent_chord_O₁_AP_directed :
    (2 : ℤ) • ∡ cfg.C cfg.A cfg.P = (2 : ℤ) • ∡ cfg.A cfg.B cfg.P := by
  exact Sphere.two_zsmul_oangle_tangent_eq cfg.A_mem_O₁ cfg.P_mem_O₁ cfg.B_mem_O₁
    cfg.O₁_tangent_AC cfg.A_ne_C.symm cfg.A_ne_B.symm cfg.P_ne_B.symm cfg.P_ne_A

/-- `O₂`, chord `AE`: the directed core behind `angle_APE`. -/
theorem tangent_chord_O₂_AE_directed :
    (2 : ℤ) • ∡ cfg.D cfg.A cfg.E = (2 : ℤ) • ∡ cfg.A cfg.P cfg.E := by
  exact Sphere.two_zsmul_oangle_tangent_eq cfg.A_mem_O₂ cfg.E_mem_O₂ cfg.P_mem_O₂
    cfg.O₂_tangent_AD cfg.D_ne_A cfg.P_ne_A cfg.P_ne_E cfg.E_ne_A

/-! ### Tangent-chord and configuration milestones

These replace the unusable pure `(2 : ℤ) • ∡` chase. The tangent data is used in unsigned-angle
form, while the hypotheses `∠A` largest and `D,E ∈ arcBC` are responsible for the ray order and
branch choices.
-/

/-- Tangent-chord theorem on `O₁`: the chord `AB` gives the angle at `P`. -/
theorem angle_APB :
    ∠ cfg.A cfg.P cfg.B = π - ∠ cfg.B cfg.A cfg.C := by
  have hsupp : ∠ cfg.A cfg.P cfg.B + ∠ cfg.B cfg.A cfg.C = π := by
    let θ : Real.Angle := ∡ cfg.A cfg.P cfg.B
    let ψ : Real.Angle := ∡ cfg.B cfg.A cfg.C
    have htwo_sum : (2 : ℤ) • (θ + ψ) = 0 := by
      dsimp [θ, ψ]
      have htwo := cfg.tangent_chord_O₁_AB_directed
      rw [oangle_rev cfg.B cfg.A cfg.C, smul_neg] at htwo
      rw [smul_add, ← htwo]
      abel
    have hsign : θ.sign = ψ.sign := by
      dsimp [θ, ψ]
      exact cfg.oangle_APB_sign_eq_BAC
    have hne : θ.sign ≠ 0 := by
      rw [hsign]
      dsimp [ψ]
      exact cfg.oangle_BAC_sign_ne_zero
    have habs :=
      Real.Angle.abs_toReal_add_abs_toReal_eq_pi_of_two_zsmul_add_eq_zero_of_sign_eq
        htwo_sum hsign hne
    rw [angle_eq_abs_oangle_toReal cfg.P_ne_A.symm cfg.P_ne_B.symm,
      angle_eq_abs_oangle_toReal cfg.A_ne_B.symm cfg.A_ne_C.symm]
    exact habs
  linarith

/-- Tangent-chord theorem on `O₁`: the chord `AP` identifies the angle at `B`. -/
theorem angle_ABP_eq_CAP :
    ∠ cfg.A cfg.B cfg.P = ∠ cfg.C cfg.A cfg.P := by
  have hsign : (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.C cfg.A cfg.P).sign := by
    exact cfg.oangle_ABP_sign_eq_CAP
  have ho : ∡ cfg.A cfg.B cfg.P = ∡ cfg.C cfg.A cfg.P := by
    exact (Real.Angle.two_zsmul_eq_iff_eq cfg.oangle_ABP_sign_ne_zero hsign).mp
      cfg.tangent_chord_O₁_AP_directed.symm
  rw [angle_eq_abs_oangle_toReal cfg.A_ne_B cfg.P_ne_B,
    angle_eq_abs_oangle_toReal cfg.A_ne_C.symm cfg.P_ne_A, ho]

/-- The fixed angle between the two arc-midpoint rays at `A`. -/
theorem angle_DAE :
    ∠ cfg.D cfg.A cfg.E = π / 2 - ∠ cfg.B cfg.A cfg.C / 2 := by
  have hdecomp :
      ∠ cfg.D cfg.A cfg.E =
        ∠ cfg.B cfg.A cfg.E + ∠ cfg.C cfg.A cfg.D - ∠ cfg.B cfg.A cfg.C := by
    have hsplit₁ := cfg.angle_BAD_add_DAE_eq_BAE
    have hsplit₂ :
        ∠ cfg.B cfg.A cfg.D + ∠ cfg.C cfg.A cfg.D = ∠ cfg.B cfg.A cfg.C := by
      simpa [angle_comm cfg.D cfg.A cfg.C] using cfg.angle_BAD_add_DAC_eq_BAC
    linarith
  have hABC_sum :=
    angle_add_angle_add_angle_eq_pi (p₁ := cfg.B) (p₂ := cfg.A) cfg.C cfg.A_ne_B
  rw [angle_comm cfg.C cfg.B cfg.A] at hABC_sum
  rw [hdecomp, cfg.angle_BAE, cfg.angle_CAD]
  linarith

theorem two_zsmul_oangle_DAE_eq_oangle_APB :
    (2 : ℤ) • ∡ cfg.D cfg.A cfg.E = ∡ cfg.A cfg.P cfg.B := by
  let ψ : Real.Angle := ∡ cfg.D cfg.A cfg.E
  let θ : Real.Angle := ∡ cfg.A cfg.P cfg.B
  have hψ_abs_lt : |ψ.toReal| < π / 2 := by
    have hA_pos : 0 < ∠ cfg.B cfg.A cfg.C :=
      angle_pos_of_not_collinear (by
        simpa [Set.insert_comm] using cfg.not_collinear_ABC)
    rw [show |ψ.toReal| = ∠ cfg.D cfg.A cfg.E by
      dsimp [ψ]
      rw [angle_eq_abs_oangle_toReal cfg.D_ne_A cfg.E_ne_A],
      cfg.angle_DAE]
    linarith
  have hψ_interval : ψ.toReal ∈ Set.Ioc (-π / 2) (π / 2) := by
    have h := abs_lt.mp hψ_abs_lt
    exact ⟨by linarith [h.1], le_of_lt h.2⟩
  have htwo_toReal : ((2 : ℤ) • ψ).toReal = 2 * ψ.toReal :=
    (Real.Angle.two_zsmul_toReal_eq_two_mul).mpr hψ_interval
  have htwo_sign : ((2 : ℤ) • ψ).sign = ψ.sign := by
    rw [Real.Angle.sign_two_zsmul_eq_sign_iff]
    exact Or.inr hψ_abs_lt
  have hsign : ((2 : ℤ) • ψ).sign = θ.sign := by
    dsimp [ψ, θ] at htwo_sign ⊢
    rw [htwo_sign, cfg.oangle_DAE_sign_eq_BAC, cfg.oangle_APB_sign_eq_BAC]
  rw [Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq hsign]
  have hψ_abs :
      |ψ.toReal| = π / 2 - ∠ cfg.B cfg.A cfg.C / 2 := by
    dsimp [ψ]
    rw [show |(∡ cfg.D cfg.A cfg.E).toReal| = ∠ cfg.D cfg.A cfg.E by
      rw [angle_eq_abs_oangle_toReal cfg.D_ne_A cfg.E_ne_A],
      cfg.angle_DAE]
  have hθ_abs : |θ.toReal| = π - ∠ cfg.B cfg.A cfg.C := by
    dsimp [θ]
    rw [show |(∡ cfg.A cfg.P cfg.B).toReal| = ∠ cfg.A cfg.P cfg.B by
      rw [angle_eq_abs_oangle_toReal cfg.P_ne_A.symm cfg.P_ne_B.symm],
      cfg.angle_APB]
  rw [htwo_toReal, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hψ_abs, hθ_abs]
  ring

theorem sin_APE_eq_sin_BPE :
    Real.sin (∠ cfg.A cfg.P cfg.E) = Real.sin (∠ cfg.B cfg.P cfg.E) := by
  let θ : Real.Angle := ∡ cfg.A cfg.P cfg.E
  let φ : Real.Angle := ∡ cfg.B cfg.P cfg.E
  have hAPE_half : (2 : ℤ) • ∡ cfg.A cfg.P cfg.E = ∡ cfg.A cfg.P cfg.B := by
    rw [← cfg.tangent_chord_O₂_AE_directed]
    exact cfg.two_zsmul_oangle_DAE_eq_oangle_APB
  have hadd : ∡ cfg.B cfg.P cfg.A + ∡ cfg.A cfg.P cfg.E = ∡ cfg.B cfg.P cfg.E :=
    oangle_add cfg.P_ne_B.symm cfg.P_ne_A.symm cfg.P_ne_E.symm
  have htwo : (2 : ℤ) • φ = (2 : ℤ) • (-θ) := by
    dsimp [θ, φ]
    rw [← hadd, smul_add, oangle_rev cfg.A cfg.P cfg.B, smul_neg, ← hAPE_half]
    abel
  have hsin_abs := Real.Angle.abs_sin_eq_of_two_zsmul_eq htwo
  rw [Real.Angle.sin_neg, abs_neg] at hsin_abs
  rw [sin_angle_eq_abs_sin_oangle cfg.P_ne_A.symm cfg.P_ne_E.symm,
    sin_angle_eq_abs_sin_oangle cfg.P_ne_B.symm cfg.P_ne_E.symm]
  exact hsin_abs.symm

/-! ### Metric crux: sine rule

The official solution now uses the sine rule in triangles `APE` and `BPE`. This is the metric
input that the old pure directed-angle chase lacked.
-/

/-- Sine equality from the sine rule in `APE` and `BPE`.

The intended derivation is:
`sin ∠PAE * PE = sin ∠APE * AE` and
`sin ∠PBE * PE = sin ∠BPE * EB`, then use `AE = EB` and the directed-angle
consequence `sin ∠APE = sin ∠BPE`. -/
theorem sin_PAE_eq_sin_PBE :
    Real.sin (∠ cfg.P cfg.A cfg.E) = Real.sin (∠ cfg.P cfg.B cfg.E) := by
  have h₁ := law_sin cfg.P cfg.A cfg.E
  have h₂ := law_sin cfg.P cfg.B cfg.E
  have hAE_BE : dist cfg.A cfg.E = dist cfg.B cfg.E := by
    simpa [dist_comm] using cfg.dist_E_A_eq_dist_E_B
  have h_rhs :
      Real.sin (∠ cfg.E cfg.P cfg.A) * dist cfg.E cfg.P =
        Real.sin (∠ cfg.E cfg.P cfg.B) * dist cfg.E cfg.P := by
    rw [angle_comm cfg.E cfg.P cfg.A, angle_comm cfg.E cfg.P cfg.B,
      cfg.sin_APE_eq_sin_BPE]
  have h_mul :
      Real.sin (∠ cfg.P cfg.A cfg.E) * dist cfg.A cfg.E =
        Real.sin (∠ cfg.P cfg.B cfg.E) * dist cfg.A cfg.E := by
    simpa [hAE_BE] using h₁.trans (h_rhs.trans h₂.symm)
  exact mul_right_cancel₀ (dist_ne_zero.mpr cfg.E_ne_A.symm) h_mul

theorem angle_PAE_lt_pi_div_two : ∠ cfg.P cfg.A cfg.E < π / 2 := by
  have hDAC_lt : ∠ cfg.D cfg.A cfg.C < π / 2 := by
    have hBpos : 0 < ∠ cfg.A cfg.B cfg.C :=
      angle_pos_of_not_collinear cfg.not_collinear_ABC
    rw [angle_comm cfg.D cfg.A cfg.C, cfg.angle_CAD]
    linarith
  have hDAE_le_DAC : ∠ cfg.D cfg.A cfg.E ≤ ∠ cfg.D cfg.A cfg.C := by
    have h := cfg.angle_DAE_add_EAC_eq_DAC
    linarith [angle_nonneg cfg.E cfg.A cfg.C]
  have hDAP_le_DAC : ∠ cfg.D cfg.A cfg.P ≤ ∠ cfg.D cfg.A cfg.C := by
    have h := cfg.angle_DAP_add_PAC_eq_DAC
    linarith [angle_nonneg cfg.P cfg.A cfg.C]
  have hsign : (∡ cfg.D cfg.A cfg.P).sign = (∡ cfg.D cfg.A cfg.E).sign := by
    have h := cfg.P_sSameSide_AD_E.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.D)
      (right_mem_affineSpan_pair ℝ cfg.A cfg.D)
    calc
      (∡ cfg.D cfg.A cfg.P).sign = (∡ cfg.A cfg.P cfg.D).sign :=
        (oangle_rotate_sign cfg.D cfg.A cfg.P).symm
      _ = (∡ cfg.A cfg.E cfg.D).sign := h.symm
      _ = (∡ cfg.D cfg.A cfg.E).sign := oangle_rotate_sign cfg.D cfg.A cfg.E
  have hDAP_ne : (∡ cfg.D cfg.A cfg.P).sign ≠ 0 := by
    rw [hsign, cfg.oangle_DAE_sign_eq_BAC]
    exact cfg.oangle_BAC_sign_ne_zero
  rcases angle_add_or_add_of_oangle_sign_eq hDAP_ne hsign with hsplit | hsplit
  ·
    linarith [hDAE_le_DAC, hDAC_lt, angle_nonneg cfg.D cfg.A cfg.P]
  ·
    rw [angle_comm cfg.E cfg.A cfg.P] at hsplit
    linarith [hDAP_le_DAC, hDAC_lt, angle_nonneg cfg.D cfg.A cfg.E]

theorem angle_PBE_lt_pi_div_two : ∠ cfg.P cfg.B cfg.E < π / 2 := by
  have hABE_lt : ∠ cfg.A cfg.B cfg.E < π / 2 := by
    have hCpos : 0 < ∠ cfg.A cfg.C cfg.B :=
      angle_pos_of_not_collinear (by
        simpa [Set.pair_comm cfg.B cfg.C] using cfg.not_collinear_ABC)
    rw [← cfg.angle_BAE_eq_ABE, cfg.angle_BAE]
    linarith
  have hDAC_lt : ∠ cfg.D cfg.A cfg.C < π / 2 := by
    have hBpos : 0 < ∠ cfg.A cfg.B cfg.C :=
      angle_pos_of_not_collinear cfg.not_collinear_ABC
    rw [angle_comm cfg.D cfg.A cfg.C, cfg.angle_CAD]
    linarith
  have hCAP_lt : ∠ cfg.C cfg.A cfg.P < π / 2 := by
    have h := cfg.angle_DAP_add_PAC_eq_DAC
    rw [angle_comm cfg.P cfg.A cfg.C] at h
    have hCAP_le : ∠ cfg.C cfg.A cfg.P ≤ ∠ cfg.D cfg.A cfg.C := by
      linarith [angle_nonneg cfg.D cfg.A cfg.P]
    exact lt_of_le_of_lt hCAP_le hDAC_lt
  have hABP_lt : ∠ cfg.A cfg.B cfg.P < π / 2 := by
    rw [cfg.angle_ABP_eq_CAP]
    exact hCAP_lt
  have hsign : (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.A cfg.B cfg.E).sign := by
    have h := cfg.P_sSameSide_AB_E.oangle_sign_eq
      (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
      (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
    calc
      (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.B cfg.P cfg.A).sign :=
        (oangle_rotate_sign cfg.A cfg.B cfg.P).symm
      _ = (∡ cfg.B cfg.E cfg.A).sign := h.symm
      _ = (∡ cfg.A cfg.B cfg.E).sign := oangle_rotate_sign cfg.A cfg.B cfg.E
  rcases angle_add_or_add_of_oangle_sign_eq cfg.oangle_ABP_sign_ne_zero hsign with
    hsplit | hsplit
  ·
    linarith [hABE_lt, angle_nonneg cfg.A cfg.B cfg.P]
  ·
    rw [angle_comm cfg.E cfg.B cfg.P] at hsplit
    linarith [hABP_lt, angle_nonneg cfg.A cfg.B cfg.E]

/-- The sine equality is on the acute branch, so the angles themselves are equal. -/
theorem angle_PAE_eq_PBE :
    ∠ cfg.P cfg.A cfg.E = ∠ cfg.P cfg.B cfg.E := by
  refine Real.injOn_sin ?_ ?_ cfg.sin_PAE_eq_sin_PBE
  · exact ⟨by linarith [angle_nonneg cfg.P cfg.A cfg.E, Real.pi_pos],
      le_of_lt cfg.angle_PAE_lt_pi_div_two⟩
  · exact ⟨by linarith [angle_nonneg cfg.P cfg.B cfg.E, Real.pi_pos],
      le_of_lt cfg.angle_PBE_lt_pi_div_two⟩

/-! ### Final assembly -/

/-- Official final step:
`∠BAP = ∠BAE - ∠PAE = ∠ABE - ∠PBE = ∠ABP = ∠CAP`. -/
theorem angle_bisector_from_official_route :
    ∠ cfg.B cfg.A cfg.P = ∠ cfg.C cfg.A cfg.P := by
  have hsign_A :
      (∡ cfg.B cfg.A cfg.P).sign = (∡ cfg.B cfg.A cfg.E).sign := by
    have h := cfg.P_sSameSide_AB_E.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
      (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
    simpa [oangle_rotate_sign cfg.B cfg.A cfg.P, oangle_rotate_sign cfg.B cfg.A cfg.E]
      using h.symm
  have hsign_B :
      (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.A cfg.B cfg.E).sign := by
    have h := cfg.P_sSameSide_AB_E.oangle_sign_eq
      (right_mem_affineSpan_pair ℝ cfg.A cfg.B)
      (left_mem_affineSpan_pair ℝ cfg.A cfg.B)
    calc
      (∡ cfg.A cfg.B cfg.P).sign = (∡ cfg.B cfg.P cfg.A).sign :=
        (oangle_rotate_sign cfg.A cfg.B cfg.P).symm
      _ = (∡ cfg.B cfg.E cfg.A).sign := h.symm
      _ = (∡ cfg.A cfg.B cfg.E).sign := oangle_rotate_sign cfg.A cfg.B cfg.E
  have hBAP_ne : (∡ cfg.B cfg.A cfg.P).sign ≠ 0 := by
    rw [hsign_A]
    intro hzero
    rw [oangle_sign_eq_zero_iff_collinear] at hzero
    exact cfg.E_not_mem_line_AB
      (hzero.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) cfg.A_ne_B)
  have hBAE_ABE := cfg.angle_BAE_eq_ABE
  have hPAE_PBE := cfg.angle_PAE_eq_PBE
  have hABP_CAP := cfg.angle_ABP_eq_CAP
  have hsumP := cfg.angle_BAP_add_PAC_eq_BAC
  have hsumP' : ∠ cfg.B cfg.A cfg.P + ∠ cfg.C cfg.A cfg.P = ∠ cfg.B cfg.A cfg.C := by
    simpa [angle_comm cfg.P cfg.A cfg.C] using hsumP
  have hABC_sum :=
    angle_add_angle_add_angle_eq_pi (p₁ := cfg.B) (p₂ := cfg.A) cfg.C cfg.A_ne_B
  rw [angle_comm cfg.C cfg.B cfg.A] at hABC_sum
  have hBpos : 0 < ∠ cfg.A cfg.B cfg.C :=
    angle_pos_of_not_collinear cfg.not_collinear_ABC
  rcases angle_add_or_add_of_oangle_sign_eq hBAP_ne hsign_A with hsplit_A | hsplit_A
  · rcases angle_add_or_add_of_oangle_sign_eq cfg.oangle_ABP_sign_ne_zero hsign_B with
      hsplit_B | hsplit_B
    ·
      calc
        ∠ cfg.B cfg.A cfg.P = ∠ cfg.A cfg.B cfg.P := by linarith
        _ = ∠ cfg.C cfg.A cfg.P := hABP_CAP
    · rw [angle_comm cfg.E cfg.B cfg.P] at hsplit_B
      have htwo : ∠ cfg.B cfg.A cfg.C = 2 * ∠ cfg.B cfg.A cfg.E := by
        linarith
      rw [cfg.angle_BAE] at htwo
      linarith
  · rw [angle_comm cfg.E cfg.A cfg.P] at hsplit_A
    rcases angle_add_or_add_of_oangle_sign_eq cfg.oangle_ABP_sign_ne_zero hsign_B with
      hsplit_B | hsplit_B
    ·
      have htwo : ∠ cfg.B cfg.A cfg.C = 2 * ∠ cfg.B cfg.A cfg.E := by
        linarith
      rw [cfg.angle_BAE] at htwo
      linarith
    · rw [angle_comm cfg.E cfg.B cfg.P] at hsplit_B
      calc
        ∠ cfg.B cfg.A cfg.P = ∠ cfg.A cfg.B cfg.P := by linarith
        _ = ∠ cfg.C cfg.A cfg.P := hABP_CAP

/-- The bundled form of the problem. -/
theorem result_cfg : ∠ cfg.B cfg.A cfg.P = ∠ cfg.C cfg.A cfg.P :=
  cfg.angle_bisector_from_official_route

end Plane

end Cfg

/-- China MO 2012 Problem 1.
In a cyclic triangle ABC with ∠A the largest angle,
D and E lie on arc BC not containing A. D is the midpoint of arc ABC and E is the
midpoint of arc ACB. Circle O₁ passes through A, B and is tangent to AC at A.
Circle O₂ passes through A, E and is tangent to AD at A. O₁ and O₂ meet again at P.
Prove that AP bisects ∠BAC. -/
theorem result [Fact (finrank ℝ V = 2)]
    {A B C D E P : Pt} {ω O₁ O₂ : Sphere Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (circumsphere_ABC_eq_ω :
      (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere = ω)
    (angle_A_gt_B : ∠ A B C < ∠ B A C)
    (angle_A_gt_C : ∠ A C B < ∠ B A C)
    -- (derivable from circumsphere_ABC_eq_ω; kept for Arc.through / Arc.avoiding construction)
    (A_mem_ω : A ∈ (ω : Set Pt))
    (B_mem_ω : B ∈ (ω : Set Pt))
    (C_mem_ω : C ∈ (ω : Set Pt))
    -- (derivable from affineIndependent_ABC; kept for Arc.through / Arc.avoiding construction)
    (A_ne_B : A ≠ B)
    (A_ne_C : A ≠ C)
    (B_ne_C : B ≠ C)
    (D_eq : D = (Sphere.Arc.through A_mem_ω B_mem_ω C_mem_ω A_ne_B.symm B_ne_C).midpoint)
    (E_eq : E = (Sphere.Arc.through A_mem_ω C_mem_ω B_mem_ω A_ne_C.symm B_ne_C.symm).midpoint)
    -- (derivable from D_eq, E_eq and arc geometry; kept for faithfulness to problem statement)
    (D_on_arc_BC : D ∈ Sphere.Arc.avoiding B_mem_ω A_mem_ω C_mem_ω A_ne_B A_ne_C)
    (E_on_arc_BC : E ∈ Sphere.Arc.avoiding B_mem_ω A_mem_ω C_mem_ω A_ne_B A_ne_C)
    (A_mem_O₁ : A ∈ (O₁ : Set Pt))
    (B_mem_O₁ : B ∈ (O₁ : Set Pt))
    (O₁_tangent_AC : O₁.IsTangentAt A line[ℝ, A, C])
    (A_mem_O₂ : A ∈ (O₂ : Set Pt))
    (E_mem_O₂ : E ∈ (O₂ : Set Pt))
    (O₂_tangent_AD : O₂.IsTangentAt A line[ℝ, A, D])
    (P_mem_O₁ : P ∈ (O₁ : Set Pt))
    (P_mem_O₂ : P ∈ (O₂ : Set Pt))
    (P_ne_A : P ≠ A)
    : ∠ B A P = ∠ C A P := by
  exact (Cfg.mk A B C D E P ω O₁ O₂ affineIndependent_ABC circumsphere_ABC_eq_ω
    angle_A_gt_B angle_A_gt_C A_mem_ω B_mem_ω C_mem_ω A_ne_B A_ne_C B_ne_C
    D_eq E_eq D_on_arc_BC E_on_arc_BC A_mem_O₁ B_mem_O₁ O₁_tangent_AC A_mem_O₂
    E_mem_O₂ O₂_tangent_AD P_mem_O₁ P_mem_O₂ P_ne_A).result_cfg

end

end ChinaMO2012P1
