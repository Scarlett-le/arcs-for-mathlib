import Mathlib
import ArcsForMathlib.Auxlemma
import ArcsForMathlib.Sphere.Arc.Basic
import ArcsForMathlib.Sphere.Arc.Degenerate
import ArcsForMathlib.Sphere.Arc.Structure
import ArcsForMathlib.Sphere.Arc.Measure

/-!
# The Incenter/Arc-Midpoint Lemma

Let triangle `ABC` be inscribed in a circle `Γ` (its circumcircle), with incenter `I`.
Let `M` be the midpoint of the arc `BC` of `Γ` *not containing* `A`.
The stronger incenter–excenter lemma also makes `M` the midpoint of `I` and the `A`-excenter; this file formalizes only its incenter half, `MB = MC = MI`.

## Proof outline

We bundle the triangle data into `Cfg`, prove the arc-specific facts there, and assemble
`MB = MC = MI`.  The equality `MB = MC` is the direct arc-library input
(`Arc.midpoint_mem_perpBisector`); the longer `MB = MI` oriented-angle chase is documented at
`Cfg.dist_M_B_eq_dist_M_incenter`.

## Implementation notes

Following `Archive/Imo/Imo2019Q2.lean`, we bundle the data into a configuration structure
`Cfg` so that the many derived facts do not have to thread hypotheses around, and deduce the
unbundled statement `result` at the very end.

The angle chase is carried out with *oriented* angles modulo `π` (`(2 : ℤ) • ∡`), which avoids
the betweenness/configuration side-conditions an unoriented (`∠`) chase would require.  The one
genuinely geometric input is `collinear_A_incenter_M`: `A`, the incenter and the arc midpoint are
collinear.  It is proved by exhibiting the arc midpoint as the second intersection of the internal
`A`-bisector with the circumcircle (`Sphere.secondInter`), the "internal/far side" being pinned
down through the incenter's barycentric cevian foot on `BC`.

## Reference

Evan Chen, *Euclidean Geometry in Mathematical Olympiads*, MAA Problem Books, volume 27,
Mathematical Association of America, 2016.
-/

open scoped Real EuclideanGeometry
open Affine EuclideanGeometry Module Sphere

namespace IncenterArcMidpoint

noncomputable section

variable (V Pt : Type*)
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt]

/-- A configuration satisfying the conditions of the lemma: just a (nondegenerate) triangle.
Everything else — circumcircle, incenter, the arc and its midpoint — is *derived*, so we never
have to carry a separate `Γ = circumsphere`, `I = incenter` hypothesis internally. -/
structure Cfg where
  (A B C : Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]

variable {V Pt}

namespace Cfg

variable [Fact (finrank ℝ V = 2)] (cfg : Cfg V Pt)

/-! ### Basic configuration facts (obvious from the diagram) -/

omit [Fact (finrank ℝ V = 2)] in
theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

omit [Fact (finrank ℝ V = 2)] in
theorem A_ne_C : cfg.A ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 2)

omit [Fact (finrank ℝ V = 2)] in
theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

/-- `ABC` as a `Triangle`. -/
def triangleABC : Triangle ℝ Pt := ⟨_, cfg.affineIndependent_ABC⟩

/-- The circumcircle of `ABC`. -/
def Γ : Sphere Pt := cfg.triangleABC.circumsphere

/-- The incenter of `ABC`. -/
def incenter : Pt := cfg.triangleABC.incenter

omit [Fact (finrank ℝ V = 2)] in
theorem A_mem_Γ : cfg.A ∈ cfg.Γ := cfg.triangleABC.mem_circumsphere 0

omit [Fact (finrank ℝ V = 2)] in
theorem B_mem_Γ : cfg.B ∈ cfg.Γ := cfg.triangleABC.mem_circumsphere 1

omit [Fact (finrank ℝ V = 2)] in
theorem C_mem_Γ : cfg.C ∈ cfg.Γ := cfg.triangleABC.mem_circumsphere 2

/-! ### The arc `BC` not containing `A`, and its midpoint `M` -/

/-- The arc from `B` to `C` not containing `A`. -/
def arcBC : Sphere.Arc cfg.Γ :=
  Sphere.Arc.avoiding cfg.B_mem_Γ cfg.A_mem_Γ cfg.C_mem_Γ cfg.A_ne_B cfg.A_ne_C

/-- `M`, the midpoint of arc `BC` not containing `A`. -/
def M : Pt := cfg.arcBC.midpoint

omit [Fact (finrank ℝ V = 2)] in
/-- `cfg.arcBC.left = B` (holds definitionally; recorded for rewriting). -/
theorem arcBC_left : cfg.arcBC.left = cfg.B := rfl

/-- `cfg.arcBC.right = C` (the right endpoint of the `avoiding` arc). -/
theorem arcBC_right : cfg.arcBC.right = cfg.C :=
  Sphere.Arc.avoiding_right cfg.B_mem_Γ cfg.A_mem_Γ cfg.C_mem_Γ cfg.A_ne_B cfg.A_ne_C

theorem arcBC_not_isDegenerate : ¬ cfg.arcBC.IsDegenerate := by
  rw [← Sphere.Arc.left_ne_right_iff_not_isDegenerate, cfg.arcBC_left, cfg.arcBC_right]
  exact cfg.B_ne_C

theorem M_mem_Γ : cfg.M ∈ cfg.Γ :=
  Sphere.Arc.midpoint_mem cfg.arcBC cfg.arcBC_not_isDegenerate

/-- `A` is not on the arc `BC` chosen to avoid `A`. -/
theorem A_not_mem_arcBC : cfg.A ∉ cfg.arcBC :=
  Sphere.Arc.notMem_avoiding cfg.B_mem_Γ cfg.A_mem_Γ cfg.C_mem_Γ
    cfg.A_ne_B cfg.A_ne_C cfg.B_ne_C

/-- `M` is the structural mid of `arcBC`. -/
theorem M_eq_arcBC_mid : cfg.M = cfg.arcBC.mid :=
  Sphere.Arc.midpoint_eq_mid cfg.arcBC cfg.arcBC_not_isDegenerate

/-- `M` is not weakly on the same side of `BC` as `A`. -/
theorem not_wSameSide_M_A : ¬ (line[ℝ, cfg.B, cfg.C]).WSameSide cfg.M cfg.A := by
  have hsubeq : cfg.Γ.lineOrOrthRadius cfg.arcBC.left cfg.arcBC.right =
      line[ℝ, cfg.B, cfg.C] := by
    rw [cfg.arcBC_left, cfg.arcBC_right, Sphere.lineOrOrthRadius_of_ne cfg.B_ne_C]
  rw [← hsubeq, cfg.M_eq_arcBC_mid]
  exact Sphere.Arc.not_wSameSide_mid_of_mem_sphere_of_notMem cfg.A_mem_Γ cfg.A_not_mem_arcBC
    (by rw [cfg.arcBC_left, cfg.arcBC_right]; exact cfg.B_ne_C)

/-! ### `MB = MC`  (the part where the arc library does the work) -/

/-- `M` is equidistant from `B` and `C`: the arc midpoint lies on the perpendicular bisector
of the chord joining the arc's endpoints. -/
theorem dist_M_B_eq_dist_M_C : dist cfg.M cfg.B = dist cfg.M cfg.C := by
  -- ★ The one place the arc library does load-bearing work: an arc's midpoint lies on the
  --   perpendicular bisector of the chord joining its two endpoints.
  have hmem := Sphere.Arc.midpoint_mem_perpBisector cfg.arcBC cfg.arcBC_not_isDegenerate
  rw [cfg.arcBC_left, cfg.arcBC_right] at hmem
  exact AffineSubspace.mem_perpBisector_iff_dist_eq.mp hmem

omit [Fact (finrank ℝ V = 2)] in
/-- Two facts proved together from the incenter's positive barycentric weights and the cevian
foot `F := lineMap B C (w₂ / (w₁ + w₂))` on side `BC`: the incenter lies strictly inside the
circumcircle, and the second intersection of line `AI` with the circumcircle lies strictly on the
opposite side of `BC` from `A`. -/
theorem incenter_lt_radius_and_secondInter_sOppSide :
    dist cfg.incenter cfg.Γ.center < cfg.Γ.radius ∧
      (line[ℝ, cfg.B, cfg.C]).SOppSide cfg.A
        (cfg.Γ.secondInter cfg.A (cfg.incenter -ᵥ cfg.A)) := by
  -- Setup: the incenter's (positive, normalized) barycentric weights.
  set O := cfg.Γ.center
  set R := cfg.Γ.radius
  set w := cfg.triangleABC.excenterWeights ∅ with hw
  have hw0 : 0 < w 0 := cfg.triangleABC.excenterWeights_empty_pos 0
  have hw1 : 0 < w 1 := cfg.triangleABC.excenterWeights_empty_pos 1
  have hw2 : 0 < w 2 := cfg.triangleABC.excenterWeights_empty_pos 2
  have hsum : ∑ i, w i = 1 := cfg.triangleABC.excenterExists_empty.sum_excenterWeights_eq_one
  have hsum3 : w 0 + w 1 + w 2 = 1 := by rw [← Fin.sum_univ_three]; exact hsum
  set sBC := w 1 + w 2 with hsBC
  have hsBC_pos : 0 < sBC := by positivity
  have h1sBC : (1 : ℝ) - sBC = w 0 := by rw [hsBC]; linarith
  -- Express `I -ᵥ A` and the cevian foot `F -ᵥ A` in the basis `{B -ᵥ A, C -ᵥ A}`.
  have hIA : cfg.incenter -ᵥ cfg.A = w 1 • (cfg.B -ᵥ cfg.A) + w 2 • (cfg.C -ᵥ cfg.A) := by
    rw [show cfg.incenter = cfg.triangleABC.incenter from rfl,
        cfg.triangleABC.incenter_eq_affineCombination,
        Finset.univ.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
          w cfg.triangleABC.points hsum cfg.A,
        vadd_vsub, Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three,
        show cfg.triangleABC.points 0 = cfg.A from rfl,
        show cfg.triangleABC.points 1 = cfg.B from rfl,
        show cfg.triangleABC.points 2 = cfg.C from rfl, vsub_self, smul_zero, zero_add]
  -- The cevian foot `F` on line `BC`, and the key relations `F -ᵥ A`, `I -ᵥ A = sBC • (F -ᵥ A)`.
  set F : Pt := AffineMap.lineMap cfg.B cfg.C (w 2 / sBC) with hF
  have hF_mem : F ∈ line[ℝ, cfg.B, cfg.C] := AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hFA : F -ᵥ cfg.A = (w 1 / sBC) • (cfg.B -ᵥ cfg.A) + (w 2 / sBC) • (cfg.C -ᵥ cfg.A) := by
    rw [hF, AffineMap.lineMap_apply, vadd_vsub_assoc,
        show (cfg.C -ᵥ cfg.B : V) = (cfg.C -ᵥ cfg.A) - (cfg.B -ᵥ cfg.A) from
          (vsub_sub_vsub_cancel_right _ _ _).symm,
        show w 1 / sBC = 1 - w 2 / sBC from by
          rw [eq_sub_iff_add_eq, ← add_div, ← hsBC, div_self hsBC_pos.ne']]
    module
  have hIsF : cfg.incenter -ᵥ cfg.A = sBC • (F -ᵥ cfg.A) := by
    rw [hFA, hIA, smul_add, smul_smul, smul_smul,
        mul_div_cancel₀ _ hsBC_pos.ne', mul_div_cancel₀ _ hsBC_pos.ne']
  have hsi : cfg.Γ.secondInter cfg.A (cfg.incenter -ᵥ cfg.A)
      = cfg.Γ.secondInter cfg.A (F -ᵥ cfg.A) := by
    rw [hIsF, Sphere.secondInter_smul _ _ _ hsBC_pos.ne']
  -- The vertices and `F` lie in the (closed) ball of radius `R`; `F` lies strictly inside.
  have hmem_ball : ∀ {p : Pt}, p ∈ cfg.Γ → (p -ᵥ O) ∈ Metric.closedBall (0 : V) R :=
    fun hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Sphere.norm_vsub_center_eq_radius hp).le
  have hAmem := hmem_ball cfg.A_mem_Γ
  have hBmem := hmem_ball cfg.B_mem_Γ
  have hCmem := hmem_ball cfg.C_mem_Γ
  have hne : (cfg.B -ᵥ O) ≠ (cfg.C -ᵥ O) := (vsub_left_injective O).ne cfg.B_ne_C
  have hFO : F -ᵥ O = (1 - w 2 / sBC) • (cfg.B -ᵥ O) + (w 2 / sBC) • (cfg.C -ᵥ O) := by
    rw [hF, AffineMap.lineMap_apply, vadd_vsub_assoc,
        show (cfg.C -ᵥ cfg.B : V) = (cfg.C -ᵥ O) - (cfg.B -ᵥ O) from
          (vsub_sub_vsub_cancel_right _ _ _).symm]
    module
  have ha_pos : 0 < 1 - w 2 / sBC := by
    rw [sub_pos, div_lt_one hsBC_pos, hsBC]; linarith
  have hF_lt : dist F O < R := by
    rw [dist_eq_norm_vsub V, hFO]
    have h := combo_mem_ball_of_ne hBmem hCmem hne ha_pos (by positivity)
      (show (1 - w 2 / sBC) + w 2 / sBC = 1 by ring)
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hA_not : cfg.A ∉ line[ℝ, cfg.B, cfg.C] := fun hmem =>
    (affineIndependent_iff_not_collinear_set.mp cfg.affineIndependent_ABC)
      (collinear_insert_of_mem_affineSpan_pair hmem)
  refine ⟨?_, ?_⟩
  · -- ① The incenter is strictly inside: it is a strict convex combination of `A` (on `Γ`) and
    --   `F` (strictly inside `Γ`).
    have hAF : cfg.A ≠ F := fun h => hA_not (h ▸ hF_mem)
    have hFmem' : (F -ᵥ O) ∈ Metric.closedBall (0 : V) R := by
      rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm_vsub V]; exact hF_lt.le
    have hneAF : (cfg.A -ᵥ O) ≠ (F -ᵥ O) := (vsub_left_injective O).ne hAF
    have hIO : cfg.incenter -ᵥ O = (1 - sBC) • (cfg.A -ᵥ O) + sBC • (F -ᵥ O) := by
      rw [show cfg.incenter -ᵥ O = (cfg.incenter -ᵥ cfg.A) + (cfg.A -ᵥ O) from
            (vsub_add_vsub_cancel _ _ _).symm, hIsF,
          show (F -ᵥ cfg.A : V) = (F -ᵥ O) - (cfg.A -ᵥ O) from
            (vsub_sub_vsub_cancel_right _ _ _).symm]
      module
    rw [dist_eq_norm_vsub V, hIO]
    have h := combo_mem_ball_of_ne hAmem hFmem' hneAF
      (show (0 : ℝ) < 1 - sBC by rw [h1sBC]; exact hw0) hsBC_pos (by ring)
    rwa [Metric.mem_ball, dist_zero_right] at h
  · -- ② The second intersection of `AI` with `Γ` is on the far side of `BC`: it equals
    --   `secondInter A (F -ᵥ A)`, and `A`–`F`–(that point) is strictly between with `F ∈ BC`.
    have hSbtw : Sbtw ℝ cfg.A F (cfg.Γ.secondInter cfg.A (F -ᵥ cfg.A)) :=
      cfg.Γ.sbtw_secondInter cfg.A_mem_Γ hF_lt
    rw [hsi]
    exact hSbtw.sOppSide_of_notMem_of_mem hA_not hF_mem

/-! ### Collinearity of `A`, `I`, `M` on the internal bisector from `A`

Both the incenter `I` and the arc-midpoint `M` lie on the internal bisector of `∠A`, hence on a
common line through `A`.  This is the single genuinely geometric input to the angle chase below;
everything else is oriented-angle bookkeeping.

We prove it by identifying `M` with `M' := Γ.secondInter A (I -ᵥ A)`, the second meeting point of
line `AI` with the circumcircle (so `A`, `I`, `M'` are automatically collinear).  Since `I` lies
on the internal `A`-bisector (`Affine.Triangle.oangle_incenter_eq`), `M'` bisects `∠A` exactly,
which forces `M'B = M'C`; thus both `M` and `M'` lie on the perpendicular bisector of `BC` and on
the far side of `BC` from `A` (the latter via `incenter_lt_radius_and_secondInter_sOppSide`).
A line meets the circle in at most two points and the two points of `perpBisector ∩ Γ` lie on
opposite sides of `BC`, so `M = M'`. -/

-- Orientation data for the oriented-angle reasoning, shared by the two theorems below.  These
-- live at `section` scope so the `(2 : ℤ) • ∡` chase and the bisector argument don't each have
-- to re-derive them; they are unavailable in the `omit [Fact …]` lemmas above, which is correct
-- (those lemmas do not mention oriented angles).
local instance : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two

local instance : Module.Oriented ℝ V (Fin 2) :=
  ⟨Module.Basis.orientation
    (Module.finBasisOfFinrankEq ℝ V (Fact.out : Module.finrank ℝ V = 2))⟩

theorem collinear_A_incenter_M : Collinear ℝ ({cfg.A, cfg.incenter, cfg.M} : Set Pt) := by
  obtain ⟨hI_lt, hM'far⟩ := cfg.incenter_lt_radius_and_secondInter_sOppSide
  set A := cfg.A
  set B := cfg.B
  set C := cfg.C
  set I := cfg.incenter
  set O := cfg.Γ.center
  set M := cfg.M
  set M' : Pt := cfg.Γ.secondInter A (I -ᵥ A)
  have hBC : B ≠ C := cfg.B_ne_C
  -- `M'` is the second intersection of line `AI` with `Γ`: collinear with `A`, `I`, on the circle,
  -- and (being strictly between `A` and `M'`) `I` is strictly inside.
  have hcolAIM' : Collinear ℝ ({A, I, M'} : Set Pt) := cfg.Γ.secondInter_collinear A I
  have hM'Γ : M' ∈ cfg.Γ := (Sphere.secondInter_mem _).2 cfg.A_mem_Γ
  have hSbtwAIM' : Sbtw ℝ A I M' := cfg.Γ.sbtw_secondInter cfg.A_mem_Γ hI_lt
  have hIA : I ≠ A := hSbtwAIM'.ne_left
  have hM'A : M' ≠ A := hSbtwAIM'.left_ne_right.symm
  -- the incenter bisects `∠A` (exact, oriented)
  have hbisA : ∡ B A I = ∡ I A C := by
    have h := cfg.triangleABC.oangle_incenter_eq (show (0 : Fin 3) ≠ 1 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide)
    rwa [show cfg.triangleABC.points 0 = A from rfl, show cfg.triangleABC.points 1 = B from rfl,
        show cfg.triangleABC.points 2 = C from rfl, show cfg.triangleABC.incenter = I from rfl] at h
  -- `M'` lies on the internal bisector line, so it bisects `∠A` exactly
  have hzIAM' : ∡ I A M' + ∡ I A M' = 0 := by
    rw [← two_zsmul, Real.Angle.two_zsmul_eq_zero_iff]
    refine oangle_eq_zero_or_eq_pi_iff_collinear.mpr ?_
    rw [show ({I, A, M'} : Set Pt) = {A, I, M'} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcolAIM'
  have key : ∡ B A M' = ∡ M' A C := by
    have h1 : ∡ B A I + ∡ I A M' = ∡ B A M' := oangle_add cfg.A_ne_B.symm hIA hM'A
    have h2 : ∡ M' A I + ∡ I A C = ∡ M' A C := oangle_add hM'A hIA cfg.A_ne_C.symm
    rw [← h1, ← h2, oangle_rev I A M', hbisA,
      show -∡ I A M' = ∡ I A M' from neg_eq_of_add_eq_zero_left hzIAM']
    abel
  -- hence `M'` is equidistant from `B` and `C`
  have hM'_notline : M' ∉ line[ℝ, B, C] := hM'far.2.2
  have hM'B : M' ≠ B := fun h => hM'_notline (by rw [h]; exact left_mem_affineSpan_pair ℝ B C)
  have hM'C : M' ≠ C := fun h => hM'_notline (by rw [h]; exact right_mem_affineSpan_pair ℝ B C)
  have hncol : ¬ Collinear ℝ ({C, M', B} : Set Pt) := fun hcol => hM'_notline
    (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC)
  have hdistM' : dist M' B = dist M' C := by
    refine dist_eq_of_two_zsmul_oangle_eq ?_ ?_ ?_
    · rw [Sphere.two_zsmul_oangle_eq hM'Γ cfg.B_mem_Γ cfg.A_mem_Γ cfg.C_mem_Γ hM'B.symm hBC
            hM'A.symm cfg.A_ne_C,
          Sphere.two_zsmul_oangle_eq cfg.B_mem_Γ cfg.C_mem_Γ cfg.A_mem_Γ hM'Γ hBC.symm hM'C.symm
            cfg.A_ne_B hM'A.symm, key]
    · exact (oangle_ne_zero_and_ne_pi_iff_not_collinear.mpr hncol).1
    · exact (oangle_ne_zero_and_ne_pi_iff_not_collinear.mpr hncol).2
  -- `M`, `M'` and the midpoint of `BC` all lie on the perpendicular bisector of `BC`
  have hMpb : M ∈ AffineSubspace.perpBisector B C :=
    AffineSubspace.mem_perpBisector_iff_dist_eq.mpr cfg.dist_M_B_eq_dist_M_C
  have hM'pb : M' ∈ AffineSubspace.perpBisector B C :=
    AffineSubspace.mem_perpBisector_iff_dist_eq.mpr hdistM'
  have hPpb : midpoint ℝ B C ∈ AffineSubspace.perpBisector B C :=
    AffineSubspace.midpoint_mem_perpBisector B C
  have hMΓ : M ∈ cfg.Γ := cfg.M_mem_Γ
  -- ★ arc library (side semantics): `M` is the structural mid of the arc, so it lies off the
  --   chord line `BC` and is *not* weakly on the same side of `BC` as `A` (which sits on the
  --   other arc).  These pin `M` to the far side, matching `M'`.
  have hnd := cfg.arcBC_not_isDegenerate
  have hsubeq : cfg.Γ.lineOrOrthRadius cfg.arcBC.left cfg.arcBC.right = line[ℝ, B, C] := by
    rw [show cfg.arcBC.left = B from rfl, cfg.arcBC_right, Sphere.lineOrOrthRadius_of_ne hBC]
  have hM_notline : M ∉ line[ℝ, B, C] := by
    rw [← hsubeq]; exact cfg.arcBC.midpoint_not_mem_lineOrOrthRadius hnd
  have hnotws : ¬ (line[ℝ, B, C]).WSameSide M A := by
    simpa only [A, B, C, M] using cfg.not_wSameSide_M_A
  -- `M, M', midpoint BC` are collinear (all inside the 1-dimensional perpendicular bisector)
  have hcolMM'P : Collinear ℝ ({M, M', midpoint ℝ B C} : Set Pt) := by
    rw [collinear_iff_finrank_le_one]
    have hsub : ({M, M', midpoint ℝ B C} : Set Pt) ⊆ (AffineSubspace.perpBisector B C : Set Pt) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hMpb, hM'pb, hPpb]
    calc finrank ℝ (vectorSpan ℝ ({M, M', midpoint ℝ B C} : Set Pt))
        ≤ finrank ℝ (AffineSubspace.perpBisector B C).direction := by
          apply Submodule.finrank_mono
          rw [← direction_affineSpan]
          exact AffineSubspace.direction_le (affineSpan_le.mpr hsub)
      _ = 1 := by
          rw [AffineSubspace.direction_perpBisector]
          haveI : Fact (Module.finrank ℝ V = 1 + 1) := ⟨(Fact.out : Module.finrank ℝ V = 2)⟩
          exact Submodule.finrank_orthogonal_span_singleton
            (by rw [ne_eq, vsub_eq_zero_iff_eq]; exact hBC.symm)
  have hMP : M ≠ midpoint ℝ B C := fun h =>
    hM_notline (by rw [h]; exact (wbtw_midpoint ℝ B C).mem_affineSpan)
  have hM'_line : M' ∈ line[ℝ, M, midpoint ℝ B C] :=
    hcolMM'P.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hMP
  -- a line through a point on the circle meets it in at most two points
  have heqor : M' = M ∨ M' = cfg.Γ.secondInter M (midpoint ℝ B C -ᵥ M) :=
    (Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair hMΓ hM'_line).mpr hM'Γ
  rcases heqor with hMM' | hMM'
  · rw [← hMM']; exact hcolAIM'
  · -- the other intersection is the near-side arc midpoint, contradicting `M'` being far side
    exfalso
    set N := cfg.Γ.secondInter M (midpoint ℝ B C -ᵥ M)
    have hPlt : dist (midpoint ℝ B C) O < cfg.Γ.radius := by
      rw [dist_comm]; exact cfg.Γ.dist_center_midpoint_lt_radius cfg.B_mem_Γ cfg.C_mem_Γ hBC
    have hSbtwMPN : Sbtw ℝ M (midpoint ℝ B C) N := cfg.Γ.sbtw_secondInter hMΓ hPlt
    have hPline : midpoint ℝ B C ∈ line[ℝ, B, C] := (wbtw_midpoint ℝ B C).mem_affineSpan
    have hMN : (line[ℝ, B, C]).SOppSide M N := hSbtwMPN.sOppSide_of_notMem_of_mem hM_notline hPline
    rw [← hMM'] at hMN
    exact hnotws (hMN.trans hM'far.symm).wSameSide

/-! ### `MB = MI` via oriented angles

We pass to oriented angles `∡` and work modulo `π`, i.e. with `(2 : ℤ) • ∡`.  Triangle `BIM` is
isosceles (`MB = MI`) once its two base angles agree mod `π`:
`2 • ∡ M B I = 2 • ∡ B I M`.  Both sides reduce to `2 • ∡ M A C + 2 • ∡ I B A`:

* `2 • ∡ M B I = 2 • ∡ M B C + 2 • ∡ C B I`        (`oangle_add` at `B`)
  `= 2 • ∡ M A C + 2 • ∡ I B A`                     (inscribed angle `Sphere.two_zsmul_oangle_eq`
                                                      on chord `MC`; `I` bisects `∠B`);
* `2 • ∡ B I M = 2 • ∡ B I A`                        (`A, I, M` collinear)
  `= 2 • ∡ I B A + 2 • ∡ B A I`                      (angle sum of `△ABI`)
  `= 2 • ∡ I B A + 2 • ∡ M A C`                      (`I` bisects `∠A`, then collinearity).

`dist_eq_of_two_zsmul_oangle_eq` then converts the base-angle equality into `MB = MI`. -/

theorem dist_M_B_eq_dist_M_incenter : dist cfg.M cfg.B = dist cfg.M cfg.incenter := by
  set A := cfg.A
  set B := cfg.B
  set C := cfg.C
  set I := cfg.incenter
  set M := cfg.M
  -- circumcircle memberships and the triangle's vertices/incenter
  have hAΓ : A ∈ cfg.Γ := cfg.A_mem_Γ
  have hBΓ : B ∈ cfg.Γ := cfg.B_mem_Γ
  have hCΓ : C ∈ cfg.Γ := cfg.C_mem_Γ
  have hMΓ : M ∈ cfg.Γ := cfg.M_mem_Γ
  -- distinctness facts
  have hAB : A ≠ B := cfg.A_ne_B
  have hAC : A ≠ C := cfg.A_ne_C
  have hBC : B ≠ C := cfg.B_ne_C
  have hIA : I ≠ A := by simpa using cfg.triangleABC.incenter_ne_point 0
  have hIB : I ≠ B := by simpa using cfg.triangleABC.incenter_ne_point 1
  -- `M` is the structural mid of the arc, hence `≠ A, B, C`
  have hnd := cfg.arcBC_not_isDegenerate
  have harcright : cfg.arcBC.right = C := cfg.arcBC_right
  have hMB : M ≠ B := cfg.arcBC.midpoint_ne_left hnd
  have hMC : M ≠ C := by rw [← harcright]; exact cfg.arcBC.midpoint_ne_right hnd
  have hMA : M ≠ A := by
    intro h
    have hMarc : M ∈ cfg.arcBC := cfg.arcBC.midpoint_mem_arc hnd
    rw [h] at hMarc; exact cfg.A_not_mem_arcBC hMarc
  -- `M ≠ I`: `I` lies on the same side of `BC` as `A`, but `M` (= arc mid) is not weakly on that
  -- side (since `A ∉ arcBC` while `A` is on the circle).
  have hMI : M ≠ I := by
    intro h
    have hI_ss : (line[ℝ, B, C]).SSameSide I A := by
      simpa using (cfg.triangleABC.sSameSide_affineSpan_pair_incenter_point
        (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
        (show (1 : Fin 3) ≠ 2 by decide))
    have hM_ws : (line[ℝ, B, C]).WSameSide M A := by
      rw [h]
      exact hI_ss.wSameSide
    exact cfg.not_wSameSide_M_A (by simpa only [A, B, C, M] using hM_ws)
  -- collinearity of `A`, `I`, `M`, in the orderings the swaps need
  have hco : Collinear ℝ ({A, I, M} : Set Pt) := cfg.collinear_A_incenter_M
  have hcolMIA : Collinear ℝ ({M, I, A} : Set Pt) := by
    convert hco using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hcolMAI : Collinear ℝ ({M, A, I} : Set Pt) := by
    convert hco using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hcolIMA : Collinear ℝ ({I, M, A} : Set Pt) := by
    convert hco using 1
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  -- ¬ Collinear {A, C, B}, used for nondegeneracy of `△IMB`
  have hncolACB : ¬ Collinear ℝ ({A, C, B} : Set Pt) := by
    rw [show ({A, C, B} : Set Pt) = {A, B, C} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact affineIndependent_iff_not_collinear_set.mp cfg.affineIndependent_ABC
  -- the directed-angle equalities of the chase
  have e1 : (2 : ℤ) • ∡ M B I = (2 : ℤ) • ∡ M B C + (2 : ℤ) • ∡ C B I := by
    rw [← smul_add, oangle_add hMB hBC.symm hIB]
  have e2 : (2 : ℤ) • ∡ M B C = (2 : ℤ) • ∡ M A C :=
    Sphere.two_zsmul_oangle_eq hMΓ hBΓ hAΓ hCΓ hMB.symm hBC hMA.symm hAC
  have e3 : (2 : ℤ) • ∡ C B I = (2 : ℤ) • ∡ I B A := by
    have h : ∡ C B I = ∡ I B A := by
      simpa using (cfg.triangleABC.oangle_incenter_eq (show (1 : Fin 3) ≠ 2 by decide)
        (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide))
    rw [h]
  have e4 : (2 : ℤ) • ∡ B I M = (2 : ℤ) • ∡ B I A :=
    hcolMIA.two_zsmul_oangle_eq_right hMI hIA.symm
  have e5 : (2 : ℤ) • ∡ B I A = (2 : ℤ) • ∡ I B A + (2 : ℤ) • ∡ B A I := by
    have hsum := oangle_add_oangle_add_oangle_eq_pi (p₁ := A) (p₂ := B) (p₃ := I)
      hAB.symm hIB hIA.symm
    have h1 : ∡ B I A = π - ∡ A B I - ∡ I A B := by rw [← hsum]; abel
    rw [h1, oangle_rev I B A, oangle_rev B A I,
      smul_sub, smul_sub, Real.Angle.two_zsmul_coe_pi, smul_neg, smul_neg]
    abel
  have e6 : (2 : ℤ) • ∡ B A I = (2 : ℤ) • ∡ M A C := by
    have hbis : ∡ B A I = ∡ I A C := by
      simpa using (cfg.triangleABC.oangle_incenter_eq (show (0 : Fin 3) ≠ 1 by decide)
        (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide))
    have hcoll : (2 : ℤ) • ∡ M A C = (2 : ℤ) • ∡ I A C :=
      hcolMAI.two_zsmul_oangle_eq_left hMA hIA
    rw [hbis, ← hcoll]
  -- nondegeneracy of `△IMB`: `2 • ∡ I M B = 2 • ∡ A C B ≠ 0`
  have hnd_IMB : ∡ I M B ≠ 0 ∧ ∡ I M B ≠ π := by
    rw [← Real.Angle.two_zsmul_ne_zero_iff,
      hcolIMA.two_zsmul_oangle_eq_left hMI.symm hMA.symm,
      Sphere.two_zsmul_oangle_eq hAΓ hMΓ hCΓ hBΓ hMA hMB hAC.symm hBC.symm,
      Real.Angle.two_zsmul_ne_zero_iff, oangle_ne_zero_and_ne_pi_iff_not_collinear]
    exact hncolACB
  -- assemble: `△BIM` is isosceles
  refine dist_eq_of_two_zsmul_oangle_eq ?_ hnd_IMB.1 hnd_IMB.2
  rw [e1, e2, e3, e4, e5, e6]; abel

/-! ### Assembling the result -/

/-- The statement of the lemma, in terms of the configuration: `MB = MC = MI`. -/
theorem result_cfg :
    dist cfg.M cfg.B = dist cfg.M cfg.C ∧ dist cfg.M cfg.C = dist cfg.M cfg.incenter := by
  refine ⟨cfg.dist_M_B_eq_dist_M_C, ?_⟩
  -- `MC = MB = MI`
  rw [← cfg.dist_M_B_eq_dist_M_C]
  exact cfg.dist_M_B_eq_dist_M_incenter

end Cfg

end

/-! ### The unbundled statement -/

variable {V Pt : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]
variable [NormedAddTorsor V Pt] [Fact (finrank ℝ V = 2)]

/-- **Incenter / Arc-Midpoint Lemma (Fact 5).**
Let triangle `ABC` be inscribed in `Γ` with incenter `I`, and let `M` be the midpoint of the arc
`BC` of `Γ` not containing `A`. Then `MB = MC = MI`. -/
theorem result {A B C I M : Pt} {Γ : Sphere Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (circumsphere_ABC_eq_Γ :
      (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere = Γ)
    (incenter_eq_I :
      (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).incenter = I)
    (A_mem_Γ : A ∈ (Γ : Set Pt)) (B_mem_Γ : B ∈ (Γ : Set Pt)) (C_mem_Γ : C ∈ (Γ : Set Pt))
    (A_ne_B : A ≠ B) (A_ne_C : A ≠ C)
    (M_eq : M = (Sphere.Arc.avoiding B_mem_Γ A_mem_Γ C_mem_Γ A_ne_B A_ne_C).midpoint) :
    dist M B = dist M C ∧ dist M C = dist M I := by
  -- Reduce to the bundled, canonical version.  After substituting the defining equations, the
  -- variable `Γ` becomes `circumsphere`, `I` becomes `incenter`, and `M` becomes the canonical
  -- arc midpoint.  The membership/≠ proofs in `M_eq`'s arc differ from the ones `Cfg` derives,
  -- but they prove the same `Prop`s, so by proof irrelevance the two arcs (hence the two `M`s)
  -- are definitionally equal, and `exact cfg.result_cfg` should close the goal.
  subst circumsphere_ABC_eq_Γ
  subst incenter_eq_I
  subst M_eq
  exact (Cfg.mk A B C affineIndependent_ABC).result_cfg

end IncenterArcMidpoint
