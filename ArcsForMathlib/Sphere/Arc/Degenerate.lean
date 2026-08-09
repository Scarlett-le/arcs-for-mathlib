/-
Copyright (c) 2026 Li Jiale. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Li Jiale
-/
module

public import ArcsForMathlib.Sphere.Arc.Basic

/-!
# Degenerate arcs

This file defines predicates classifying degenerate arcs on spheres.

## Main definitions

* `EuclideanGeometry.Sphere.Arc.IsSinglePoint`: An arc whose mid equals its left endpoint, so the
  arc collapses to a single point.
* `EuclideanGeometry.Sphere.Arc.IsFullCircle`: An arc whose left and right endpoints coincide but
  whose mid differs from the left endpoint.
* `EuclideanGeometry.Sphere.Arc.IsDegenerate`: An arc that is either a single point or a full
  circle.

## Main results

* `EuclideanGeometry.Sphere.Arc.not_isSinglePoint_and_isFullCircle`: the single-point and
  full-circle predicates are mutually exclusive.
* `EuclideanGeometry.Sphere.Arc.isSinglePoint_or_isFullCircle_of_left_eq_right`: an arc whose
  left and right endpoints coincide is either a single point or a full circle.
* `EuclideanGeometry.Sphere.Arc.mid_eq_pointReflection_center_left_of_isFullCircle`: for a
  full-circle arc, the mid is the reflection of the left endpoint through the center.
* `EuclideanGeometry.Sphere.Arc.left_ne_right_iff_not_isDegenerate`: an arc has distinct left and
  right endpoints iff it is not degenerate.
* `EuclideanGeometry.Sphere.Arc.coe_eq_singleton_of_isSinglePoint`: a single-point arc coerces to
  the singleton containing its endpoint.
* `EuclideanGeometry.Sphere.Arc.coe_eq_sphere_of_isFullCircle`: a full-circle arc coerces to its
  underlying sphere.
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

/-- An arc is a single point when its mid equals its left endpoint, which forces the right
endpoint to coincide as well. -/
def IsSinglePoint (a : Arc s) : Prop := a.mid = a.left

/-- An arc is a full circle when its left and right endpoints coincide but its mid differs from
the left endpoint. -/
def IsFullCircle (a : Arc s) : Prop :=
  a.left = a.right ∧ a.mid ≠ a.left

/-- An arc is degenerate when it is either a single point or a full circle. -/
def IsDegenerate (a : Arc s) : Prop :=
  a.IsSinglePoint ∨ a.IsFullCircle

/-! ### Basic equivalences -/

/-- An arc cannot be both a single point and a full circle. -/
theorem not_isSinglePoint_and_isFullCircle (a : Arc s) :
    ¬(a.IsSinglePoint ∧ a.IsFullCircle) :=
  fun ⟨hs, hf⟩ => hf.2 hs

/-- A single-point arc has equal left and right endpoints. -/
theorem left_eq_right_of_isSinglePoint (a : Arc s) (h : a.IsSinglePoint) :
    a.left = a.right :=
  left_eq_right_of_left_eq_mid a h.symm

/-- A full-circle arc has equal left and right endpoints. -/
theorem left_eq_right_of_isFullCircle (a : Arc s) (h : a.IsFullCircle) :
    a.left = a.right := h.1

/-- An arc with equal left and right endpoints is either a single point or a full circle,
determined by whether the mid equals the left endpoint. -/
theorem isSinglePoint_or_isFullCircle_of_left_eq_right (a : Arc s)
    (h : a.left = a.right) : a.IsSinglePoint ∨ a.IsFullCircle := by
  by_cases hm : a.mid = a.left
  · exact Or.inl hm
  · exact Or.inr ⟨h, hm⟩

/-- An arc with distinct left and right endpoints is not a single point. -/
theorem not_isSinglePoint_of_left_ne_right (a : Arc s) :
    a.left ≠ a.right → ¬a.IsSinglePoint :=
  mt (left_eq_right_of_isSinglePoint a)

/-- An arc with distinct left and right endpoints is not a full circle. -/
theorem not_isFullCircle_of_left_ne_right (a : Arc s) :
    a.left ≠ a.right → ¬a.IsFullCircle :=
  mt (left_eq_right_of_isFullCircle a)

/-! ### Characterizations -/

/-- For a full-circle arc, the mid is the reflection of the left endpoint through the center. -/
theorem mid_eq_pointReflection_center_left_of_isFullCircle (a : Arc s) (h : a.IsFullCircle) :
    a.mid = AffineEquiv.pointReflection ℝ s.center a.left := by
  obtain ⟨hLR, hML⟩ := h
  have hleft_line : a.left ∈ line[ℝ, s.center, a.mid] :=
    (left_eq_right_iff_mem_line a).mp hLR
  have hcol : Collinear ℝ ({a.mid, s.center, a.left} : Set P) := by
    have h' : Collinear ℝ ({a.left, s.center, a.mid} : Set P) :=
      collinear_insert_of_mem_affineSpan_pair hleft_line
    simpa [Set.insert_comm, Set.pair_comm] using h'
  have hdiam : s.IsDiameter a.mid a.left :=
    isDiameter_iff_mem_and_mem_and_wbtw.2 ⟨a.mid_mem, a.left_mem,
      wbtw_of_collinear_of_dist_center_le_radius hcol a.mid_mem
        (by simpa using radius_nonneg_of_mem a.mid_mem) a.left_mem hML⟩
  simpa [AffineEquiv.pointReflection_apply_eq_equivPointReflection_apply]
    using hdiam.symm.pointReflection_center_left.symm

/-! ### Point-set semantics -/

/-- The interior of a single-point arc is empty. -/
theorem interior_eq_empty_of_isSinglePoint (a : Arc s) (h : a.IsSinglePoint) :
    a.interior = ∅ := by
  ext p
  rw [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact (sSameSide_of_mem_interior hp).left_notMem
    (by rw [h]; exact left_mem_lineOrOrthRadius)

/-- A single-point arc contains exactly its coincident endpoint. -/
theorem coe_eq_singleton_of_isSinglePoint (a : Arc s) (h : a.IsSinglePoint) :
    (a : Set P) = {a.left} := by
  rw [coe_eq_interior_union_endpoints, interior_eq_empty_of_isSinglePoint a h,
    left_eq_right_of_isSinglePoint a h, Set.empty_union]
  simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem]

/-- A full-circle arc contains every point of its underlying sphere. -/
theorem coe_eq_sphere_of_isFullCircle (a : Arc s) (h : a.IsFullCircle) :
    (a : Set P) = (s : Set P) := by
  ext p
  constructor
  · exact fun hp => (mem_iff.mp hp).1
  · intro hp
    refine mem_iff.mpr ⟨hp, ?_⟩
    by_cases hpl : p = a.left
    · exact Or.inl hpl
    · right; right
      rw [lineOrOrthRadius_of_eq (left_eq_right_of_isFullCircle a h)]
      exact sSameSide_orthRadius_of_mem a.left_mem a.mid_mem hp h.2.symm (Ne.symm hpl)

/-- An arc has distinct left and right endpoints if and only if it is not degenerate. -/
theorem left_ne_right_iff_not_isDegenerate (a : Arc s) :
    a.left ≠ a.right ↔ ¬a.IsDegenerate :=
  ⟨fun h hd => hd.elim
    (fun hs => h (left_eq_right_of_isSinglePoint a hs))
    (fun hf => h (left_eq_right_of_isFullCircle a hf)),
   fun h heq => h (isSinglePoint_or_isFullCircle_of_left_eq_right a heq)⟩

end

end Arc

end Sphere

end EuclideanGeometry
