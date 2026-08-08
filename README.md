# arcs-for-mathlib

[![Lean CI](https://github.com/Scarlett-le/arcs-for-mathlib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Scarlett-le/arcs-for-mathlib/actions/workflows/lean_action_ci.yml)

**First-class circular arcs for Mathlib's Euclidean geometry, in Lean 4.**

The pinned Mathlib snapshot has a rich API for circles: `Sphere`, `secondInter`, `circumsphere`,
power of a point, Ptolemy, tangency, unoriented (`∠`) angles, and oriented (`∡`) angles. What it
lacks is an object for an **arc**: something that joins two points on a circle while selecting one
of the two portions between them.

Consequently, statements such as "the arc `BC` not containing `A`", "the midpoint of an arc", or
"`P` lies on arc `XY`" must otherwise be re-encoded problem by problem using `secondInter`, angle
conditions, and side relations. Those encodings can prove the intended facts, but the arc itself is
not a reusable object.

This repository introduces `EuclideanGeometry.Sphere.Arc`, built on Mathlib's existing `Sphere`
and angle machinery without adding a project-defined axiomatic layer. It provides complementary-arc
selection, membership and interior, degeneracy semantics, real-valued measure, midpoint geometry,
and bridges to inscribed-angle and tangent-chord results. Three Olympiad problems and one benchmark
incenter lemma are formalized on top of the API, with no `sorry` or `admit`.

## Example

The Incenter/Arc-Midpoint Lemma states that if `M` is the midpoint of arc `BC` avoiding `A`, then
`MB = MC = MI`:

```lean
theorem result {A B C I M : Pt} {Γ : Sphere Pt}
    (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (circumsphere_ABC_eq_Γ :
      (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).circumsphere = Γ)
    (incenter_eq_I :
      (⟨![A, B, C], affineIndependent_ABC⟩ : Triangle ℝ Pt).incenter = I)
    (A_mem_Γ : A ∈ (Γ : Set Pt)) (B_mem_Γ : B ∈ (Γ : Set Pt)) (C_mem_Γ : C ∈ (Γ : Set Pt))
    (A_ne_B : A ≠ B) (A_ne_C : A ≠ C)
    (M_eq : M = (Sphere.Arc.avoiding B_mem_Γ A_mem_Γ C_mem_Γ A_ne_B A_ne_C).midpoint) :
    dist M B = dist M C ∧ dist M C = dist M I
```

The geometric phrase "the midpoint of arc `BC` avoiding `A`" is represented by one typed term.
The same value can be passed to `.midpoint`, membership, `.interior`, `.measure`, and `.opposite`
without reconstructing its branch choice.

## Building and verification

The project requires an `elan`-managed toolchain. Lean is pinned by `lean-toolchain`, and Mathlib is
pinned by `lake-manifest.json`.

```bash
lake exe cache get
lake build
lake env lean ArcsForMathlib/Audit.lean
```

`lake exe cache get` downloads prebuilt Mathlib oleans; building Mathlib from source on a cold setup
can take hours. The top-level module imports the complete arc library and all four case studies, so
`lake build` checks the full artifact.

`ArcsForMathlib/Audit.lean` is an executable axiom audit. Its guarded `#print axioms` commands fail
if the dependency set of any final case-study theorem changes. At the pinned snapshot, each theorem
depends exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

There are no project-defined axioms. GitHub Actions runs both the build and this audit. Documentation
deployment is intentionally not part of verification CI; it can be enabled separately after GitHub
Pages is configured for the repository.

Pinned versions:

- Lean: `v4.30.0-rc2`
- Mathlib: `d2ffb33f962f4f8d59e5e80f1ca85150966b49b7`

## Layout

```text
ArcsForMathlib.lean                    umbrella module for the full artifact
ArcsForMathlib/
  Basic.lean                           umbrella module for the reusable geometry library
  Audit.lean                           guarded #print axioms audit for the four final theorems
  Auxlemma.lean                        general lemmas absent from the pinned Mathlib snapshot
  Sphere/
    RadicalAxis.lean                   radical-axis and power-of-a-point infrastructure
    Arc/
      Basic.lean                       Arc structure, opposite, and the four constructors
      Degenerate.lean                  single-point and full-circle classification
      Structure.lean                   membership, interiors, and complementary-arc structure
      Measure.lean                     measure, midpoint, and angle bridges
  Archive/
    IncenterArcMidpoint.lean
    BMO1_2018P4.lean
    ChineseMO_2010P1.lean
    ChineseMO_2012P1.lean
```

The arc-module dependency order is
`Auxlemma -> Arc.Basic -> {Arc.Degenerate, Arc.Structure} -> Arc.Measure`.

## The abstraction

An arc stores a left endpoint and a structural anchor `mid`, both on the sphere:

```lean
structure Arc (s : Sphere P) where
  left     : P
  mid      : P
  left_mem : left ∈ s
  mid_mem  : mid ∈ s

def right (a : Arc s) : P :=
  reflection (line[ℝ, s.center, a.mid]) a.left
```

The right endpoint is derived rather than stored. Carrying `mid` instead of two endpoints plus a
branch flag keeps the choice between complementary arcs in the data. It also represents coincident
endpoints uniformly: such an arc is either a single point or a full circle, classified by
`IsSinglePoint`, `IsFullCircle`, and `IsDegenerate`.

Membership uses strict same-sidedness of `lineOrOrthRadius`, with the endpoints added back:

```lean
def interior (a : Arc s) : Set P :=
  { p | p ∈ s ∧ (s.lineOrOrthRadius a.left a.right).SSameSide a.mid p }

theorem coe_eq_interior_union_endpoints (a : Arc s) :
    (a : Set P) = a.interior ∪ {a.left, a.right}
```

`lineOrOrthRadius` handles the coincident-endpoint case, so downstream membership statements do not
need to split on endpoint equality merely to define the relevant affine subspace.

### Constructors

The four constructors are organized by the involution `opposite`:

| Constructor | Meaning | Additional conditions |
|---|---|---|
| `Arc.minor hA hC hNotDiam` | minor arc from `A` to `C` | endpoints are not diametrically opposite |
| `Arc.major hA hC hNotDiam` | major arc from `A` to `C` | same; defined as the opposite minor arc |
| `Arc.through hA hB hC hBA hBC` | arc from `A` to `C` through `B` | `B ≠ A` and `B ≠ C` |
| `Arc.avoiding hA hB hC hBA hBC` | arc from `A` to `C` avoiding `B` | same; defined as the opposite through arc |

The arguments `hA`, `hB`, and `hC` are sphere-membership proofs. `minor_right` and `major_right`
identify the right endpoint in arbitrary dimension; the current semantic theorems for `through` and
`avoiding`, including `through_right`, `avoiding_right`, `mem_through`, and `not_mem_avoiding`, use a
two-dimensional hypothesis.

### Measure and bridges

`Arc.measure : ℝ` is a central-angle measure in `[0, 2π]`, including the represented degenerate
cases: a single point has measure `0`, a full circle has measure `2π`, and a zero-radius sphere has
measure `0`. `Arc.midpoint` is defined for every arc; its geometric bisection properties and its
identification with the structural anchor are currently proved for nondegenerate arcs.

```lean
theorem measure_add_measure_opposite [Fact (Module.finrank ℝ V = 2)]
    (a : Arc s) (hr : s.radius ≠ 0) :
    a.measure + a.opposite.measure = 2 * π

/-- Inscribed angle theorem, in terms of arc measure. -/
theorem inscribed_angle_eq_half_measure (a : Arc s)
    {B : P} (hB : B ∈ a.opposite.interior) (hBl : B ≠ a.left) (hBr : B ≠ a.right) :
    ∠ a.left B a.right = a.measure / 2

/-- Tangent-chord angle, in radius-chord form. -/
theorem tangent_chord_angle_eq_pi_div_two_add_half_measure (a : Arc s)
    (hne : a.left ≠ a.right) (h_le : a.measure ≤ π) :
    InnerProductGeometry.angle (a.left -ᵥ s.center) (a.right -ᵥ a.left)
      = π / 2 + a.measure / 2
```

The complementary-measure and inscribed-angle theorems currently require planarity. The
radius-chord tangent theorem is dimension-independent. Public interfaces use unoriented angles and
real-valued measure; oriented angles appear selectively inside proofs where Mathlib's existing
quotient-valued machinery is useful.

## Case studies

The case studies drove the library design: their statements determined which constructors,
membership results, midpoint facts, and angle bridges were needed.

| Case study | Formalized conclusion |
|---|---|
| Incenter/Arc-Midpoint Lemma | `M` is the midpoint of arc `BC` avoiding `A` implies `MB = MC = MI` |
| BMO1 2018 P4 | tangents at `D`, `E` meet at `F`; `∠ACD = ∠ECB` implies `∠EFD = ∠ACD + ∠ECB` |
| Chinese MO 2010 P1 | under the stated secant and arc-position hypotheses, `C`, `F`, `M`, `N` are concyclic |
| Chinese MO 2012 P1 | the specified arc midpoints and tangent circles imply that `AP` bisects `∠BAC` |

## Upstream status

General lemmas discovered while proving the case studies have been separated from the arc API and
submitted to Mathlib. Status below was checked on 2026-08-08.

Merged through Bors:

- same-side and opposite-side scalar-multiple criteria ([#40245])
- sphere chord, radius, interior, and central-angle boundary lemmas ([#35957], [#36241], [#41143], [#41314])
- `mem_span_singleton_of_inner_eq_zero_of_inner_eq_zero` ([#35956])
- `angle_add_angle_eq_of_sbtw_of_sameRay` ([#40497])

Open:

- `Sphere.Arc.Basic` ([#34164])
- central-angle branches ([#41123])
- doubled oriented tangent-chord interfaces ([#41121])
- signed-power converses ([#40651])
- inner-product angle criteria ([#41188])
- `secondInter` formulae ([#42308])

The remaining arc modules are intended to follow `Basic` in dependency order.

[#34164]: https://github.com/leanprover-community/mathlib4/pull/34164
[#35956]: https://github.com/leanprover-community/mathlib4/pull/35956
[#35957]: https://github.com/leanprover-community/mathlib4/pull/35957
[#36241]: https://github.com/leanprover-community/mathlib4/pull/36241
[#40245]: https://github.com/leanprover-community/mathlib4/pull/40245
[#40497]: https://github.com/leanprover-community/mathlib4/pull/40497
[#40651]: https://github.com/leanprover-community/mathlib4/pull/40651
[#41121]: https://github.com/leanprover-community/mathlib4/pull/41121
[#41123]: https://github.com/leanprover-community/mathlib4/pull/41123
[#41143]: https://github.com/leanprover-community/mathlib4/pull/41143
[#41188]: https://github.com/leanprover-community/mathlib4/pull/41188
[#41314]: https://github.com/leanprover-community/mathlib4/pull/41314
[#42308]: https://github.com/leanprover-community/mathlib4/pull/42308

## Known gaps

- **No signed individual oriented-angle interface.** The public inscribed-angle and tangent-chord
  bridges do not distinguish `φ` from `-φ`; proofs needing a specific sign still provide branch
  information locally.
- **No classical tangent-ray interface.** The existing theorem relates a radius to a chord, not a
  chosen one of the two tangent rays.
- **Degenerate arc midpoints.** `Arc.midpoint` is total, but its geometric membership and bisection
  properties are established only under `¬IsDegenerate`.
- **Some planar assumptions are global.** Several theorems use
  `[Fact (Module.finrank ℝ V = 2)]` where a future local-coplanarity formulation may suffice.

## Contributing

Issues and pull requests are welcome, particularly for the gaps above. Code follows
[Mathlib's style guide](https://leanprover-community.github.io/contribute/style.html) and naming
conventions because the intended destination is upstream Mathlib. New declarations should include
appropriate documentation, and submitted proofs must not contain `sorry`.

## License

Apache 2.0. See [LICENSE](LICENSE).
