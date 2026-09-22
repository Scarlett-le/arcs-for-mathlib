# Changelog

## 1.1.0

- Define `Arc.midpoint` as the structural anchor. Membership and perpendicular-bisector results
  now hold for every arc; measure bisection requires only nonzero radius, and strict positional
  properties require only `¬IsSinglePoint`.
- Prove an unconditional endpoint-sum identity and use it for complementary measures,
  constructor measures, and midpoint bisection. Complementary measures no longer
  require dimension two.
- Recover the anchor from the scalar bounds `measure < π` and `π < measure`, including
  the zero-radius case in the former. Keep the angle-symmetry
  theorem in `Measure`, so the structural modules contain no angle statements.
- Expose the scalar long-arc and central-angle criteria and named measure branches. Prove
  chord length directly from the law of cosines, then derive its measure form. Remove two
  unused chord-related wrappers.
- Update the four case studies for the revised API and state the Chinese MO 2012 P1 conclusion
  as two half-angle equalities.

The Lean and Mathlib versions are unchanged. The Zenodo concept DOI remains
`10.5281/zenodo.21964632`; publishing the 1.1.0 archive is a separate release step.
