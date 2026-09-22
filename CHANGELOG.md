# Changelog

## 1.1.0

- Define `Arc.midpoint` as the structural anchor. Membership and perpendicular-bisector results
  now hold for every arc; measure bisection requires only nonzero radius, and strict positional
  properties require only `¬IsSinglePoint`.
- Prove an unconditional endpoint-sum identity and use it for complementary measures,
  constructor measures, chord length, and midpoint bisection. Complementary measures no longer
  require dimension two.
- Recover the anchor from non-diametral endpoints and branch data. Keep the angle-symmetry
  theorem in `Measure`, so the structural modules contain no angle statements.
- Update the four case studies for the revised API and state the Chinese MO 2012 P1 conclusion
  as two half-angle equalities.

The Lean and Mathlib versions are unchanged. The Zenodo concept DOI remains
`10.5281/zenodo.21964632`; publishing the 1.1.0 archive is a separate release step.
