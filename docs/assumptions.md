# Public assumption audit

Generated from 177 explicitly named public declarations by `scripts/audit_assumptions.py`. Signatures include inherited section parameters. Conclusions and proof bodies are excluded from the premise lists.

First, exactly the following public declarations require two-dimensionality: in `Basic`, `sbtw_mid_midpoint_opposite_mid`, `sOppSide_mid_opposite_mid`, `sOppSide_mid_opposite_mid_line`, `eq_or_eq_opposite_of_left_eq_of_right_eq`, `eq_of_left_eq_of_right_eq_of_sSameSide_mid`, `sSameSide_opposite_mid_iff`, `eq_minor_or_eq_major_of_ne`, `through_right`, `mem_interior_through`, `mem_through`, `avoiding_right`, `notMem_avoiding`; in `Degenerate`, `eq_minor_or_eq_major`; in `Structure`, `mem_arc_or_mem_opposite`, `mem_interior_or_mem_opposite_interior`, `sOppSide_of_mem_interior_of_mem_opposite_interior`, `interior_disjoint_opposite`, `mem_and_mem_opposite_iff_eq_left_or_eq_right`, `eq_of_left_eq_of_right_eq_of_mem_interior_of_mem_interior`, `eq_of_left_eq_of_right_eq_of_coe_eq`, `mem_minor_interior_or_mem_major_interior`, `mem_interior_through_iff`, `mem_interior_through_of_sSameSide`, `sSameSide_of_mem_interior_through`, `through_eq_of_mem_interior`, `avoiding_eq_of_mem_opposite_interior`, `through_eq_through_of_sSameSide`, `avoiding_eq_avoiding_of_sSameSide`, `through_eq_avoiding_of_sOppSide`, `avoiding_eq_through_of_sOppSide`, `through_eq_minor_of_mem_minor_interior`, `through_eq_major_of_mem_major_interior`; in `Measure`, `measure_through_eq_angle_add_angle_of_mem_minor_interior`, `angle_eq_measure_sub_angle_of_mem_through_interior`, `inscribed_angle_eq_half_measure`, `angle_ge_pi_div_two_of_mem_minor_interior`, `angle_le_pi_div_two_of_mem_major_interior`, `pi_div_two_lt_angle_of_mem_minor_interior`, `angle_lt_pi_div_two_of_mem_major_interior`, `mem_major_interior_iff_angle_lt_pi_div_two`, `mem_minor_interior_iff_pi_div_two_lt_angle`, `angle_bisect_of_mem_opposite`, `angle_eq_of_mem_opposite_interior`, `angle_add_angle_opposite_eq_pi`. No other public declaration in these modules carries a `[Fact (Module.finrank ℝ V = 2)]` assumption.

Second, exactly the following public declarations take `s.radius ≠ 0` as an explicit parameter: in `Basic`, `minorMidpoint_self`; in `Measure`, `measure_eq_two_pi_of_isFullCircle`, `measure_eq_zero_iff_isSinglePoint`, `measure_eq_two_pi_iff_isFullCircle`, `measure_eq_angle_iff_not_sSameSide`, `measure_eq_pi_iff_isDiameter`, `cos_half_measure_eq_zero_iff_isDiameter`, `sSameSide_iff_cos_half_measure_neg`, `measure_opposite`, `measure_add_measure_opposite`, `angle_center_midpoint_eq_half_measure`. No other public declaration in these modules takes `s.radius ≠ 0` explicitly.

Third, exactly the following public declarations take `¬a.IsSinglePoint` as an explicit parameter: in `Measure`, `midpoint_ne_left`, `midpoint_ne_right`, `midpoint_mem_interior`, `midpoint_notMem_lineOrOrthRadius`, `midpoint_notMem_line`. No other public declaration in these modules takes `¬a.IsSinglePoint` explicitly.

No public declaration in these four modules takes `¬a.IsDegenerate` as an explicit parameter.

## Structural-layer checks

`Basic`, `Structure`, and `Degenerate` contain none of `∠`, `∡`, `Real.Angle`, or `Module.Oriented`.

Occurrences of `left_ne_right_iff_not_isDegenerate` in the four modules:

```text
Degenerate.lean:35:* `EuclideanGeometry.Sphere.Arc.left_ne_right_iff_not_isDegenerate`: an arc has distinct left and
Degenerate.lean:160:theorem left_ne_right_iff_not_isDegenerate (a : Arc s) :
```
