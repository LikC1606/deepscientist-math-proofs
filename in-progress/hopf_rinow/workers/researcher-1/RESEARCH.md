# Current checkpoint: coordinate metric chart derivative norm

Researcher-1, task `help_7a33deda96c44a0190b7520489080182`.

Added `Submission.Helpers.sqrt_coordinate_metric_chart_derivative_eq_norm` at
`generated/hopf_rinow/Submission/Helpers.lean:29`.

The exact premise is the quadratic identity supplied by the coordinate metric
construction: for `z ∈ (extChartAt I p).target` and `w : E`,
`g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
(Set.range I) z w‖ ^ 2`, with the scoped Bundle Riemannian tangent norm.
For `x ∈ (extChartAt I p).source` and `v : TangentSpace I x`, the conclusion is
`sqrt (g (extChartAt I p x) (mfderiv I (modelWithCornersSelf ℝ E)
(extChartAt I p) x v) (same)) = ‖v‖`.

The helper needs only `IsManifold I 1 M` and the Riemannian bundle. It does not
need finite dimension, boundarylessness, smoothness/continuity of the metric,
distance, connectedness, compactness, or completeness. The library theorem
`mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'` already cancels the two
derivatives within `range I`, so conversion to the ordinary inverse derivative
is unnecessary. Apply the composition identity to `v`, rewrite the chart left
inverse in the dependent tangent norm, and use `Real.sqrt_sq (norm_nonneg v)`.

The Riemannian norm scope is explicit in the statement. A pointwise Riemannian
`NormedAddCommGroup` instance is local to the proof, to elaborate `norm_nonneg`.
No imports, existing declarations/proofs/definitions, options, or namespace
contexts were changed. `Submission.lean` is untouched. All probes were removed;
the addition has no placeholders, axioms, or unsafe code.

Saved Helpers check: pinned `check_lean`, `exitCode: 0`, `timedOut: false`,
22720 ms. Full saved Submission/imports check also passed: `exitCode: 0`,
`timedOut: false`; ChallengeDeps 63207 ms, Helpers 67550 ms, Submission 60170 ms.

Helpers SHA256: `67611d6117af48815fa39934510a692d3bf149813669d53cfb2a5e3cb81e4d83`.
Unchanged Submission SHA256:
`f50bee957e9ae45913950fad3c1b67d8c7d2817332f9634129a2f51515a4ca55`.

This completes the assigned manifold norm bridge. It can replace the coordinate
speed `sqrt (g z w w)` by the Riemannian norm of a tangent velocity once the
manifold chain rule identifies `w`. It does not prove local minimality or
endpoint continuation. The original `Submission.hopf_rinow` still has its
unchanged `sorry` at line 110; no original-target or official-evaluation success
is claimed.
