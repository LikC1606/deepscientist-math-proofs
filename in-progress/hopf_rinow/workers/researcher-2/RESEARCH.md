# Current checkpoint: quadratic composition Hessian at a zero

Researcher-2, task `help_656306d960644189be9ad1427c255991`.
The assigned calculus bridge is complete. Three new complete helpers are
saved at the start of `generated/hopf_rinow/Submission/Helpers.lean`.
Existing imports, declarations, contexts, options, and `Submission.lean`
are unchanged. No new imports, probes, placeholders, or instances remain.

## Checked statements

All statements allow distinct real normed domain E and target F. Let
`B : F →L[ℝ] F →L[ℝ] ℝ`, `ξ : E → F`, `p : E`, and
`A : E →L[ℝ] F`, with `ξ p = 0` and `HasFDerivAt ξ A p`.

- `hasFDerivAt_fderiv_bilinear_self_of_zero` (:29): if ξ is differentiable
  near p and `fderiv ℝ ξ` is differentiable at p, then
  `HasFDerivAt (fderiv ℝ (fun y => B (ξ y) (ξ y)))
  (B.bilinearComp A A + B.flip.bilinearComp A A) p`.
- `hasFDerivAt_fderiv_bilinear_self_of_contDiffAt` (:54): derives both
  regularity premises internally from `ContDiffAt ℝ 2 ξ p` and gives the
  same exact second derivative.
- `fderiv_fderiv_bilinear_self_of_contDiffAt` (:67): evaluated form,
  `fderiv ℝ (fderiv ℝ (fun y => B (ξ y) (ξ y))) p u w =
  B (A u) (A w) + B (A w) (A u)`.

No symmetry, positivity, finite dimensionality, or completeness assumptions
are needed. The formula on the diagonal is therefore `2 * B (A u) (A u)`;
with positive B and injective A this is positive for nonzero u. A fixed
factor such as τ² can be absorbed into B.

## Proof and dependencies

Use `B.fderiv_of_bilinear` locally to express the first derivative using
`B.precompR` and `B.precompL`. Differentiate those continuous bilinear
expressions via `ContinuousLinearMap.hasFDerivAt_of_bilinear`. All terms
containing the second derivative of ξ vanish because ξ p = 0. CLM
extensionality and simp identify the remaining bundled Hessian.
The C2 wrapper uses `ContDiffAt.eventually`, `ContDiffAt.fderiv_right`,
and `ContDiffAt.differentiableAt_one` from the existing imports.

## Verification and remaining obligations

Saved Helpers-only check passed: exitCode 0, timedOut false, 24532 ms.
Full saved Submission/import check is pending. `hopf_rinow` is untouched;
this conditional calculus result does not prove the missing local
squared-distance formula or the original target. The primary must supply
that geometric formula, the endpoint-velocity derivative at the diagonal,
and the other midpoint-route hypotheses before using this Hessian result.
