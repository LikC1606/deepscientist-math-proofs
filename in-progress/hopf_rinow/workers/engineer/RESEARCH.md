# Current checkpoint: constant coordinate energy and path length

Research task `help_09bd1055fe214657989e4c337c3b026e`, engineer.
The assigned independent path-length bridge is complete. Added three checked
helpers at the start of `generated/hopf_rinow/Submission/Helpers.lean`.
Existing imports, declarations, options, and namespace context are unchanged;
all new scopes/instances are local to their statements/proofs. Submission is
unchanged. The current seed does not contain the earlier coordinate metric
construction; these helpers take its exact quadratic identity as a premise.

## Checked declarations and exact premises

All helpers assume only a real normed model E, a C1 manifold M modeled by I,
and `Bundle.RiemannianBundle (fun z : M => TangentSpace I z)`. Let
`c = extChartAt I p` and `g : E → E →L[ℝ] E →L[ℝ] ℝ`. Their common metric
premise is exactly:

```lean
∀ z ∈ (extChartAt I p).target, ∀ w : E,
  g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
    (extChartAt I p).symm (Set.range I) z w‖ ^ 2
```

The norms use the scoped Bundle Riemannian instance.

- `norm_mfderivWithin_inverse_chart_curve` (:29): for x:ℝ→E mapping S into
  c.target, t∈S, `UniqueDiffWithinAt ℝ S t`, and `HasDerivWithinAt x v S t`,
  concludes
  `‖mfderivWithin self I (c.symm ∘ x) S t 1‖ = sqrt(g(x t) v v)`.
  Uses `mfderivWithin_comp` with the exact inverse-chart derivative within
  range I, and identifies the coordinate derivative evaluated at 1 with v.
- `pathELength_inverse_chart_eq_of_constant_energy` (:65): for x,v:ℝ→E,
  a≤b, k≥0, x maps Icc a b into c.target, x'=v within Icc a b at every point,
  and `g(x t)(v t)(v t)=k^2` there, concludes
  `Manifold.pathELength I (c.symm ∘ x) a b = ENNReal.ofReal ((b-a)*k)`.
  Handles a=b separately. For a<b it applies the pointwise helper and
  integrates the constant speed using the within-Icc length formula.
  It needs no C1 curve premise. HasDerivAt implies the within derivative
  premise directly via `.hasDerivWithinAt`.
- `riemannianEDist_inverse_chart_le_of_constant_energy` (:106): under the same
  premises and `ContDiffOn ℝ 1 x (Icc a b)`, concludes
  `riemannianEDist I (c.symm(x a)) (c.symm(x b)) ≤ ofReal((b-a)*k)`.
  Constructs the C1 manifold path by composing x with c.symm, then applies
  `riemannianEDist_le_pathELength` and the checked length formula.

No finite dimension, boundarylessness, metric continuity/smoothness,
completeness, or symmetry/positivity of g is needed beyond the displayed
identity and energy equation. This applies directly to a smooth coordinate
spray curve once its constant energy is supplied. For actual `edist`, the
lead can rewrite with `IsRiemannianManifold.out`.

## Cooperation and remaining work

Read the explicitly cited current-session peer checkpoint
`8ac00c1d12ef5230c81e97408e378ff0542da283:RESEARCH.md`. Its radial Gauss helper
specializes to [0,1] and derives constant energy from Gauss pairing; the
present helpers handle arbitrary intervals and supplied spray energy, retain
the within-range derivative, and require no boundarylessness. No peer source
was integrated. No topology or Hessian/midpoint work was duplicated.

The three helpers are complete. The original Hopf–Rinow proof still needs the
lead's geometric integration; the unchanged original sorry remains.

## Validation

Final pinned `check_lean({files:["Submission.lean"]})` on actual saved sources
passed exitCode 0, timedOut false: ChallengeDeps cached, Helpers 23247 ms,
Submission 15855 ms. Earlier Helpers-only checks also passed. No new probes,
placeholders, axioms, unsafe code, or disallowed tactics remain. The only sorry
is the existing original target at Submission.lean:110. No full original-target
or independent official-evaluation success is claimed.

Helpers SHA256:
`c687cb941f8814d74e2beda264ec62e7a3058c78717e2998121e88e2e8832eae`.
Unchanged Submission SHA256:
`f50bee957e9ae45913950fad3c1b67d8c7d2817332f9634129a2f51515a4ca55`.
