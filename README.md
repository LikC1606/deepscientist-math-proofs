# TheoremOS: four LeanEval proofs

This snapshot contains four independently reviewed candidates for statement
revision 1 of the following LeanEval problems:

| Problem | Solver commit | Persisted role turns |
| --- | --- | ---: |
| `annals_improved_bounds_sunflower_lemma` | `89d3b2ae1046b769c61bec916b7b2e514bb3b51f` | 1 |
| `annals_lorentzian_polynomials` | `dc082e99532a292b8d7cfd800f9830db8651e696` | 32 |
| `annals_optimal_moebius` | `b48eebc842a49f114c97ac439f3aa3991858284b` | 38 |
| `annals_algebraic_integers` | `431e8fb70db64d14b8d510a4f1e759ff5be3dada` | 64 |

The proofs were produced using TheoremOS, the standalone continuation of
DeepScientist Math, with `gpt-6.1-sol` and `xhigh` reasoning. The cooperative
workflow uses a Lead, two Researchers, an Engineer, and fixed-candidate
independent review. The counts describe persisted final continuations; they
exclude earlier research and retries and are not total production cost.

These are continuation results, reusing saved same-problem research and helpers.
Human direction selected tasks, requested runtime recovery, and authorized
submission. A coding assistant repaired the runtime and prepared this package.
The Sunflower recovery also integrated a saved same-problem completion before
fresh helper rechecks and independent review; its one recorded role turn is the
final reviewer, not a claim of a one-turn solve.

Each candidate passed local official `lake test` against
`leanprover/lean-eval` commit `38361be884302c7edce1908c4aef8296eb2cb27e`,
Lean `4.35.0-rc3`, and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.
Both Nanoda and the Lean default kernel accepted the solutions. Local acceptance
does not establish hosted CI acceptance or public leaderboard inclusion.

Each workspace contains `verification.json` with source hashes, the independent
review binding, and a local official comparator receipt. Every published proof
file is byte-identical to its reviewed solver commit and accepted official
projection. Dependency files preserve the frozen pins. Packaging made no proof
edits and no new solver model calls.

Only solver-owned proof sources and dependency metadata are included. The
submission service generates its own trusted challenge and evaluation bridge.
