# Continued mathematical work

Continues run 40fe716a-9414-4f77-84cd-fa0627fedf74 after 0 turns. This is not a from-zero attempt. Prior evidence is archived in /storage/zhangyueLab/wengyixuan/ssh_gpu/workspaces/lzh/.deepscientist-math-runs/leaneval-v1-batch-20261014-125935/restart-batch-restore-20261015-ebabb3b0/dimitrov. New runtime checks and final evaluation are required.

Saved proof candidate: 6a1de291e542fa81e2c0ad09ea5a7febb5faa097. Current files retain this work. Recheck before delivery.

# Continued mathematical work

Continues run 50dd46f8-f982-4410-bf39-e9aa85205173 after 40 turns. This is not a from-zero attempt. Prior evidence is archived in /storage/zhangyueLab/wengyixuan/ssh_gpu/workspaces/lzh/.deepscientist-math-runs/leaneval-v1-batch-20261014-125935/restart-session-recovery-20261015-484a4e72/dimitrov. New runtime checks and final evaluation are required.

Saved proof candidate: f0667d7f74901602844dbe29d49a81da18161233. Current files retain this work. Recheck before delivery.

# Dimitrov Current Checkpoint

## Empirical Energy Reduction, Revision 1

Assigned task: `energy_empirical_support`, digest
`03ede74147199063db182f11a47260eeab4783f03cc7a2ce8acab3d4b9fa3e11`.
Retained the exact
`Submission.Helpers.radial_finite_truncated_energy_of_probability_bound`
at `Submission/Helpers.lean:3128`. Both owned Lean sources are unchanged
from seed `30793fec9dae6930d4d2859456fa9460c3e9bc7f`. No repair, probe,
import, definition change or new assumption was needed.

Inspected its actual local prerequisite:
`radial_empirical_product_integral` at line 3088. For n>0 it pushes the
uniform PMF on Fin n forward by z and obtains a probability measure mu.
`PMF.toMeasure_map`, measurable_of_finite and `PMF.integral_eq_sum`, together
with `PMF.uniformOfFintype_apply`, show that continuous-function integrals
are the finite average. Compactness makes the continuous product kernel
integrable. `integral_prod` and the two average formulas give exactly
`integral K d(mu.prod mu)=n^(-2)*sum_i sum_j K(z_i,z_j)`.
The installed PMF declarations were inspected in existing imported modules.

The root handles n=0 directly. For positive n it packages the truncated
logarithm as a continuous map: its exponential floor is strictly positive
for every real M. It applies the preserved universal probability bound to
this empirical measure, multiplies by positive n^2 and cancels n^2*n^(-2).
All diagonal terms and repeated points are retained. No injectivity,
nonemptiness of E, second countability or positivity of M is added.
The universal strict probability-energy inequality is an input hypothesis,
not a consequence established by this reduction.

Prescribed complete saved `Submission.lean` and local-import check passed:
exitCode 0, timedOut false; both phases cached with durationMs 0. This is
explicit cache reuse for identical sources, not a new compilation. The
same source digest was compiled uncached in the earlier Fekete restoration
turn (Helpers 86113 ms, Submission 129525 ms including shared-lock wait).
Its only diagnostic is the retained original dimitrov sorry warning.
Source digest:
`a9cea480c4abdfe74365eb02c2e10c307a8b52955f5e3140379a4981e6dacda5`.
Helpers SHA256:
`f9eeac8e1d10cd0c9b2c5e1adfee027231675e6fed0362f943ed0768a7c1baea`.
Submission SHA256:
`4ccc782999c50bb2bfb202882f675c6c2dc34fa54fbe1609796c781e9177b84e`.
No fresh error, unsolved helper goal, forbidden construct, probe or running
checker. Independent host checking of the assigned root is still required
after delivery; none is claimed here.

## Remaining Work

The original `Submission.dimitrov` remains unproved. The sharp pointwise
arbitrary-ray energy estimate is open. Prior research isolates paired
resolvent comparison, per-mode probability Cauchy/Fubini, finite-mode
extraction, annular cutoff and full-tree comparison. Pair both frequency
signs and subtract equal zero modes before integration; preserve atomic
diagonals through increasing truncations. That pointwise estimate can feed
uniformization, this empirical reduction, normalized Fekete bounds and
polynomial contraction.

Current COOPERATION.json records host-verified uniformization receipt
`94490891-90cb-47ec-9b8e-1dc4e62ea0bc` and Fekete reduction receipt
`d91803ae-14b4-4bc7-bb5d-aa3c2b7dc9a8`, both present in this seed.
These separate roots are not dependencies of the empirical reduction.
Retain the checked angular Green, Fourier, mod-four and degree proof work.
Read the new peer progress `cd6829b3-2d3b-4d41-972f-b3cf3e8b9b01` and
host-verified proof `ca9a935c-825c-42a3-ae28-08e6116cc33f` for
`argument_card_sq_of_degree_drop` at commit
`1d6803c468f2d8f412057c74d94fea8d67722210`. That direction-halving proof
is not in this isolated seed, is not an empirical-root dependency, and
requires host integration before local use.

Number-field integration still needs the verified direction-halving result
imported, reciprocal-minpoly identification and quantitative descent. Use distinct
minpoly roots or Q(a): larger ambient embedding products can repeat each
conjugate an even number of times. Reverse the square-product identity and
use monic equal-degree matching. Both degree-drop descent and the
degree-preserving house contradiction remain obligations.

Next: independent host empirical-root check, sharp radial energy proof,
number-field descent and original-target official local evaluation.
