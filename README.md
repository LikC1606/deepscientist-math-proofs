# Dimitrov and Hopf–Rinow — LeanEval submission

Exact proof sources for LeanEval `dimitrov` and `hopf_rinow`, both statement revision 1.

Produced by TheoremOS (the standalone continuation of DeepScientist Math) using `gpt-6.1-sol`, `xhigh`, with cooperative Lead, two Researchers, Engineer, and independent fixed-candidate review. The final continuations recorded 13 role turns for Dimitrov and 16 for Hopf–Rinow. They reused same-problem helper proofs and research from earlier runs; these counts exclude earlier work and environment-repair retries. Human direction selected the tasks and requested runtime repairs, continuation, and submission. A coding assistant repaired the environment and prepared this source snapshot.

Both unchanged candidates passed the local official `lake test` against `leanprover/lean-eval` commit `38361be884302c7edce1908c4aef8296eb2cb27e`, with Lean `4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. Both Nanoda and the Lean default kernel accepted each solution. Final environment-repair retries made no new model calls and changed no proof bytes. Solving policy prohibited reading, copying, or importing protected reference `Solution.lean`.

Each workspace's `verification.json` records its solver commit, independent review source digest, published file hashes, and local official comparator receipt. The published proof files are byte-identical to the corresponding reviewed and locally accepted candidate. Hosted CI acceptance and leaderboard inclusion must be checked separately.

For reproduction, overlay each workspace's `Submission.lean` and `Submission/` into the corresponding pristine official generated workspace at the pinned benchmark commit, then run its original `lake test`. The included Lake files enable intake discovery and record dependency pins; this snapshot contains neither the full official workspace nor compiled dependencies.
