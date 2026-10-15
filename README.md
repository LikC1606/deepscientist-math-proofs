# Accepted LeanEval V1 Proofs

This repository collects three proofs accepted by the official LeanEval evaluator. Each problem directory preserves the complete original submission package byte for byte.

| Problem | Proof Directory | Declared Model | Official Acceptance |
| --- | --- | --- | --- |
| Unit conjecture | [annals_unit_conjecture](annals_unit_conjecture/) | DeepScientist + GPT-5.6 | [#1246](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| Rademacher type and Enflo type | [annals_rademacher_enflo_type](annals_rademacher_enflo_type/) | DeepScientist Math + GPT-6.1 | [#2115](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| Equiangular lines with a fixed angle | [annals_equiangular_lines_fixed_angle](annals_equiangular_lines_fixed_angle/) | DeepScientist Math + GPT-6.1 | [#2135](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |

[accepted.json](accepted.json) records the original submission URLs, pinned source commits, official acceptance comments, and SHA-256 hashes of the original archived files.

The unit conjecture package is the historical GPT-5.6 submission from its accepted Gist revision. The other packages are the accepted GPT-6.1 submissions; equiangular lines includes the Lean 4.35 compatibility repair. The linked submissions and original package documentation describe continuation runs, helper-proof reuse, and compatibility edits.

Original `verification.json` and `compatibility-verification.json` files retain their publication-time snapshots. Subsequent official acceptance is recorded by the result comments linked in `accepted.json`.

To reproduce a result, use the official generated LeanEval workspace and toolchain corresponding to the original submission. Copy that problem's `Submission.lean` and `Submission/` directory, when present, into its generated workspace and run the official evaluator. Dependency pins are recorded in each package's `lakefile.toml`, `lean-toolchain` when present, and original submission record.

Current work on Dimitrov, Hopf-Rinow, and Szemeredi is archived separately in [in-progress](in-progress/). These are unfinished research snapshots, not officially accepted proofs.
