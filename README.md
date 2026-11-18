<!-- README_SYNC: source=f529520b40c4d8805ce1a27330e6e03256d3fad0; updated=2026-11-18 -->

English · [简体中文](README_CN.md)

# Accepted LeanEval V1 Proofs

Three Lean proof packages accepted by the official LeanEval V1 evaluator, with the published result and pinned source for each submission. Start with the result comment to establish acceptance, then open the archived package to inspect the proof and its provenance.

[![GitHub Stars](https://img.shields.io/github/stars/LikC1606/deepscientist-math-proofs)](https://github.com/LikC1606/deepscientist-math-proofs/stargazers)

Star the archive to find the accepted packages again.

## Accepted submissions

| Problem | Proof Directory | Declared Model | Official Acceptance |
| --- | --- | --- | --- |
| Unit conjecture | [annals_unit_conjecture](annals_unit_conjecture/) | DeepScientist + GPT-5.6 | [#1246](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| Rademacher type and Enflo type | [annals_rademacher_enflo_type](annals_rademacher_enflo_type/) | DeepScientist Math + GPT-6.1 | [#2115](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| Equiangular lines with a fixed angle | [annals_equiangular_lines_fixed_angle](annals_equiangular_lines_fixed_angle/) | DeepScientist Math + GPT-6.1 | [#2135](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |

The unit conjecture package comes from the accepted historical Gist revision. The other two packages record continuation runs, including reuse of helper proofs and, for equiangular lines, a Lean 4.35 compatibility repair. The original submission records and package notes explain those changes. The archived `verification.json` and `compatibility-verification.json` retain their original snapshots; official acceptance is recorded by the linked result comments.

## Check the archived files

[accepted.json](accepted.json) lists the original submission URLs, pinned source revisions, result comments, and SHA-256 digests. From the repository root, use `jq` and `sha256sum` to check the listed files:

```bash
jq -r '.[] | .directory as $dir | .source_sha256 | to_entries[] | "\(.value)  \($dir)/\(.key)"' accepted.json |
  sha256sum --check
```

This checks file identity. To check a proof itself, use the official generated LeanEval workspace for the recorded submission. Match the dependencies in `lakefile.toml` and `lean-toolchain` where provided, copy `Submission.lean` and `Submission/` where present, then run that workspace's official evaluator. This archive does not bundle the trusted benchmark files.

## Unfinished research

[In-progress snapshots](in-progress/) preserve work on Dimitrov, Hopf–Rinow, and Szemerédi. They may include unverified drafts or `sorry`; none of these snapshots is an accepted submission.

There is no repository-wide license file at the root. Check the terms of the original materials before reuse.
