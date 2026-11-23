<!-- README_SYNC: source=f529520b40c4d8805ce1a27330e6e03256d3fad0; updated=2026-11-23 -->
<p align="center">English · <a href="./README_CN.md" lang="zh-CN">简体中文</a></p>

# Accepted LeanEval V1 Proofs

Three early Lean 4 proof packages accepted by the official LeanEval V1 evaluator, complete with published result comments, pinned source revisions, and SHA-256 checksums. Start with each result comment to confirm acceptance, then inspect the archived package for its proof and provenance.

> **Looking for the expanded proof archive & workbench?** See [**TheoremOS**](https://github.com/HuggingMath/TheoremOS) ([theoremos.top](https://theoremos.top/en/)), developed at [**WestlakeNLP**](https://westlakenlp.com/) (Westlake University), which now archives **10 officially accepted Lean-Eval proofs** (including the completed Dimitrov and Hopf–Rinow proofs) alongside **18 locally verified OpenAI Math records**.

<a href="https://github.com/LikC1606/deepscientist-math-proofs/stargazers"><img alt="GitHub Stars" src="https://img.shields.io/github/stars/LikC1606/deepscientist-math-proofs"></a>
<img alt="Lean 4" src="https://img.shields.io/badge/verification-Lean_4-2f855a">
<a href="https://github.com/HuggingMath/TheoremOS"><img alt="TheoremOS · WestlakeNLP" src="https://img.shields.io/badge/expanded_archive-TheoremOS_(WestlakeNLP)-1e3a5f"></a>

[Star this archive](https://github.com/LikC1606/deepscientist-math-proofs/stargazers) to keep these early accepted LeanEval V1 packages handy.

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

## Unfinished research snapshots

[In-progress snapshots](in-progress/) preserve earlier drafts on Dimitrov, Hopf–Rinow, and Szemerédi; they may include unverified code or `sorry` and are not accepted submissions in this repository. Subsequent accepted proofs for Dimitrov and Hopf–Rinow are archived in [TheoremOS](https://github.com/HuggingMath/TheoremOS).

There is no repository-wide license file at the root. Check the terms of the original materials before reuse.
