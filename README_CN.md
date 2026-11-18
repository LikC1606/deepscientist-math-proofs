<!-- README_SYNC: source=f529520b40c4d8805ce1a27330e6e03256d3fad0; updated=2026-11-18 -->

[English](README.md) · 简体中文

# LeanEval V1 已接收的证明

这里归档了三份通过 LeanEval V1 官方评测的 Lean 证明包，每份都有官方结果和对应的源码版本。先看评测结果确认是否通过，再打开归档检查证明和来源。

[![GitHub Stars](https://img.shields.io/github/stars/LikC1606/deepscientist-math-proofs)](https://github.com/LikC1606/deepscientist-math-proofs/stargazers)

可以给仓库点个 Star，方便日后查找这些证明。

## 已接收的提交

| 问题 | 证明目录 | 提交注明的模型 | 官方评测结果 |
| --- | --- | --- | --- |
| 单位猜想 | [annals_unit_conjecture](annals_unit_conjecture/) | DeepScientist + GPT-5.6 | [#1246](https://github.com/leanprover/lean-eval-submissions/issues/1246#issuecomment-5380977645) |
| Rademacher 型与 Enflo 型 | [annals_rademacher_enflo_type](annals_rademacher_enflo_type/) | DeepScientist Math + GPT-6.1 | [#2115](https://github.com/leanprover/lean-eval-submissions/issues/2115#issuecomment-6161355838) |
| 固定夹角的等角线 | [annals_equiangular_lines_fixed_angle](annals_equiangular_lines_fixed_angle/) | DeepScientist Math + GPT-6.1 | [#2135](https://github.com/leanprover/lean-eval-submissions/issues/2135#issuecomment-6186332699) |

单位猜想归档对应最初被接收的 Gist 版本。另外两份来自续跑，期间复用了辅助证明；等角线证明还包含 Lean 4.35 兼容性修复。原始提交和各证明包的说明记录了这些变化。归档中的 `verification.json` 和 `compatibility-verification.json` 保留当时的验证记录，官方接收情况以表中的结果链接为准。

## 检查归档文件

[accepted.json](accepted.json) 列出了原始提交、固定源码版本、官方结果和 SHA-256 校验值。在仓库根目录用 `jq` 和 `sha256sum` 检查所列文件：

```bash
jq -r '.[] | .directory as $dir | .source_sha256 | to_entries[] | "\(.value)  \($dir)/\(.key)"' accepted.json |
  sha256sum --check
```

这一步核对文件内容。若要复核证明，使用该次提交对应的官方 LeanEval 工作区，按 `lakefile.toml` 和可用的 `lean-toolchain` 匹配依赖，把 `Submission.lean` 及可用的 `Submission/` 放入工作区，再运行官方评测。归档不附带受信任的评测文件。

## 尚未完成的研究

[研究快照](in-progress/) 记录了 Dimitrov、Hopf–Rinow 和 Szemerédi 问题的进度，可能含有未经检查的草稿或 `sorry`，不属于表中的已接收提交。

仓库根目录没有统一许可证文件。复用前请核对原始材料的授权。
