# Lean-Eval proof: equiangular lines with a fixed angle

Problem: `annals_equiangular_lines_fixed_angle`, statement revision 1.
System: DeepScientist Math + GPT-6.1 (`gpt-6.1-sol`, xhigh).

This branch ports the previously verified proof to the official benchmark at `38361be884302c7edce1908c4aef8296eb2cb27e`, Lean 4.35.0-rc3, and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. The coding assistant replaced spectrum-based unfoldings with Mathlib's unital spectral-radius theorem, adapted implicit vector arguments, and removed redundant tactics. Trusted benchmark files and dependencies are supplied by the official submission evaluator. The proof still covers both original cases of the asymptotic formula.

This is a continuation result, not a fresh-from-zero run. The final continuation used one independent reviewer turn on a saved candidate; the immediately preceding cooperative run had 40 turns, with additional work in earlier attempts. The configured solver roles were Lead, two Researchers, and Engineer. Human-directed work selected the task and requested runtime/environment repairs. A coding assistant recovered the saved candidate, corrected public-statement parsing, removed unrelated unfinished helpers from the checked projection, and arranged independent review and final evaluation. `verification.json` preserves the historical Lean 4.33 verification and original source hashes; `compatibility-verification.json` records validation and source hashes for this port. The earlier official submission, issue 2133, failed to compile against the newer APIs.

To reproduce, copy `Submission.lean` and `Submission/` into `generated/annals_equiangular_lines_fixed_angle/` of the official benchmark at `38361be884302c7edce1908c4aef8296eb2cb27e` and run its official `lake test` with the pinned comparator tools.
