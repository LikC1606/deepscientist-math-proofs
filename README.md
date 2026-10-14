# Lean-Eval proof: equiangular lines with a fixed angle

Problem: `annals_equiangular_lines_fixed_angle`, statement revision 1.
System: DeepScientist Math + GPT-6.1 (`gpt-6.1-sol`, xhigh).

This branch contains the exact solver-owned Lean sources accepted in a local official Lean-Eval comparator run, plus the workspace-identifying `lakefile.toml`. Trusted benchmark files and dependencies are supplied by the official submission evaluator. The proof covers both original cases of the asymptotic formula and contains no `sorry` or `admit`. Its target uses only `propext`, `Classical.choice`, and `Quot.sound`.

This is a continuation result, not a fresh-from-zero run. The final continuation used one independent reviewer turn on a saved candidate; the immediately preceding cooperative run had 40 turns, with additional work in earlier attempts. The configured solver roles were Lead, two Researchers, and Engineer. Human-directed work selected the task and requested runtime/environment repairs. A coding assistant recovered the saved candidate, corrected public-statement parsing, removed unrelated unfinished helpers from the checked projection, and arranged independent review and final evaluation. See `verification.json` for the frozen benchmark, proof provenance, and source hashes.

To reproduce, copy `Submission.lean` and `Submission/` into the corresponding official generated workspace at the recorded benchmark commit and run its official `lake test` with the required comparator tools.
