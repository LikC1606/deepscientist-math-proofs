# Lean-Eval proof: Rademacher type and Enflo type coincide

Problem: `annals_rademacher_enflo_type`, statement revision 1.
System: DeepScientist Math + GPT-6.1 (`gpt-6.1-sol`, xhigh).

This repository contains the exact solver-owned Lean sources accepted in a local official Lean-Eval comparator run, plus the workspace-identifying `lakefile.toml`. Trusted benchmark files and dependencies are supplied by the official submission evaluator. The result proves both original inequalities for complete real normed spaces and real exponents from 1 to 2. The proof sources contain no `sorry`.

The final cooperative continuation took 30 turns and approximately 250 minutes, including preparation and evaluation. It reused helper proofs from earlier attempts with the same system. Human-directed work selected the task, fixed runtime/environment issues, adjusted library access and scheduling, and arranged the continuation. It is a continuation result; see `verification.json` for the frozen benchmark, proof provenance and source hashes.

To reproduce, copy `Submission.lean` and `Submission/` into the corresponding official generated workspace at the recorded benchmark commit and run its official `lake test` with the required comparator tools.
