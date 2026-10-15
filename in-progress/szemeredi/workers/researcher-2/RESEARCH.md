Durable Slurm continuation (gate repair, 2026-10-15). Continue from the checked dense-prefix, finite-to-density and 3-AP conversion lemmas. The arbitrary-k finite-density theorem is still unproved. Before ending a turn, delegate a smaller concrete supporting theorem or save a new proof attempt addressing that gap. Do not resubmit the absent full theorem or repeatedly conclude that the general theorem is missing. Keep all arbitrary-k obligations visible.
Preserved worker snapshots: [{"workerId":"solver","commit":"10cd4e2ea084185d66236bc589031eef300e49c4"},{"workerId":"researcher-1","commit":"759246e48d442aec0d863a10f93b82a6eff073a0"},{"workerId":"researcher-2","commit":"a307026a360d0c26f13852b4f6d6d2fba69c6aa3"},{"workerId":"engineer","commit":"20010b4e4c689566d8a83826074f6bdbc6509284"}]

# AP3 Conversion Checkpoint

The assigned helper is proved and saved at `generated/szemeredi/Submission/Helpers.lean:6`:

```lean
theorem ap3_of_not_threeAPFree (A : Set Nat) (h : ¬ ThreeAPFree A) :
    ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < 3 → a + b * j ∈ A
```

The proof unfolds `ThreeAPFree` and extracts `x,y,z ∈ A`, `x+z=y+y`, and `x≠y`. A local ordered-endpoint argument uses `a=x`, `b=y-x` when `x<y`. Otherwise it reverses `x,z`; the equality and nontriviality imply `z<y`. `omega` checks positivity, the reversal, and the identities for the three indices. All instances are local to the proof. No placeholders or axioms were added.

Final `check_lean` on saved `Submission/Helpers.lean` and `Submission.lean` returned `exitCode: 0`, `timedOut: false`, empty stderr. Helpers compiled with no diagnostics. The importing Submission file emitted only the unchanged original target's `declaration uses sorry` warning at line 56. `Submission.lean` itself was not edited. The exact checked helper text was also sent to the primary solver for selective integration; git commits are managed by the host.

The current assignment is complete as a supporting lemma. The original arbitrary-k Szemeredi target remains unproved; this conversion only establishes the requested three-term AP format from non-3AP-freeness. The prior narrow library audit found no suitable hypergraph-removal, multiple-recurrence, or density Hales-Jewett bridge. The conditional `Submission.szemeredi_of_finite_density` still requires the full finite-density theorem for arbitrary lengths.
