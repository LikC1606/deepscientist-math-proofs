import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic

namespace Submission.Helpers

theorem ap3_of_not_threeAPFree (A : Set Nat) (h : ¬ ThreeAPFree A) :
    ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < 3 → a + b * j ∈ A := by
  classical
  have ordered (x y z : Nat) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
      (hsum : x + z = y + y) (hxy : x < y) :
      ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < 3 → a + b * j ∈ A := by
    refine ⟨x, y - x, by omega, ?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · simpa using hx
    · have heq : x + (y - x) * 1 = y := by omega
      rwa [heq]
    · have heq : x + (y - x) * 2 = z := by omega
      rwa [heq]
  unfold ThreeAPFree at h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hsum, hne⟩ := h
  by_cases hxy : x < y
  · exact ordered x y z hx hy hz hsum hxy
  · exact ordered z y x hz hy hx (by omega) (by omega)

end Submission.Helpers
