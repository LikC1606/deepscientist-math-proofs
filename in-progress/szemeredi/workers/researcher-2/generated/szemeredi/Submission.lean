import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics
open scoped BigOperators

namespace Submission

theorem dense_prefixes (A : Set ℕ) (h : 0 < upperDensity A) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      epsilon * ((n : ℝ) + 1) <
        (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) := by
  let d : ℕ → ℝ := fun n =>
    (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) /
      ((n : ℝ) + 1)
  have hd : ∀ n, 0 ≤ d n := by
    intro n
    exact div_nonneg
      (Finset.sum_nonneg fun k _ => Set.indicator_nonneg (by intros; norm_num) k)
      (by positivity)
  have hhalf : upperDensity A / 2 < Filter.limsup d Filter.atTop := by
    change upperDensity A / 2 < upperDensity A
    linarith
  have hfreq := Filter.frequently_lt_of_lt_limsup
    (Filter.isCoboundedUnder_le_of_le Filter.atTop hd) hhalf
  refine ⟨upperDensity A / 2, half_pos h, ?_⟩
  intro N
  obtain ⟨n, hn, hdense⟩ := Filter.frequently_atTop.mp hfreq N
  refine ⟨n, hn, ?_⟩
  exact (lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp hdense
theorem szemeredi_of_finite_density
    (hfinite : ∀ (k : ℕ) (epsilon : ℝ), 0 < epsilon → ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ, s ⊆ Finset.range n →
        epsilon * (n : ℝ) ≤ (s.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s) :
    ∀ (A : Set ℕ), 0 < upperDensity A → ContainsArbitraryAPs A := by
  classical
  intro A hA k
  obtain ⟨epsilon, hepsilon, hdense⟩ := dense_prefixes A hA
  obtain ⟨N, hN⟩ := hfinite k epsilon hepsilon
  obtain ⟨n, hn, hcard⟩ := hdense N
  let s := (Finset.range (n + 1)).filter (fun x => x ∈ A)
  have hsum : (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) =
      (s.card : ℝ) := by
    calc
      _ = ∑ x ∈ s, (1 : ℝ) := by
        simp only [s, Finset.sum_filter, Set.indicator_apply]
      _ = (s.card : ℝ) := by simp
  have hs : epsilon * ((n + 1 : ℕ) : ℝ) ≤ (s.card : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcard.le.trans_eq hsum
  obtain ⟨a, b, hb, hap⟩ :=
    hN (n + 1) (by omega) s (Finset.filter_subset _ _) hs
  refine ⟨a, b, hb, ?_⟩
  intro j hj
  exact (Finset.mem_filter.mp (hap j hj)).2
theorem szemeredi (A : Set ℕ) (h : 0 < upperDensity A) :
    ContainsArbitraryAPs A := by
  sorry

end Submission
