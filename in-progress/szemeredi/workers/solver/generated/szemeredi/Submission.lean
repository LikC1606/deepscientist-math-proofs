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

theorem not_threeAPFree_of_positive_upperDensity (A : Set ℕ)
    (h : 0 < upperDensity A) : ¬ ThreeAPFree A := by
  classical
  obtain ⟨epsilon, hepsilon, hdense⟩ := dense_prefixes A h
  obtain ⟨N, hN⟩ := Helpers.finite_density_not_threeAPFree epsilon hepsilon
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
  have hnot := hN (n + 1) (by omega) s (Finset.filter_subset _ _) hs
  intro hfree
  exact hnot (hfree.mono (by
    intro x hx
    exact (Finset.mem_filter.mp hx).2))

theorem progressions_of_length_le_three (A : Set ℕ) (h : 0 < upperDensity A)
    (k : ℕ) (hk : k ≤ 3) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A := by
  obtain ⟨a, b, hb, hap⟩ := Helpers.ap3_of_not_threeAPFree A
    (not_threeAPFree_of_positive_upperDensity A h)
  exact ⟨a, b, hb, fun j hj => hap j (lt_of_lt_of_le hj hk)⟩

theorem dense_prefixes_above (A : Set ℕ) (epsilon : ℝ)
    (hepsilon : epsilon < upperDensity A) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
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
  have hfreq := Filter.frequently_lt_of_lt_limsup
    (Filter.isCoboundedUnder_le_of_le Filter.atTop hd)
    (show epsilon < Filter.limsup d Filter.atTop from hepsilon)
  intro N
  obtain ⟨n, hn, hdense⟩ := Filter.frequently_atTop.mp hfreq N
  exact ⟨n, hn, (lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp hdense⟩

theorem consecutive_of_upperDensity_gt (A : Set ℕ) (k : ℕ) (hk : 0 < k)
    (h : ((k - 1 : ℕ) : ℝ) < upperDensity A * (k : ℝ)) :
    ∃ a : ℕ, ∀ j : ℕ, j < k → a + j ∈ A := by
  classical
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  obtain ⟨epsilon, hepsilon, hlt⟩ :=
    exists_between ((div_lt_iff₀ hkreal).mpr h)
  obtain ⟨N, hN⟩ := Helpers.finite_density_consecutive k hk epsilon
    ((div_lt_iff₀ hkreal).mp hepsilon)
  obtain ⟨n, hn, hcard⟩ := dense_prefixes_above A epsilon hlt N
  let s := (Finset.range (n + 1)).filter (fun x => x ∈ A)
  have hsum : (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) =
      (s.card : ℝ) := by
    calc
      _ = ∑ x ∈ s, (1 : ℝ) := by
        simp only [s, Finset.sum_filter, Set.indicator_apply]
      _ = (s.card : ℝ) := by simp
  have hs : epsilon * ((n + 1 : ℕ) : ℝ) ≤ (s.card : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcard.le.trans_eq hsum
  obtain ⟨a, ha⟩ := hN (n + 1) (by omega) s (Finset.filter_subset _ _) hs
  exact ⟨a, fun j hj => (Finset.mem_filter.mp (ha j hj)).2⟩

theorem szemeredi_of_upperDensity_eq_one (A : Set ℕ) (h : upperDensity A = 1) :
    ContainsArbitraryAPs A := by
  intro k
  by_cases hk : k = 0
  · exact ⟨0, 1, by omega, by simp [hk]⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨a, ha⟩ := consecutive_of_upperDensity_gt A k hkpos (by
    rw [h, one_mul]
    exact_mod_cast Nat.sub_lt hkpos (by omega : 0 < 1))
  exact ⟨a, 1, by omega, by simpa using ha⟩

theorem upperDensity_le_one (A : Set ℕ) : upperDensity A ≤ 1 := by
  let d : ℕ → ℝ := fun n =>
    (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) /
      ((n : ℝ) + 1)
  have hd : ∀ n, 0 ≤ d n := by
    intro n
    exact div_nonneg
      (Finset.sum_nonneg fun k _ => Set.indicator_nonneg (by intros; norm_num) k)
      (by positivity)
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_le Filter.atTop hd)
  apply Filter.Eventually.of_forall
  intro n
  change _ / ((n : ℝ) + 1) ≤ 1
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  have hsum : (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) ≤
      ∑ _ ∈ Finset.range (n + 1), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    by_cases hka : k ∈ A <;> simp [hka]
  simpa using hsum

theorem szemeredi_of_affine_density_increment
    (hincrement : ∀ (k : ℕ) (epsilon0 : ℝ), 0 < epsilon0 →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ eta : ℝ, epsilon0 ≤ eta → eta ≤ 1 → ∀ M : ℕ,
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ,
            s ⊆ Finset.range n → eta * (n : ℝ) ≤ (s.card : ℝ) →
            (∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s) ∨
              ∃ m u v : ℕ, M ≤ m ∧ 1 ≤ v ∧
                (eta + delta) * (m : ℝ) ≤
                  (((Finset.range m).filter (fun x => u + v * x ∈ s)).card : ℝ)) :
    ∀ (A : Set ℕ), 0 < upperDensity A → ContainsArbitraryAPs A := by
  classical
  apply szemeredi_of_finite_density
  intro k epsilon0 hepsilon0
  obtain ⟨delta, hdelta, hinc⟩ := hincrement k epsilon0 hepsilon0
  apply Helpers.finite_density_ap_of_increment k epsilon0 delta hdelta
  intro eta heta htop M
  obtain ⟨N, hN⟩ := hinc eta heta htop M
  refine ⟨N, ?_⟩
  intro n hn s hs hdense
  rcases hN n hn s hs hdense with hap | hnew
  · exact Or.inl hap
  · obtain ⟨m, u, v, hm, hv, hdense'⟩ := hnew
    let t := (Finset.range m).filter (fun x => u + v * x ∈ s)
    refine Or.inr ⟨m, hm, t, Finset.filter_subset _ _, hdense', ?_⟩
    apply Helpers.ap_of_affine_indices s t u v k hv
    intro x hx
    exact (Finset.mem_filter.mp hx).2

theorem progressions_of_square_density (A : Set ℕ) (k : ℕ) (hk : 3 ≤ k)
    (h : ((k * (k - 1) - 1 : ℕ) : ℝ) <
      upperDensity A * ((k * k : ℕ) : ℝ)) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A := by
  classical
  have hm : (0 : ℝ) < ((k * k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
  obtain ⟨epsilon, hepsilon, hlt⟩ := exists_between ((div_lt_iff₀ hm).mpr h)
  obtain ⟨N, hN⟩ := Helpers.finite_density_square k hk epsilon
    ((div_lt_iff₀ hm).mp hepsilon)
  obtain ⟨n, hn, hcard⟩ := dense_prefixes_above A epsilon hlt N
  let s := (Finset.range (n + 1)).filter (fun x => x ∈ A)
  have hsum : (Finset.range (n + 1)).sum (A.indicator (fun _ => (1 : ℝ))) =
      (s.card : ℝ) := by
    calc
      _ = ∑ x ∈ s, (1 : ℝ) := by
        simp only [s, Finset.sum_filter, Set.indicator_apply]
      _ = (s.card : ℝ) := by simp
  have hs : epsilon * ((n + 1 : ℕ) : ℝ) ≤ (s.card : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcard.le.trans_eq hsum
  obtain ⟨a, b, hb, ha⟩ :=
    hN (n + 1) (by omega) s (Finset.filter_subset _ _) hs
  exact ⟨a, b, hb, fun j hj => (Finset.mem_filter.mp (ha j hj)).2⟩

theorem progressions_of_bounded_gaps (A : Set ℕ) (D : ℕ)
    (hgap : ∀ n : ℕ, ∃ t : ℕ, t < D ∧ n + t ∈ A) :
    ContainsArbitraryAPs A := by
  classical
  choose t ht hmem using hgap
  let C : ℕ → Fin D := fun n => ⟨t n, ht n⟩
  intro k
  obtain ⟨N, hN, hmono⟩ := Helpers.finite_van_der_waerden k D
  obtain ⟨a, b, hb, c, hap⟩ := hmono C
  refine ⟨a + c.val, b, hb, ?_⟩
  intro j hj
  have hc := congrArg Fin.val (hap j hj).2
  change t (a + b * j) = c.val at hc
  have hm := hmem (a + b * j)
  rw [hc] at hm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem progressions_of_piecewise_bounded_gaps (A : Set ℕ) (D : ℕ)
    (hblocks : ∀ L : ℕ, ∃ u : ℕ, ∀ i : ℕ, i < L →
      ∃ t : ℕ, t < D ∧ u + i + t ∈ A) :
    ContainsArbitraryAPs A := by
  classical
  have hD : 1 ≤ D := by
    obtain ⟨u, hu⟩ := hblocks 1
    obtain ⟨t, ht, _⟩ := hu 0 (by omega)
    omega
  intro k
  obtain ⟨N, hN, hmono⟩ := Helpers.finite_van_der_waerden_on_interval k D hD
  obtain ⟨u, hu⟩ := hblocks N
  have hchoose : ∀ i : Fin N, ∃ t : Fin D, u + i.val + t.val ∈ A := by
    intro i
    obtain ⟨t, ht, hmem⟩ := hu i.val i.isLt
    exact ⟨⟨t, ht⟩, hmem⟩
  choose C hC using hchoose
  obtain ⟨a, b, hb, c, hap⟩ := hmono C
  refine ⟨u + a + c.val, b, hb, ?_⟩
  intro j hj
  obtain ⟨hbound, hcolor⟩ := hap j hj
  have hm := hC ⟨a + b * j, hbound⟩
  have hc := congrArg Fin.val hcolor
  rw [hc] at hm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

theorem szemeredi (A : Set ℕ) (h : 0 < upperDensity A) :
    ContainsArbitraryAPs A := by
  intro k
  by_cases hk : k ≤ 3
  · exact progressions_of_length_le_three A h k hk
  have hkpos : 0 < k := by omega
  by_cases hdense : ((k - 1 : ℕ) : ℝ) < upperDensity A * (k : ℝ)
  · obtain ⟨a, ha⟩ := consecutive_of_upperDensity_gt A k hkpos hdense
    exact ⟨a, 1, by omega, by simpa using ha⟩
  have hkfour : 4 ≤ k := by omega
  have hsmall : upperDensity A * (k : ℝ) ≤ ((k - 1 : ℕ) : ℝ) :=
    le_of_not_gt hdense
  by_cases hsquare : ((k * (k - 1) - 1 : ℕ) : ℝ) <
      upperDensity A * ((k * k : ℕ) : ℝ)
  · exact progressions_of_square_density A k (by omega) hsquare
  have hsquare_small : upperDensity A * ((k * k : ℕ) : ℝ) ≤
      ((k * (k - 1) - 1 : ℕ) : ℝ) := le_of_not_gt hsquare
  by_cases hbounded : ∃ D : ℕ, ∀ n : ℕ, ∃ t : ℕ, t < D ∧ n + t ∈ A
  · obtain ⟨D, hgap⟩ := hbounded
    exact progressions_of_bounded_gaps A D hgap k
  have hunbounded : ∀ D : ℕ, ∃ n : ℕ, ∀ t : ℕ, t < D → n + t ∉ A := by
    simpa only [not_exists, not_forall, not_and] using hbounded
  by_cases hpiece : ∃ D : ℕ, ∀ L : ℕ, ∃ u : ℕ, ∀ i : ℕ, i < L →
      ∃ t : ℕ, t < D ∧ u + i + t ∈ A
  · obtain ⟨D, hblocks⟩ := hpiece
    exact progressions_of_piecewise_bounded_gaps A D hblocks k
  have hnotpiece : ∀ D : ℕ, ∃ L : ℕ, ∀ u : ℕ, ∃ i : ℕ,
      i < L ∧ ∀ t : ℕ, t < D → u + i + t ∉ A := by
    push Not at hpiece
    exact hpiece
  sorry

end Submission
