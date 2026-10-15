import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.LocallyConvex.Separation
namespace Submission.Helpers

theorem finite_cover_functional_eq_sum {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ)
    (z : Fin m → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  conv_lhs => rw [pi_eq_sum_univ' z]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
theorem finite_cover_functional_const {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ)
    (t : ℝ) : f (fun _ => t) = t * f (fun _ => (1 : ℝ)) := by
  have heq : (fun _ : Fin m => t) = t • (fun _ : Fin m => (1 : ℝ)) := by
    ext i
    simp
  rw [heq, map_smul]
  rfl
theorem finite_cover_sum_mul_combination {n : ℕ} (c x y : Fin n → ℝ) (a b : ℝ) :
    (∑ j, c j * (a * x j + b * y j)) =
      a * (∑ j, c j * x j) + b * (∑ j, c j * y j) := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
theorem finite_cover_duality (m n : ℕ) (A : Fin m → Fin n → ℝ) (c : Fin n → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hc : ∀ j, 0 < c j)
    (hno : ¬ ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, 1 ≤ ∑ j : Fin n, A i j * x j) ∧
      (∑ j : Fin n, c j * x j) ≤ (1 / 2 : ℝ)) :
    ∃ w : Fin m → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i) = 1 ∧
      ∀ j, (∑ i : Fin m, w i * A i j) ≤ 2 * c j := by
  classical
  let P : Set (Fin m → ℝ) := {z | ∃ x : Fin n → ℝ,
    (∀ j, 0 ≤ x j) ∧ (∑ j, c j * x j) ≤ (1 / 2 : ℝ) ∧
      z = fun i => ∑ j, A i j * x j}
  let T : Set (Fin m → ℝ) := {z | ∀ i, 1 < z i}
  have hP : Convex ℝ P := by
    rintro u ⟨x, hx, hcostx, rfl⟩ v ⟨y, hy, hcosty, rfl⟩ a b ha hb hab
    refine ⟨fun j => a * x j + b * y j, ?_, ?_, ?_⟩
    · intro j
      exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hb (hy j))
    · rw [finite_cover_sum_mul_combination]
      calc
        a * (∑ j, c j * x j) + b * (∑ j, c j * y j) ≤ a * (1 / 2) + b * (1 / 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hcostx ha)
            (mul_le_mul_of_nonneg_left hcosty hb)
        _ = 1 / 2 := by linarith
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (finite_cover_sum_mul_combination (A i) x y a b).symm
  have hT : Convex ℝ T := by
    intro z hz y hy a b ha hb hab i
    exact (convex_Ioi (𝕜 := ℝ) (1 : ℝ)) (hz i) (hy i) ha hb hab
  have hTop : IsOpen T := by
    have heq : T = ⋂ i : Fin m, {z : Fin m → ℝ | 1 < z i} := by
      ext z
      simp [T]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  have hdisj : Disjoint T P := by
    refine Set.disjoint_left.mpr ?_
    rintro z hz ⟨x, hx, hcost, rfl⟩
    exact hno ⟨x, hx, fun i => (hz i).le, hcost⟩
  obtain ⟨f, u, hfT, hfP⟩ := geometric_hahn_banach_open hT hTop hP hdisj
  let g := -f
  let d := -u
  have hgP : ∀ z ∈ P, g z ≤ d := by
    intro z hz
    exact neg_le_neg (hfP z hz)
  have hgT : ∀ z ∈ T, d < g z := by
    intro z hz
    exact neg_lt_neg (hfT z hz)
  have hzero : (0 : Fin m → ℝ) ∈ P := by
    refine ⟨0, by simp, by norm_num, ?_⟩
    ext i
    simp
  have hd : 0 ≤ d := by simpa using hgP 0 hzero
  let s := g (fun _ : Fin m => (1 : ℝ))
  have hs : 0 < s := by
    have hh := hgT (fun _ => (2 : ℝ)) (by intro i; norm_num)
    have heq : g (fun _ : Fin m => (2 : ℝ)) = 2 * s := by
      exact finite_cover_functional_const g 2
    rw [heq] at hh
    linarith
  let v : Fin m → ℝ := fun i => g (Pi.single i 1)
  have hsum : (∑ i, v i) = s := by
    simpa only [v, s, mul_one] using (finite_cover_functional_eq_sum g (fun _ => (1 : ℝ))).symm
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    by_contra hi
    have hi' : v i < 0 := lt_of_not_ge hi
    let t := (2 * s + 1) / (-v i)
    have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hi')
    have hz : (fun _ => (2 : ℝ)) + t • Pi.single i 1 ∈ T := by
      intro k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> nlinarith
    have hh := hgT _ hz
    have heq : g ((fun _ : Fin m => (2 : ℝ)) + t • Pi.single i 1) = 2 * s + t * v i := by
      rw [map_add, map_smul]
      have htwo : g (fun _ : Fin m => (2 : ℝ)) = 2 * s := by
        exact finite_cover_functional_const g 2
      exact congrArg (· + t * v i) htwo
    rw [heq] at hh
    have htval : t * v i = -(2 * s + 1) := by
      dsimp [t]
      field_simp [ne_of_lt hi']
    rw [htval] at hh
    linarith
  have hdle : d ≤ s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let t := 1 + ε / s
    have ht : 1 < t := by dsimp [t]; exact lt_add_of_pos_right _ (div_pos hε hs)
    have hh := hgT (fun _ => t) (by intro i; exact ht)
    have heq : g (fun _ : Fin m => t) = s + ε := by
      rw [finite_cover_functional_const]
      change t * s = s + ε
      dsimp [t]
      field_simp [ne_of_gt hs]
    exact (heq ▸ hh).le
  refine ⟨fun i => v i / s, fun i => div_nonneg (hv i) hs.le, ?_, ?_⟩
  · rw [← Finset.sum_div, hsum, div_self (ne_of_gt hs)]
  · intro j
    have hcj : 0 < c j := hc j
    let x : Fin n → ℝ := Pi.single j ((2 * c j)⁻¹)
    have hx : ∀ k, 0 ≤ x k := by
      intro k
      dsimp [x]
      simp only [Pi.single_apply]
      split_ifs
      · positivity
      · exact le_rfl
    have hcost : (∑ k, c k * x k) ≤ (1 / 2 : ℝ) := by
      dsimp [x]
      simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      rw [show c j * (2 * c j)⁻¹ = (1 / 2 : ℝ) by field_simp [ne_of_gt hcj]]
    have hcol := (hgP (fun i => ∑ k, A i k * x k) ⟨x, hx, hcost, rfl⟩).trans hdle
    rw [finite_cover_functional_eq_sum] at hcol
    have hcol' : (∑ i, v i * A i j) / (2 * c j) ≤ s := by
      calc
        (∑ i, v i * A i j) / (2 * c j) =
            ∑ i, v i * (∑ k, A i k * x k) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _
          simp [x, Pi.single_apply, div_eq_mul_inv, mul_assoc]
        _ ≤ s := hcol
    have hbound : (∑ i, v i * A i j) ≤ s * (2 * c j) :=
      (div_le_iff₀ (by positivity : 0 < 2 * c j)).mp hcol'
    rw [show (∑ i, v i / s * A i j) = (∑ i, v i * A i j) / s by
      simp [Finset.sum_div, div_mul_eq_mul_div]]
    exact (div_le_iff₀ hs).mpr (by nlinarith [hbound])
theorem bernoulli_finset_normalization (n : ℕ) (p : ℝ) :
    (∑ W : Finset (Fin n), p ^ W.card * (1 - p) ^ (n - W.card)) = 1 := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p)
theorem bernoulli_powerset_normalization {α : Type*} (A : Finset α) (p : ℝ) :
    (∑ B ∈ A.powerset, p ^ B.card * (1 - p) ^ (A.card - B.card)) = 1 := by
  simpa using Finset.sum_pow_mul_eq_add_pow p (1 - p) A
theorem sum_union_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (A U : Finset α) (hAU : A ⊆ U) (f : Finset α → ℝ) :
    (∑ W : Finset α, if A ∪ W = U then f W else 0) =
      ∑ B ∈ A.powerset, f ((U \ A) ∪ B) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun B _ => (U \ A) ∪ B) (fun W _ => W ∩ A)
    ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro B hB
    have hBA := Finset.mem_powerset.mp hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    have hAx : x ∈ A → x ∈ U := fun hx => hAU hx
    have hBx : x ∈ B → x ∈ A := fun hx => hBA hx
    tauto
  · intro W _
    exact Finset.mem_powerset.mpr Finset.inter_subset_right
  · intro B hB
    have hBA := Finset.mem_powerset.mp hB
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    have hBx : x ∈ B → x ∈ A := fun hx => hBA hx
    tauto
  · intro W hW
    have hW' := (Finset.mem_filter.mp hW).2
    rw [← hW']
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
theorem bernoulli_union_fiber (n : ℕ) (p : ℝ) (A U : Finset (Fin n)) :
    (∑ W : Finset (Fin n),
      if A ∪ W = U then p ^ W.card * (1 - p) ^ (n - W.card) else 0) =
      if A ⊆ U then p ^ (U.card - A.card) * (1 - p) ^ (n - U.card) else 0 := by
  classical
  by_cases hAU : A ⊆ U
  · rw [ite_eq_left hAU, sum_union_fiber A U hAU]
    have hcardU : U.card ≤ n := by simpa using Finset.card_le_univ U
    have hcardA : A.card ≤ U.card := Finset.card_le_card hAU
    calc
      (∑ B ∈ A.powerset,
          p ^ ((U \ A) ∪ B).card * (1 - p) ^ (n - ((U \ A) ∪ B).card)) =
          (p ^ (U.card - A.card) * (1 - p) ^ (n - U.card)) *
            ∑ B ∈ A.powerset, p ^ B.card * (1 - p) ^ (A.card - B.card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        have hBA := Finset.mem_powerset.mp hB
        have hcardB : B.card ≤ A.card := Finset.card_le_card hBA
        have hdisj : Disjoint (U \ A) B := by
          apply Finset.disjoint_left.mpr
          intro x hx hxB
          exact (Finset.mem_sdiff.mp hx).2 (hBA hxB)
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hAU]
        rw [show n - (U.card - A.card + B.card) =
          (n - U.card) + (A.card - B.card) by omega]
        simp only [pow_add]
        ring
      _ = p ^ (U.card - A.card) * (1 - p) ^ (n - U.card) := by
        rw [bernoulli_powerset_normalization, mul_one]
  · rw [ite_eq_right hAU]
    apply Finset.sum_eq_zero
    intro W _
    rw [ite_eq_right]
    intro hW
    exact hAU (hW ▸ Finset.subset_union_left)
theorem bernoulli_union_fiber_density (n : ℕ) (p : ℝ) (hp : p ≠ 0)
    (A U : Finset (Fin n)) :
    (∑ W : Finset (Fin n),
      if A ∪ W = U then p ^ W.card * (1 - p) ^ (n - W.card) else 0) =
      if A ⊆ U then (p ^ A.card)⁻¹ *
        (p ^ U.card * (1 - p) ^ (n - U.card)) else 0 := by
  classical
  rw [bernoulli_union_fiber]
  by_cases hAU : A ⊆ U
  · simp only [ite_eq_left hAU]
    have hpow : p ^ U.card = p ^ A.card * p ^ (U.card - A.card) := by
      rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_card hAU)]
    rw [hpow]
    simp only [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp), one_mul]
  · simp only [ite_eq_right hAU]
theorem sum_union_reindex {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (f g : Finset α → ℝ) :
    (∑ W : Finset α, f W * g (A ∪ W)) =
      ∑ U : Finset α, (∑ W : Finset α, if A ∪ W = U then f W else 0) * g U := by
  classical
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W _
  simp
theorem bernoulli_union_expectation (n : ℕ) (p : ℝ) (hp : p ≠ 0)
    (A : Finset (Fin n)) (g : Finset (Fin n) → ℝ) :
    (∑ W : Finset (Fin n),
      (p ^ W.card * (1 - p) ^ (n - W.card)) * g (A ∪ W)) =
      (p ^ A.card)⁻¹ * ∑ U : Finset (Fin n),
        (p ^ U.card * (1 - p) ^ (n - U.card)) * (if A ⊆ U then g U else 0) := by
  classical
  rw [sum_union_reindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [bernoulli_union_fiber_density n p hp]
  by_cases hAU : A ⊆ U <;> simp [hAU, mul_assoc]
theorem planted_union_density (n r : ℕ) (ν : Finset (Fin n) → ℝ) (p : ℝ)
    (g : Finset (Fin n) → ℝ) (hp : 0 < p) (_hp1 : p ≤ 1)
    (hν : ∀ A, ν A ≠ 0 → A.card = r) :
    (∑ A : Finset (Fin n), ν A * ∑ W : Finset (Fin n),
      (p ^ W.card * (1 - p) ^ (n - W.card)) * g (A ∪ W)) =
      (p ^ r)⁻¹ * ∑ U : Finset (Fin n),
        (p ^ U.card * (1 - p) ^ (n - U.card)) *
          (∑ A : Finset (Fin n), if A ⊆ U then ν A else 0) * g U := by
  classical
  calc
    _ = ∑ A : Finset (Fin n), (p ^ r)⁻¹ * ∑ U : Finset (Fin n),
        (p ^ U.card * (1 - p) ^ (n - U.card)) *
          (if A ⊆ U then ν A else 0) * g U := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases hzero : ν A = 0
      · simp [hzero]
      · rw [bernoulli_union_expectation n p (ne_of_gt hp) A g, hν A hzero]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U _
        by_cases hAU : A ⊆ U
        · simp only [ite_eq_left hAU]
          ring
        · simp [hAU]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
theorem bernoulli_containment (n : ℕ) (p : ℝ) (B : Finset (Fin n)) :
    (∑ W : Finset (Fin n),
      if B ⊆ W then p ^ W.card * (1 - p) ^ (n - W.card) else 0) = p ^ B.card := by
  classical
  have hcond (W : Finset (Fin n)) : B ⊆ W ↔ Bᶜ ∪ W = Finset.univ := by
    constructor
    · intro h
      ext x
      simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_univ, iff_true]
      by_cases hx : x ∈ B
      · exact Or.inr (h hx)
      · exact Or.inl hx
    · intro h x hx
      have hm : x ∈ Bᶜ ∪ W := by rw [h]; exact Finset.mem_univ x
      exact (Finset.mem_union.mp hm).resolve_left (by simpa using hx)
  have hcard : n - Bᶜ.card = B.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    have hc : B.card ≤ n := by simpa using Finset.card_le_univ B
    omega
  calc
    _ = ∑ W : Finset (Fin n),
        if Bᶜ ∪ W = Finset.univ then p ^ W.card * (1 - p) ^ (n - W.card) else 0 := by
      simp only [hcond]
    _ = _ := by
      rw [bernoulli_union_fiber, ite_eq_left (Finset.subset_univ _),
        Finset.card_univ, Fintype.card_fin, hcard]
      simp
theorem bernoulli_planted_containment (n : ℕ) (p : ℝ) (A B : Finset (Fin n)) :
    (∑ W : Finset (Fin n),
      if B ⊆ A ∪ W then p ^ W.card * (1 - p) ^ (n - W.card) else 0) =
        p ^ (B \ A).card := by
  classical
  have hcond (W : Finset (Fin n)) : B ⊆ A ∪ W ↔ B \ A ⊆ W := by
    constructor
    · intro h x hx
      exact (Finset.mem_union.mp (h (Finset.mem_sdiff.mp hx).1)).resolve_left
        (Finset.mem_sdiff.mp hx).2
    · intro h x hx
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_left W hxA
      · exact Finset.mem_union_right A (h (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))
  simp only [hcond]
  exact bernoulli_containment n p (B \ A)
noncomputable def paddingPush {ι β : Type*} [Fintype ι] [DecidableEq β]
    (μ : ι → ℝ) (f : ι → Finset β) (B : Finset β) : ℝ :=
  ∑ i, if f i = B then μ i else 0
theorem paddingPush_eval {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (μ : ι → ℝ) (f : ι → Finset β) (g : Finset β → ℝ) :
    (∑ B, paddingPush μ f B * g B) = ∑ i, μ i * g (f i) := by
  classical
  simp only [paddingPush, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp
theorem paddingPush_nonneg {ι β : Type*} [Fintype ι] [DecidableEq β]
    (μ : ι → ℝ) (f : ι → Finset β) (hμ : ∀ i, 0 ≤ μ i) (B : Finset β) :
    0 ≤ paddingPush μ f B := by
  classical
  exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp_all)
theorem paddingPush_support {ι β : Type*} [Fintype ι] [DecidableEq β]
    (μ : ι → ℝ) (f : ι → Finset β) (P : Finset β → Prop)
    (hP : ∀ i, μ i ≠ 0 → P (f i)) (B : Finset β)
    (hB : paddingPush μ f B ≠ 0) : P B := by
  classical
  by_contra h
  apply hB
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · by_contra hμ
    exact h (hi ▸ hP i hμ)
  · rfl
def paddingStepEdge {α : Type*} [DecidableEq α] {M : ℕ}
    (r : ℕ) (A : Finset α) (j : Fin M) : Finset (α ⊕ Fin M) :=
  A.disjSum (if A.card < r then {j} else ∅)
theorem paddingStepEdge_left {α : Type*} [DecidableEq α] {M : ℕ}
    (r : ℕ) (A : Finset α) (j : Fin M) : (paddingStepEdge r A j).toLeft = A := by
  simp [paddingStepEdge]
theorem paddingStepEdge_card {α : Type*} [DecidableEq α] {M : ℕ}
    (r : ℕ) (A : Finset α) (j : Fin M) :
    (paddingStepEdge r A j).card = A.card + if A.card < r then 1 else 0 := by
  by_cases h : A.card < r <;> simp [paddingStepEdge, h]
noncomputable def paddingStepWeights {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Finset α → ℝ) (r M : ℕ) : Finset (α ⊕ Fin M) → ℝ :=
  paddingPush (fun z : Finset α × Fin M => ν z.1 / M)
    (fun z => paddingStepEdge r z.1 z.2)
theorem paddingStepWeights_eval {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Finset α → ℝ) (r M : ℕ) (g : Finset (α ⊕ Fin M) → ℝ) :
    (∑ B, paddingStepWeights ν r M B * g B) =
      ∑ A, ∑ j : Fin M, ν A / M * g (paddingStepEdge r A j) := by
  classical
  simpa only [paddingStepWeights, Fintype.sum_prod_type] using
    paddingPush_eval (fun z : Finset α × Fin M => ν z.1 / M)
      (fun z => paddingStepEdge r z.1 z.2) g
theorem paddingStepWeights_left {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Finset α → ℝ) (r M : ℕ) (hM : 0 < M) (g : Finset α → ℝ) :
    (∑ B, paddingStepWeights ν r M B * g B.toLeft) = ∑ A, ν A * g A := by
  classical
  rw [paddingStepWeights_eval]
  apply Finset.sum_congr rfl
  intro A _
  simp only [paddingStepEdge_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
theorem paddingStepWeights_cone {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Finset α → ℝ) (r M : ℕ) (S : Finset (α ⊕ Fin M)) :
    (∑ B, if S ⊆ B then paddingStepWeights ν r M B else 0) =
      ∑ A, ∑ j : Fin M, if S ⊆ paddingStepEdge r A j then ν A / M else 0 := by
  classical
  simpa only [mul_ite, mul_one, mul_zero] using
    paddingStepWeights_eval ν r M (fun B => if S ⊆ B then 1 else 0)
theorem paddingStepWeights_spread {α : Type*} [Fintype α] [DecidableEq α]
    (ν : Finset α → ℝ) (r M : ℕ) (b : ℝ) (hb : 0 ≤ b) (hM : 0 < M)
    (hMb : 1 / (M : ℝ) ≤ b) (hν : ∀ A, 0 ≤ ν A)
    (hs : ∀ S : Finset α, (∑ A, if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (S : Finset (α ⊕ Fin M)) :
    (∑ B, if S ⊆ B then paddingStepWeights ν r M B else 0) ≤ b ^ S.card := by
  classical
  rw [paddingStepWeights_cone]
  have hpoint (A : Finset α) :
      (∑ j : Fin M, if S ⊆ paddingStepEdge r A j then ν A / M else 0) ≤
        (if S.toLeft ⊆ A then ν A else 0) * b ^ S.toRight.card := by
    by_cases hleft : S.toLeft ⊆ A
    · rw [if_pos hleft]
      by_cases hzero : S.toRight = ∅
      · simp only [paddingStepEdge, Finset.subset_disjSum, hleft, true_and, hzero,
          Finset.empty_subset, ite_true, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.card_empty, pow_zero, mul_one]
        have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
        exact le_of_eq (by field_simp)
      · by_cases hone : S.toRight.card = 1
        · obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hone
          by_cases hAr : A.card < r
          · simp only [paddingStepEdge, hAr, ite_true, Finset.subset_disjSum, hleft,
              true_and, hj₀, Finset.singleton_subset_iff, Finset.mem_singleton]
            rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
            simpa only [Finset.card_singleton, pow_one, div_eq_mul_inv, one_mul] using
              mul_le_mul_of_nonneg_left hMb (hν A)
          · have hnot (j : Fin M) : ¬ S ⊆ paddingStepEdge r A j := by
              intro h
              have hh : S.toRight ⊆ (if A.card < r then {j} else ∅) :=
                (Finset.subset_disjSum.mp h).2
              rw [if_neg hAr] at hh
              exact hzero (Finset.subset_empty.mp hh)
            simp only [hnot, ite_false, Finset.sum_const_zero]
            exact mul_nonneg (hν A) (pow_nonneg hb _)
        · have hnot (j : Fin M) : ¬ S ⊆ paddingStepEdge r A j := by
            intro h
            have hcard : S.toRight.card ≤ 1 := by
              have hh : S.toRight ⊆ (if A.card < r then {j} else ∅) :=
                (Finset.subset_disjSum.mp h).2
              have hh' := Finset.card_le_card hh
              by_cases hAr : A.card < r
              · simpa only [if_pos hAr, Finset.card_singleton] using hh'
              · have hh0 : S.toRight.card ≤ 0 := by
                  simpa only [if_neg hAr, Finset.card_empty] using hh'
                omega
            have hnz : S.toRight.card ≠ 0 := by simpa using hzero
            omega
          simp only [hnot, ite_false, Finset.sum_const_zero]
          exact mul_nonneg (hν A) (pow_nonneg hb _)
    · have hnot (j : Fin M) : ¬ S ⊆ paddingStepEdge r A j := by
        intro h
        exact hleft (by simpa only [paddingStepEdge_left] using Finset.toLeft_subset_toLeft h)
      simp [hnot, hleft]
  calc
    _ ≤ ∑ A, (if S.toLeft ⊆ A then ν A else 0) * b ^ S.toRight.card :=
      Finset.sum_le_sum (fun A _ => hpoint A)
    _ = (∑ A, if S.toLeft ⊆ A then ν A else 0) * b ^ S.toRight.card :=
      (Finset.sum_mul ..).symm
    _ ≤ b ^ S.toLeft.card * b ^ S.toRight.card :=
      mul_le_mul_of_nonneg_right (hs S.toLeft) (pow_nonneg hb _)
    _ = b ^ S.card := by rw [← pow_add, Finset.card_toLeft_add_card_toRight]
def paddingPull {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (B : Finset β) : Finset α :=
  Finset.univ.filter (fun x => e x ∈ B)
theorem paddingPull_mem {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (B : Finset β) (x : α) : x ∈ paddingPull e B ↔ e x ∈ B := by
  simp [paddingPull]
theorem paddingPull_refl {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) :
    paddingPull (Function.Embedding.refl α) B = B := by
  ext x
  simp [paddingPull]
theorem paddingPull_step {α β γ : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] {M : ℕ} (e : α ↪ β)
    (E : β ⊕ Fin M ≃ γ) (B : Finset (β ⊕ Fin M)) :
    paddingPull ((e.trans Function.Embedding.inl).trans E.toEmbedding)
      (B.map E.toEmbedding) = paddingPull e B.toLeft := by
  ext x
  simp [paddingPull, Function.Embedding.trans_apply]
theorem paddingRelabel_sum {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (E : α ≃ β)
    (w : Finset α → ℝ) (g : Finset β → ℝ) :
    (∑ B : Finset β, w (B.map E.symm.toEmbedding) * g B) =
      ∑ A : Finset α, w A * g (A.map E.toEmbedding) := by
  classical
  symm
  apply Fintype.sum_equiv E.finsetCongr
  intro A
  simp [Finset.map_map]
theorem paddingRelabel_spread {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (E : α ≃ β) (w : Finset α → ℝ) (b : ℝ)
    (hs : ∀ S : Finset α, (∑ A, if S ⊆ A then w A else 0) ≤ b ^ S.card)
    (S : Finset β) :
    (∑ B : Finset β, if S ⊆ B then w (B.map E.symm.toEmbedding) else 0) ≤
      b ^ S.card := by
  classical
  have heval := paddingRelabel_sum E w (fun B => if S ⊆ B then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at heval
  rw [heval]
  have heq (A : Finset α) : S ⊆ A.map E.toEmbedding ↔ S.map E.symm.toEmbedding ⊆ A := by
    constructor
    · intro h
      have hh := (Finset.map_subset_map (f := E.symm.toEmbedding)).mpr h
      simpa [Finset.map_map] using hh
    · intro h
      have hh := (Finset.map_subset_map (f := E.toEmbedding)).mpr h
      simpa [Finset.map_map] using hh
  simp only [heq]
  simpa only [Finset.card_map] using hs (S.map E.symm.toEmbedding)
theorem padding_iterate (n r M : ℕ) (ν : Finset (Fin n) → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hM : 0 < M) (hMb : 1 / (M : ℝ) ≤ b)
    (hν : ∀ A, 0 ≤ ν A) (hr : ∀ A, ν A ≠ 0 → A.card ≤ r)
    (hs : ∀ S : Finset (Fin n), (∑ A, if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (k : ℕ) :
    ∃ (N : ℕ) (e : Fin n ↪ Fin N) (w : Finset (Fin N) → ℝ),
      (∀ B, 0 ≤ w B) ∧
      (∀ B, w B ≠ 0 → min k r ≤ B.card ∧ B.card ≤ r) ∧
      (∀ S : Finset (Fin N), (∑ B, if S ⊆ B then w B else 0) ≤ b ^ S.card) ∧
      ∀ g : Finset (Fin n) → ℝ,
        (∑ B, w B * g (paddingPull e B)) = ∑ A, ν A * g A := by
  classical
  induction k with
  | zero =>
    refine ⟨n, Function.Embedding.refl _, ν, hν, ?_, hs, ?_⟩
    · intro A hA
      exact ⟨by simp, hr A hA⟩
    · intro g
      simp only [paddingPull_refl]
  | succ k ih =>
    obtain ⟨N, e, w, hw, hcard, hspread, heval⟩ := ih
    let E : Fin N ⊕ Fin M ≃ Fin (N + M) := finSumFinEquiv
    let v := paddingStepWeights w r M
    let e' := (e.trans Function.Embedding.inl).trans E.toEmbedding
    let w' : Finset (Fin (N + M)) → ℝ := fun B => v (B.map E.symm.toEmbedding)
    have hv : ∀ B, 0 ≤ v B := by
      apply paddingPush_nonneg
      intro z
      exact div_nonneg (hw z.1) (Nat.cast_nonneg M)
    have hvcard : ∀ B, v B ≠ 0 → min (k + 1) r ≤ B.card ∧ B.card ≤ r := by
      apply paddingPush_support
      intro z hz
      have hz' : w z.1 ≠ 0 := by
        intro hz0
        exact hz (by simp [hz0])
      obtain ⟨hlo, hhi⟩ := hcard z.1 hz'
      rw [paddingStepEdge_card]
      split_ifs <;> omega
    refine ⟨N + M, e', w', ?_, ?_, ?_, ?_⟩
    · intro B
      exact hv _
    · intro B hB
      simpa only [Finset.card_map] using hvcard _ hB
    · exact paddingRelabel_spread E v b
        (paddingStepWeights_spread w r M b hb hM hMb hw hspread)
    · intro g
      change (∑ B, v (B.map E.symm.toEmbedding) * g (paddingPull e' B)) = _
      rw [paddingRelabel_sum]
      have hp (B : Finset (Fin N ⊕ Fin M)) :
          paddingPull e' (B.map E.toEmbedding) = paddingPull e B.toLeft :=
        paddingPull_step e E B
      simp only [hp]
      exact (paddingStepWeights_left w r M hM (fun A => g (paddingPull e A))).trans (heval g)
theorem spread_padding (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b : ℝ)
    (hb : 0 < b) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A : Finset (Fin n), ν A) ≤ 1)
    (hr : ∀ A, ν A ≠ 0 → A.card ≤ r)
    (hs : ∀ S : Finset (Fin n), (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card) :
    ∃ (N : ℕ) (e : Fin n ↪ Fin N) (w : Finset (Fin N) → ℝ),
      (∀ B, 0 ≤ w B) ∧ (∀ B, w B ≠ 0 → B.card = r) ∧
      (∑ B : Finset (Fin N), w B) = (∑ A : Finset (Fin n), ν A) ∧
      (∀ S : Finset (Fin N), (∑ B : Finset (Fin N), if S ⊆ B then w B else 0) ≤ b ^ S.card) ∧
      ∀ A : Finset (Fin n),
        (∑ B : Finset (Fin N), if (∀ x : Fin n, e x ∈ B ↔ x ∈ A) then w B else 0) = ν A := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hb
  have hMb : 1 / ((m + 1 : ℕ) : ℝ) ≤ b := by
    have hm' : 1 / ((m + 1 : ℕ) : ℝ) < b := by
      simpa only [Nat.cast_add, Nat.cast_one] using hm
    exact hm'.le
  obtain ⟨N, e, w, hw, hcard, hspread, heval⟩ :=
    padding_iterate n r (m + 1) ν b hb.le (by omega) hMb hν hr hs r
  refine ⟨N, e, w, hw, ?_, ?_, hspread, ?_⟩
  · intro B hB
    have hh := hcard B hB
    simp only [min_self] at hh
    exact Nat.le_antisymm hh.2 hh.1
  · simpa only [mul_one] using heval (fun _ => 1)
  · intro A
    have hp (B : Finset (Fin N)) :
        (∀ x : Fin n, e x ∈ B ↔ x ∈ A) ↔ paddingPull e B = A := by
      simp only [Finset.ext_iff, paddingPull_mem]
    simp only [hp]
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using heval (fun A' => if A' = A then 1 else 0)
theorem fragmentation_ratio_pow (r s : ℕ) (b p : ℝ) (hb : 0 ≤ b) (hp : 0 < p)
    (hbp : (2 : ℝ) ^ 32 * b ≤ p) (hrs : r ≤ 2 * s) :
    (b / p) ^ s ≤ ((65536 : ℝ) ^ r)⁻¹ := by
  have hratio : b / p ≤ ((2 : ℝ) ^ 32)⁻¹ := by
    apply (div_le_iff₀ hp).mpr
    calc
      b = ((2 : ℝ) ^ 32)⁻¹ * ((2 : ℝ) ^ 32 * b) := by norm_num; ring
      _ ≤ ((2 : ℝ) ^ 32)⁻¹ * p :=
        mul_le_mul_of_nonneg_left hbp (by positivity)
  calc
    (b / p) ^ s ≤ (((2 : ℝ) ^ 32)⁻¹) ^ s :=
      pow_le_pow_left₀ (div_nonneg hb hp.le) hratio _
    _ = ((2 : ℝ) ^ (32 * s))⁻¹ := by rw [inv_pow, ← pow_mul]
    _ ≤ ((2 : ℝ) ^ (16 * r))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ = ((65536 : ℝ) ^ r)⁻¹ := by rw [pow_mul]; norm_num
def fragmentWeight (n : ℕ) (p : ℝ) (W : Finset (Fin n)) : ℝ :=
  p ^ W.card * (1 - p) ^ (n - W.card)
noncomputable def fragmentDensity {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (U : Finset (Fin n)) : ℝ := ∑ B, if B ⊆ U then ν B else 0
noncomputable def fragmentHigh {n : ℕ} (ν : Finset (Fin n) → ℝ) (r : ℕ)
    (A U : Finset (Fin n)) : ℝ :=
  ∑ B, if r < 2 * (A ∩ B).card ∧ B ⊆ U then ν B else 0
def fragmentBad {n : ℕ} (ν : Finset (Fin n) → ℝ) (r : ℕ)
    (A W : Finset (Fin n)) : Prop :=
  ¬ ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ A ∪ W ∧ (B \ W).card ≤ r / 2
theorem fragmentWeight_nonneg (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Finset (Fin n)) : 0 ≤ fragmentWeight n p W := by
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)
theorem fragmentDensity_nonneg {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (hν : ∀ B, 0 ≤ ν B) (U : Finset (Fin n)) : 0 ≤ fragmentDensity ν U := by
  classical
  apply Finset.sum_nonneg
  intro B _
  split_ifs
  · exact hν B
  · exact le_rfl
theorem fragmentHigh_nonneg {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (hν : ∀ B, 0 ≤ ν B) (r : ℕ) (A U : Finset (Fin n)) :
    0 ≤ fragmentHigh ν r A U := by
  classical
  apply Finset.sum_nonneg
  intro B _
  split_ifs
  · exact hν B
  · exact le_rfl
theorem fragmentation_high_moment_eq (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (p : ℝ) (A : Finset (Fin n)) :
    (∑ W, fragmentWeight n p W * fragmentHigh ν r A (A ∪ W)) =
      ∑ B : Finset (Fin n),
        if r < 2 * (A ∩ B).card then ν B * p ^ (B \ A).card else 0 := by
  classical
  simp only [fragmentHigh, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hh : r < 2 * (A ∩ B).card
  · simp only [hh, true_and, ite_true]
    calc
      _ = (∑ W : Finset (Fin n),
          if B ⊆ A ∪ W then fragmentWeight n p W else 0) * ν B := by
        simp only [Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
      _ = _ := by
        simp only [fragmentWeight]
        rw [bernoulli_planted_containment]
        ring
  · simp [hh]
theorem fragmentation_inter_moment_le (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (hν : ∀ B, 0 ≤ ν B)
    (huniform : ∀ B, ν B ≠ 0 → B.card = r) (A S : Finset (Fin n))
    (hh : r < 2 * S.card) :
    (∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => A ∩ B = S),
      if r < 2 * (A ∩ B).card then ν B * p ^ (B \ A).card else 0) ≤
      p ^ (r - S.card) * ∑ B : Finset (Fin n), if S ⊆ B then ν B else 0 := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B _
  by_cases heq : A ∩ B = S
  · have hSB : S ⊆ B := by rw [← heq]; exact Finset.inter_subset_right
    simp only [heq, ite_eq_left hh, ite_eq_left hSB]
    by_cases hz : ν B = 0
    · simp [hz]
    · have hc := Finset.card_sdiff_add_card_inter B A
      rw [Finset.inter_comm B A, heq, huniform B hz] at hc
      rw [show (B \ A).card = r - S.card by omega]
      exact le_of_eq (mul_comm _ _)
  · rw [ite_eq_right heq]
    apply mul_nonneg (pow_nonneg hp _)
    split_ifs
    · exact hν B
    · exact le_rfl
theorem fragmentation_high_moment_le (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (b p : ℝ) (hν : ∀ B, 0 ≤ ν B)
    (huniform : ∀ B, ν B ≠ 0 → B.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ B : Finset (Fin n), if S ⊆ B then ν B else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hbp : (2 : ℝ) ^ 32 * b ≤ p)
    (A : Finset (Fin n)) (hA : A.card = r) :
    (∑ W, fragmentWeight n p W * fragmentHigh ν r A (A ∪ W)) ≤
      p ^ r * ((32768 : ℝ) ^ r)⁻¹ := by
  classical
  rw [fragmentation_high_moment_eq]
  have hmap : ∀ B ∈ (Finset.univ : Finset (Finset (Fin n))), A ∩ B ∈ A.powerset := by
    intro B _
    exact Finset.mem_powerset.mpr Finset.inter_subset_left
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ S ∈ A.powerset, p ^ r * ((65536 : ℝ) ^ r)⁻¹ := by
      apply Finset.sum_le_sum
      intro S hS
      have hSr : S.card ≤ r := by
        rw [← hA]
        exact Finset.card_le_card (Finset.mem_powerset.mp hS)
      by_cases hh : r < 2 * S.card
      · calc
          _ ≤ p ^ (r - S.card) * ∑ B : Finset (Fin n), if S ⊆ B then ν B else 0 :=
            fragmentation_inter_moment_le n r ν p hp.le hν huniform A S hh
          _ ≤ p ^ (r - S.card) * b ^ S.card :=
            mul_le_mul_of_nonneg_left (hspread S) (pow_nonneg hp.le _)
          _ = p ^ r * (b / p) ^ S.card := by
            rw [div_pow, ← mul_div_assoc]
            apply (eq_div_iff (pow_ne_zero _ (ne_of_gt hp))).mpr
            calc
              _ = (p ^ (r - S.card) * p ^ S.card) * b ^ S.card := by ring
              _ = _ := by rw [← pow_add, Nat.sub_add_cancel hSr]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (fragmentation_ratio_pow r S.card b p hb hp hbp (by omega)) (pow_nonneg hp.le _)
      · have hz : (∑ B ∈ Finset.univ.filter (fun B : Finset (Fin n) => A ∩ B = S),
            if r < 2 * (A ∩ B).card then ν B * p ^ (B \ A).card else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro B hB
          have heq := (Finset.mem_filter.mp hB).2
          simp [heq, hh]
        rw [hz]
        positivity
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powerset, hA, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      have heq : (2 : ℝ) ^ r * ((65536 : ℝ) ^ r)⁻¹ = ((32768 : ℝ) ^ r)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_pow,
          show (2 : ℝ) / 65536 = (32768 : ℝ)⁻¹ by norm_num, inv_pow]
      calc
        _ = p ^ r * ((2 : ℝ) ^ r * ((65536 : ℝ) ^ r)⁻¹) := by ring
        _ = _ := by rw [heq]
theorem fragmentBad_density_eq_high {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (hν : ∀ B, 0 ≤ ν B) (r : ℕ) (A W : Finset (Fin n))
    (hbad : fragmentBad ν r A W) :
    fragmentDensity ν (A ∪ W) = fragmentHigh ν r A (A ∪ W) := by
  classical
  apply Finset.sum_congr rfl
  intro B _
  by_cases hBU : B ⊆ A ∪ W
  · by_cases hz : ν B = 0
    · simp [hz]
    · have hv : 0 < ν B := lt_of_le_of_ne (hν B) (Ne.symm hz)
      have hlarge : ¬ (B \ W).card ≤ r / 2 := fun hh => hbad ⟨B, hv, hBU, hh⟩
      have hsub : B \ W ⊆ A ∩ B := by
        intro x hx
        have hxB := (Finset.mem_sdiff.mp hx).1
        have hxW := (Finset.mem_sdiff.mp hx).2
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_union.mp (hBU hxB)).resolve_right hxW, hxB⟩
      have hc := Finset.card_le_card hsub
      have hh : r < 2 * (A ∩ B).card := by omega
      simp [hBU, hh]
  · simp [hBU]
theorem fragmentation_low_density_le (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (p t : ℝ) (hν : ∀ A, 0 ≤ ν A)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r)
    (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (∑ A, ν A * ∑ W, fragmentWeight n p W *
      (if fragmentDensity ν (A ∪ W) ≤ t then (1 : ℝ) else 0)) ≤
      (p ^ r)⁻¹ * t := by
  classical
  have hd := planted_union_density n r ν p
    (fun U => if fragmentDensity ν U ≤ t then (1 : ℝ) else 0) hp hp1 huniform
  change (∑ A, ν A * ∑ W, fragmentWeight n p W *
      (if fragmentDensity ν (A ∪ W) ≤ t then (1 : ℝ) else 0)) =
    (p ^ r)⁻¹ * ∑ U, fragmentWeight n p U * fragmentDensity ν U *
      (if fragmentDensity ν U ≤ t then (1 : ℝ) else 0) at hd
  rw [hd]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ U : Finset (Fin n), fragmentWeight n p U * t := by
      apply Finset.sum_le_sum
      intro U _
      have hw := fragmentWeight_nonneg n p hp.le hp1 U
      by_cases hU : fragmentDensity ν U ≤ t
      · simp only [ite_eq_left hU, mul_one]
        exact mul_le_mul_of_nonneg_left hU hw
      · simp only [ite_eq_right hU, mul_zero]
        exact mul_nonneg hw ht
    _ = t := by
      rw [← Finset.sum_mul]
      simp only [fragmentWeight]
      rw [bernoulli_finset_normalization, one_mul]
theorem fragmentation_bad_indicator_le {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (hν : ∀ B, 0 ≤ ν B) (r : ℕ) (A W : Finset (Fin n))
    (t : ℝ) (ht : 0 < t) :
    (@ite ℝ (fragmentBad ν r A W) (Classical.propDecidable _) 1 0) ≤
      (if fragmentDensity ν (A ∪ W) ≤ t then (1 : ℝ) else 0) +
        fragmentHigh ν r A (A ∪ W) / t := by
  classical
  have hH := fragmentHigh_nonneg ν hν r A (A ∪ W)
  have hHt : 0 ≤ fragmentHigh ν r A (A ∪ W) / t := div_nonneg hH ht.le
  by_cases hbad : fragmentBad ν r A W
  · rw [ite_eq_left hbad]
    by_cases hlow : fragmentDensity ν (A ∪ W) ≤ t
    · rw [ite_eq_left hlow]
      linarith
    · rw [ite_eq_right hlow, zero_add, le_div_iff₀ ht, one_mul]
      rw [← fragmentBad_density_eq_high ν hν r A W hbad]
      exact (lt_of_not_ge hlow).le
  · rw [ite_eq_right hbad]
    split_ifs <;> linarith
theorem fragmentation_total_high_le (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (b p : ℝ) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A, ν A) ≤ 1)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hbp : (2 : ℝ) ^ 32 * b ≤ p) :
    (∑ A, ν A * ∑ W, fragmentWeight n p W * fragmentHigh ν r A (A ∪ W)) ≤
      p ^ r * ((32768 : ℝ) ^ r)⁻¹ := by
  classical
  calc
    _ ≤ ∑ A : Finset (Fin n), ν A * (p ^ r * ((32768 : ℝ) ^ r)⁻¹) := by
      apply Finset.sum_le_sum
      intro A _
      by_cases hz : ν A = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (fragmentation_high_moment_le n r ν b p hν huniform hb hspread hp hbp A
            (huniform A hz)) (hν A)
    _ = (∑ A, ν A) * (p ^ r * ((32768 : ℝ) ^ r)⁻¹) := by rw [Finset.sum_mul]
    _ ≤ 1 * (p ^ r * ((32768 : ℝ) ^ r)⁻¹) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := one_mul _
theorem fragmentation_loss_le (n r : ℕ) (ν : Finset (Fin n) → ℝ)
    (b p t : ℝ) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A, ν A) ≤ 1)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hp1 : p ≤ 1) (hbp : (2 : ℝ) ^ 32 * b ≤ p) (ht : 0 < t) :
    (∑ W, fragmentWeight n p W * ∑ A : Finset (Fin n),
      @ite ℝ (fragmentBad ν r A W) (Classical.propDecidable _) (ν A) 0) ≤
      (p ^ r)⁻¹ * t + (p ^ r * ((32768 : ℝ) ^ r)⁻¹) / t := by
  classical
  calc
    _ = ∑ A : Finset (Fin n), ν A * ∑ W : Finset (Fin n),
        fragmentWeight n p W * (if fragmentBad ν r A W then (1 : ℝ) else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro W _
      split_ifs <;> ring
    _ ≤ ∑ A : Finset (Fin n), ν A * ∑ W : Finset (Fin n),
        fragmentWeight n p W *
          ((if fragmentDensity ν (A ∪ W) ≤ t then (1 : ℝ) else 0) +
            fragmentHigh ν r A (A ∪ W) / t) := by
      apply Finset.sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_left _ (hν A)
      apply Finset.sum_le_sum
      intro W _
      exact mul_le_mul_of_nonneg_left (fragmentation_bad_indicator_le ν hν r A W t ht)
        (fragmentWeight_nonneg n p hp.le hp1 W)
    _ = (∑ A, ν A * ∑ W, fragmentWeight n p W *
          (if fragmentDensity ν (A ∪ W) ≤ t then (1 : ℝ) else 0)) +
        (∑ A, ν A * ∑ W, fragmentWeight n p W * fragmentHigh ν r A (A ∪ W)) / t := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, ← Finset.sum_div]
    _ ≤ _ := add_le_add
      (fragmentation_low_density_le n r ν p t hν huniform hp hp1 ht.le)
      (div_le_div_of_nonneg_right
        (fragmentation_total_high_le n r ν b p hν hmass huniform hb hspread hp hbp) ht.le)
theorem fragmentation_error_sum_le (r : ℕ) (hr : 1 ≤ r) :
    ((128 : ℝ) ^ r)⁻¹ + ((256 : ℝ) ^ r)⁻¹ ≤ ((64 : ℝ) ^ r)⁻¹ := by
  have h2 : ((2 : ℝ) ^ r)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div, pow_one] using
      (one_div_pow_le_one_div_pow_of_le (a := (2 : ℝ)) (by norm_num) hr)
  have h4 : ((4 : ℝ) ^ r)⁻¹ ≤ 1 / 4 := by
    simpa only [one_div, pow_one] using
      (one_div_pow_le_one_div_pow_of_le (a := (4 : ℝ)) (by norm_num) hr)
  have h128 : (128 : ℝ) ^ r = (64 : ℝ) ^ r * (2 : ℝ) ^ r := by
    rw [← mul_pow]; norm_num
  have h256 : (256 : ℝ) ^ r = (64 : ℝ) ^ r * (4 : ℝ) ^ r := by
    rw [← mul_pow]; norm_num
  calc
    _ = ((64 : ℝ) ^ r)⁻¹ * (((2 : ℝ) ^ r)⁻¹ + ((4 : ℝ) ^ r)⁻¹) := by
      rw [h128, h256, mul_inv_rev, mul_inv_rev]
      ring
    _ ≤ ((64 : ℝ) ^ r)⁻¹ * (1 / 2 + 1 / 4) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h4) (by positivity)
    _ ≤ _ := by nlinarith [show 0 ≤ ((64 : ℝ) ^ r)⁻¹ by positivity]
theorem fragmentation_step (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ)
    (hr : 1 ≤ r) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A : Finset (Fin n), ν A) ≤ 1)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hp1 : p ≤ 1) (hbp : (2 : ℝ) ^ 32 * b ≤ p) :
    (∑ W : Finset (Fin n), (p ^ W.card * (1 - p) ^ (n - W.card)) *
      ∑ A : Finset (Fin n),
        @ite ℝ (¬ ∃ B : Finset (Fin n),
          0 < ν B ∧ B ⊆ A ∪ W ∧ (B \ W).card ≤ r / 2)
          (Classical.propDecidable _) (ν A) 0) ≤ ((64 : ℝ) ^ r)⁻¹ := by
  classical
  have hpR : p ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hp)
  have h128 : (128 : ℝ) ^ r ≠ 0 := by positivity
  have h256 : (256 : ℝ) ^ r ≠ 0 := by positivity
  have hnum : (32768 : ℝ) ^ r = (128 : ℝ) ^ r * (256 : ℝ) ^ r := by
    rw [← mul_pow]; norm_num
  calc
    _ ≤ (p ^ r)⁻¹ * (p ^ r * ((128 : ℝ) ^ r)⁻¹) +
        (p ^ r * ((32768 : ℝ) ^ r)⁻¹) / (p ^ r * ((128 : ℝ) ^ r)⁻¹) :=
      fragmentation_loss_le n r ν b p (p ^ r * ((128 : ℝ) ^ r)⁻¹)
        hν hmass huniform hb hspread hp hp1 hbp (by positivity)
    _ = ((128 : ℝ) ^ r)⁻¹ + ((256 : ℝ) ^ r)⁻¹ := by
      rw [hnum]
      field_simp
    _ ≤ _ := fragmentation_error_sum_le r hr
theorem bernoulli_union_kernel (n : ℕ) (p q : ℝ) (W : Finset (Fin n)) :
    (∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
      (if U ⊆ W then q ^ (W.card - U.card) * (1 - q) ^ (n - W.card) else 0)) =
      (p + q - p * q) ^ W.card *
        (1 - (p + q - p * q)) ^ (n - W.card) := by
  classical
  have hcW : W.card ≤ n := by simpa using Finset.card_le_univ W
  calc
    _ = ∑ U ∈ W.powerset, (p ^ U.card * (1 - p) ^ (n - U.card)) *
        (q ^ (W.card - U.card) * (1 - q) ^ (n - W.card)) := by
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext U
      simp
    _ = ((1 - p) * (1 - q)) ^ (n - W.card) *
        ∑ U ∈ W.powerset, p ^ U.card * ((1 - p) * q) ^ (W.card - U.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      have hcU : U.card ≤ W.card := Finset.card_le_card (Finset.mem_powerset.mp hU)
      rw [show n - U.card = (n - W.card) + (W.card - U.card) by omega]
      simp only [pow_add, mul_pow]
      ring
    _ = _ := by
      rw [Finset.sum_pow_mul_eq_add_pow]
      rw [show (1 - p) * (1 - q) = 1 - (p + q - p * q) by ring,
        show p + (1 - p) * q = p + q - p * q by ring]
      ring
theorem bernoulli_union_convolution (n : ℕ) (p q : ℝ) (g : Finset (Fin n) → ℝ) :
    (∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
      ∑ V : Finset (Fin n), (q ^ V.card * (1 - q) ^ (n - V.card)) * g (U ∪ V)) =
      ∑ W : Finset (Fin n), ((p + q - p * q) ^ W.card *
        (1 - (p + q - p * q)) ^ (n - W.card)) * g W := by
  classical
  calc
    _ = ∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
        ∑ W : Finset (Fin n),
          (if U ⊆ W then q ^ (W.card - U.card) * (1 - q) ^ (n - W.card) else 0) * g W := by
      apply Finset.sum_congr rfl
      intro U _
      rw [sum_union_reindex]
      simp only [bernoulli_union_fiber]
    _ = ∑ W : Finset (Fin n),
        (∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
          (if U ⊆ W then q ^ (W.card - U.card) * (1 - q) ^ (n - W.card) else 0)) * g W := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro W _
      rw [bernoulli_union_kernel]
theorem bernoulli_expectation_mono (n : ℕ) (p t : ℝ) (g : Finset (Fin n) → ℝ)
    (hp : 0 ≤ p) (hpt : p ≤ t) (ht : t ≤ 1)
    (hg : ∀ A B : Finset (Fin n), A ⊆ B → g A ≤ g B) :
    (∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) * g U) ≤
      ∑ U : Finset (Fin n), (t ^ U.card * (1 - t) ^ (n - U.card)) * g U := by
  classical
  by_cases hpeq : p = 1
  · have hteq : t = 1 := by linarith
    simp only [hpeq, hteq, le_refl]
  have hp1 : p < 1 := lt_of_le_of_ne (hpt.trans ht) hpeq
  let q := (t - p) / (1 - p)
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hpt) (by linarith)
  have hq1 : q ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 - p)).mpr
    linarith
  have hparam : p + q - p * q = t := by
    dsimp [q]
    field_simp
    <;> ring
  calc
    _ = ∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
        ∑ V : Finset (Fin n), (q ^ V.card * (1 - q) ^ (n - V.card)) * g U := by
      apply Finset.sum_congr rfl
      intro U _
      rw [← Finset.sum_mul, bernoulli_finset_normalization, one_mul]
    _ ≤ ∑ U : Finset (Fin n), (p ^ U.card * (1 - p) ^ (n - U.card)) *
        ∑ V : Finset (Fin n), (q ^ V.card * (1 - q) ^ (n - V.card)) * g (U ∪ V) := by
      apply Finset.sum_le_sum
      intro U _
      apply mul_le_mul_of_nonneg_left _ (fragmentWeight_nonneg n p hp hp1.le U)
      apply Finset.sum_le_sum
      intro V _
      exact mul_le_mul_of_nonneg_left (hg U (U ∪ V) Finset.subset_union_left)
        (fragmentWeight_nonneg n q hq hq1 V)
    _ = _ := by rw [bernoulli_union_convolution, hparam]
theorem fragment_update (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ)
    (hr : 1 ≤ r) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A : Finset (Fin n), ν A) ≤ 1)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hp1 : p ≤ 1) (hbp : (2 : ℝ) ^ 32 * b ≤ p) :
    ∃ μ : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ W T, 0 ≤ μ W T) ∧
      (∀ W T, μ W T ≠ 0 → T.card ≤ r / 2) ∧
      (∀ W, (∑ T : Finset (Fin n), μ W T) ≤ (∑ A : Finset (Fin n), ν A)) ∧
      (∀ W S : Finset (Fin n),
        (∑ T : Finset (Fin n), if S ⊆ T then μ W T else 0) ≤ b ^ S.card) ∧
      (∀ W T, 0 < μ W T → ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ T ∪ W) ∧
      (∑ W : Finset (Fin n), (p ^ W.card * (1 - p) ^ (n - W.card)) *
        ((∑ A : Finset (Fin n), ν A) - ∑ T : Finset (Fin n), μ W T)) ≤
          ((64 : ℝ) ^ r)⁻¹ := by
  classical
  let good (W A : Finset (Fin n)) : Prop :=
    ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ A ∪ W ∧ (B \ W).card ≤ r / 2
  let f (W A : Finset (Fin n)) : Finset (Fin n) :=
    if hg : good W A then (Classical.choose hg) \ W else ∅
  have hf (W A : Finset (Fin n)) (hg : good W A) :
      f W A ⊆ A ∧ (f W A).card ≤ r / 2 ∧
        ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ f W A ∪ W := by
    have hB := Classical.choose_spec hg
    dsimp only [f]
    rw [dite_eq_left hg]
    refine ⟨?_, hB.2.2, Classical.choose hg, hB.1, ?_⟩
    · intro x hx
      exact (Finset.mem_union.mp (hB.2.1 (Finset.mem_sdiff.mp hx).1)).resolve_right
        (Finset.mem_sdiff.mp hx).2
    · intro x hx
      by_cases hxW : x ∈ W
      · exact Finset.mem_union_right _ hxW
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxW⟩)
  let v (W A : Finset (Fin n)) : ℝ := if good W A then ν A else 0
  let μ (W : Finset (Fin n)) := paddingPush (v W) (f W)
  have hv (W A : Finset (Fin n)) : 0 ≤ v W A := by
    dsimp [v]
    split_ifs
    · exact hν A
    · exact le_rfl
  have hvle (W A : Finset (Fin n)) : v W A ≤ ν A := by
    dsimp [v]
    split_ifs
    · exact le_rfl
    · exact hν A
  have hgood (W A : Finset (Fin n)) (h : v W A ≠ 0) : good W A := by
    by_contra hbad
    exact h (by simp [v, hbad])
  have hsum (W : Finset (Fin n)) : (∑ T, μ W T) = ∑ A, v W A := by
    simpa only [mul_one] using paddingPush_eval (v W) (f W) (fun _ => (1 : ℝ))
  have hcone (W S : Finset (Fin n)) :
      (∑ T, if S ⊆ T then μ W T else 0) =
        ∑ A, if S ⊆ f W A then v W A else 0 := by
    simpa only [mul_ite, mul_one, mul_zero] using
      paddingPush_eval (v W) (f W) (fun T => if S ⊆ T then (1 : ℝ) else 0)
  refine ⟨μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W T
    exact paddingPush_nonneg (v W) (f W) (hv W) T
  · intro W T hT
    exact paddingPush_support (v W) (f W) (fun T => T.card ≤ r / 2)
      (fun A hA => (hf W A (hgood W A hA)).2.1) T hT
  · intro W
    rw [hsum]
    exact Finset.sum_le_sum (fun A _ => hvle W A)
  · intro W S
    rw [hcone]
    apply le_trans _ (hspread S)
    apply Finset.sum_le_sum
    intro A _
    by_cases hSA : S ⊆ f W A
    · rw [ite_eq_left hSA]
      by_cases hz : v W A = 0
      · rw [hz]
        split_ifs
        · exact hν A
        · exact le_rfl
      · have hsub : S ⊆ A := hSA.trans (hf W A (hgood W A hz)).1
        rw [ite_eq_left hsub]
        exact hvle W A
    · rw [ite_eq_right hSA]
      split_ifs
      · exact hν A
      · exact le_rfl
  · intro W T hT
    exact paddingPush_support (v W) (f W)
      (fun T => ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ T ∪ W)
      (fun A hA => (hf W A (hgood W A hA)).2.2) T (ne_of_gt hT)
  · have hloss (W : Finset (Fin n)) :
        (∑ A, ν A) - ∑ T, μ W T =
          ∑ A : Finset (Fin n),
            @ite ℝ (¬ good W A) (Classical.propDecidable _) (ν A) 0 := by
      rw [hsum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hg : good W A <;> simp [v, hg]
    simp_rw [hloss]
    exact fragmentation_step n r ν b p hr hν hmass huniform hb hspread hp hp1 hbp
def modelWeaklySmall {X : Type*} [Fintype X] (p : unitInterval) (𝓕 : Set (Set X)) : Prop := by
  classical
  exact ∃ g : Set X → NNReal, (∀ T ∈ 𝓕, ∑ S with S ⊆ T, g S ≥ 1) ∧ ∑ S, g S * (p : ℝ) ^ S.ncard ≤ 2⁻¹
noncomputable def modelPC {X : Type*} (𝓕 : Set (Set X)) : unitInterval := by
  classical
  exact if h : ∃ p, (ProbabilityTheory.setBernoulli Set.univ p).real (𝓕 : Set (Set X)) = 2⁻¹ then Classical.choose h else 0
noncomputable def modelQF {X : Type*} [Fintype X] (𝓕 : Set (Set X)) : unitInterval :=
  sSup {p | modelWeaklySmall p 𝓕}
noncomputable def modelRank {X : Type*} (𝓕 : Set (Set X)) : ℕ :=
  ⨆ (A : 𝓕) (_ : IsMin A), (A : Set X).ncard
theorem finite_cover_duality_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j) (hc : ∀ j, 0 < c j)
    (hno : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, 1 ≤ ∑ j, A i j * x j) ∧ (∑ j, c j * x j) ≤ (1 / 2 : ℝ)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ j, (∑ i, w i * A i j) ≤ 2 * c j := by
  classical
  let e := (Fintype.equivFin ι).symm
  let f := (Fintype.equivFin κ).symm
  have hn : ¬ ∃ x : Fin (Fintype.card κ) → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, 1 ≤ ∑ j, A (e i) (f j) * x j) ∧
      (∑ j, c (f j) * x j) ≤ (1 / 2 : ℝ) := by
    rintro ⟨x, hx, hcov, hcost⟩
    apply hno
    refine ⟨fun j => x (f.symm j), fun j => hx _, ?_, ?_⟩
    · intro i
      rw [← f.sum_comp (fun j => A i j * x (f.symm j))]
      simpa using hcov (e.symm i)
    · rw [← f.sum_comp (fun j => c j * x (f.symm j))]
      simpa using hcost
  obtain ⟨w, hw, hsum, hcone⟩ := finite_cover_duality _ _
    (fun i j => A (e i) (f j)) (fun j => c (f j))
    (fun i j => hA _ _) (fun j => hc _) hn
  refine ⟨fun i => w (e.symm i), fun i => hw _, ?_, ?_⟩
  · rw [← e.sum_comp (fun i => w (e.symm i))]
    simpa using hsum
  · intro j
    rw [← e.sum_comp (fun i => w (e.symm i) * A i j)]
    simpa using hcone (f.symm j)
theorem model_minimal_below {X : Type*} [Finite X] (𝓕 : Set (Set X))
    (T : 𝓕) : ∃ A : 𝓕, IsMin A ∧ (A : Set X) ⊆ T := by
  classical
  obtain ⟨A, hAT, hmin⟩ := Finite.exists_le_minimal (p := fun _ : 𝓕 => True)
    (a := T) trivial
  exact ⟨A, fun B hBA => hmin.2 trivial hBA, hAT⟩
theorem model_minimal_card_le {X : Type*} [Fintype X] (𝓕 : Set (Set X))
    (A : 𝓕) (hA : IsMin A) : (A : Set X).ncard ≤ modelRank 𝓕 := by
  classical
  have hbound : ∀ B : 𝓕, (B : Set X).ncard ≤ Fintype.card X := by
    intro B
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using
      Set.ncard_le_ncard (Set.subset_univ (B : Set X))
  have hinner : ∀ B : 𝓕, (⨆ (_ : IsMin B), (B : Set X).ncard) ≤ Fintype.card X :=
    fun B => ciSup_le' (fun _ => hbound B)
  apply le_ciSup_of_le (f := fun B : 𝓕 => ⨆ (_ : IsMin B), (B : Set X).ncard)
    ⟨Fintype.card X, by rintro _ ⟨B, rfl⟩; exact hinner B⟩ A
  exact le_ciSup (f := fun _ : IsMin A => (A : Set X).ncard)
    ⟨(A : Set X).ncard, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩ hA
theorem model_measure_sum (n : ℕ) (p : unitInterval) (𝓕 : Set (Set (Fin n))) :
    (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 =
      ∑ W : Finset (Fin n), @ite ℝ ((W : Set (Fin n)) ∈ 𝓕) (Classical.propDecidable _)
        ((p : ℝ) ^ W.card * (1 - (p : ℝ)) ^ (n - W.card)) 0 := by
  classical
  let e : Finset (Fin n) ≃ Set (Fin n) :=
    { toFun := fun W => (W : Set (Fin n))
      invFun := fun S => S.toFinset
      left_inv := by intro W; simp
      right_inv := by intro W; simp }
  have hs := MeasureTheory.sum_measureReal_singleton
    (μ := ProbabilityTheory.setBernoulli Set.univ p) 𝓕.toFinset
  have hs' : (∑ b ∈ 𝓕.toFinset, (ProbabilityTheory.setBernoulli Set.univ p).real {b}) =
      (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 := by simpa using hs
  rw [← hs', ← Fintype.sum_extend_by_zero]
  rw [← e.sum_comp (fun W => if W ∈ 𝓕.toFinset then
    (ProbabilityTheory.setBernoulli Set.univ p).real {W} else 0)]
  apply Finset.sum_congr rfl
  intro W _
  simp only [e, Equiv.coe_fn_mk, Set.mem_toFinset]
  congr 1
  rw [ProbabilityTheory.setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _), Set.ncard_univ, Set.ncard_coe_finset]
  simp
theorem model_not_small_one {X : Type*} [Fintype X] (𝓕 : Set (Set X))
    (h𝓕 : 𝓕.Nonempty) : ¬ modelWeaklySmall 1 𝓕 := by
  classical
  rintro ⟨g, hcov, hcost⟩
  obtain ⟨T, hT⟩ := h𝓕
  have hh := hcov T hT
  have hle : (∑ S with S ⊆ T, g S) ≤ ∑ S, g S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
  have hle' : (1 : ℝ) ≤ ∑ S, (g S : ℝ) := by
    exact_mod_cast hh.trans hle
  change (∑ S, (g S : ℝ) * (1 : ℝ) ^ S.ncard) ≤ _ at hcost
  simp only [one_pow, mul_one] at hcost
  norm_num at hcost
  linarith
theorem model_dual_spread (n : ℕ) (𝓕 : Set (Set (Fin n)))
    (hempty : ∅ ∉ 𝓕) (q : unitInterval) (hq : 0 < (q : ℝ))
    (hno : ¬ modelWeaklySmall q 𝓕) :
    ∃ ν : Finset (Fin n) → ℝ, (∀ A, 0 ≤ ν A) ∧ (∑ A, ν A) = 1 ∧
      (∀ A, ν A ≠ 0 → 1 ≤ A.card ∧ A.card ≤ modelRank 𝓕) ∧
      (∀ A, ν A ≠ 0 → (A : Set (Fin n)) ∈ 𝓕) ∧
      ∀ S : Finset (Fin n),
        (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤
          (2 * (q : ℝ)) ^ S.card := by
  classical
  let M := {A : 𝓕 // IsMin A}
  let coeff : M → Set (Fin n) → ℝ := fun A S => if S ⊆ A.1.1 then 1 else 0
  have hn : ¬ ∃ x : Set (Fin n) → ℝ, (∀ S, 0 ≤ x S) ∧
      (∀ A, 1 ≤ ∑ S, coeff A S * x S) ∧
      (∑ S, (q : ℝ) ^ S.ncard * x S) ≤ (1 / 2 : ℝ) := by
    rintro ⟨x, hx, hcov, hcost⟩
    apply hno
    refine ⟨fun S => NNReal.mk (x S) (hx S), ?_, ?_⟩
    · intro T hT
      obtain ⟨A, hA, hAT⟩ := model_minimal_below 𝓕 ⟨T, hT⟩
      have hrow : 1 ≤ ∑ S with S ⊆ (A : Set (Fin n)), x S := by
        simpa [coeff, Finset.sum_filter] using hcov (⟨A, hA⟩ : M)
      have hsub : (Finset.univ.filter (fun S : Set (Fin n) => S ⊆ A)) ⊆
          Finset.univ.filter (fun S : Set (Fin n) => S ⊆ T) := by
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        exact hS.trans hAT
      have hreal := hrow.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun S _ _ => hx S))
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_one, NNReal.coe_sum]
      exact hreal
    · change (∑ S, x S * (q : ℝ) ^ S.ncard) ≤ 2⁻¹
      simpa [mul_comm, one_div] using hcost
  obtain ⟨w, hw, hmass, hcone⟩ := finite_cover_duality_fintype coeff
    (fun S => (q : ℝ) ^ S.ncard)
    (by intro A S; dsimp [coeff]; split_ifs <;> norm_num)
    (fun S => pow_pos hq _) hn
  let edge : M → Finset (Fin n) := fun A => A.1.1.toFinset
  let ν := paddingPush w edge
  have hν : ∀ A, 0 ≤ ν A := paddingPush_nonneg w edge hw
  have htotal : (∑ A, ν A) = 1 := by
    have hh : (∑ A, ν A) = ∑ A, w A := by
      simpa only [mul_one] using paddingPush_eval w edge (fun _ => 1)
    exact hh.trans hmass
  have hmem : ∀ A, ν A ≠ 0 → (A : Set (Fin n)) ∈ 𝓕 := by
    apply paddingPush_support w edge
    intro A _
    simpa [edge] using A.1.2
  have hsize : ∀ A, ν A ≠ 0 → 1 ≤ A.card ∧ A.card ≤ modelRank 𝓕 := by
    apply paddingPush_support w edge
    intro A _
    have hpos : 1 ≤ (edge A).card := by
      apply Finset.card_pos.mpr
      by_contra he
      have hz : edge A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      have hset : A.1.1 = ∅ := by simpa [edge] using congrArg (fun S : Finset (Fin n) => (S : Set (Fin n))) hz
      exact hempty (hset ▸ A.1.2)
    refine ⟨hpos, ?_⟩
    rw [← Set.ncard_coe_finset]
    simpa only [edge, Set.coe_toFinset] using model_minimal_card_le 𝓕 A.1 A.2
  refine ⟨ν, hν, htotal, hsize, hmem, ?_⟩
  intro S
  by_cases hS : S = ∅
  · subst S
    simp [htotal]
  · have hSpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have hconesum : (∑ A, if S ⊆ A then ν A else 0) =
        ∑ A : M, w A * coeff A (S : Set (Fin n)) := by
      have hh := paddingPush_eval w edge (fun A => if S ⊆ A then (1 : ℝ) else 0)
      simpa only [mul_ite, mul_one, mul_zero, coeff, edge,
        Set.subset_toFinset] using hh
    rw [hconesum]
    calc
      _ ≤ 2 * (q : ℝ) ^ (S : Set (Fin n)).ncard := hcone _
      _ = 2 * (q : ℝ) ^ S.card := by rw [Set.ncard_coe_finset]
      _ ≤ (2 * (q : ℝ)) ^ S.card := by
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq.le _)
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hSpos)
theorem threshold_reduction (C : ℝ) (hC : 0 < C)
    (hsampling : ∀ (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ),
      2 ≤ r → (∀ A, 0 ≤ ν A) → (∑ A : Finset (Fin n), ν A) = 1 →
      (∀ A, ν A ≠ 0 → 1 ≤ A.card ∧ A.card ≤ r) →
      0 ≤ b → (∀ S : Finset (Fin n),
        (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card) →
      0 < p → p ≤ 1 → C * b * Real.log r ≤ p →
      (3 / 4 : ℝ) ≤ ∑ W : Finset (Fin n),
        @ite ℝ (∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W)
          (Classical.propDecidable _) (p ^ W.card * (1 - p) ^ (n - W.card)) 0)
    (n : ℕ) (𝓕 : Set (Set (Fin n))) (h𝓕 : IsUpperSet 𝓕)
    (hr : 2 ≤ modelRank 𝓕) :
    (modelPC 𝓕 : ℝ) ≤ (2 * C) * (modelQF 𝓕 : ℝ) * Real.log (modelRank 𝓕) := by
  classical
  by_contra hgoal
  have hlt := lt_of_not_ge hgoal
  have hlog : 0 < Real.log (modelRank 𝓕) :=
    Real.log_pos (by exact_mod_cast (show 1 < modelRank 𝓕 by omega))
  have hpc : 0 < (modelPC 𝓕 : ℝ) := lt_of_le_of_lt
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * C) (modelQF 𝓕).2.1) hlog.le) hlt
  have hex : ∃ p, (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 = (2 : ℝ)⁻¹ := by
    by_contra h
    have hz : modelPC 𝓕 = 0 := by simp only [modelPC, dif_neg h]
    rw [hz] at hpc
    norm_num at hpc
  have hroot : (ProbabilityTheory.setBernoulli Set.univ (modelPC 𝓕)).real 𝓕 = (2 : ℝ)⁻¹ := by
    simpa only [modelPC, dif_pos hex] using Classical.choose_spec hex
  have hnonempty : 𝓕.Nonempty := MeasureTheory.nonempty_of_measureReal_ne_zero
    (by rw [hroot]; norm_num)
  have hempty : ∅ ∉ 𝓕 := by
    intro he
    have heq : 𝓕 = Set.univ := Set.eq_univ_of_forall (fun T => h𝓕 (Set.empty_subset T) he)
    rw [heq, MeasureTheory.probReal_univ] at hroot
    norm_num at hroot
  let D := 2 * C * Real.log (modelRank 𝓕)
  have hD : 0 < D := by dsimp [D]; positivity
  have hltD : D * (modelQF 𝓕 : ℝ) < (modelPC 𝓕 : ℝ) := by
    dsimp [D]
    nlinarith only [hlt]
  have hq : ∃ q : unitInterval, 0 < (q : ℝ) ∧ ¬ modelWeaklySmall q 𝓕 ∧
      C * (2 * (q : ℝ)) * Real.log (modelRank 𝓕) ≤ (modelPC 𝓕 : ℝ) := by
    by_cases hq1 : modelQF 𝓕 = 1
    · refine ⟨1, by norm_num, model_not_small_one 𝓕 hnonempty, ?_⟩
      rw [hq1] at hltD
      change D * 1 < (modelPC 𝓕 : ℝ) at hltD
      dsimp [D] at hltD
      change C * (2 * (1 : ℝ)) * Real.log (modelRank 𝓕) ≤ (modelPC 𝓕 : ℝ)
      nlinarith only [hltD]
    · have hqf1 : (modelQF 𝓕 : ℝ) < 1 := by
        by_contra hh
        apply hq1
        apply Subtype.ext
        exact le_antisymm (modelQF 𝓕).2.2 (le_of_not_gt hh)
      have hratio : (modelQF 𝓕 : ℝ) < (modelPC 𝓕 : ℝ) / D :=
        (lt_div_iff₀ hD).mpr (by nlinarith only [hltD])
      obtain ⟨t, hqt, ht⟩ := exists_between (lt_min hqf1 hratio)
      have htpos : 0 < t := lt_of_le_of_lt (modelQF 𝓕).2.1 hqt
      let q : unitInterval := ⟨t, htpos.le, (lt_min_iff.mp ht).1.le⟩
      refine ⟨q, htpos, ?_, ?_⟩
      · intro hsmall
        have hle : q ≤ modelQF 𝓕 := le_sSup hsmall
        exact (not_le_of_gt hqt) hle
      · have hh := (lt_div_iff₀ hD).mp (lt_min_iff.mp ht).2
        change C * (2 * t) * Real.log (modelRank 𝓕) ≤ (modelPC 𝓕 : ℝ)
        dsimp [D] at hh
        nlinarith only [hh]
  obtain ⟨q, hqpos, hqno, hqcost⟩ := hq
  obtain ⟨ν, hν, hmass, hsize, hmem, hspread⟩ := model_dual_spread n 𝓕 hempty q hqpos hqno
  have hsample := hsampling n (modelRank 𝓕) ν (2 * (q : ℝ)) (modelPC 𝓕)
    hr hν hmass hsize (by positivity) hspread hpc (modelPC 𝓕).2.2 hqcost
  have hle : (∑ W : Finset (Fin n),
      @ite ℝ (∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W) (Classical.propDecidable _)
        ((modelPC 𝓕 : ℝ) ^ W.card * (1 - (modelPC 𝓕 : ℝ)) ^ (n - W.card)) 0) ≤
      (ProbabilityTheory.setBernoulli Set.univ (modelPC 𝓕)).real 𝓕 := by
    rw [model_measure_sum]
    apply Finset.sum_le_sum
    intro W _
    by_cases he : ∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W
    · obtain ⟨A, hA, hAW⟩ := he
      have hW : (W : Set (Fin n)) ∈ 𝓕 := h𝓕 (Finset.coe_subset.mpr hAW) (hmem A hA)
      have hE : ∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W := ⟨A, hA, hAW⟩
      simp only [if_pos hE, if_pos hW, le_refl]
    · simp only [if_neg he]
      split_ifs
      · exact mul_nonneg (pow_nonneg (modelPC 𝓕).2.1 _)
          (pow_nonneg (sub_nonneg.mpr (modelPC 𝓕).2.2) _)
      · exact le_rfl
  rw [hroot] at hle
  have hbad : (3 / 4 : ℝ) ≤ 2⁻¹ := hsample.trans hle
  norm_num at hbad
theorem bernoulli_projection_fiber (n N : ℕ) (e : Fin n ↪ Fin N) (p : ℝ)
    (A : Finset (Fin n)) :
    (∑ W : Finset (Fin N), if paddingPull e W = A then fragmentWeight N p W else 0) =
      fragmentWeight n p A := by
  classical
  let E : Finset (Fin N) := Finset.univ.map e
  have hmap : A.map e ⊆ E := Finset.map_subset_map.mpr (Finset.subset_univ A)
  have hcond (W : Finset (Fin N)) :
      paddingPull e W = A ↔ Eᶜ ∪ W = Eᶜ ∪ A.map e := by
    constructor
    · intro h
      ext y
      by_cases hy : y ∈ E
      · obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hy
        have hx : e x ∈ W ↔ x ∈ A := by
          rw [← paddingPull_mem e W x, h]
        simpa [E] using hx
      · simp [hy]
    · intro h
      ext x
      have hx := Finset.ext_iff.mp h (e x)
      simpa [E, paddingPull_mem] using hx
  have hcardE : E.card = n := by simp [E]
  have hcA : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hcN : n ≤ N := by simpa using Fintype.card_le_of_injective e e.injective
  have hdisj : Disjoint Eᶜ (A.map e) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxA
    exact (Finset.mem_compl.mp hx) (hmap hxA)
  have hcardU : (Eᶜ ∪ A.map e).card = N - n + A.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_compl, hcardE,
      Finset.card_map, Fintype.card_fin]
  simp only [hcond, fragmentWeight]
  rw [bernoulli_union_fiber, ite_eq_left Finset.subset_union_left, hcardU,
    Finset.card_compl, Fintype.card_fin, hcardE]
  rw [show N - n + A.card - (N - n) = A.card by omega,
    show N - (N - n + A.card) = n - A.card by omega]
theorem bernoulli_projection_expectation (n N : ℕ) (e : Fin n ↪ Fin N) (p : ℝ)
    (g : Finset (Fin n) → ℝ) :
    (∑ W : Finset (Fin N), fragmentWeight N p W * g (paddingPull e W)) =
      ∑ A : Finset (Fin n), fragmentWeight n p A * g A := by
  classical
  calc
    _ = ∑ A : Finset (Fin n),
        (∑ W : Finset (Fin N), if paddingPull e W = A then fragmentWeight N p W else 0) * g A := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W _
      simp
    _ = _ := by simp only [bernoulli_projection_fiber]
noncomputable def samplingHit {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (W : Finset (Fin n)) : ℝ :=
  if ∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W then 1 else 0
noncomputable def samplingProb {n : ℕ} (ν : Finset (Fin n) → ℝ) (p : ℝ) : ℝ :=
  ∑ W : Finset (Fin n), fragmentWeight n p W * samplingHit ν W
theorem samplingHit_mono {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) : samplingHit ν A ≤ samplingHit ν B := by
  classical
  by_cases hA : ∃ T : Finset (Fin n), ν T ≠ 0 ∧ T ⊆ A
  · obtain ⟨T, hT, hTA⟩ := hA
    have hB : ∃ T : Finset (Fin n), ν T ≠ 0 ∧ T ⊆ B := ⟨T, hT, hTA.trans hAB⟩
    simp [samplingHit, hB, show ∃ T, ν T ≠ 0 ∧ T ⊆ A from ⟨T, hT, hTA⟩]
  · simp only [samplingHit, ite_eq_right hA]
    split_ifs <;> norm_num
theorem samplingProb_mono {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (p t : ℝ) (hp : 0 ≤ p) (hpt : p ≤ t) (ht : t ≤ 1) :
    samplingProb ν p ≤ samplingProb ν t :=
  bernoulli_expectation_mono n p t (samplingHit ν) hp hpt ht (samplingHit_mono ν)
theorem sampling_projection_le (n N : ℕ) (e : Fin n ↪ Fin N)
    (ν : Finset (Fin n) → ℝ) (w : Finset (Fin N) → ℝ)
    (hw : ∀ B, 0 ≤ w B)
    (hfiber : ∀ A : Finset (Fin n),
      (∑ B : Finset (Fin N), if (∀ x : Fin n, e x ∈ B ↔ x ∈ A) then w B else 0) = ν A)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    samplingProb w p ≤ samplingProb ν p := by
  classical
  have hsupport (B : Finset (Fin N)) (hB : w B ≠ 0) : ν (paddingPull e B) ≠ 0 := by
    have hcond (D : Finset (Fin N)) :
        (∀ x : Fin n, e x ∈ D ↔ x ∈ paddingPull e B) ↔ paddingPull e D = paddingPull e B := by
      simp only [Finset.ext_iff, paddingPull_mem]
    have hh := hfiber (paddingPull e B)
    simp only [hcond] at hh
    have hle : w B ≤ ν (paddingPull e B) := by
      rw [← hh]
      calc
        w B = (if paddingPull e B = paddingPull e B then w B else 0) := by simp
        _ ≤ ∑ D : Finset (Fin N), if paddingPull e D = paddingPull e B then w D else 0 :=
          Finset.single_le_sum
            (f := fun D : Finset (Fin N) => if paddingPull e D = paddingPull e B then w D else 0)
            (fun D _ => by split_ifs; exact hw D; exact le_rfl) (Finset.mem_univ B)
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hw B) (Ne.symm hB)) hle)
  have hhit (W : Finset (Fin N)) : samplingHit w W ≤ samplingHit ν (paddingPull e W) := by
    by_cases hW : ∃ B : Finset (Fin N), w B ≠ 0 ∧ B ⊆ W
    · obtain ⟨B, hB, hBW⟩ := hW
      have hW' : ∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ paddingPull e W := by
        refine ⟨paddingPull e B, hsupport B hB, ?_⟩
        intro x hx
        exact (paddingPull_mem e W x).mpr (hBW ((paddingPull_mem e B x).mp hx))
      simp [samplingHit, hW', show ∃ B, w B ≠ 0 ∧ B ⊆ W from ⟨B, hB, hBW⟩]
    · simp only [samplingHit, ite_eq_right hW]
      split_ifs <;> norm_num
  calc
    samplingProb w p ≤ ∑ W : Finset (Fin N), fragmentWeight N p W *
        samplingHit ν (paddingPull e W) := by
      apply Finset.sum_le_sum
      intro W _
      exact mul_le_mul_of_nonneg_left (hhit W) (fragmentWeight_nonneg N p hp hp1 W)
    _ = samplingProb ν p := bernoulli_projection_expectation n N e p (samplingHit ν)
def samplingRound (p : ℝ) (k : ℕ) : ℝ := 1 - (1 - p) ^ k
noncomputable def samplingError (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, ((64 : ℝ) ^ (j + 1))⁻¹
theorem samplingError_mono {r s : ℕ} (hrs : r ≤ s) : samplingError r ≤ samplingError s := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrs)
  intros
  positivity
theorem samplingError_step (r : ℕ) (hr : 1 ≤ r) :
    samplingError (r / 2) + ((64 : ℝ) ^ r)⁻¹ ≤ samplingError r := by
  have hh := samplingError_mono (show r / 2 ≤ r - 1 by omega)
  have heq : samplingError r = samplingError (r - 1) + ((64 : ℝ) ^ r)⁻¹ := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    simp only [samplingError, Finset.sum_range_succ]
    rw [Nat.sub_add_cancel hr]
  linarith
theorem samplingError_eq (r : ℕ) :
    samplingError r = (1 - ((64 : ℝ) ^ r)⁻¹) / 63 := by
  induction r with
  | zero => simp [samplingError]
  | succ r ih =>
    rw [samplingError, Finset.sum_range_succ]
    change samplingError r + ((64 : ℝ) ^ (r + 1))⁻¹ = _
    rw [ih, pow_succ]
    field_simp
    <;> ring
theorem samplingError_le (r : ℕ) : samplingError r ≤ 1 / 63 := by
  rw [samplingError_eq]
  have h : 0 ≤ ((64 : ℝ) ^ r)⁻¹ := by positivity
  linarith
theorem samplingRound_mem (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ samplingRound p k ∧ samplingRound p k ≤ 1 := by
  have h0 : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) _
  have h1 : (1 - p) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  constructor <;> dsimp [samplingRound] <;> linarith
theorem samplingRound_succ (p : ℝ) (k : ℕ) :
    p + samplingRound p k - p * samplingRound p k = samplingRound p (k + 1) := by
  simp only [samplingRound, pow_succ]
  ring
theorem samplingProb_nonneg {n : ℕ} (ν : Finset (Fin n) → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ samplingProb ν p := by
  classical
  apply Finset.sum_nonneg
  intro W _
  apply mul_nonneg (fragmentWeight_nonneg n p hp hp1 W)
  dsimp [samplingHit]
  split_ifs <;> norm_num
theorem sampling_zero_rank (n : ℕ) (ν : Finset (Fin n) → ℝ)
    (hmass : (∑ A : Finset (Fin n), ν A) ≤ 1)
    (hcard : ∀ A, ν A ≠ 0 → A.card ≤ 0)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ A : Finset (Fin n), ν A) ≤ samplingProb ν p := by
  classical
  have hsum : (∑ A : Finset (Fin n), ν A) = ν ∅ := by
    apply Finset.sum_eq_single ∅
    · intro A _ hA
      by_contra hνA
      exact hA (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hcard A hνA)))
    · simp
  by_cases hz : ν ∅ = 0
  · rw [hsum, hz]
    exact samplingProb_nonneg ν p hp hp1
  · have hhit (W : Finset (Fin n)) : samplingHit ν W = 1 := by
      exact ite_eq_left ⟨∅, hz, Finset.empty_subset W⟩
    have hprob : samplingProb ν p = 1 := by
      simp only [samplingProb, hhit, mul_one, fragmentWeight]
      exact bernoulli_finset_normalization n p
    rw [hprob]
    exact hmass
theorem sampling_witness_le {n : ℕ} (ν μ : Finset (Fin n) → ℝ)
    (hμ : ∀ T, 0 ≤ μ T) (W V : Finset (Fin n))
    (hwit : ∀ T, 0 < μ T → ∃ B : Finset (Fin n), 0 < ν B ∧ B ⊆ T ∪ W) :
    samplingHit μ V ≤ samplingHit ν (W ∪ V) := by
  classical
  by_cases hV : ∃ T : Finset (Fin n), μ T ≠ 0 ∧ T ⊆ V
  · obtain ⟨T, hT, hTV⟩ := hV
    obtain ⟨B, hB, hBT⟩ := hwit T (lt_of_le_of_ne (hμ T) (Ne.symm hT))
    have hWV : ∃ B : Finset (Fin n), ν B ≠ 0 ∧ B ⊆ W ∪ V := by
      refine ⟨B, ne_of_gt hB, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hBT hx) with hxT | hxW
      · exact Finset.mem_union_right W (hTV hxT)
      · exact Finset.mem_union_left V hxW
    simp [samplingHit, hWV, show ∃ T, μ T ≠ 0 ∧ T ⊆ V from ⟨T, hT, hTV⟩]
  · simp only [samplingHit, ite_eq_right hV]
    split_ifs <;> norm_num
theorem sampling_uniform_step (n r k : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ)
    (hr : 1 ≤ r) (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A : Finset (Fin n), ν A) ≤ 1)
    (huniform : ∀ A, ν A ≠ 0 → A.card = r) (hb : 0 ≤ b)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card)
    (hp : 0 < p) (hp1 : p ≤ 1) (hbp : (2 : ℝ) ^ 32 * b ≤ p)
    (hind : ∀ μ : Finset (Fin n) → ℝ, (∀ T, 0 ≤ μ T) →
      (∑ T : Finset (Fin n), μ T) ≤ 1 → (∀ T, μ T ≠ 0 → T.card ≤ r / 2) →
      (∀ S : Finset (Fin n), (∑ T : Finset (Fin n), if S ⊆ T then μ T else 0) ≤ b ^ S.card) →
      (∑ T : Finset (Fin n), μ T) - samplingError (r / 2) ≤ samplingProb μ (samplingRound p k)) :
    (∑ A : Finset (Fin n), ν A) - samplingError r ≤
      samplingProb ν (samplingRound p (k + 1)) := by
  classical
  obtain ⟨μ, hμ, hcard, hmassμ, hspreadμ, hwit, hloss⟩ :=
    fragment_update n r ν b p hr hν hmass huniform hb hspread hp hp1 hbp
  have hs := samplingRound_mem p hp.le hp1 k
  have hnorm : (∑ W : Finset (Fin n), fragmentWeight n p W) = 1 :=
    bernoulli_finset_normalization n p
  have hW (W : Finset (Fin n)) :
      (∑ T : Finset (Fin n), μ W T) - samplingError (r / 2) ≤
        ∑ V : Finset (Fin n), fragmentWeight n (samplingRound p k) V * samplingHit ν (W ∪ V) := by
    apply (hind (μ W) (hμ W) ((hmassμ W).trans hmass) (hcard W) (hspreadμ W)).trans
    apply Finset.sum_le_sum
    intro V _
    exact mul_le_mul_of_nonneg_left (sampling_witness_le ν (μ W) (hμ W) W V (hwit W))
      (fragmentWeight_nonneg n (samplingRound p k) hs.1 hs.2 V)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun W _ => mul_le_mul_of_nonneg_left (hW W) (fragmentWeight_nonneg n p hp.le hp1 W))
  change (∑ W : Finset (Fin n), fragmentWeight n p W *
    ((∑ A : Finset (Fin n), ν A) - ∑ T : Finset (Fin n), μ W T)) ≤ _ at hloss
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hnorm, one_mul] at hsum hloss
  have herr := samplingError_step r hr
  calc
    (∑ A : Finset (Fin n), ν A) - samplingError r ≤
        ∑ W : Finset (Fin n), fragmentWeight n p W *
          ∑ V : Finset (Fin n), fragmentWeight n (samplingRound p k) V * samplingHit ν (W ∪ V) := by
      linarith
    _ = samplingProb ν (samplingRound p (k + 1)) := by
      simp only [fragmentWeight]
      rw [bernoulli_union_convolution, samplingRound_succ]
      rfl
theorem sampling_iterate (k : ℕ) :
    ∀ (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ), r < 2 ^ k →
      (∀ A, 0 ≤ ν A) → (∑ A : Finset (Fin n), ν A) ≤ 1 →
      (∀ A, ν A ≠ 0 → A.card ≤ r) → 0 < b →
      (∀ S : Finset (Fin n), (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card) →
      0 < p → p ≤ 1 → (2 : ℝ) ^ 32 * b ≤ p →
      (∑ A : Finset (Fin n), ν A) - samplingError r ≤ samplingProb ν (samplingRound p k) := by
  classical
  induction k with
  | zero =>
    intro n r ν b p hr hν hmass hcard hb hspread hp hp1 hbp
    have hr0 : r = 0 := by norm_num at hr; omega
    subst r
    have hs := samplingRound_mem p hp.le hp1 0
    simpa [samplingError] using sampling_zero_rank n ν hmass hcard (samplingRound p 0) hs.1 hs.2
  | succ k ih =>
    intro n r ν b p hr hν hmass hcard hb hspread hp hp1 hbp
    have hs := samplingRound_mem p hp.le hp1 (k + 1)
    by_cases hr0 : r = 0
    · subst r
      simpa [samplingError] using sampling_zero_rank n ν hmass hcard (samplingRound p (k + 1)) hs.1 hs.2
    have hr1 : 1 ≤ r := by omega
    have hhalf : r / 2 < 2 ^ k := by
      rw [pow_succ] at hr
      omega
    obtain ⟨N, e, w, hw, hwcard, hwmass, hwspread, hwfiber⟩ :=
      spread_padding n r ν b hb hν hmass hcard hspread
    have hstep := sampling_uniform_step N r k w b p hr1 hw (hwmass.trans_le hmass)
      hwcard hb.le hwspread hp hp1 hbp
      (fun μ hμ hmassμ hcardμ hspreadμ =>
        ih N (r / 2) μ b p hhalf hμ hmassμ hcardμ hb hspreadμ hp hp1 hbp)
    calc
      (∑ A : Finset (Fin n), ν A) - samplingError r =
          (∑ B : Finset (Fin N), w B) - samplingError r := by rw [hwmass]
      _ ≤ samplingProb w (samplingRound p (k + 1)) := hstep
      _ ≤ samplingProb ν (samplingRound p (k + 1)) :=
        sampling_projection_le n N e ν w hw hwfiber _ hs.1 hs.2
theorem samplingRound_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    samplingRound p k ≤ (k : ℝ) * p := by
  induction k with
  | zero => simp [samplingRound]
  | succ k ih =>
    have hs := samplingRound_mem p hp hp1 k
    rw [← samplingRound_succ]
    calc
      p + samplingRound p k - p * samplingRound p k ≤ p + samplingRound p k := by
        nlinarith [mul_nonneg hp hs.1]
      _ ≤ p + (k : ℝ) * p := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * p := by push_cast; ring
theorem sampling_log_rounds (r : ℕ) (hr : 2 ≤ r) :
    ((Nat.log 2 r + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hnat := Nat.pow_log_le_self 2 (show r ≠ 0 by omega)
  have hreal : (2 : ℝ) ^ Nat.log 2 r ≤ (r : ℝ) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 r) hreal
  rw [Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ Real.log r :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hr)
  push_cast
  nlinarith
theorem sampling_spread_pos (n : ℕ) (ν : Finset (Fin n) → ℝ) (b : ℝ)
    (hν : ∀ A, 0 ≤ ν A) (hmass : (∑ A : Finset (Fin n), ν A) = 1)
    (hcard : ∀ A, ν A ≠ 0 → 1 ≤ A.card)
    (hspread : ∀ S : Finset (Fin n),
      (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card) : 0 < b := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), ν A ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hmass
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < A.card by have := hcard A hA; omega)
  have hcone : ν A ≤ ∑ B : Finset (Fin n), if {x} ⊆ B then ν B else 0 := by
    calc
      ν A = (if {x} ⊆ A then ν A else 0) := by simp [Finset.singleton_subset_iff, hx]
      _ ≤ ∑ B : Finset (Fin n), if {x} ⊆ B then ν B else 0 :=
        Finset.single_le_sum
          (f := fun B : Finset (Fin n) => if {x} ⊆ B then ν B else 0)
          (fun B _ => by split_ifs; exact hν B; exact le_rfl) (Finset.mem_univ A)
  have hh := hcone.trans (hspread {x})
  simp only [Finset.card_singleton, pow_one] at hh
  exact lt_of_lt_of_le (lt_of_le_of_ne (hν A) (Ne.symm hA)) hh
theorem spread_sampling :
    ∃ C : ℝ, 0 < C ∧ ∀ (n r : ℕ) (ν : Finset (Fin n) → ℝ) (b p : ℝ),
      2 ≤ r → (∀ A, 0 ≤ ν A) → (∑ A : Finset (Fin n), ν A) = 1 →
      (∀ A, ν A ≠ 0 → 1 ≤ A.card ∧ A.card ≤ r) → 0 ≤ b →
      (∀ S : Finset (Fin n),
        (∑ A : Finset (Fin n), if S ⊆ A then ν A else 0) ≤ b ^ S.card) →
      0 < p → p ≤ 1 → C * b * Real.log r ≤ p →
      (3 / 4 : ℝ) ≤ ∑ W : Finset (Fin n),
        @ite ℝ (∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W) (Classical.propDecidable _)
          (p ^ W.card * (1 - p) ^ (n - W.card)) 0 := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (2 : ℝ) ^ 33 / Real.log 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n r ν b p hr hν hmass hcard hb hspread hp hp1 hbound
  have hbpos : 0 < b := sampling_spread_pos n ν b hν hmass
    (fun A hA => (hcard A hA).1) hspread
  let k : ℕ := Nat.log 2 r + 1
  let u : ℝ := (2 : ℝ) ^ 32 * b
  have hu : 0 < u := by dsimp [u]; positivity
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hklog : (k : ℝ) ≤ 2 * Real.log r / Real.log 2 :=
    (le_div_iff₀ hl2).mpr (sampling_log_rounds r hr)
  have hbudget : (k : ℝ) * u ≤ p := by
    calc
      (k : ℝ) * u ≤ (2 * Real.log r / Real.log 2) * u :=
        mul_le_mul_of_nonneg_right hklog hu.le
      _ = C * b * Real.log r := by dsimp [C, u]; norm_num; ring
      _ ≤ p := hbound
  have hu1 : u ≤ 1 := by
    have hule : u ≤ (k : ℝ) * u := by nlinarith
    exact hule.trans (hbudget.trans hp1)
  have hiter := sampling_iterate k n r ν b u
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r) hν hmass.le
    (fun A hA => (hcard A hA).2) hbpos hspread hu hu1 le_rfl
  have herr := samplingError_le r
  have hround := samplingRound_mem u hu.le hu1 k
  have hroundle : samplingRound u k ≤ p := (samplingRound_le u hu.le hu1 k).trans hbudget
  have hmono := samplingProb_mono ν (samplingRound u k) p hround.1 hroundle hp1
  have hprob : (3 / 4 : ℝ) ≤ samplingProb ν p := by rw [hmass] at hiter; linarith
  convert hprob using 1
  unfold samplingProb
  apply Finset.sum_congr rfl
  intro W _
  by_cases hW : ∃ A : Finset (Fin n), ν A ≠ 0 ∧ A ⊆ W <;>
    simp [samplingHit, fragmentWeight, hW]
theorem finite_threshold_bound_exists :
    ∃ C : ℝ, ∀ (n : ℕ) (𝓕 : Set (Set (Fin n))), IsUpperSet 𝓕 →
      2 ≤ modelRank 𝓕 →
      (modelPC 𝓕 : ℝ) ≤ C * (modelQF 𝓕 : ℝ) * Real.log (modelRank 𝓕) := by
  obtain ⟨C, hC, hsampling⟩ := spread_sampling
  exact ⟨2 * C, threshold_reduction C hC hsampling⟩
theorem model_set_ncard_equiv {X Y : Type*} (e : X ≃ Y) (S : Set X) :
    (e '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S e.injective
theorem model_relabel_small_of {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : unitInterval) (𝓕 : Set (Set X))
    (h : modelWeaklySmall p (e.setCongr '' 𝓕)) : modelWeaklySmall p 𝓕 := by
  classical
  obtain ⟨g, hcov, hcost⟩ := h
  refine ⟨fun S => g (e '' S), ?_, ?_⟩
  · intro T hT
    have h := hcov (e '' T) ⟨T, hT, rfl⟩
    have hs : (∑ S with S ⊆ T, g (e '' S)) = ∑ S with S ⊆ e '' T, g S := by
      simp only [Finset.sum_filter]
      rw [← e.setCongr.sum_comp (fun S => if S ⊆ e '' T then g S else 0)]
      simp only [Equiv.setCongr_apply, e.image_subset]
    rw [hs]
    exact h
  · have hs : (∑ S : Set X, g (e '' S) * (p : ℝ) ^ S.ncard) =
        ∑ S : Set Y, g S * (p : ℝ) ^ S.ncard := by
      rw [← e.setCongr.sum_comp (fun S => g S * (p : ℝ) ^ S.ncard)]
      simp only [Equiv.setCongr_apply, model_set_ncard_equiv]
    rw [hs]
    exact hcost
theorem model_measure_set_sum {X : Type*} [Fintype X]
    (p : unitInterval) (𝓕 : Set (Set X)) :
    (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 =
      ∑ S : Set X, @ite ℝ (S ∈ 𝓕) (Classical.propDecidable _)
        ((p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (Fintype.card X - S.ncard)) 0 := by
  classical
  have hs := MeasureTheory.sum_measureReal_singleton
    (μ := ProbabilityTheory.setBernoulli Set.univ p) 𝓕.toFinset
  have hs' : (∑ S ∈ 𝓕.toFinset, (ProbabilityTheory.setBernoulli Set.univ p).real {S}) =
      (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 := by simpa using hs
  rw [← hs', ← Fintype.sum_extend_by_zero]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Set.mem_toFinset]
  congr 1
  rw [ProbabilityTheory.setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ,
    Set.ncard_sdiff' (Set.subset_univ _), Set.ncard_univ]
  simp
theorem model_relabel_cancel {X Y : Type*} (e : X ≃ Y) (𝓕 : Set (Set X)) :
    e.symm.setCongr '' (e.setCongr '' 𝓕) = 𝓕 := by
  change e.setCongr.symm '' (e.setCongr '' 𝓕) = 𝓕
  exact e.setCongr.symm_image_image 𝓕
theorem model_relabel_small_iff {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : unitInterval) (𝓕 : Set (Set X)) :
    modelWeaklySmall p (e.setCongr '' 𝓕) ↔ modelWeaklySmall p 𝓕 := by
  constructor
  · exact model_relabel_small_of e p 𝓕
  · intro h
    apply model_relabel_small_of e.symm p (e.setCongr '' 𝓕)
    rwa [model_relabel_cancel]
theorem model_relabel_QF {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (𝓕 : Set (Set X)) : modelQF (e.setCongr '' 𝓕) = modelQF 𝓕 := by
  unfold modelQF
  congr 1
  ext p
  exact model_relabel_small_iff e p 𝓕
theorem model_relabel_measure {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (p : unitInterval) (𝓕 : Set (Set X)) :
    (ProbabilityTheory.setBernoulli Set.univ p).real (e.setCongr '' 𝓕) =
      (ProbabilityTheory.setBernoulli Set.univ p).real 𝓕 := by
  classical
  rw [model_measure_set_sum, model_measure_set_sum,
    ← e.setCongr.sum_comp (fun S =>
      @ite ℝ (S ∈ e.setCongr '' 𝓕) (Classical.propDecidable _)
        ((p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (Fintype.card Y - S.ncard)) 0)]
  apply Finset.sum_congr rfl
  intro S _
  have hm : e.setCongr S ∈ e.setCongr '' 𝓕 ↔ S ∈ 𝓕 := by
    constructor
    · rintro ⟨T, hT, heq⟩
      exact e.setCongr.injective heq ▸ hT
    · intro hS
      exact ⟨S, hS, rfl⟩
  have hc : (e.setCongr S).ncard = S.ncard := model_set_ncard_equiv e S
  simp only [hm, hc, Fintype.card_congr e]
theorem model_relabel_PC {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (𝓕 : Set (Set X)) : modelPC (e.setCongr '' 𝓕) = modelPC 𝓕 := by
  classical
  unfold modelPC
  simp_rw [model_relabel_measure e]
theorem model_relabel_rank_le {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (𝓕 : Set (Set X)) : modelRank (e.setCongr '' 𝓕) ≤ modelRank 𝓕 := by
  classical
  apply ciSup_le'
  intro A
  apply ciSup_le'
  intro hA
  obtain ⟨B, hB, heq⟩ := A.property
  change e '' B = (A : Set Y) at heq
  have hmin : IsMin (⟨B, hB⟩ : 𝓕) := by
    intro D hDB
    let D' : e.setCongr '' 𝓕 := ⟨e '' (D : Set X), ⟨D, D.property, rfl⟩⟩
    have hDA : D' ≤ A := by
      change e '' (D : Set X) ⊆ (A : Set Y)
      rw [← heq]
      exact Set.image_mono hDB
    have hAD : A ≤ D' := hA hDA
    change B ⊆ (D : Set X)
    apply (e.image_subset B D).mp
    change e '' B ⊆ e '' (D : Set X)
    rw [heq]
    exact hAD
  change (A : Set Y).ncard ≤ modelRank 𝓕
  rw [← heq, model_set_ncard_equiv]
  exact model_minimal_card_le 𝓕 ⟨B, hB⟩ hmin
theorem model_relabel_rank {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (𝓕 : Set (Set X)) : modelRank (e.setCongr '' 𝓕) = modelRank 𝓕 := by
  apply le_antisymm (model_relabel_rank_le e 𝓕)
  have h := model_relabel_rank_le e.symm (e.setCongr '' 𝓕)
  rwa [model_relabel_cancel] at h
theorem model_relabel_upper {X Y : Type*} (e : X ≃ Y)
    (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕) : IsUpperSet (e.setCongr '' 𝓕) := by
  rintro S T hST ⟨A, hA, rfl⟩
  refine ⟨e.symm '' T, h𝓕 ?_ hA, ?_⟩
  · rw [← e.symm_image_image A]
    exact Set.image_mono hST
  · exact e.image_symm_image T
theorem finite_bound_transfer (C : ℝ)
    (hfinite : ∀ (n : ℕ) (𝓕 : Set (Set (Fin n))), IsUpperSet 𝓕 →
      2 ≤ modelRank 𝓕 → (modelPC 𝓕 : ℝ) ≤ C * (modelQF 𝓕 : ℝ) * Real.log (modelRank 𝓕))
    (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hr : 2 ≤ modelRank 𝓕) :
    (modelPC 𝓕 : ℝ) ≤ C * (modelQF 𝓕 : ℝ) * Real.log (modelRank 𝓕) := by
  classical
  let e := Fintype.equivFin X
  have hr' : 2 ≤ modelRank (e.setCongr '' 𝓕) := by rwa [model_relabel_rank]
  have h := hfinite (Fintype.card X) (e.setCongr '' 𝓕) (model_relabel_upper e 𝓕 h𝓕) hr'
  simpa only [model_relabel_PC, model_relabel_QF, model_relabel_rank] using h
end Submission.Helpers
