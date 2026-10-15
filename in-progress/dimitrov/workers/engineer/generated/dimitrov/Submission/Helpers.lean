import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.House
namespace Submission.Helpers

theorem house_gt_one {K : Type*} [Field K] [NumberField K] (α : K)
    (α_int : IsIntegral ℤ α) (α_ne_zero : α ≠ 0)
    (α_not_rootOfUnity : ¬ IsOfFinOrder α) : 1 < NumberField.house α := by
  by_contra h
  have hhouse : NumberField.house α ≤ 1 := le_of_not_gt h
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ α_ne_zero α_int
      (fun σ => (NumberField.norm_embedding_le_house α σ).trans hhouse)
  exact α_not_rootOfUnity (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)
theorem argument_card_pos {K : Type*} [Field K] [NumberField K] (α : K) :
    0 < (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card := by
  classical
  exact Finset.card_pos.mpr (Finset.univ_nonempty.image _)
noncomputable def radial_fekete_product {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖
noncomputable def radial_fekete_fiber {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖
noncomputable def radial_fekete_remainder {n : ℕ} (z : Fin n → ℂ) (i : Fin n) : ℝ :=
  ∏ k ∈ Finset.univ.erase i, ∏ j ∈ (Finset.univ.erase i).erase k, ‖z k - z j‖
theorem radial_fekete_product_factor {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    radial_fekete_product z =
      radial_fekete_remainder z i * radial_fekete_fiber z i ^ 2 := by
  classical
  unfold radial_fekete_product radial_fekete_remainder radial_fekete_fiber
  have hrow : ∀ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      (∏ j ∈ Finset.univ.erase k, ‖z k - z j‖) =
        (∏ j ∈ (Finset.univ.erase i).erase k, ‖z k - z j‖) * ‖z k - z i‖ := by
    intro k hk
    have hik : i ≠ k := ((Finset.mem_erase.mp hk).1).symm
    rw [← Finset.prod_erase_mul (Finset.univ.erase k)
      (fun j => ‖z k - z j‖) (a := i) (by simp [hik])]
    rw [Finset.erase_right_comm]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun k => ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖) (Finset.mem_univ i)]
  rw [Finset.prod_congr rfl hrow, Finset.prod_mul_distrib]
  have hrev : (∏ k ∈ Finset.univ.erase i, ‖z k - z i‖) =
      ∏ k ∈ Finset.univ.erase i, ‖z i - z k‖ := by
    apply Finset.prod_congr rfl
    intro k hk
    exact norm_sub_rev _ _
  rw [hrev, pow_two]
  ac_rfl
theorem radial_contracting_monic_of_fekete {n : ℕ} (hn : 1 < n)
    (E : Set ℂ) (z : Fin n → ℂ) (hz : ∀ i, z i ∈ E)
    (hmax : ∀ w : Fin n → ℂ, (∀ i, w i ∈ E) →
      radial_fekete_product w ≤ radial_fekete_product z)
    (hpos : 0 < radial_fekete_product z)
    (hlt : radial_fekete_product z < 1) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x ∈ E, ‖p.eval x‖ ≤ q := by
  classical
  have hex : ∃ i : Fin n, radial_fekete_fiber z i < 1 := by
    by_contra h
    have hge : ∀ i : Fin n, 1 ≤ radial_fekete_fiber z i :=
      fun i => le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hprod : 1 ≤ radial_fekete_product z :=
      Finset.one_le_prod (fun i _ => hge i)
    exact hlt.not_ge hprod
  obtain ⟨i, hi⟩ := hex
  have hq : 0 ≤ radial_fekete_fiber z i :=
    Finset.prod_nonneg (fun j _ => norm_nonneg _)
  have hC : 0 ≤ radial_fekete_remainder z i :=
    Finset.prod_nonneg (fun k _ => Finset.prod_nonneg (fun j _ => norm_nonneg _))
  have hCne : radial_fekete_remainder z i ≠ 0 := by
    intro hzero
    rw [radial_fekete_product_factor z i, hzero, zero_mul] at hpos
    exact (lt_irrefl 0) hpos
  have hCpos : 0 < radial_fekete_remainder z i := lt_of_le_of_ne hC hCne.symm
  refine ⟨∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (z j)),
    Polynomial.monic_prod_X_sub_C z _, ?_, radial_fekete_fiber z i, hq, hi, ?_⟩
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_pos_of_lt hn
  · intro x hx
    have hmem : ∀ j : Fin n, Function.update z i x j ∈ E := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using hx
      · rw [Function.update_of_ne hji]
        exact hz j
    have hrem : radial_fekete_remainder (Function.update z i x) i =
        radial_fekete_remainder z i := by
      unfold radial_fekete_remainder
      apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      rw [Function.update_of_ne hki, Function.update_of_ne hji]
    have hfiber : radial_fekete_fiber (Function.update z i x) i =
        ∏ j ∈ Finset.univ.erase i, ‖x - z j‖ := by
      unfold radial_fekete_fiber
      apply Finset.prod_congr rfl
      intro j hj
      rw [Function.update_self, Function.update_of_ne (Finset.mem_erase.mp hj).1]
    have hcomp := hmax (Function.update z i x) hmem
    rw [radial_fekete_product_factor (Function.update z i x) i,
      radial_fekete_product_factor z i, hrem, hfiber] at hcomp
    have hsquare : (∏ j ∈ Finset.univ.erase i, ‖x - z j‖) ^ 2 ≤
        radial_fekete_fiber z i ^ 2 := le_of_mul_le_mul_left hcomp hCpos
    have hxprod : 0 ≤ ∏ j ∈ Finset.univ.erase i, ‖x - z j‖ :=
      Finset.prod_nonneg (fun j _ => norm_nonneg _)
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, norm_prod]
    nlinarith
theorem radial_fekete_product_continuous (n : ℕ) :
    Continuous (radial_fekete_product (n := n)) := by
  classical
  unfold radial_fekete_product
  exact continuous_finsetProd Finset.univ (fun i _ =>
    continuous_finsetProd (Finset.univ.erase i) (fun j _ =>
      ((continuous_apply i).sub (continuous_apply j)).norm))
theorem radial_contracting_monic_of_compact_fekete_bound {n : ℕ} (hn : 1 < n)
    (E : Set ℂ) (hE : IsCompact E) (z₀ : Fin n → ℂ)
    (hz₀ : ∀ i, z₀ i ∈ E) (hpos₀ : 0 < radial_fekete_product z₀)
    (hbound : ∀ z : Fin n → ℂ, (∀ i, z i ∈ E) → radial_fekete_product z < 1) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x ∈ E, ‖p.eval x‖ ≤ q := by
  let S : Set (Fin n → ℂ) := Set.pi Set.univ (fun _ => E)
  have hS : IsCompact S := isCompact_univ_pi (fun _ => hE)
  have hz₀S : z₀ ∈ S := by simpa only [S, Set.mem_univ_pi] using hz₀
  obtain ⟨z, hz, hmax⟩ := hS.exists_isMaxOn ⟨z₀, hz₀S⟩
    (radial_fekete_product_continuous n).continuousOn
  have hzE : ∀ i, z i ∈ E := by simpa only [S, Set.mem_univ_pi] using hz
  have hmaxE : ∀ w : Fin n → ℂ, (∀ i, w i ∈ E) →
      radial_fekete_product w ≤ radial_fekete_product z := by
    intro w hw
    exact hmax (by simpa only [S, Set.mem_univ_pi] using hw)
  exact radial_contracting_monic_of_fekete hn E z hzE hmaxE
    (hpos₀.trans_le (hmax hz₀S)) (hbound z hzE)
noncomputable def radial_tree_set (A : Finset ℂ) (T : ℝ) : Set ℂ :=
  ⋃ a ∈ A, (fun t : ℝ => (t : ℂ) * a) '' Set.Icc 0 T
theorem radial_tree_set_compact (A : Finset ℂ) (T : ℝ) :
    IsCompact (radial_tree_set A T) := by
  exact A.isCompact_biUnion (fun a _ =>
    isCompact_Icc.image (Complex.continuous_ofReal.mul continuous_const))
theorem radial_tree_set_mem_iff (A : Finset ℂ) (T : ℝ) (z : ℂ) :
    z ∈ radial_tree_set A T ↔
      ∃ a ∈ A, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ z = (t : ℂ) * a := by
  simp only [radial_tree_set, Set.mem_iUnion, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨a, ha, t, ht, htz⟩
    exact ⟨a, ha, t, ht.1, ht.2, htz.symm⟩
  · rintro ⟨a, ha, t, ht₀, htT, hzt⟩
    exact ⟨a, ha, t, ⟨ht₀, htT⟩, hzt.symm⟩
theorem radial_tree_fekete_positive (A : Finset ℂ) (T : ℝ) (n : ℕ)
    (hA : A.Nonempty) (hunit : ∀ a ∈ A, ‖a‖ = 1) (hT : 0 < T) :
    ∃ z : Fin n → ℂ, (∀ i, z i ∈ radial_tree_set A T) ∧
      0 < radial_fekete_product z := by
  classical
  obtain ⟨a, ha⟩ := hA
  have ha₀ : a ≠ 0 := by
    intro ha₀
    have := hunit a ha
    simp [ha₀] at this
  let r : Fin n → ℝ := fun i => T * (i.val : ℝ) / ((n : ℝ) + 1)
  let z : Fin n → ℂ := fun i => (r i : ℂ) * a
  have hden : 0 < (n : ℝ) + 1 := by
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hr : ∀ i, r i ∈ Set.Icc 0 T := by
    intro i
    have hi : (i.val : ℝ) < (n : ℝ) := by exact_mod_cast i.isLt
    constructor
    · exact div_nonneg (mul_nonneg hT.le (Nat.cast_nonneg _)) hden.le
    · apply (div_le_iff₀ hden).mpr
      nlinarith
  have hz : ∀ i, z i ∈ radial_tree_set A T := by
    intro i
    exact (radial_tree_set_mem_iff A T (z i)).mpr
      ⟨a, ha, r i, (hr i).1, (hr i).2, rfl⟩
  have hinj : Function.Injective z := by
    intro i j hij
    have hrij : r i = r j := Complex.ofReal_injective (mul_right_cancel₀ ha₀ hij)
    have hmul : T * (i.val : ℝ) = T * (j.val : ℝ) :=
      (div_left_inj' hden.ne').mp hrij
    have hval : (i.val : ℝ) = (j.val : ℝ) := mul_left_cancel₀ hT.ne' hmul
    exact Fin.ext (by exact_mod_cast hval)
  refine ⟨z, hz, ?_⟩
  unfold radial_fekete_product
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun hij =>
    (Finset.mem_erase.mp hj).1 (hinj hij).symm))
theorem radial_tree_contracting_monic_of_fekete_estimate (A : Finset ℂ) (T : ℝ)
    (hA : A.Nonempty) (hunit : ∀ a ∈ A, ‖a‖ = 1) (hT : 0 ≤ T)
    (hestimate : ∃ n : ℕ, 1 < n ∧
      ∀ z : Fin n → ℂ, (∀ i, z i ∈ radial_tree_set A T) →
        radial_fekete_product z < 1) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ a ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q := by
  by_cases hT₀ : T = 0
  · refine ⟨Polynomial.X, Polynomial.monic_X, by simp, 0, le_rfl, zero_lt_one, ?_⟩
    intro a ha t ht₀ htT
    have ht : t = 0 := le_antisymm (hT₀ ▸ htT) ht₀
    simp [ht]
  · obtain ⟨n, hn, hbound⟩ := hestimate
    obtain ⟨z₀, hz₀, hpos₀⟩ := radial_tree_fekete_positive A T n hA hunit
      (lt_of_le_of_ne hT (Ne.symm hT₀))
    obtain ⟨p, hp, hdegree, q, hq₀, hq₁, hnorm⟩ :=
      radial_contracting_monic_of_compact_fekete_bound hn (radial_tree_set A T)
        (radial_tree_set_compact A T) z₀ hz₀ hpos₀ hbound
    refine ⟨p, hp, hdegree, q, hq₀, hq₁, ?_⟩
    intro a ha t ht₀ htT
    exact hnorm _ ((radial_tree_set_mem_iff A T _).mpr ⟨a, ha, t, ht₀, htT, rfl⟩)
theorem radial_fekete_product_scale {n : ℕ} (c : ℂ) (z : Fin n → ℂ) :
    radial_fekete_product (fun i => c * z i) =
      ‖c‖ ^ (n * (n - 1)) * radial_fekete_product z := by
  classical
  unfold radial_fekete_product
  simp_rw [← mul_sub, norm_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Nat.mul_comm]
theorem radial_tree_set_scale_mem (A : Finset ℂ) (T : ℝ) (hT : 0 < T)
    (z : ℂ) (hz : z ∈ radial_tree_set A T) :
    z / (T : ℂ) ∈ radial_tree_set A 1 := by
  obtain ⟨a, ha, t, ht₀, htT, rfl⟩ := (radial_tree_set_mem_iff A T z).mp hz
  refine (radial_tree_set_mem_iff A 1 _).mpr
    ⟨a, ha, t / T, div_nonneg ht₀ hT.le, (div_le_one hT).mpr htT, ?_⟩
  rw [Complex.ofReal_div]
  exact mul_div_right_comm _ _ _
theorem radial_tree_fekete_estimate_of_unit_estimate (A : Finset ℂ) (T : ℝ)
    (hT : 0 < T) (n : ℕ)
    (hunit : ∀ z : Fin n → ℂ, (∀ i, z i ∈ radial_tree_set A 1) →
      T ^ (n * (n - 1)) * radial_fekete_product z < 1) :
    ∀ z : Fin n → ℂ, (∀ i, z i ∈ radial_tree_set A T) →
      radial_fekete_product z < 1 := by
  intro z hz
  let w : Fin n → ℂ := fun i => z i / (T : ℂ)
  have hw : ∀ i, w i ∈ radial_tree_set A 1 :=
    fun i => radial_tree_set_scale_mem A T hT (z i) (hz i)
  have hTw : (fun i => (T : ℂ) * w i) = z := by
    funext i
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hT.ne')
  have hscale := radial_fekete_product_scale (T : ℂ) w
  rw [hTw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT] at hscale
  rw [hscale]
  exact hunit w hw
theorem radial_tree_contracting_monic_of_normalized_fekete_estimate
    (A : Finset ℂ) (T : ℝ) (hA : A.Nonempty)
    (hunit : ∀ a ∈ A, ‖a‖ = 1) (hT : 0 ≤ T) (hpower : T ^ A.card < 4)
    (hestimate : ∀ b : ℝ, (1 : ℝ) / 4 < b →
      ∃ n : ℕ, 1 < n ∧ ∀ z : Fin n → ℂ,
        (∀ i, z i ∈ radial_tree_set A 1) →
          radial_fekete_product z ^ A.card ≤ b ^ (n * (n - 1))) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ a ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q := by
  by_cases hT₀ : T = 0
  · refine ⟨Polynomial.X, Polynomial.monic_X, by simp, 0, le_rfl, zero_lt_one, ?_⟩
    intro a ha t ht₀ htT
    have ht : t = 0 := le_antisymm (hT₀ ▸ htT) ht₀
    simp [ht]
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT₀)
    have hr : 0 < A.card := Finset.card_pos.mpr hA
    have hTp : 0 < T ^ A.card := pow_pos hTpos _
    have hquarter : (1 : ℝ) / 4 < 1 / T ^ A.card := by
      apply (lt_div_iff₀ hTp).mpr
      nlinarith
    obtain ⟨b, hb₁, hb₂⟩ := exists_between hquarter
    have hbpos : 0 < b := lt_trans (by norm_num) hb₁
    have hTb : T ^ A.card * b < 1 := by
      have := (lt_div_iff₀ hTp).mp hb₂
      nlinarith
    obtain ⟨n, hn, hbound⟩ := hestimate b hb₁
    have hd : 0 < n * (n - 1) :=
      Nat.mul_pos (lt_trans Nat.zero_lt_one hn) (Nat.sub_pos_of_lt hn)
    have hunitbound : ∀ z : Fin n → ℂ, (∀ i, z i ∈ radial_tree_set A 1) →
        T ^ (n * (n - 1)) * radial_fekete_product z < 1 := by
      intro z hz
      have hnonneg : 0 ≤ radial_fekete_product z :=
        Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => norm_nonneg _))
      have hcompare : (T ^ (n * (n - 1)) * radial_fekete_product z) ^ A.card ≤
          (T ^ A.card * b) ^ (n * (n - 1)) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul,
          Nat.mul_comm (n * (n - 1)) A.card]
        exact mul_le_mul_of_nonneg_left (hbound z hz) (pow_nonneg hT _)
      exact (pow_lt_one_iff_of_nonneg
        (mul_nonneg (pow_nonneg hT _) hnonneg) hr.ne').mp
        (hcompare.trans_lt (pow_lt_one₀ (mul_nonneg hTp.le hbpos.le) hTb hd.ne'))
    exact radial_tree_contracting_monic_of_fekete_estimate A T hA hunit hT
      ⟨n, hn, radial_tree_fekete_estimate_of_unit_estimate A T hTpos n hunitbound⟩
theorem radial_tree_contracting_monic_of_normalized_fekete_estimate_expanded
    (A : Finset ℂ) (T : ℝ) (hA : A.Nonempty)
    (hunit : ∀ a ∈ A, ‖a‖ = 1) (hT : 0 ≤ T) (hpower : T ^ A.card < 4)
    (hestimate : ∀ b : ℝ, (1 : ℝ) / 4 < b →
      ∃ n : ℕ, 1 < n ∧ ∀ z : Fin n → ℂ,
        (∀ i, z i ∈ (⋃ a ∈ A,
          (fun t : ℝ => (t : ℂ) * a) '' Set.Icc 0 (1 : ℝ))) →
          (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            ‖z i - z j‖) ^ A.card ≤ b ^ (n * (n - 1))) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ a ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q := by
  exact radial_tree_contracting_monic_of_normalized_fekete_estimate
    A T hA hunit hT hpower hestimate
theorem ratFunc_square_root_is_polynomial {F : Type*} [Field F]
    (r : RatFunc F) (P : Polynomial F)
    (h : r ^ 2 = algebraMap (Polynomial F) (RatFunc F) P) :
    ∃ Q : Polynomial F, Q ^ 2 = P := by
  have hr : IsIntegral (Polynomial F) (r ^ 2) := by
    rw [h]
    exact isIntegral_algebraMap
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by norm_num : 0 < (2 : ℕ)) hr
  refine ⟨Q, RatFunc.algebraMap_injective F ?_⟩
  rw [map_pow, hQ, h]
theorem radial_tree_isCompact (A : Finset ℂ) (T : ℝ) :
    IsCompact (⋃ a ∈ A, (fun t : ℝ => (t : ℂ) * a) '' Set.Icc 0 T) := by
  exact A.isCompact_biUnion fun a _ =>
    isCompact_Icc.image (Complex.continuous_ofReal.mul continuous_const)
theorem polynomial_contracts_on_cthickening (E : Set ℂ) (hE : IsCompact E)
    (p : Polynomial ℂ) (q : ℝ) (hq : q < 1)
    (hp : ∀ z ∈ E, ‖p.eval z‖ ≤ q) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q' : ℝ, q < q' ∧ q' < 1 ∧
      ∀ z ∈ Metric.cthickening δ E, ‖p.eval z‖ ≤ q' := by
  let q' := (q + 1) / 2
  have hqq' : q < q' := by dsimp [q']; linarith
  have hq' : q' < 1 := by dsimp [q']; linarith
  have hopen : IsOpen {z : ℂ | ‖p.eval z‖ < q'} :=
    isOpen_lt p.continuous.norm continuous_const
  obtain ⟨δ, hδ, hsub⟩ := hE.exists_cthickening_subset_open hopen
    (fun z hz => lt_of_le_of_lt (hp z hz) hqq')
  exact ⟨δ, hδ, q', hqq', hq', fun z hz => (hsub hz).le⟩
noncomputable def parametric_polynomial_moment (a b : ℝ) (γ g : ℝ → ℂ)
    (hγ : ContinuousOn γ (Set.uIcc a b)) (hg : ContinuousOn g (Set.uIcc a b)) :
    Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun P := ∫ t in a..b, g t * P.eval (γ t)
  map_add' P Q := by
    simp only [Polynomial.eval_add, mul_add]
    exact intervalIntegral.integral_add
      (hg.mul (P.continuous.comp_continuousOn hγ)).intervalIntegrable
      (hg.mul (Q.continuous.comp_continuousOn hγ)).intervalIntegrable
  map_smul' c P := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (g _) c]
    exact intervalIntegral.integral_const_mul c _
theorem norm_parametric_polynomial_moment_le (a b : ℝ) (γ g : ℝ → ℂ)
    (hγ : ContinuousOn γ (Set.uIcc a b)) (hg : ContinuousOn g (Set.uIcc a b))
    (P : Polynomial ℂ) (C B : ℝ) (hC : 0 ≤ C)
    (hgC : ∀ t ∈ Set.uIcc a b, ‖g t‖ ≤ C)
    (hPB : ∀ t ∈ Set.uIcc a b, ‖P.eval (γ t)‖ ≤ B) :
    ‖parametric_polynomial_moment a b γ g hγ hg P‖ ≤ C * B * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [norm_mul]
  exact mul_le_mul (hgC t (Set.uIoc_subset_uIcc ht))
    (hPB t (Set.uIoc_subset_uIcc ht)) (norm_nonneg _) hC
theorem one_sub_div_mem_slitPlane (b z : ℂ) (hz : z ≠ 0)
    (hseg : z ∉ (fun t : ℝ => (t : ℂ) * b) '' Set.Icc 0 1) :
    1 - b / z ∈ Complex.slitPlane := by
  by_contra h
  have hbad : (1 - b / z).re ≤ 0 ∧ (1 - b / z).im = 0 := by
    simpa only [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] using h
  let w := b / z
  have hwre : 1 ≤ w.re := by
    dsimp [w]
    simpa only [Complex.sub_re, Complex.one_re, sub_nonpos] using hbad.1
  have hwpos : 0 < w.re := lt_of_lt_of_le zero_lt_one hwre
  have hwim : w.im = 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_eq_zero] using hbad.2
  have hw : w = (w.re : ℂ) := by
    apply Complex.ext <;> simp [hwim]
  have hb : b = (w.re : ℂ) * z := by
    calc
      b = w * z := (div_mul_cancel₀ b hz).symm
      _ = (w.re : ℂ) * z := congrArg (fun v : ℂ => v * z) hw
  apply hseg
  refine ⟨w.re⁻¹, ⟨inv_nonneg.mpr hwpos.le, (inv_le_one₀ hwpos).mpr hwre⟩, ?_⟩
  change ((w.re⁻¹ : ℝ) : ℂ) * b = z
  rw [hb, Complex.ofReal_inv, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hwpos.ne'), one_mul]
theorem differentiableAt_radial_sqrt (b z : ℂ) (hz : z ≠ 0)
    (hseg : z ∉ (fun t : ℝ => (t : ℂ) * b) '' Set.Icc 0 1) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.sqrt (1 - b / w)) z := by
  have hg : DifferentiableAt ℂ (fun w : ℂ => 1 - b / w) z :=
    (differentiableAt_const 1).sub ((differentiableAt_const b).div differentiableAt_id hz)
  exact (Complex.differentiableAt_sqrt (one_sub_div_mem_slitPlane b z hz hseg)).comp z hg
theorem differentiableAt_radial_sqrt_product {ι : Type*} (B : Finset ι) (b : ι → ℂ)
    (n : ℕ) (z : ℂ)
    (hz : z ≠ 0)
    (hseg : z ∉ ⋃ i ∈ B, (fun t : ℝ => (t : ℂ) * b i) '' Set.Icc 0 1) :
    DifferentiableAt ℂ
      (fun w : ℂ => w ^ n * ∏ i ∈ B, Complex.sqrt (1 - b i / w)) z := by
  refine (differentiableAt_id.pow n).mul (DifferentiableAt.fun_finsetProd ?_)
  intro i hi
  apply differentiableAt_radial_sqrt (b i) z hz
  intro h
  exact hseg (Set.mem_iUnion₂.mpr ⟨i, hi, h⟩)
theorem radial_sqrt_product_sq {ι : Type*} (B : Finset ι) (b : ι → ℂ) (n : ℕ) (z : ℂ) :
    (z ^ n * ∏ i ∈ B, Complex.sqrt (1 - b i / z)) ^ 2 =
      z ^ (2 * n) * ∏ i ∈ B, (1 - b i / z) := by
  simp only [mul_pow, ← Finset.prod_pow, Complex.sqrt, Complex.cpow_ofNat_inv_pow]
  rw [← pow_mul, Nat.mul_comm n 2]
theorem norm_det_le_factorial_mul_products {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (u v : Fin n → ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ u i * v j) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * (∏ i, u i) * ∏ i, v i := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm (Fin n), (↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ ≤
        ∑ σ : Equiv.Perm (Fin n),
          ‖(↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), (∏ i, u i) * ∏ i, v i := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : ‖(↑(Equiv.Perm.sign σ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      rw [norm_mul, hsign, one_mul, norm_prod]
      calc
        (∏ i, ‖M (σ i) i‖) ≤ ∏ i, u (σ i) * v i :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hM (σ i) i)
        _ = (∏ i, u i) * ∏ i, v i := by
          rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]
    _ = (n.factorial : ℝ) * (∏ i, u i) * ∏ i, v i := by
      simp [Fintype.card_perm, mul_assoc]
theorem norm_det_le_factorial_mul_weight_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (C : ℝ) (u : Fin n → ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ C * u i * u j) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * C ^ n * (∏ i, u i) ^ 2 := by
  have h := norm_det_le_factorial_mul_products M (fun i => C * u i) u
    hM
  simpa [Finset.prod_mul_distrib, sq, mul_assoc] using h
theorem polynomial_moment_det_monic_basis {n : ℕ}
    (L : Polynomial ℂ →ₗ[ℂ] ℂ) (p : Fin n → Polynomial ℂ)
    (hdeg : ∀ i, (p i).natDegree = i.val) (hmonic : ∀ i, (p i).Monic) :
    Matrix.det (fun i j : Fin n => L (p i * p j)) =
      Matrix.det (fun i j : Fin n => L (Polynomial.X ^ (i.val + j.val))) := by
  classical
  let C : Matrix (Fin n) (Fin n) ℂ := fun i j => (p j).coeff i.val
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => L (Polynomial.X ^ (i.val + j.val))
  have hC : C.det = 1 := Matrix.det_matrixOfPolynomials p hdeg hmonic
  have hexp (i : Fin n) : p i =
      ∑ k : Fin n, (p i).coeff k.val • (Polynomial.X : Polynomial ℂ) ^ k.val := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (p i).coeff k • (Polynomial.X : Polynomial ℂ) ^ k)]
    simpa only [Polynomial.smul_eq_C_mul] using
      (p i).as_sum_range_C_mul_X_pow' (hdeg i ▸ i.isLt)
  have hmat : (fun i j : Fin n => L (p i * p j)) = C.transpose * H * C := by
    ext i j
    calc
      L (p i * p j) =
          ∑ k : Fin n, ∑ l : Fin n,
            (p i).coeff k.val * (p j).coeff l.val *
              L (Polynomial.X ^ (k.val + l.val)) := by
        conv_lhs => rw [hexp i, hexp j]
        simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
          map_sum, map_smul, smul_eq_mul, ← pow_add]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = (C.transpose * H * C) i j := by
        change _ = ∑ l : Fin n, (∑ k : Fin n,
          (p i).coeff k.val * L (Polynomial.X ^ (k.val + l.val))) * (p j).coeff l.val
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hC, one_mul, mul_one]
theorem quotient_polynomial_basis_monic (p : Polynomial ℂ) (hp : p.Monic) (i : ℕ) :
    (Polynomial.X ^ (i % p.natDegree) * p ^ (i / p.natDegree)).Monic :=
  (Polynomial.monic_X.pow _).mul (hp.pow _)
theorem quotient_polynomial_basis_natDegree (p : Polynomial ℂ) (hp : p.Monic) (i : ℕ) :
    (Polynomial.X ^ (i % p.natDegree) * p ^ (i / p.natDegree)).natDegree = i := by
  rw [(Polynomial.monic_X.pow _).natDegree_mul (hp.pow _), Polynomial.natDegree_X_pow,
    hp.natDegree_pow]
  simpa only [Nat.mul_comm] using Nat.mod_add_div i p.natDegree
theorem norm_eval_quotient_polynomial_basis_le (p : Polynomial ℂ) (i : ℕ) (z : ℂ)
    (R q : ℝ) (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) (hp : ‖p.eval z‖ ≤ q) :
    ‖(Polynomial.X ^ (i % p.natDegree) * p ^ (i / p.natDegree)).eval z‖ ≤
      R ^ (i % p.natDegree) * q ^ (i / p.natDegree) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
    (pow_le_pow_left₀ (norm_nonneg _) hp _) (pow_nonneg (norm_nonneg _) _) (pow_nonneg hR _)
theorem norm_moment_hankel_det_le (L : Polynomial ℂ →ₗ[ℂ] ℂ) (Γ : Set ℂ)
    (p : Polynomial ℂ) (hp : p.Monic) (M R q : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q)
    (hz : ∀ z ∈ Γ, ‖z‖ ≤ R) (hpΓ : ∀ z ∈ Γ, ‖p.eval z‖ ≤ q)
    (hL : ∀ (A : Polynomial ℂ) (B : ℝ), 0 ≤ B →
      (∀ z ∈ Γ, ‖A.eval z‖ ≤ B) → ‖L A‖ ≤ M * B) (n : ℕ) :
    ‖Matrix.det (fun i j : Fin n => L (Polynomial.X ^ (i.val + j.val)))‖ ≤
      (n.factorial : ℝ) * M ^ n *
        R ^ (2 * ∑ i : Fin n, i.val % p.natDegree) *
        q ^ (2 * ∑ i : Fin n, i.val / p.natDegree) := by
  classical
  let b (i : Fin n) : Polynomial ℂ :=
    Polynomial.X ^ (i.val % p.natDegree) * p ^ (i.val / p.natDegree)
  let u (i : Fin n) : ℝ := R ^ (i.val % p.natDegree) * q ^ (i.val / p.natDegree)
  have hu : ∀ i, 0 ≤ u i := fun i => mul_nonneg (pow_nonneg hR _) (pow_nonneg hq _)
  have hentry (i j : Fin n) : ‖L (b i * b j)‖ ≤ M * u i * u j := by
    calc
      ‖L (b i * b j)‖ ≤ M * (u i * u j) := by
        apply hL _ _ (mul_nonneg (hu i) (hu j))
        intro z hzΓ
        rw [Polynomial.eval_mul, norm_mul]
        exact mul_le_mul
          (norm_eval_quotient_polynomial_basis_le p i.val z R q hR (hz z hzΓ) (hpΓ z hzΓ))
          (norm_eval_quotient_polynomial_basis_le p j.val z R q hR (hz z hzΓ) (hpΓ z hzΓ))
          (norm_nonneg _) (hu i)
      _ = M * u i * u j := (mul_assoc _ _ _).symm
  have hdet := norm_det_le_factorial_mul_weight_sq
    (fun i j : Fin n => L (b i * b j)) M u hentry
  rw [polynomial_moment_det_monic_basis L b
    (fun i => quotient_polynomial_basis_natDegree p hp i.val)
    (fun i => quotient_polynomial_basis_monic p hp i.val)] at hdet
  simpa only [u, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_pow,
    ← pow_mul, Nat.mul_comm, mul_assoc] using hdet
theorem int_eq_zero_of_complex_norm_lt_one (a : ℤ) (h : ‖(a : ℂ)‖ < 1) : a = 0 := by
  rw [Complex.norm_intCast, abs_lt] at h
  have hlo : (-1 : ℤ) < a := by exact_mod_cast h.1
  have hhi : a < (1 : ℤ) := by exact_mod_cast h.2
  omega
theorem int_hankel_det_eq_zero_of_complex_norm_lt_one (a : ℕ → ℤ) (n : ℕ)
    (h : ‖Matrix.det (fun i j : Fin n => (a (i.val + j.val) : ℂ))‖ < 1) :
    Matrix.det (fun i j : Fin n => a (i.val + j.val)) = 0 := by
  apply int_eq_zero_of_complex_norm_lt_one
  have hc := Int.cast_det (R := ℂ)
    (show Matrix (Fin n) (Fin n) ℤ from fun i j => a (i.val + j.val))
  exact (congrArg norm hc).trans_lt h
theorem factorial_geometric_quotient_sum_tendsto_zero (d : ℕ) (hd : 0 < d)
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto
      (fun n : ℕ => (n.factorial : ℝ) * C ^ n *
        q ^ (2 * ∑ i ∈ Finset.range n, i / d)) Filter.atTop (nhds 0) := by
  let r := q ^ 2
  have hr0 : 0 ≤ r := pow_nonneg hq _
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hq1.le)]
  have hlim : Filter.Tendsto (fun k : ℕ => C * (d : ℝ) * ((k : ℝ) + 1) * r ^ k)
      Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_lt_one 1 hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
    convert h.const_mul (C * (d : ℝ)) using 1 <;> simp only [pow_one, mul_zero, add_zero]
    ext k
    ring
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let f (n : ℕ) : ℝ := (n.factorial : ℝ) * C ^ n *
    q ^ (2 * ∑ i ∈ Finset.range n, i / d)
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hrec (n : ℕ) : f (n + 1) = ((n : ℝ) + 1) * C * q ^ (2 * (n / d)) * f n := by
    dsimp [f]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ, Finset.sum_range_succ, Nat.mul_add, pow_add]
    ring
  have hs : Summable f := by
    apply summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1)
    apply Filter.eventually_atTop.mpr
    refine ⟨K * d, fun n hn => ?_⟩
    have hkn : K ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr hn
    have hnlt : n + 1 ≤ d * (n / d + 1) := by
      have hmod := Nat.mod_lt n hd
      have hdiv := Nat.div_add_mod n d
      nlinarith
    have hnR : (n : ℝ) + 1 ≤ (d : ℝ) * ((n / d : ℕ) + 1 : ℝ) := by exact_mod_cast hnlt
    have hratio : ((n : ℝ) + 1) * C * q ^ (2 * (n / d)) ≤ 1 / 2 := by
      calc
        ((n : ℝ) + 1) * C * q ^ (2 * (n / d)) ≤
            ((d : ℝ) * ((n / d : ℕ) + 1 : ℝ)) * C * q ^ (2 * (n / d)) := by
          gcongr
        _ = C * (d : ℝ) * ((n / d : ℕ) + 1 : ℝ) * r ^ (n / d) := by
          rw [pow_mul]
          ring
        _ ≤ 1 / 2 := (hK _ hkn).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 _), hrec]
    exact mul_le_mul_of_nonneg_right hratio (hf0 n)
  exact hs.tendsto_atTop_zero
theorem integer_moment_hankel_eventually_zero (a : ℕ → ℤ)
    (L : Polynomial ℂ →ₗ[ℂ] ℂ) (Γ : Set ℂ)
    (p : Polynomial ℂ) (hp : p.Monic) (hd : 0 < p.natDegree)
    (M R q : ℝ) (hM : 0 ≤ M) (hR : 1 ≤ R) (hq : 0 ≤ q) (hq1 : q < 1)
    (hz : ∀ z ∈ Γ, ‖z‖ ≤ R) (hpΓ : ∀ z ∈ Γ, ‖p.eval z‖ ≤ q)
    (hmoment : ∀ k : ℕ, L (Polynomial.X ^ k) = (a k : ℂ))
    (hL : ∀ (A : Polynomial ℂ) (B : ℝ), 0 ≤ B →
      (∀ z ∈ Γ, ‖A.eval z‖ ≤ B) → ‖L A‖ ≤ M * B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Matrix.det (fun i j : Fin n => a (i.val + j.val)) = 0 := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  -- Absorb the bounded basis remainders into the exponential factor C ^ n.
  let C := M * R ^ (2 * p.natDegree)
  have hC : 0 ≤ C := mul_nonneg hM (pow_nonneg hR0 _)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((factorial_geometric_quotient_sum_tendsto_zero p.natDegree hd C q hC hq hq1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨N, fun n hn => int_hankel_det_eq_zero_of_complex_norm_lt_one a n ?_⟩
  have hdet := norm_moment_hankel_det_le L Γ p hp M R q hR0 hq hz hpΓ hL n
  simp only [hmoment] at hdet
  have hsum : (∑ i : Fin n, i.val % p.natDegree) ≤ p.natDegree * n := by
    calc
      (∑ i : Fin n, i.val % p.natDegree) ≤ ∑ _i : Fin n, p.natDegree :=
        Finset.sum_le_sum fun i _ => (Nat.mod_lt i.val hd).le
      _ = p.natDegree * n := by simp [Nat.mul_comm]
  have hrem : R ^ (2 * ∑ i : Fin n, i.val % p.natDegree) ≤
      R ^ ((2 * p.natDegree) * n) := by
    apply pow_le_pow_right₀ hR
    nlinarith
  calc
    ‖Matrix.det (fun i j : Fin n => (a (i.val + j.val) : ℂ))‖ ≤
        (n.factorial : ℝ) * M ^ n * R ^ (2 * ∑ i : Fin n, i.val % p.natDegree) *
          q ^ (2 * ∑ i : Fin n, i.val / p.natDegree) := hdet
    _ ≤ (n.factorial : ℝ) * M ^ n * R ^ ((2 * p.natDegree) * n) *
          q ^ (2 * ∑ i : Fin n, i.val / p.natDegree) := by
      gcongr
    _ = (n.factorial : ℝ) * C ^ n *
          q ^ (2 * ∑ i ∈ Finset.range n, i / p.natDegree) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i / p.natDegree)]
      simp only [C, mul_pow, pow_mul, mul_assoc]
    _ < 1 := hN n hn
theorem hankel_mulVec_column_operation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (M : Matrix ι ι ℚ) (j : ι) (u : Fin r → ι) (c : Fin r → ℚ) :
    M.mulVec (Pi.single j 1 - ∑ l, c l • Pi.single (u l) 1) =
      fun i => M i j - ∑ l, c l * M i (u l) := by
  classical
  ext i
  simp [Matrix.mulVec_sub, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Matrix.mulVec_single, Matrix.col, Finset.sum_apply]
theorem hankel_residual_nonzero (a : ℕ → ℚ) (r s : ℕ) (c : Fin r → ℚ)
    (hrs : r ≤ s)
    (hdet : Matrix.det (fun i j : Fin r => a (i.val + j.val)) ≠ 0)
    (hrec : ∀ k : ℕ, k < s → a (k + r) = ∑ l : Fin r, c l * a (k + l.val))
    (hfail : a (s + r) ≠ ∑ l : Fin r, c l * a (s + l.val)) :
    Matrix.det (fun i j : Fin (s + 1) => a (i.val + j.val)) ≠ 0 := by
  classical
  let t := s - r + 1
  have htotal : r + t = s + 1 := by dsimp [t]; omega
  let e : Fin r ⊕ Fin t ≃ Fin (r + t) := finSumFinEquiv
  let idx : Fin r ⊕ Fin t → ℕ := fun i => (e i).val
  have hleft (i : Fin r) : idx (Sum.inl i) = i.val := rfl
  have hright (j : Fin t) : idx (Sum.inr j) = r + j.val := rfl
  let u : Fin r → Fin t → Fin r ⊕ Fin t :=
    fun l j => e.symm ⟨l.val + j.val, by omega⟩
  have hu (l : Fin r) (j : Fin t) : idx (u l j) = l.val + j.val := by
    simp [idx, u]
  let M : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) ℚ :=
    fun i j => a (idx i + idx j)
  let C : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) ℚ :=
    fun i j => (show (Fin r ⊕ Fin t) → ℚ from match j with
      | Sum.inl l => Pi.single (Sum.inl l) 1
      | Sum.inr j => Pi.single (Sum.inr j) 1 - ∑ l, c l • Pi.single (u l j) 1) i
  have hmul_left (i : Fin r ⊕ Fin t) (j : Fin r) :
      (M * C) i (Sum.inl j) = a (idx i + j.val) := by
    change (M.mulVec (Pi.single (Sum.inl j) 1)) i = _
    rw [Matrix.mulVec_single]
    simp only [MulOpposite.op_one, one_smul]
    rfl
  have hmul_right (i : Fin r ⊕ Fin t) (j : Fin t) :
      (M * C) i (Sum.inr j) =
        a (idx i + (r + j.val)) - ∑ l, c l * a (idx i + (l.val + j.val)) := by
    change (M.mulVec (Pi.single (Sum.inr j) 1 -
      ∑ l, c l • Pi.single (u l j) 1)) i = _
    rw [hankel_mulVec_column_operation]
    simp only [M, hright, hu]
  let b : ℕ → ℚ := fun k => a (k + r) - ∑ l, c l * a (k + l.val)
  have hbzero (k : ℕ) (hk : k < s) : b k = 0 := sub_eq_zero.mpr (hrec k hk)
  have hbne : b s ≠ 0 := sub_ne_zero.mpr hfail
  have hmul_residual (i : Fin r ⊕ Fin t) (j : Fin t) :
      (M * C) i (Sum.inr j) = b (idx i + j.val) := by
    rw [hmul_right]
    simp only [b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  let D : Matrix (Fin t) (Fin t) ℚ := fun i j => b (r + i.val + j.val)
  let Drev : Matrix (Fin t) (Fin t) ℚ := D.submatrix id Fin.revPerm
  have htri : Drev.IsLowerTriangular := by
    intro i j hij
    change b (r + i.val + (Fin.rev j).val) = 0
    apply hbzero
    have hji : i.val < j.val := hij
    rw [Fin.val_rev]
    dsimp [t] at *
    omega
  have hdiag (i : Fin t) : Drev i i = b s := by
    change b (r + i.val + (Fin.rev i).val) = b s
    congr 1
    rw [Fin.val_rev]
    dsimp [t] at *
    omega
  have hdetrev : Matrix.det Drev ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular Drev htri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i ▸ hbne)
  have hdetD : Matrix.det D ≠ 0 := by
    intro hzero
    apply hdetrev
    change Matrix.det (D.submatrix id Fin.revPerm) = 0
    rw [Matrix.det_permute', hzero, mul_zero]
  let Hsmall : Matrix (Fin r) (Fin r) ℚ := fun i j => a (i.val + j.val)
  let L : Matrix (Fin t) (Fin r) ℚ := fun i j => a (r + i.val + j.val)
  have hblocks : M * C = Matrix.fromBlocks Hsmall 0 L D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hmul_left _ _
      | inr j =>
        rw [hmul_residual, hleft]
        apply hbzero
        have hi := i.isLt
        have hj := j.isLt
        dsimp [t] at hj
        omega
    | inr i =>
      cases j with
      | inl j => exact hmul_left _ _
      | inr j => exact hmul_residual _ _
  have hdetMC : Matrix.det (M * C) ≠ 0 := by
    rw [hblocks, Matrix.det_fromBlocks_zero₁₂ Hsmall L D]
    exact mul_ne_zero hdet hdetD
  have hdetM : Matrix.det M ≠ 0 := by
    intro hzero
    apply hdetMC
    rw [Matrix.det_mul, hzero, zero_mul]
  let H : Matrix (Fin (s + 1)) (Fin (s + 1)) ℚ := fun i j => a (i.val + j.val)
  let f : Fin r ⊕ Fin t ≃ Fin (s + 1) := e.trans (finCongr htotal)
  rwa [show M = H.submatrix f f
    from rfl, Matrix.det_submatrix_equiv_self] at hdetM
theorem radial_powerSeries_square_root_unique (U V : PowerSeries ℂ)
    (hU : PowerSeries.constantCoeff U = 1)
    (hV : PowerSeries.constantCoeff V = 1) (hsq : U ^ 2 = V ^ 2) : U = V := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hc := congrArg PowerSeries.constantCoeff h
    simp only [map_neg, hU, hV] at hc
    norm_num at hc
noncomputable def radial_binomial_root {ι : Type*} (B : Finset ι) (b : ι → ℂ) :
    PowerSeries ℂ :=
  ∏ i ∈ B, PowerSeries.rescale (-b i) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))
theorem radial_binomial_root_constantCoeff {ι : Type*} (B : Finset ι) (b : ι → ℂ) :
    PowerSeries.constantCoeff (radial_binomial_root B b) = 1 := by
  classical
  simp [radial_binomial_root, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
theorem radial_binomial_factor_sq (b : ℂ) :
    (PowerSeries.rescale (-b) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))) ^ 2 =
      1 - PowerSeries.C b * PowerSeries.X := by
  have hhalf : (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)) ^ 2 =
      1 + PowerSeries.X := by
    rw [pow_two, ← PowerSeries.binomialSeries_add]
    have hh : (1 / 2 : ℂ) + 1 / 2 = (1 : ℕ) := by norm_num
    rw [hh, PowerSeries.binomialSeries_nat, pow_one]
  rw [← map_pow, hhalf, map_add, map_one, PowerSeries.rescale_X, map_neg]
  ring
theorem radial_binomial_root_sq {ι : Type*} (B : Finset ι) (b : ι → ℂ) :
    (radial_binomial_root B b) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X) := by
  classical
  simp only [radial_binomial_root, ← Finset.prod_pow, radial_binomial_factor_sq]
theorem radial_formal_square_root_eq_binomial {ι : Type*} (B : Finset ι) (b : ι → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X)) :
    PowerSeries.map (Int.castRingHom ℂ) S = radial_binomial_root B b := by
  apply radial_powerSeries_square_root_unique
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hS₀, map_one]
  · exact radial_binomial_root_constantCoeff B b
  · exact hS.trans (radial_binomial_root_sq B b).symm
theorem radial_powerSeries_mul_hasSum (U V : PowerSeries ℂ) (z u v : ℂ)
    (hU : Summable (fun k : ℕ => ‖PowerSeries.coeff k U * z ^ k‖))
    (hV : Summable (fun k : ℕ => ‖PowerSeries.coeff k V * z ^ k‖))
    (hUs : HasSum (fun k : ℕ => PowerSeries.coeff k U * z ^ k) u)
    (hVs : HasSum (fun k : ℕ => PowerSeries.coeff k V * z ^ k) v) :
    Summable (fun k : ℕ => ‖PowerSeries.coeff k (U * V) * z ^ k‖) ∧
      HasSum (fun k : ℕ => PowerSeries.coeff k (U * V) * z ^ k) (u * v) := by
  have hcoeff (k : ℕ) : PowerSeries.coeff k (U * V) * z ^ k =
      ∑ ij ∈ Finset.antidiagonal k,
        (PowerSeries.coeff ij.1 U * z ^ ij.1) *
          (PowerSeries.coeff ij.2 V * z ^ ij.2) := by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [← Finset.mem_antidiagonal.mp hij, pow_add]
    ring
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hU hV
  simp_rw [← hcoeff] at hnorm
  refine ⟨hnorm, ?_⟩
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hU hV
  rw [hUs.tsum_eq, hVs.tsum_eq] at htsum
  simp_rw [← hcoeff] at htsum
  exact htsum.symm ▸ hnorm.of_norm.hasSum
theorem radial_binomial_factor_hasSum (b z : ℂ) (hz : ‖b‖ * ‖z‖ < 1) :
    Summable (fun k : ℕ =>
      ‖PowerSeries.coeff k
        (PowerSeries.rescale (-b) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))) * z ^ k‖) ∧
    HasSum (fun k : ℕ => PowerSeries.coeff k
        (PowerSeries.rescale (-b) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))) * z ^ k)
      (Complex.sqrt (1 - b * z)) := by
  have hx : -b * z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [norm_mul] using hz
  have hterm (k : ℕ) :
      PowerSeries.coeff k
        (PowerSeries.rescale (-b) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ))) * z ^ k =
      binomialSeries ℂ (1 / 2 : ℂ) k (fun _ => -b * z) := by
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      smul_eq_mul, mul_one, mul_pow]
    ring
  have hnorm := (binomialSeries ℂ (1 / 2 : ℂ)).summable_norm_apply
    (Metric.eball_subset_eball binomialSeries_radius_ge_one hx)
  have hsum := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℂ))).hasSum hx
  simp_rw [← hterm] at hnorm hsum
  refine ⟨hnorm, ?_⟩
  simpa [Complex.sqrt, div_eq_mul_inv, sub_eq_add_neg] using hsum
theorem radial_binomial_root_hasSum {ι : Type*} (B : Finset ι) (b : ι → ℂ)
    (z : ℂ) (hz : ∀ i ∈ B, ‖b i‖ * ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖PowerSeries.coeff k (radial_binomial_root B b) * z ^ k‖) ∧
      HasSum (fun k : ℕ => PowerSeries.coeff k (radial_binomial_root B b) * z ^ k)
        (∏ i ∈ B, Complex.sqrt (1 - b i * z)) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    simp only [radial_binomial_root, Finset.prod_empty]
    have hzero (k : ℕ) (hk : k ≠ 0) :
        PowerSeries.coeff k (1 : PowerSeries ℂ) * z ^ k = 0 := by
      rw [PowerSeries.coeff_one, if_neg hk, zero_mul]
    have h := hasSum_single (f := fun k : ℕ =>
      PowerSeries.coeff k (1 : PowerSeries ℂ) * z ^ k) 0 hzero
    have hnorm := hasSum_single (f := fun k : ℕ =>
      ‖PowerSeries.coeff k (1 : PowerSeries ℂ) * z ^ k‖) 0
      (fun k hk => by rw [hzero k hk, norm_zero])
    exact ⟨hnorm.summable, by simpa only [PowerSeries.coeff_zero_one, pow_zero, mul_one] using h⟩
  | @insert i B hi ih =>
    have hfactor := radial_binomial_factor_hasSum (b i) z (hz i (Finset.mem_insert_self _ _))
    have hB := ih (fun j hj => hz j (Finset.mem_insert_of_mem hj))
    simpa only [radial_binomial_root, Finset.prod_insert hi] using
      radial_powerSeries_mul_hasSum
        (PowerSeries.rescale (-b i) (PowerSeries.binomialSeries ℂ (1 / 2 : ℂ)))
        (radial_binomial_root B b) z _ _ hfactor.1 hB.1 hfactor.2 hB.2
theorem radial_formal_square_root_hasSum {ι : Type*} (B : Finset ι) (b : ι → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X))
    (z : ℂ) (hz : ∀ i ∈ B, ‖b i‖ * ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖((PowerSeries.coeff k S : ℤ) : ℂ) * z ^ k‖) ∧
      HasSum (fun k : ℕ => ((PowerSeries.coeff k S : ℤ) : ℂ) * z ^ k)
        (∏ i ∈ B, Complex.sqrt (1 - b i * z)) := by
  have h := radial_binomial_root_hasSum B b z hz
  rw [← radial_formal_square_root_eq_binomial B b S hS₀ hS] at h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom] using h
theorem radial_formal_square_root_laurent_hasSum (n : ℕ) (b : Fin (2 * n) → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X))
    (z : ℂ) (hz : ∀ i, ‖b i‖ * ‖z⁻¹‖ < 1) :
    HasSum (fun k : ℕ => z ^ n * ((PowerSeries.coeff k S : ℤ) : ℂ) * (z⁻¹) ^ k)
      (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) := by
  have h := (radial_formal_square_root_hasSum Finset.univ b S hS₀ hS z⁻¹
    (fun i _ => hz i)).2.mul_left (z ^ n)
  simpa only [mul_assoc, div_eq_mul_inv] using h
theorem radial_formal_square_root_hasFPowerSeriesOnBall {ι : Type*}
    (B : Finset ι) (b : ι → ℂ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X))
    (r : NNReal) (hr : 0 < r) (hb : ∀ i ∈ B, ‖b i‖ * (r : ℝ) < 1) :
    HasFPowerSeriesOnBall (fun z : ℂ => ∏ i ∈ B, Complex.sqrt (1 - b i * z))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => ((PowerSeries.coeff k S : ℤ) : ℂ))) 0 r := by
  have hnormr : ‖((r : ℝ) : ℂ)‖ = (r : ℝ) := by
    exact_mod_cast r.norm_eq
  have hsumr := (radial_formal_square_root_hasSum B b S hS₀ hS ((r : ℝ) : ℂ)
    (fun i hi => by rw [hnormr]; exact hb i hi)).1
  simp only [norm_mul, norm_pow, hnormr] at hsumr
  refine ⟨?_, ENNReal.coe_pos.mpr hr, ?_⟩
  · exact (FormalMultilinearSeries.ofScalars ℂ
      (fun k => ((PowerSeries.coeff k S : ℤ) : ℂ))).le_radius_of_summable_norm
      (by simpa only [FormalMultilinearSeries.ofScalars_norm] using hsumr)
  · intro z hz
    have hzr : ‖z‖ < (r : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal, Metric.eball_ofReal] at hz
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hsumz := (radial_formal_square_root_hasSum B b S hS₀ hS z (fun i hi =>
      (mul_le_mul_of_nonneg_left hzr.le (norm_nonneg _)).trans_lt (hb i hi))).2
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hsumz
theorem radial_formal_square_root_circle_coeff {ι : Type*}
    (B : Finset ι) (b : ι → ℂ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X))
    (r R : NNReal) (hR : 0 < R) (hRr : R < r)
    (hb : ∀ i ∈ B, ‖b i‖ * (r : ℝ) < 1) (k : ℕ) :
    ((PowerSeries.coeff k S : ℤ) : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        circleIntegral (fun z : ℂ => z⁻¹ ^ k * z⁻¹ *
          ∏ i ∈ B, Complex.sqrt (1 - b i * z)) 0 R := by
  have hf := radial_formal_square_root_hasFPowerSeriesOnBall B b S hS₀ hS r
    (hR.trans hRr) hb
  have hsub : Metric.closedBall (0 : ℂ) (R : ℝ) ⊆ Metric.eball 0 (r : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, Metric.eball_ofReal]
    exact Metric.closedBall_subset_ball (by exact_mod_cast hRr)
  have hc := (hf.differentiableOn.mono hsub).hasFPowerSeriesOnBall hR
  have heq := hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have hk := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1)) heq
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    mul_one, cauchyPowerSeries_apply, sub_zero, one_div, mul_assoc] using hk
theorem radial_formal_square_root_hasFPowerSeriesAt {ι : Type*}
    (B : Finset ι) (b : ι → ℂ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i ∈ B, (1 - PowerSeries.C (b i) * PowerSeries.X)) :
    HasFPowerSeriesAt (fun z : ℂ => ∏ i ∈ B, Complex.sqrt (1 - b i * z))
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => ((PowerSeries.coeff k S : ℤ) : ℂ))) 0 := by
  classical
  let C : ℝ := 1 + ∑ i ∈ B, ‖b i‖
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ i ∈ B, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    dsimp [C]
    linarith
  let r : NNReal := ⟨C⁻¹, inv_nonneg.mpr hC.le⟩
  have hr : 0 < r := inv_pos.mpr hC
  apply (radial_formal_square_root_hasFPowerSeriesOnBall B b S hS₀ hS r hr ?_).hasFPowerSeriesAt
  intro i hi
  change ‖b i‖ * C⁻¹ < 1
  apply (mul_inv_lt_iff₀ hC).mpr
  have hle : ‖b i‖ ≤ ∑ j ∈ B, ‖b j‖ := Finset.single_le_sum (fun j _ => norm_nonneg _) hi
  dsimp [C]
  linarith
theorem radial_formal_square_root_laurent_converges (n : ℕ) (b : Fin (2 * n) → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X)) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
      HasSum (fun k : ℕ => z ^ n * ((PowerSeries.coeff k S : ℤ) : ℂ) * (z⁻¹) ^ k)
        (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) := by
  classical
  let R : ℝ := 1 + ∑ i : Fin (2 * n), ‖b i‖
  have hR : 0 < R := by
    have hsum : 0 ≤ ∑ i : Fin (2 * n), ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    dsimp [R]
    linarith
  refine ⟨R, hR, fun z hz => radial_formal_square_root_laurent_hasSum n b S hS₀ hS z ?_⟩
  intro i
  rw [norm_inv]
  apply (mul_inv_lt_iff₀ (hR.trans hz)).mpr
  have hle : ‖b i‖ ≤ ∑ j : Fin (2 * n), ‖b j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have hi : ‖b i‖ < R := by dsimp [R]; linarith
  simpa only [one_mul] using hi.trans hz
theorem radial_circleMap_inv (R θ : ℝ) :
    (circleMap 0 R θ)⁻¹ = circleMap 0 R⁻¹ (-θ) := by
  simp only [circleMap, zero_add, mul_inv_rev, Complex.ofReal_inv,
    Complex.ofReal_neg, neg_mul, Complex.exp_neg]
  ring
theorem radial_circleIntegral_inv (f : ℂ → ℂ) (R : ℝ) (hR : R ≠ 0) :
    circleIntegral (fun z : ℂ => z⁻¹ ^ 2 * f z⁻¹) 0 R⁻¹ =
      circleIntegral f 0 R := by
  let g : ℝ → ℂ := fun θ => circleMap 0 R θ * Complex.I * f (circleMap 0 R θ)
  have hpoint (θ : ℝ) :
      circleMap 0 R⁻¹ θ * Complex.I *
        ((circleMap 0 R⁻¹ θ)⁻¹ ^ 2 * f (circleMap 0 R⁻¹ θ)⁻¹) = g (-θ) := by
    have hinv : (circleMap 0 R⁻¹ θ)⁻¹ = circleMap 0 R (-θ) := by
      simpa only [inv_inv] using radial_circleMap_inv R⁻¹ θ
    have hne : circleMap 0 R⁻¹ θ ≠ 0 := circleMap_ne_center (inv_ne_zero hR)
    dsimp [g]
    rw [← hinv]
    field_simp
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [g, periodic_circleMap 0 R θ]
  calc
    circleIntegral (fun z : ℂ => z⁻¹ ^ 2 * f z⁻¹) 0 R⁻¹ =
        ∫ θ in 0..2 * Real.pi, g (-θ) := by
      unfold circleIntegral
      simp only [deriv_circleMap, smul_eq_mul]
      exact intervalIntegral.integral_congr (fun θ _ => hpoint θ)
    _ = ∫ θ in -(2 * Real.pi)..0, g θ := by
      simpa only [neg_zero] using (intervalIntegral.integral_comp_neg (f := g)
        (a := 0) (b := 2 * Real.pi))
    _ = ∫ θ in 0..2 * Real.pi, g θ := by
      simpa only [neg_add_cancel, zero_add] using hg.intervalIntegral_add_eq (-(2 * Real.pi)) 0
    _ = circleIntegral f 0 R := by
      unfold circleIntegral
      simp only [deriv_circleMap, smul_eq_mul, g]
theorem radial_formal_square_root_laurent_circle_coeff (n : ℕ) (b : Fin (2 * n) → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X))
    (r R : NNReal) (hR : 0 < R) (hRr : R < r)
    (hb : ∀ i, ‖b i‖ * (r : ℝ) < 1) (k : ℕ) :
    ((PowerSeries.coeff (n + 1 + k) S : ℤ) : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        circleIntegral (fun z : ℂ =>
          (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) * z ^ k) 0
          (R : ℝ)⁻¹ := by
  have hsmall := radial_formal_square_root_circle_coeff Finset.univ b S hS₀ hS r R hR hRr
    (fun i _ => hb i) (n + 1 + k)
  have hpoint (z : ℂ) : z⁻¹ ^ (n + 1 + k) * z⁻¹ *
      (∏ i : Fin (2 * n), Complex.sqrt (1 - b i * z)) =
      z⁻¹ ^ 2 * (((z⁻¹) ^ n *
        ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z⁻¹)) * (z⁻¹) ^ k) := by
    simp only [div_eq_mul_inv, inv_inv, pow_add, pow_one, pow_two]
    ring
  simp_rw [hpoint] at hsmall
  have hRi : (R : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hR.ne')
  have hchange := radial_circleIntegral_inv
    (fun z : ℂ =>
      (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) * z ^ k) (R : ℝ)⁻¹ hRi
  simp only [inv_inv] at hchange
  exact hsmall.trans (congrArg (fun w : ℂ => (2 * Real.pi * Complex.I : ℂ)⁻¹ * w) hchange)
noncomputable def radial_holomorphic_form (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  f z • ContinuousLinearMap.id ℂ ℂ
noncomputable def radial_holomorphic_form_deriv (f : ℂ → ℂ) (z : ℂ) :
    ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  (((ContinuousLinearMap.id ℂ ℂ).smulRight (deriv f z)).smulRight
    (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
theorem radial_holomorphic_form_hasFDerivAt (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z) :
    HasFDerivAt (radial_holomorphic_form f) (radial_holomorphic_form_deriv f z) z := by
  exact (hf.hasDerivAt.hasFDerivAt.smul_const (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ
theorem radial_holomorphic_form_deriv_symmetric (f : ℂ → ℂ) (z u v : ℂ) :
    radial_holomorphic_form_deriv f z u v = radial_holomorphic_form_deriv f z v u := by
  change (u • deriv f z) • v = (v • deriv f z) • u
  simp only [smul_eq_mul]
  ring
theorem radial_holomorphic_curveIntegral_homotopy {a b : ℂ}
    {γ₁ : Path a a} {γ₂ : Path b b}
    (φ : (γ₁ : ContinuousMap unitInterval ℂ).Homotopy γ₂)
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hfc : ContinuousOn f (closure U))
    (hφ : ∀ s ∈ Set.Ioo 0 1, ∀ t ∈ Set.Ioo 0 1, φ (s, t) ∈ U)
    (hclosed : (φ.evalAt 1).cast (by simp) (by simp) = φ.evalAt 0)
    (hsm : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
        (Set.Icc 0 1)) :
    curveIntegral (radial_holomorphic_form f) γ₁ =
      curveIntegral (radial_holomorphic_form f) γ₂ := by
  have h := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (ω := radial_holomorphic_form f) (dω := radial_holomorphic_form_deriv f) hφ
    (fun z hz => (radial_holomorphic_form_hasFDerivAt f z
      ((hf z hz).differentiableAt (hU.mem_nhds hz))).hasFDerivWithinAt)
    (hfc.smul continuousOn_const)
    (fun z _ u _ v _ => radial_holomorphic_form_deriv_symmetric f z u v) hsm
  have heq : curveIntegral (radial_holomorphic_form f) (φ.evalAt 1) =
      curveIntegral (radial_holomorphic_form f) (φ.evalAt 0) := by
    rw [← curveIntegral_cast (c := γ₁ 0) (d := γ₂ 0)
      (radial_holomorphic_form f) (φ.evalAt 1) (by simp) (by simp), hclosed]
  rw [heq] at h
  exact add_right_cancel h
theorem radial_holomorphic_curveIntegral_homotopy_of_differentiableAt {a b : ℂ}
    {γ₁ : Path a a} {γ₂ : Path b b}
    (φ : (γ₁ : ContinuousMap unitInterval ℂ).Homotopy γ₂) (f : ℂ → ℂ)
    (hf : ∀ x : unitInterval × unitInterval, DifferentiableAt ℂ f (φ x))
    (hclosed : (φ.evalAt 1).cast (by simp) (by simp) = φ.evalAt 0)
    (hsm : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
        (Set.Icc 0 1)) :
    curveIntegral (radial_holomorphic_form f) γ₁ =
      curveIntegral (radial_holomorphic_form f) γ₂ := by
  have hc : IsCompact (Set.range φ) := isCompact_range (map_continuous φ)
  have hcont : ContinuousOn (radial_holomorphic_form f) (closure (Set.range φ)) := by
    rw [hc.isClosed.closure_eq]
    rintro z ⟨x, rfl⟩
    exact (radial_holomorphic_form_hasFDerivAt f (φ x) (hf x)).continuousAt.continuousWithinAt
  have h := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    (t := Set.range φ) (ω := radial_holomorphic_form f)
    (dω := radial_holomorphic_form_deriv f)
    (fun _ _ _ _ => Set.mem_range_self _)
    (fun z hz => by
      obtain ⟨x, rfl⟩ := hz
      exact (radial_holomorphic_form_hasFDerivAt f (φ x) (hf x)).hasFDerivWithinAt)
    hcont (fun z _ u _ v _ => radial_holomorphic_form_deriv_symmetric f z u v) hsm
  have heq : curveIntegral (radial_holomorphic_form f) (φ.evalAt 1) =
      curveIntegral (radial_holomorphic_form f) (φ.evalAt 0) := by
    rw [← curveIntegral_cast (c := γ₁ 0) (d := γ₂ 0)
      (radial_holomorphic_form f) (φ.evalAt 1) (by simp) (by simp), hclosed]
  rw [heq] at h
  exact add_right_cancel h
theorem radial_formal_square_root_hankel_eventually_zero_of_n_eq_zero
    (n : ℕ) (hn : n = 0) (b : Fin (2 * n) → ℂ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Matrix.det
      (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val) S) = 0 := by
  subst n
  have hU : PowerSeries.map (Int.castRingHom ℂ) S = 1 := by
    apply radial_powerSeries_square_root_unique
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hS₀, map_one]
    · exact map_one _
    · simpa only [Nat.mul_zero, Finset.prod_empty, pow_one, one_pow,
        Finset.univ_eq_empty] using hS
  have hcoeff (k : ℕ) (hk : 0 < k) : PowerSeries.coeff k S = 0 := by
    have h := congrArg (PowerSeries.coeff k) hU
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom, PowerSeries.coeff_one,
      if_neg hk.ne'] at h
    exact_mod_cast h
  refine ⟨1, fun m hm => ?_⟩
  have : NeZero m := ⟨by omega⟩
  have hM : (fun i j : Fin m => PowerSeries.coeff (0 + 1 + i.val + j.val) S) =
      (0 : Matrix (Fin m) (Fin m) ℤ) := by
    ext i j
    exact hcoeff _ (by omega)
  rw [hM]
  exact Matrix.det_zero
end Submission.Helpers
