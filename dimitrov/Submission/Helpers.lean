import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.AddCircle
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
theorem power_argument_card_le {K : Type*} [Field K] [NumberField K]
    (α : K) (k : ℕ) :
    (Finset.univ.image fun σ : K →+* ℂ ↦ (σ (α ^ k)).arg).card ≤
      (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card := by
  classical
  let f : ℝ → ℝ := fun θ => (k • (θ : Real.Angle)).toReal
  have harg (σ : K →+* ℂ) : (σ (α ^ k)).arg = f (σ α).arg := by
    rw [map_pow]
    exact Complex.arg_coe_angle_eq_iff_eq_toReal.mp
      (Complex.arg_pow_coe_angle (σ α) k)
  have himage : (Finset.univ.image fun σ : K →+* ℂ ↦ (σ (α ^ k)).arg) =
      (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).image f := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro σ _
    exact harg σ
  rw [himage]
  exact Finset.card_image_le
theorem rpow_from_nat_power (x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n)
    (hpow : (2 : ℝ) ≤ x ^ (4 * n)) :
    (2 : ℝ) ^ (1 / (4 * (n : ℝ)) : ℝ) ≤ x := by
  have hpos : (0 : ℝ) < 4 * (n : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hn)
  have hcast : (4 : ℝ) * (n : ℝ) = ((4 * n : ℕ) : ℝ) := by simp
  rw [one_div, Real.rpow_inv_le_iff_of_pos (by norm_num) hx hpos,
    hcast, Real.rpow_natCast]
  exact hpow
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
      Finset.one_le_prod₀ (fun i _ => hge i)
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
    have hbpos : 0 < b := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hb₁
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
theorem rational_power_series_square_root_is_polynomial
    (S : PowerSeries ℚ) (F : Polynomial ℚ)
    (hS : S ^ 2 = (F : PowerSeries ℚ))
    (hrational : ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (Q : PowerSeries ℚ) * S = (P : PowerSeries ℚ)) :
    ∃ G : Polynomial ℚ, G ^ 2 = F := by
  obtain ⟨P, Q, hQ, hPQ⟩ := hrational
  have hpoly : P ^ 2 = F * Q ^ 2 := by
    apply Polynomial.coe_injective ℚ
    simp only [Polynomial.coe_pow, Polynomial.coe_mul]
    rw [← hPQ, mul_pow, hS]
    ring
  let A := algebraMap (Polynomial ℚ) (RatFunc ℚ)
  apply ratFunc_square_root_is_polynomial (A P / A Q) F
  rw [div_pow, div_eq_iff (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hQ))]
  simpa only [map_pow, map_mul] using congrArg A hpoly
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
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hM (σ i) i)
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
  -- An integer determinant with complex norm below one must vanish.
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
  -- Reversing columns makes the residual block triangular with diagonal b s.
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
theorem radial_exp_abs_integrable (k ω : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun x : ℝ =>
      Complex.exp ((-k * |x| : ℝ) + (ω * x : ℝ) * Complex.I)) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((-k * |x| : ℝ) + (ω * x : ℝ) * Complex.I)
  have hneg : ∀ x ∈ Set.Iic (0 : ℝ),
      Complex.exp (((k : ℂ) + (ω : ℂ) * Complex.I) * x) = f x := by
    intro x hx
    dsimp only [f]
    congr 1
    simp only [abs_of_nonpos (Set.mem_Iic.mp hx), Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      Complex.exp (((-k : ℂ) + (ω : ℂ) * Complex.I) * x) = f x := by
    intro x hx
    dsimp only [f]
    congr 1
    simp only [abs_of_pos (Set.mem_Ioi.mp hx), Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hi : MeasureTheory.IntegrableOn f (Set.Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Iic (a := (k : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using hk) 0).congr_fun hneg measurableSet_Iic
  have ho : MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_complex_Ioi (a := (-k : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_neg_of_pos hk) 0).congr_fun hpos measurableSet_Ioi
  have hu := MeasureTheory.integrableOn_union.mpr ⟨hi, ho⟩
  simpa only [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] using hu
theorem radial_exp_abs_integral (k ω : ℝ) (hk : 0 < k) :
    (∫ x : ℝ, Complex.exp ((-k * |x| : ℝ) + (ω * x : ℝ) * Complex.I)) =
      (2 * k : ℂ) / ((k ^ 2 + ω ^ 2 : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((-k * |x| : ℝ) + (ω * x : ℝ) * Complex.I)
  have hi : (∫ x : ℝ in Set.Iic 0, f x) =
      1 / ((k : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ x : ℝ in Set.Iic 0,
          Complex.exp (((k : ℂ) + (ω : ℂ) * Complex.I) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
        intro x hx
        dsimp only [f]
        congr 1
        simp only [abs_of_nonpos (Set.mem_Iic.mp hx), Complex.ofReal_mul, Complex.ofReal_neg]
        ring
      _ = _ := by rw [integral_exp_mul_complex_Iic (by simpa using hk)]; simp
  have ho : (∫ x : ℝ in Set.Ioi 0, f x) =
      -1 / ((-k : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ x : ℝ in Set.Ioi 0,
          Complex.exp (((-k : ℂ) + (ω : ℂ) * Complex.I) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only [f]
        congr 1
        simp only [abs_of_pos (Set.mem_Ioi.mp hx), Complex.ofReal_mul, Complex.ofReal_neg]
        ring
      _ = _ := by
        rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hk)]; simp
  have hsplit : (∫ x : ℝ in Set.Iic 0, f x) + (∫ x : ℝ in Set.Ioi 0, f x) =
      ∫ x : ℝ, f x := by
    simpa only [Set.compl_Iic] using
      MeasureTheory.integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic
        (radial_exp_abs_integrable k ω hk)
  change (∫ x : ℝ, f x) = _
  rw [← hsplit, hi, ho]
  have hp : (k : ℂ) + (ω : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hk.ne' this
  have hm : (-k : ℂ) + (ω : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hk.ne' this
  have hd : ((k ^ 2 + ω ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hd' : (k : ℂ) ^ 2 + (ω : ℂ) ^ 2 ≠ 0 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_pow] using hd
  simp only [Complex.ofReal_add, Complex.ofReal_pow]
  field_simp [hp, hm, hd']
  ring_nf
  simp [Complex.I_sq]
theorem radial_exp_abs_fourier (k : ℝ) (hk : 0 < k) (v : ℝ) :
    FourierTransform.fourier (fun x : ℝ => Complex.exp (-k * |x| : ℝ)) v =
      (2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, ← Complex.exp_add]
  convert radial_exp_abs_integral k (-2 * Real.pi * v) hk using 1
  · congr 1
    ext x
    congr 1
    push_cast
    ring
  · congr 2
    ring
theorem radial_cauchy_kernel_integrable (k : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun v : ℝ =>
      (2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ)) := by
  have hc : 2 * Real.pi / k ≠ 0 := by positivity
  have hbase := (MeasureTheory.integrable_comp_mul_left_iff
    (fun x : ℝ => (1 + x ^ 2)⁻¹) hc).mpr integrable_inv_one_add_sq
  have hcomplex := (hbase.ofReal (𝕜 := ℂ)).const_mul ((2 / k : ℝ) : ℂ)
  convert hcomplex using 1
  ext v
  push_cast
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hd : (k : ℂ) ^ 2 + (2 * (Real.pi : ℂ) * (v : ℂ)) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < k ^ 2 + (2 * Real.pi * v) ^ 2 by positivity))
  have hden : 1 + (2 * (Real.pi : ℂ) / (k : ℂ) * (v : ℂ)) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + (2 * Real.pi / k * v) ^ 2 by positivity))
  field_simp [hk', hd, hden]
  ring_nf
  rfl
theorem radial_exp_abs_fourier_inverse (k : ℝ) (hk : 0 < k) (x : ℝ) :
    (∫ v : ℝ, Complex.exp ((2 * Real.pi * v * x : ℝ) * Complex.I) *
      ((2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ))) =
      Complex.exp (-k * |x| : ℝ) := by
  let f : ℝ → ℂ := fun t => Complex.exp (-k * |t| : ℝ)
  have hcont : Continuous f := by fun_prop
  have hf : MeasureTheory.Integrable f := by
    simpa only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero] using
      radial_exp_abs_integrable k 0 hk
  have hFT : FourierTransform.fourier f = fun v : ℝ =>
      (2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ) := by
    funext v
    exact radial_exp_abs_fourier k hk v
  have hinv := congrFun
    (hcont.fourierInv_fourier_eq hf (hFT ▸ radial_cauchy_kernel_integrable k hk)) x
  rw [hFT, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  simpa only [f, mul_neg, neg_mul, neg_neg, smul_eq_mul] using hinv
theorem radial_cauchy_kernel_inverse (k : ℝ) (hk : 0 < k) (x : ℝ) :
    (∫ v : ℝ, Complex.exp ((v * x : ℝ) * Complex.I) /
      ((k ^ 2 + v ^ 2 : ℝ) : ℂ)) =
      ((Real.pi / k : ℝ) : ℂ) * Complex.exp (-k * |x| : ℝ) := by
  let g : ℝ → ℂ := fun v =>
    Complex.exp ((v * x : ℝ) * Complex.I) / ((k ^ 2 + v ^ 2 : ℝ) : ℂ)
  have hinv := radial_exp_abs_fourier_inverse k hk x
  have hscaled : (∫ v : ℝ, Complex.exp ((2 * Real.pi * v * x : ℝ) * Complex.I) *
      ((2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ))) =
      (2 * k : ℂ) * ∫ v : ℝ, g (2 * Real.pi * v) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext v
    dsimp only [g]
    ring
  rw [hscaled, MeasureTheory.Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos)),
    Complex.real_smul] at hinv
  change (∫ v : ℝ, g v) = _
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (2 * k : ℂ) * ((2 * Real.pi : ℝ)⁻¹ : ℝ) =
      ((Real.pi / k : ℝ) : ℂ)⁻¹ := by
    push_cast
    field_simp
  rw [← mul_assoc, hc] at hinv
  calc
    _ = ((Real.pi / k : ℝ) : ℂ) *
        (((Real.pi / k : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, g v) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (div_ne_zero Real.pi_ne_zero hk.ne')),
        one_mul]
    _ = _ := by rw [hinv]
theorem radial_cauchy_kernel_integrable_unscaled (k : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun v : ℝ => (1 : ℂ) / ((k ^ 2 + v ^ 2 : ℝ) : ℂ)) := by
  have hc : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have h := (MeasureTheory.integrable_comp_mul_left_iff
    (fun v : ℝ => (2 * k : ℂ) / ((k ^ 2 + (2 * Real.pi * v) ^ 2 : ℝ) : ℂ))
      hc).mpr (radial_cauchy_kernel_integrable k hk)
  have hmul : ∀ v : ℝ, 2 * Real.pi * ((2 * Real.pi)⁻¹ * v) = v := by
    intro v
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]
  have hi : MeasureTheory.Integrable (fun v : ℝ =>
      (2 * k : ℂ) / ((k ^ 2 + v ^ 2 : ℝ) : ℂ)) := by
    simpa only [hmul] using h
  convert hi.const_mul ((2 * k : ℂ)⁻¹) using 1
  ext v
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt (show 0 < 2 * k by positivity))), one_mul]
theorem radial_cauchy_kernel_phase_integrable (k x : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun v : ℝ =>
      Complex.exp ((v * x : ℝ) * Complex.I) / ((k ^ 2 + v ^ 2 : ℝ) : ℂ)) := by
  have hp : Continuous (fun v : ℝ => Complex.exp ((v * x : ℝ) * Complex.I)) := by
    fun_prop
  have h := (radial_cauchy_kernel_integrable_unscaled k hk).bdd_mul
    hp.aestronglyMeasurable (c := 1) (by
      filter_upwards with v
      simp [Complex.norm_exp])
  simpa only [div_eq_mul_inv, one_mul] using h
theorem radial_curveIntegral_ofLine (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hloop : γ 1 = γ 0) (f : ℂ → ℂ) :
    curveIntegral (radial_holomorphic_form f)
      (Path.ofLine hγ.continuous.continuousOn rfl hloop) =
        ∫ t in (0 : ℝ)..1, f (γ t) * deriv γ t := by
  let γp : Path (γ 0) (γ 0) := Path.ofLine hγ.continuous.continuousOn rfl hloop
  have hext (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : γp.extend t = γ t := by
    rw [Path.extend_apply γp ht]
    rfl
  rw [curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using ht
  have hderiv : derivWithin γp.extend (Set.Icc (0 : ℝ) 1) t = deriv γ t := by
    apply HasDerivWithinAt.derivWithin
      (((hγ.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt).congr_of_mem hext htI)
    exact (uniqueDiffOn_Icc zero_lt_one) t htI
  rw [curveIntegralFun_def]
  change radial_holomorphic_form f (γp.extend t)
    (derivWithin γp.extend (Set.Icc (0 : ℝ) 1) t) = _
  rw [hext t htI, hderiv]
  rfl
theorem radial_parametric_integral_homotopy (H : ℝ × ℝ → ℂ)
    (hH : ContDiff ℝ 2 H) (hloop : ∀ s : ℝ, H (s, 1) = H (s, 0))
    (f : ℂ → ℂ)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ × ℝ) 1, DifferentiableAt ℂ f (H x)) :
    (∫ t in (0 : ℝ)..1, f (H (0, t)) * deriv (fun u : ℝ => H (0, u)) t) =
      ∫ t in (0 : ℝ)..1, f (H (1, t)) * deriv (fun u : ℝ => H (1, u)) t := by
  have hslice (s : ℝ) : ContDiff ℝ 1 (fun t : ℝ => H (s, t)) :=
    (hH.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id)
  let γ₀ : Path (H (0, 0)) (H (0, 0)) :=
    Path.ofLine (hslice 0).continuous.continuousOn rfl (hloop 0)
  let γ₁ : Path (H (1, 0)) (H (1, 0)) :=
    Path.ofLine (hslice 1).continuous.continuousOn rfl (hloop 1)
  let φ : (γ₀ : ContinuousMap unitInterval ℂ).Homotopy γ₁ :=
    { toFun := fun x => H (x.1, x.2)
      continuous_toFun := hH.continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  have hext (x : ℝ × ℝ) (hx : x ∈ Set.Icc (0 : ℝ × ℝ) 1) :
      Set.IccExtend zero_le_one (φ.extend x.1) x.2 = H x := by
    have hx₁ : x.1 ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.1, hx.2.1⟩
    have hx₂ : x.2 ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.2, hx.2.2⟩
    rw [Set.IccExtend_of_mem zero_le_one _ hx₂,
      ContinuousMap.Homotopy.extend_apply_of_mem_I φ hx₁]
    rfl
  have hsm : ContDiffOn ℝ 2
      (fun x : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend x.1) x.2)
        (Set.Icc (0 : ℝ × ℝ) 1) :=
    hH.contDiffOn.congr hext
  have hclosed : (φ.evalAt 1).cast (by simp) (by simp) = φ.evalAt 0 := by
    ext s
    exact hloop s
  have hφ : ∀ x : unitInterval × unitInterval, DifferentiableAt ℂ f (φ x) := by
    intro x
    exact hf (x.1, x.2) ⟨⟨x.1.prop.1, x.2.prop.1⟩, ⟨x.1.prop.2, x.2.prop.2⟩⟩
  have h := radial_holomorphic_curveIntegral_homotopy_of_differentiableAt
    φ f hφ hclosed hsm
  rw [radial_curveIntegral_ofLine (fun t => H (0, t)) (hslice 0) (hloop 0),
    radial_curveIntegral_ofLine (fun t => H (1, t)) (hslice 1) (hloop 1)] at h
  exact h
noncomputable def radial_tent_radius (B : Finset ℂ) (hB : B.Nonempty) (C : ℝ)
    (u : ℂ) : ℝ :=
  B.sup' hB (fun a => max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))))
theorem radial_tent_radius_lipschitz (B : Finset ℂ) (hB : B.Nonempty) (C : ℝ)
    (hC : 0 ≤ C) : LipschitzWith ⟨C, hC⟩ (radial_tent_radius B hB C) := by
  let K : NNReal := ⟨C, hC⟩
  have hfactor (a : ℂ) : LipschitzWith K
      (fun u : ℂ => max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ)))) := by
    apply LipschitzWith.iff_le_add_mul.mpr
    intro u v
    change max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))) ≤
      max 0 (‖a‖ - C * dist v (a / (‖a‖ : ℂ))) + C * dist u v
    apply max_le
    · exact add_nonneg (le_max_left _ _) (mul_nonneg hC dist_nonneg)
    · have ht := mul_le_mul_of_nonneg_left
        (dist_triangle v u (a / (‖a‖ : ℂ))) hC
      have hm := le_max_right 0 (‖a‖ - C * dist v (a / (‖a‖ : ℂ)))
      rw [dist_comm v u] at ht
      nlinarith
  have hsup : LipschitzWith K
      (B.sup' hB (fun a => fun u : ℂ => max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))))) := by
    apply Finset.sup'_induction
    · intro f hf g hg
      simpa only [Pi.sup_def, max_self] using hf.max hg
    · intro a _
      exact hfactor a
  have heq : (B.sup' hB (fun a => fun u : ℂ =>
      max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))))) = radial_tent_radius B hB C := by
    funext u
    exact Finset.sup'_apply hB _ u
  rw [heq] at hsup
  exact hsup
theorem radial_tent_radius_nonneg (B : Finset ℂ) (hB : B.Nonempty) (C : ℝ)
    (u : ℂ) : 0 ≤ radial_tent_radius B hB C u := by
  obtain ⟨a, ha⟩ := hB
  exact (le_max_left _ _).trans (Finset.le_sup' (f := fun a =>
    max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ)))) ha)
theorem radial_smooth_radius_approx (B : Finset ℂ) (hB : B.Nonempty) (C : ℝ)
    (hC : 0 ≤ C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℂ → ℝ, ContDiff ℝ 2 ρ ∧ ∀ u : ℂ,
      0 < ρ u ∧ radial_tent_radius B hB C u + δ < ρ u ∧
        ρ u < radial_tent_radius B hB C u + 3 * δ := by
  obtain ⟨g, hg, hgf⟩ :=
    (radial_tent_radius_lipschitz B hB C hC).uniformContinuous.exists_contDiff_dist_le hδ
  refine ⟨fun u => g u + 2 * δ,
    (hg.of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).add contDiff_const,
    fun u => ?_⟩
  have h := hgf u
  rw [Real.dist_eq, abs_lt] at h
  have hnonneg := radial_tent_radius_nonneg B hB C u
  exact ⟨by linarith, by linarith, by linarith⟩
theorem radial_smooth_surrounding_radius (B : Finset ℂ) (hB : B.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℂ → ℝ, ContDiff ℝ 2 ρ ∧ ∀ u : ℂ, ‖u‖ = 1 →
      0 < ρ u ∧ (∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < ρ u) ∧
        (ρ u : ℂ) * u ∈ Metric.cthickening ε (radial_tree_set B 1) := by
  classical
  let η : ℝ := ε / 5
  have hη : 0 < η := div_pos hε (by norm_num)
  let A : ℝ := 1 + ∑ a ∈ B, ‖a‖
  have hA : 0 < A := by
    have hs : 0 ≤ ∑ a ∈ B, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [A]
    linarith
  have haA (a : ℂ) (ha : a ∈ B) : ‖a‖ ≤ A := by
    have hs := Finset.single_le_sum (fun a (_ : a ∈ B) => norm_nonneg a) ha
    dsimp [A]
    linarith
  let C : ℝ := A ^ 2 / η
  have hC : 0 < C := div_pos (sq_pos_of_pos hA) hη
  have hCη : C * η = A ^ 2 := div_mul_cancel₀ _ hη.ne'
  obtain ⟨ρ, hρ, happrox⟩ := radial_smooth_radius_approx B hB C hC.le η hη
  refine ⟨ρ, hρ, fun u hu => ⟨(happrox u).1, ?_, ?_⟩⟩
  · intro a ha hua
    have hle : ‖a‖ ≤ radial_tent_radius B hB C u := by
      have h := Finset.le_sup' (f := fun a =>
        max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ)))) ha
      simpa only [radial_tent_radius, hua, dist_self, mul_zero, sub_zero,
        max_eq_right (norm_nonneg a)] using h
    exact lt_of_le_of_lt hle (by linarith [(happrox u).2.1])
  · obtain ⟨a, ha, hmax⟩ := B.exists_mem_eq_sup' hB
      (fun a => max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))))
    let w : ℝ := radial_tent_radius B hB C u
    have hw : w = max 0 (‖a‖ - C * dist u (a / (‖a‖ : ℂ))) := hmax
    have hw0 : 0 ≤ w := radial_tent_radius_nonneg B hB C u
    have hρw : |ρ u - w| ≤ 3 * η := by
      have h := happrox u
      change 0 < ρ u ∧ w + η < ρ u ∧ ρ u < w + 3 * η at h
      rw [abs_of_nonneg (by linarith : 0 ≤ ρ u - w)]
      linarith
    by_cases hwz : w = 0
    · obtain ⟨a₀, ha₀⟩ := hB
      have hzero : (0 : ℂ) ∈ radial_tree_set B 1 := by
        exact (radial_tree_set_mem_iff B 1 0).mpr
          ⟨a₀, ha₀, 0, le_rfl, zero_le_one, by simp⟩
      apply Metric.mem_cthickening_of_dist_le ((ρ u : ℂ) * u) 0 ε _ hzero
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (happrox u).1, hu, mul_one]
      have := happrox u
      change 0 < ρ u ∧ w + η < ρ u ∧ ρ u < w + 3 * η at this
      dsimp [η] at this
      linarith
    · have hwpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwz)
      have hinside : 0 < ‖a‖ - C * dist u (a / (‖a‖ : ℂ)) := by
        rw [hw, lt_max_iff] at hwpos
        exact hwpos.resolve_left (lt_irrefl _)
      have hw_eq : w = ‖a‖ - C * dist u (a / (‖a‖ : ℂ)) := by
        rw [hw, max_eq_right hinside.le]
      have hdist0 : 0 ≤ C * dist u (a / (‖a‖ : ℂ)) := mul_nonneg hC.le dist_nonneg
      have hanorm : 0 < ‖a‖ := by linarith
      have hwlen : w ≤ ‖a‖ := by rw [hw_eq]; linarith
      have hwA : w ≤ A := hwlen.trans (haA a ha)
      have hCd : C * dist u (a / (‖a‖ : ℂ)) ≤ A := by linarith [haA a ha]
      have hwd : w * dist u (a / (‖a‖ : ℂ)) ≤ η := by
        apply (mul_le_mul_iff_right₀ hC).mp
        calc
          C * (w * dist u (a / (‖a‖ : ℂ))) =
              w * (C * dist u (a / (‖a‖ : ℂ))) := by ring
          _ ≤ A * A := mul_le_mul hwA hCd hdist0 hA.le
          _ = C * η := by rw [hCη]; ring
      have hy : (w : ℂ) * (a / (‖a‖ : ℂ)) ∈ radial_tree_set B 1 := by
        apply (radial_tree_set_mem_iff B 1 _).mpr
        refine ⟨a, ha, w / ‖a‖, div_nonneg hw0 hanorm.le,
          (div_le_one hanorm).mpr hwlen, ?_⟩
        rw [Complex.ofReal_div]
        ring
      apply Metric.mem_cthickening_of_dist_le ((ρ u : ℂ) * u)
        ((w : ℂ) * (a / (‖a‖ : ℂ))) ε _ hy
      rw [dist_eq_norm]
      calc
        ‖(ρ u : ℂ) * u - (w : ℂ) * (a / (‖a‖ : ℂ))‖ =
            ‖((ρ u - w : ℝ) : ℂ) * u +
              (w : ℂ) * (u - a / (‖a‖ : ℂ))‖ := by
          congr 1
          push_cast
          ring
        _ ≤ ‖((ρ u - w : ℝ) : ℂ) * u‖ +
              ‖(w : ℂ) * (u - a / (‖a‖ : ℂ))‖ := norm_add_le _ _
        _ = |ρ u - w| + w * dist u (a / (‖a‖ : ℂ)) := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one,
            abs_of_nonneg hw0, dist_eq_norm]
        _ ≤ 3 * η + η := add_le_add hρw hwd
        _ ≤ ε := by dsimp [η]; linarith
theorem linear_recurrence_rational_series (a : ℕ → ℚ) (r : ℕ) (c : Fin r → ℚ)
    (hrec : ∀ k : ℕ, a (k + r) = ∑ l : Fin r, c l * a (k + l.val)) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (Q : PowerSeries ℚ) * PowerSeries.mk a = (P : PowerSeries ℚ) := by
  classical
  let Q : Polynomial ℚ := 1 - ∑ l : Fin r,
    Polynomial.C (c l) * Polynomial.X ^ (r - l.val)
  have hQ0 : Q.coeff 0 = 1 := by
    simp only [Q, Polynomial.coeff_sub, Polynomial.coeff_one, if_true,
      Polynomial.finsetSum_coeff]
    rw [sub_eq_self]
    apply Finset.sum_eq_zero
    intro l hl
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    exact (Nat.sub_pos_of_lt l.isLt).ne
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hQ0
    exact zero_ne_one hQ0
  -- The recurrence cancels every coefficient from degree r onward.
  have htail : ∀ k : ℕ,
      PowerSeries.coeff (k + r) ((Q : PowerSeries ℚ) * PowerSeries.mk a) = 0 := by
    intro k
    have hQcoe : (Q : PowerSeries ℚ) = 1 - ∑ l : Fin r,
        PowerSeries.C (c l) * PowerSeries.X ^ (r - l.val) := by
      change (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) Q = _
      simp only [Q, map_sub, map_one, map_sum, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
    rw [hQcoe, sub_mul, one_mul, Finset.sum_mul, map_sub, map_sum,
      PowerSeries.coeff_mk, sub_eq_zero]
    rw [hrec]
    apply Finset.sum_congr rfl
    intro l hl
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      if_pos (by omega : r - l.val ≤ k + r), PowerSeries.coeff_mk]
    congr 2
    omega
  refine ⟨PowerSeries.trunc r ((Q : PowerSeries ℚ) * PowerSeries.mk a),
    Q, hQne, ?_⟩
  apply PowerSeries.ext
  intro k
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hk
  · rfl
  · have hkr : r ≤ k := Nat.le_of_not_gt hk
    simpa [Nat.sub_add_cancel hkr] using htail (k - r)
theorem hankel_initial_recurrence_of_det_ne_zero (a : ℕ → ℚ) (r : ℕ)
    (hdet : Matrix.det (fun i j : Fin r => a (i.val + j.val)) ≠ 0) :
    ∃ c : Fin r → ℚ, ∀ k : ℕ, k < r →
      a (k + r) = ∑ l : Fin r, c l * a (k + l.val) := by
  classical
  let H : Matrix (Fin r) (Fin r) ℚ := fun i j => a (i.val + j.val)
  have hunit : IsUnit H :=
    (Matrix.isUnit_iff_isUnit_det H).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit)
    (fun i : Fin r => a (i.val + r))
  refine ⟨c, fun k hk => ?_⟩
  have hi := congrFun hc (⟨k, hk⟩ : Fin r)
  simpa only [Matrix.mulVec, dotProduct, H, mul_comm] using hi.symm
theorem hankel_maximal_nonzero_minor (a : ℕ → ℚ)
    (hzero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Matrix.det (fun i j : Fin n => a (i.val + j.val)) = 0) :
    ∃ r : ℕ, Matrix.det (fun i j : Fin r => a (i.val + j.val)) ≠ 0 ∧
      ∀ s : ℕ, r < s → Matrix.det (fun i j : Fin s => a (i.val + j.val)) = 0 := by
  classical
  obtain ⟨N, hN⟩ := hzero
  let D := fun n : ℕ => Matrix.det (fun i j : Fin n => a (i.val + j.val))
  have hD0 : D 0 ≠ 0 := by
    have he : D 0 = 1 := Matrix.det_fin_zero
    rw [he]
    exact one_ne_zero
  have hNpos : 0 < N := by
    by_contra h
    exact hD0 (hN 0 (Nat.le_of_not_gt h))
  let B := (Finset.range N).filter (fun n => D n ≠ 0)
  have hB : B.Nonempty := ⟨0, by simp [B, hNpos, hD0]⟩
  let r := B.max' hB
  have hr : r ∈ B := B.max'_mem hB
  refine ⟨r, (Finset.mem_filter.mp hr).2, fun s hrs => ?_⟩
  by_cases hsN : N ≤ s
  · exact hN s hsN
  · by_contra hs
    have hsB : s ∈ B := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_of_not_ge hsN), hs⟩
    exact (not_le_of_gt hrs) (B.le_max' s hsB)
theorem hankel_eventually_zero_rational (a : ℕ → ℚ)
    (hzero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Matrix.det (fun i j : Fin n => a (i.val + j.val)) = 0) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (Q : PowerSeries ℚ) * PowerSeries.mk a = (P : PowerSeries ℚ) := by
  classical
  obtain ⟨r, hr, hmax⟩ := hankel_maximal_nonzero_minor a hzero
  obtain ⟨c, hc⟩ := hankel_initial_recurrence_of_det_ne_zero a r hr
  -- A first failed recurrence would force a larger nonzero leading minor.
  have hrec : ∀ k : ℕ, a (k + r) = ∑ l : Fin r, c l * a (k + l.val) := by
    by_contra h
    push Not at h
    let s := Nat.find h
    have hfail : a (s + r) ≠ ∑ l : Fin r, c l * a (s + l.val) := Nat.find_spec h
    have hrs : r ≤ s := by
      by_contra hsr
      exact hfail (hc s (Nat.lt_of_not_ge hsr))
    have hbefore : ∀ k : ℕ, k < s →
        a (k + r) = ∑ l : Fin r, c l * a (k + l.val) := by
      intro k hk
      exact not_ne_iff.mp (Nat.find_min h hk)
    have hlarge := hankel_residual_nonzero a r s c hrs hr hbefore hfail
    exact hlarge (hmax (s + 1) (by omega))
  exact linear_recurrence_rational_series a r c hrec
theorem shifted_hankel_eventually_zero_rational (S : PowerSeries ℚ) (d : ℕ)
    (hzero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Matrix.det (fun i j : Fin n => PowerSeries.coeff (d + i.val + j.val) S) = 0) :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧
      (Q : PowerSeries ℚ) * S = (P : PowerSeries ℚ) := by
  classical
  let a : ℕ → ℚ := fun k => PowerSeries.coeff (k + d) S
  have hzero_a : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Matrix.det (fun i j : Fin n => a (i.val + j.val)) = 0 := by
    obtain ⟨N, hN⟩ := hzero
    refine ⟨N, fun n hn => ?_⟩
    simpa [a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hN n hn
  obtain ⟨P₀, Q, hQ, hQP⟩ := hankel_eventually_zero_rational a hzero_a
  let P : Polynomial ℚ := Polynomial.X ^ d * P₀ + Q * PowerSeries.trunc d S
  refine ⟨P, Q, hQ, ?_⟩
  calc
    (Q : PowerSeries ℚ) * S =
        (Q : PowerSeries ℚ) *
          (PowerSeries.X ^ d * PowerSeries.mk a +
            (PowerSeries.trunc d S : PowerSeries ℚ)) := by
      exact congrArg (fun T : PowerSeries ℚ => (Q : PowerSeries ℚ) * T)
        (PowerSeries.eq_X_pow_mul_shift_add_trunc d S)
    _ = PowerSeries.X ^ d * ((Q : PowerSeries ℚ) * PowerSeries.mk a) +
          (Q : PowerSeries ℚ) * (PowerSeries.trunc d S : PowerSeries ℚ) := by
      ring
    _ = PowerSeries.X ^ d * (P₀ : PowerSeries ℚ) +
          (Q : PowerSeries ℚ) * (PowerSeries.trunc d S : PowerSeries ℚ) := by
      rw [hQP]
    _ = (P : PowerSeries ℚ) := by
      simp only [P, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow,
        Polynomial.coe_X]
theorem integral_square_root_one_add_four (H : PowerSeries ℤ)
    (hH : PowerSeries.constantCoeff H = 0) :
    ∃ U : PowerSeries ℤ, PowerSeries.constantCoeff U = 1 ∧ U ^ 2 = 1 + 4 * H := by
  let C : PowerSeries ℤ := PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)
  have hC : C ^ 2 * PowerSeries.X + 1 = C := by
    simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] using
      congrArg (PowerSeries.map (Nat.castRingHom ℤ))
        PowerSeries.catalanSeries_sq_mul_X_add_one
  have hneg : PowerSeries.HasSubst (-H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hH])
  let D : PowerSeries ℤ := PowerSeries.substAlgHom hneg C
  have hD : D ^ 2 * (-H) + 1 = D := by
    simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.substAlgHom_X] using
      congrArg (PowerSeries.substAlgHom hneg) hC
  refine ⟨1 + 2 * H * D, by simp [hH], ?_⟩
  linear_combination -4 * H * hD
theorem integral_square_root_mod_four (F Q : PowerSeries ℤ)
    (hF : PowerSeries.constantCoeff F = 1)
    (hQ : PowerSeries.constantCoeff Q = 0) :
    ∃ S : PowerSeries ℤ, PowerSeries.constantCoeff S = 1 ∧
      S ^ 2 = F * (F + 4 * Q) := by
  let J : PowerSeries ℤ := F.invOfUnit 1
  have hFJ : F * J = 1 := PowerSeries.mul_invOfUnit F 1 (by simpa using hF)
  have hH : PowerSeries.constantCoeff (Q * J) = 0 := by simp [hQ]
  obtain ⟨U, hU, hUsq⟩ := integral_square_root_one_add_four (Q * J) hH
  refine ⟨F * U, by simp [hF, hU], ?_⟩
  calc
    (F * U) ^ 2 = F ^ 2 * (1 + 4 * (Q * J)) := by rw [mul_pow, hUsq]
    _ = F ^ 2 + 4 * F * Q * (F * J) := by ring
    _ = F * (F + 4 * Q) := by rw [hFJ]; ring
theorem radial_positive_ray_avoids_tree (B : Finset ℂ) (u : ℂ) (hu : ‖u‖ = 1)
    (r : ℝ) (hr : 0 < r)
    (hout : ∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < r) :
    (r : ℂ) * u ≠ 0 ∧ (r : ℂ) * u ∉ radial_tree_set B 1 := by
  have hnorm : ‖(r : ℂ) * u‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  refine ⟨by intro h; exact hr.ne' (by simpa [h] using hnorm.symm), ?_⟩
  intro hz
  obtain ⟨a, ha, t, ht, ht1, heq⟩ := (radial_tree_set_mem_iff B 1 _).mp hz
  have htr : t * ‖a‖ = r := by
    have h := congrArg norm heq
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
      hnorm] using h.symm
  have hna : 0 < ‖a‖ := by
    by_contra h
    have hzero : ‖a‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hzero, mul_zero] at htr
    exact hr.ne htr
  have hdir : u = a / (‖a‖ : ℂ) := by
    apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'))
    rw [heq, ← htr, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr hna.ne']
  have hlt := hout a ha hdir
  have hle : r ≤ ‖a‖ := by nlinarith
  exact hlt.not_ge hle
noncomputable def radial_unit_loop (t : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * t)
theorem radial_unit_loop_norm (t : ℝ) : ‖radial_unit_loop t‖ = 1 := by
  simp [radial_unit_loop, norm_circleMap_zero]
theorem radial_unit_loop_closed : radial_unit_loop 1 = radial_unit_loop 0 := by
  simpa [radial_unit_loop] using periodic_circleMap 0 1 0
theorem radial_unit_loop_smooth : ContDiff ℝ 2 radial_unit_loop := by
  unfold radial_unit_loop circleMap
  have hc : ContDiff ℝ 2 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop
noncomputable def radial_radius_homotopy (ρ : ℂ → ℝ) (R : ℝ) (x : ℝ × ℝ) : ℂ :=
  (((1 - x.1) * R + x.1 * ρ (radial_unit_loop x.2) : ℝ) : ℂ) *
    radial_unit_loop x.2
theorem radial_radius_homotopy_smooth (ρ : ℂ → ℝ) (hρ : ContDiff ℝ 2 ρ) (R : ℝ) :
    ContDiff ℝ 2 (radial_radius_homotopy ρ R) := by
  unfold radial_radius_homotopy
  have hu : ContDiff ℝ 2 (fun x : ℝ × ℝ => radial_unit_loop x.2) :=
    radial_unit_loop_smooth.comp contDiff_snd
  have hr : ContDiff ℝ 2 (fun x : ℝ × ℝ =>
      (1 - x.1) * R + x.1 * ρ (radial_unit_loop x.2)) :=
    ((contDiff_const.sub contDiff_fst).mul contDiff_const).add
      (contDiff_fst.mul (hρ.comp hu))
  exact (Complex.ofRealCLM.contDiff.comp hr).mul hu
theorem radial_radius_homotopy_closed (ρ : ℂ → ℝ) (R s : ℝ) :
    radial_radius_homotopy ρ R (s, 1) = radial_radius_homotopy ρ R (s, 0) := by
  simp only [radial_radius_homotopy, radial_unit_loop_closed]
theorem radial_radius_homotopy_avoids (B : Finset ℂ) (ρ : ℂ → ℝ) (R : ℝ)
    (hR : 0 < R) (hbR : ∀ a ∈ B, ‖a‖ < R)
    (hρ : ∀ u : ℂ, ‖u‖ = 1 → 0 < ρ u ∧
      ∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < ρ u)
    (x : ℝ × ℝ) (hx : x ∈ Set.Icc (0 : ℝ × ℝ) 1) :
    radial_radius_homotopy ρ R x ≠ 0 ∧
      radial_radius_homotopy ρ R x ∉ radial_tree_set B 1 := by
  have hs : 0 ≤ x.1 ∧ x.1 ≤ 1 := ⟨hx.1.1, hx.2.1⟩
  have hu := radial_unit_loop_norm x.2
  have hp := hρ _ hu
  apply radial_positive_ray_avoids_tree B _ hu
  · by_cases h : x.1 = 0
    · simpa [h] using hR
    · have ha := mul_nonneg (sub_nonneg.mpr hs.2) hR.le
      have hb := mul_pos (lt_of_le_of_ne hs.1 (Ne.symm h)) hp.1
      linarith
  · intro a ha hdir
    have h₁ := hbR a ha
    have h₂ := hp.2 a ha hdir
    by_cases h : x.1 = 0
    · simpa [h] using h₁
    · have hstrict := mul_pos (lt_of_le_of_ne hs.1 (Ne.symm h)) (sub_pos.mpr h₂)
      have hweak := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₁.le)
      nlinarith
theorem radial_circle_integral_unit_parameter (R : ℝ) (f : ℂ → ℂ) :
    (∫ t in (0 : ℝ)..1, f ((R : ℂ) * radial_unit_loop t) *
      deriv (fun u : ℝ => (R : ℂ) * radial_unit_loop u) t) =
      circleIntegral f 0 R := by
  have heq : (fun u : ℝ => (R : ℂ) * radial_unit_loop u) =
      fun u : ℝ => circleMap 0 R (2 * Real.pi * u) := by
    ext u
    simp [radial_unit_loop, circleMap]
  have heqpoint (t : ℝ) := congrFun heq t
  rw [heq]
  have hd (t : ℝ) : deriv (fun u : ℝ => circleMap 0 R (2 * Real.pi * u)) t =
      (2 * Real.pi) • deriv (circleMap 0 R) (2 * Real.pi * t) := by
    have hinner : HasDerivAt (fun u : ℝ => 2 * Real.pi * u) (2 * Real.pi) t := by
      simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul (2 * Real.pi)
    simpa only [deriv_circleMap, Function.comp_def] using
      ((hasDerivAt_circleMap 0 R (2 * Real.pi * t)).scomp t
        hinner).deriv
  simp_rw [heqpoint, hd]
  calc
    _ = ∫ t in (0 : ℝ)..1, (2 * Real.pi) •
        (deriv (circleMap 0 R) (2 * Real.pi * t) *
          f (circleMap 0 R (2 * Real.pi * t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [Complex.real_smul]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_smul]
      simpa only [mul_zero, mul_one, circleIntegral, smul_eq_mul] using!
        (intervalIntegral.smul_integral_comp_mul_left
          (f := fun θ : ℝ => deriv (circleMap 0 R) θ * f (circleMap 0 R θ))
          (a := 0) (b := 1) (2 * Real.pi))
noncomputable def radial_radius_loop (ρ : ℂ → ℝ) (t : ℝ) : ℂ :=
  (ρ (radial_unit_loop t) : ℂ) * radial_unit_loop t
theorem radial_radius_loop_smooth (ρ : ℂ → ℝ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (radial_radius_loop ρ) := by
  exact (Complex.ofRealCLM.contDiff.comp (hρ.comp radial_unit_loop_smooth)).mul
    radial_unit_loop_smooth
theorem radial_radius_loop_integral_eq_circle (B : Finset ℂ) (ρ : ℂ → ℝ)
    (hρsm : ContDiff ℝ 2 ρ)
    (hρ : ∀ u : ℂ, ‖u‖ = 1 → 0 < ρ u ∧
      ∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < ρ u)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ a ∈ B, ‖a‖ < R)
    (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, z ≠ 0 → z ∉ radial_tree_set B 1 → DifferentiableAt ℂ f z) :
    (∫ t in (0 : ℝ)..1, f (radial_radius_loop ρ t) * deriv (radial_radius_loop ρ) t) =
      circleIntegral f 0 R := by
  have h := radial_parametric_integral_homotopy (radial_radius_homotopy ρ R)
    (radial_radius_homotopy_smooth ρ hρsm R) (radial_radius_homotopy_closed ρ R) f
    (fun x hx => by
      have havoid := radial_radius_homotopy_avoids B ρ R hR hbR hρ x hx
      exact hf _ havoid.1 havoid.2)
  have hzero : (fun t : ℝ => radial_radius_homotopy ρ R (0, t)) =
      fun t : ℝ => (R : ℂ) * radial_unit_loop t := by
    funext t
    simp [radial_radius_homotopy]
  have hone : (fun t : ℝ => radial_radius_homotopy ρ R (1, t)) =
      radial_radius_loop ρ := by
    funext t
    simp [radial_radius_homotopy, radial_radius_loop]
  simp_rw [hzero, hone] at h
  have hzero' (t : ℝ) := congrFun hzero t
  have hone' (t : ℝ) := congrFun hone t
  simp_rw [hzero', hone'] at h
  exact h.symm.trans (radial_circle_integral_unit_parameter R f)
theorem radial_formal_square_root_large_circle (n : ℕ) (b : Fin (2 * n) → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X)) :
    ∃ R : ℝ, 0 < R ∧ (∀ i, ‖b i‖ < R) ∧ ∀ k : ℕ,
      ((PowerSeries.coeff (n + 1 + k) S : ℤ) : ℂ) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          circleIntegral (fun z : ℂ =>
            (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) * z ^ k) 0 R := by
  classical
  let C : ℝ := 1 + ∑ i : Fin (2 * n), ‖b i‖
  have hC : 0 < C := by
    have hs : 0 ≤ ∑ i : Fin (2 * n), ‖b i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    dsimp [C]
    linarith
  let r : NNReal := ⟨C⁻¹, (inv_pos.mpr hC).le⟩
  have hr : 0 < r := inv_pos.mpr hC
  have hb (i : Fin (2 * n)) : ‖b i‖ * (r : ℝ) < 1 := by
    apply (mul_inv_lt_iff₀ hC).mpr
    have hs : ‖b i‖ ≤ ∑ j : Fin (2 * n), ‖b j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  let s : NNReal := r / 2
  have hs : 0 < s := div_pos hr (by norm_num)
  have hsr : s < r := by dsimp [s]; exact half_lt_self hr
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  refine ⟨(s : ℝ)⁻¹, inv_pos.mpr hsR, ?_, ?_⟩
  · intro i
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hsR).mpr
    have hle : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hsr.le
    exact (mul_le_mul_of_nonneg_left hle (norm_nonneg _)).trans_lt (hb i)
  · exact radial_formal_square_root_laurent_circle_coeff n b S hS₀ hS r s hs hsr hb
theorem radial_tree_image_univ {ι : Type*} [Fintype ι] (b : ι → ℂ) :
    radial_tree_set (Finset.univ.image b) 1 =
      ⋃ i ∈ (Finset.univ : Finset ι),
        (fun t : ℝ => (t : ℂ) * b i) '' Set.Icc 0 1 := by
  classical
  ext z
  simp only [radial_tree_set, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and, exists_prop]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨b i, ⟨i, rfl⟩, h⟩
theorem radial_formal_square_root_contour_moments (n : ℕ) (b : Fin (2 * n) → ℂ)
    (S : PowerSeries ℤ) (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X))
    (ρ : ℂ → ℝ) (hρsm : ContDiff ℝ 2 ρ)
    (hρ : ∀ u : ℂ, ‖u‖ = 1 → 0 < ρ u ∧
      ∀ i : Fin (2 * n), u = b i / (‖b i‖ : ℂ) → ‖b i‖ < ρ u) :
    ∀ k : ℕ, ((PowerSeries.coeff (n + 1 + k) S : ℤ) : ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..1,
          ((radial_radius_loop ρ t) ^ n *
            ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / radial_radius_loop ρ t)) *
          (radial_radius_loop ρ t) ^ k * deriv (radial_radius_loop ρ) t := by
  classical
  let B := Finset.univ.image b
  obtain ⟨R, hR, hbR, hcoeff⟩ := radial_formal_square_root_large_circle n b S hS₀ hS
  have hρB : ∀ u : ℂ, ‖u‖ = 1 → 0 < ρ u ∧
      ∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < ρ u := by
    intro u hu
    refine ⟨(hρ u hu).1, ?_⟩
    intro a ha hdir
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (hρ u hu).2 i hdir
  intro k
  have heq := radial_radius_loop_integral_eq_circle B ρ hρsm hρB R hR
    (by intro a ha; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha; exact hbR i)
    (fun z : ℂ => (z ^ n * ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)) * z ^ k)
    (by
      intro z hz hseg
      apply DifferentiableAt.mul
      · apply differentiableAt_radial_sqrt_product Finset.univ b n z hz
        simpa only [← radial_tree_image_univ b] using hseg
      · exact differentiableAt_id.pow k)
  exact (hcoeff k).trans (congrArg (fun z : ℂ => (2 * Real.pi * Complex.I : ℂ)⁻¹ * z)
    heq.symm)
theorem radial_formal_square_root_hankel_eventually_zero
    (n : ℕ) (b : Fin (2 * n) → ℂ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X))
    (hcontract : ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i : Fin (2 * n), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 → ‖p.eval ((t : ℂ) * b i)‖ ≤ q) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Matrix.det
      (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val) S) = 0 := by
  classical
  by_cases hn : n = 0
  · exact radial_formal_square_root_hankel_eventually_zero_of_n_eq_zero n hn b S hS₀ hS
  have hnpos : 0 < 2 * n := by omega
  have : NeZero (2 * n) := ⟨hnpos.ne'⟩
  let B : Finset ℂ := Finset.univ.image b
  have hB : B.Nonempty := Finset.univ_nonempty.image b
  obtain ⟨p, hp, hd, q, hq, hq1, hpseg⟩ := hcontract
  have hpB : ∀ z ∈ radial_tree_set B 1, ‖p.eval z‖ ≤ q := by
    intro z hz
    obtain ⟨a, ha, t, ht, ht1, rfl⟩ := (radial_tree_set_mem_iff B 1 z).mp hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hpseg i t ht ht1
  obtain ⟨δ, hδ, q', hqq', hq'1, hpδ⟩ :=
    polynomial_contracts_on_cthickening _ (radial_tree_set_compact B 1) p q hq1 hpB
  have hq' : 0 ≤ q' := hq.trans hqq'.le
  obtain ⟨ρ, hρsm, hρ⟩ := radial_smooth_surrounding_radius B hB δ hδ
  have hρout : ∀ u : ℂ, ‖u‖ = 1 → 0 < ρ u ∧
      ∀ a ∈ B, u = a / (‖a‖ : ℂ) → ‖a‖ < ρ u :=
    fun u hu => ⟨(hρ u hu).1, (hρ u hu).2.1⟩
  let γ : ℝ → ℂ := radial_radius_loop ρ
  have hγsm : ContDiff ℝ 2 γ := radial_radius_loop_smooth ρ hρsm
  have hγavoid (t : ℝ) : γ t ≠ 0 ∧ γ t ∉ radial_tree_set B 1 :=
    radial_positive_ray_avoids_tree B _ (radial_unit_loop_norm t) _
      (hρout _ (radial_unit_loop_norm t)).1 (hρout _ (radial_unit_loop_norm t)).2
  let f : ℂ → ℂ := fun z => z ^ n *
    ∏ i : Fin (2 * n), Complex.sqrt (1 - b i / z)
  have hf : ∀ z : ℂ, z ≠ 0 → z ∉ radial_tree_set B 1 → DifferentiableAt ℂ f z := by
    intro z hz hseg
    apply differentiableAt_radial_sqrt_product Finset.univ b n z hz
    simpa only [← radial_tree_image_univ b] using hseg
  have hfγ : Continuous (fun t : ℝ => f (γ t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hf _ (hγavoid t).1 (hγavoid t).2).continuousAt.comp hγsm.continuous.continuousAt
  let c : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹
  let g : ℝ → ℂ := fun t => c * f (γ t) * deriv γ t
  have hg : Continuous g :=
    (continuous_const.mul hfγ).mul (hγsm.continuous_deriv (by norm_num))
  have hγI : ContinuousOn γ (Set.uIcc (0 : ℝ) 1) := hγsm.continuous.continuousOn
  have hgI : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := hg.continuousOn
  let L : Polynomial ℂ →ₗ[ℂ] ℂ := parametric_polynomial_moment 0 1 γ g hγI hgI
  have hmom (k : ℕ) : L (Polynomial.X ^ k) =
      ((PowerSeries.coeff (n + 1 + k) S : ℤ) : ℂ) := by
    have hcoeff := radial_formal_square_root_contour_moments n b S hS₀ hS ρ hρsm
      (fun u hu => ⟨(hρout u hu).1,
        fun i hdir => (hρout u hu).2 (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hdir⟩) k
    rw [hcoeff, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    dsimp [g, γ, f, c]
    ring
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  let M : ℝ := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hgM : ∀ t ∈ Set.uIcc (0 : ℝ) 1, ‖g t‖ ≤ M := by
    intro t ht
    exact (hM₀ t (by simpa using ht)).trans (le_max_right _ _)
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hγsm.continuous.continuousOn
  let R : ℝ := max 1 R₀
  let Γ : Set ℂ := γ '' Set.Icc 0 1
  have hzR : ∀ z ∈ Γ, ‖z‖ ≤ R := by
    rintro z ⟨t, ht, rfl⟩
    exact (hR₀ t ht).trans (le_max_right _ _)
  have hpΓ : ∀ z ∈ Γ, ‖p.eval z‖ ≤ q' := by
    rintro z ⟨t, ht, rfl⟩
    exact hpδ _ (hρ _ (radial_unit_loop_norm t)).2.2
  have hL : ∀ (A : Polynomial ℂ) (T : ℝ), 0 ≤ T →
      (∀ z ∈ Γ, ‖A.eval z‖ ≤ T) → ‖L A‖ ≤ M * T := by
    intro A T hT hAT
    have h := norm_parametric_polynomial_moment_le 0 1 γ g hγI hgI A M T hM hgM
      (fun t ht => hAT _ ⟨t, by simpa using ht, rfl⟩)
    simpa only [sub_zero, abs_one, mul_one] using h
  obtain ⟨N, hN⟩ := integer_moment_hankel_eventually_zero
    (fun k => PowerSeries.coeff (n + 1 + k) S) L Γ p hp hd M R q' hM
    (le_max_left _ _) hq' hq'1 hzR hpΓ hmom hL
  refine ⟨N, fun m hm => ?_⟩
  simpa only [Nat.add_assoc] using hN m hm
theorem radial_weighted_complex_sum_norm_sq_le {ι : Type*} (s : Finset ι)
    (τ : ι → ℝ) (hτ : ∀ i ∈ s, 0 ≤ τ i) (v : ι → ℂ) :
    ‖∑ i ∈ s, (τ i : ℂ) * v i‖ ^ 2 ≤
      (∑ i ∈ s, τ i) * ∑ i ∈ s, τ i * ‖v i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, (τ i : ℂ) * v i‖ ≤ ∑ i ∈ s, τ i * ‖v i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖(τ i : ℂ) * v i‖ := norm_sum_le _ _
      _ = _ := Finset.sum_congr rfl (fun i hi => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hτ i hi)])
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    hτ (fun i hi => mul_nonneg (hτ i hi) (sq_nonneg ‖v i‖))
    (r := fun i => τ i * ‖v i‖) (fun i hi => by nlinarith)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hCS
theorem radial_boundary_energy_bound {ι : Type*} (s : Finset ι)
    (τ : ι → ℝ) (hτ : ∀ i ∈ s, 0 < τ i) (p d : ι → ℂ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖(ξ : ℂ) * ∑ i ∈ s, (τ i : ℂ) * p i‖ ^ 2 ≤
      (2 * ξ * ∑ i ∈ s, τ i) *
        (ξ / 2 * ∑ i ∈ s, (τ i * ‖p i‖ ^ 2 + (τ i)⁻¹ * ‖d i‖ ^ 2)) := by
  have hCS := radial_weighted_complex_sum_norm_sq_le s τ
    (fun i hi => (hτ i hi).le) p
  have hS : 0 ≤ ∑ i ∈ s, τ i := Finset.sum_nonneg (fun i hi => (hτ i hi).le)
  have hextra : (∑ i ∈ s, τ i * ‖p i‖ ^ 2) ≤
      ∑ i ∈ s, (τ i * ‖p i‖ ^ 2 + (τ i)⁻¹ * ‖d i‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (hτ i hi).le) (sq_nonneg _))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hξ, mul_pow]
  calc
    ξ ^ 2 * ‖∑ i ∈ s, (τ i : ℂ) * p i‖ ^ 2 ≤
        ξ ^ 2 * ((∑ i ∈ s, τ i) * ∑ i ∈ s, τ i * ‖p i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg ξ)
    _ ≤ ξ ^ 2 * ((∑ i ∈ s, τ i) *
        ∑ i ∈ s, (τ i * ‖p i‖ ^ 2 + (τ i)⁻¹ * ‖d i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hextra hS) (sq_nonneg ξ)
    _ = _ := by ring_nf
theorem radial_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have hfun : (Real.sinh / Real.cosh) = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh y).symm
  rw [hfun] at h
  simpa only [← pow_two, Real.cosh_sq_sub_sinh_sq] using h
theorem radial_tanh_concave_nonneg : ConcaveOn ℝ (Set.Ici 0) Real.tanh := by
  have hanti : AntitoneOn (deriv Real.tanh) (interior (Set.Ici 0)) := by
    intro x hx y hy hxy
    rw [(radial_hasDerivAt_tanh x).deriv, (radial_hasDerivAt_tanh y).deriv]
    apply one_div_le_one_div_of_le (sq_pos_of_pos (Real.cosh_pos x))
    apply pow_le_pow_left₀ (Real.cosh_pos x).le
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (interior_subset hx), abs_of_nonneg (interior_subset hy)]
    exact hxy
  apply hanti.concaveOn_of_deriv (convex_Ici 0)
  · exact (continuous_iff_continuousAt.mpr
      (fun x => (radial_hasDerivAt_tanh x).continuousAt)).continuousOn
  · exact fun x _ => (radial_hasDerivAt_tanh x).differentiableAt.differentiableWithinAt
theorem radial_tanh_sum_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, Real.tanh (x i)) ≤
      (s.card : ℝ) * Real.tanh ((∑ i ∈ s, x i) / s.card) := by
  have hn : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hJ := radial_tanh_concave_nonneg.le_map_sum
    (t := s) (w := fun _ => (1 : ℝ) / s.card) (p := x)
    (fun i _ => (div_pos zero_lt_one hn).le)
    (by simp [hn.ne']) hx
  simp only [smul_eq_mul, one_div_mul_eq_div, ← Finset.sum_div] at hJ
  exact (div_le_iff₀ hn).mp hJ |>.trans_eq (mul_comm _ _)
theorem radial_cyclic_gap_energy_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (δ : ι → ℝ) (hδ : ∀ i ∈ s, 0 < δ i)
    (hδsum : ∑ i ∈ s, δ i = 2 * Real.pi)
    (v : ι → ℂ) (next : ι → ι) (ξ : ℝ) (hξ : 0 < ξ) :
    ‖(ξ : ℂ) * ∑ i ∈ s, (Real.tanh (ξ * δ i / 2) : ℂ) * (v i + v (next i))‖ ^ 2 ≤
      (2 * ξ * s.card * Real.tanh (Real.pi * ξ / s.card)) *
        (ξ / 2 * ∑ i ∈ s,
          (Real.tanh (ξ * δ i / 2) * ‖v i + v (next i)‖ ^ 2 +
            (Real.tanh (ξ * δ i / 2))⁻¹ * ‖v i - v (next i)‖ ^ 2)) := by
  let τ : ι → ℝ := fun i => Real.tanh (ξ * δ i / 2)
  have hτ (i : ι) (hi : i ∈ s) : 0 < τ i := by
    dsimp only [τ]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr
      (div_pos (mul_pos hξ (hδ i hi)) (by norm_num))) (Real.cosh_pos _)
  have hsum : (∑ i ∈ s, τ i) ≤ s.card * Real.tanh (Real.pi * ξ / s.card) := by
    have hJ := radial_tanh_sum_le s hs (fun i => ξ * δ i / 2)
      (fun i hi => (div_pos (mul_pos hξ (hδ i hi)) (by norm_num)).le)
    have hmean : (∑ i ∈ s, ξ * δ i / 2) = Real.pi * ξ := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hδsum]
      ring_nf
    simpa only [hmean, τ] using hJ
  have hQ : 0 ≤ ξ / 2 * ∑ i ∈ s,
      (τ i * ‖v i + v (next i)‖ ^ 2 + (τ i)⁻¹ * ‖v i - v (next i)‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i hi
    exact add_nonneg (mul_nonneg (hτ i hi).le (sq_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (hτ i hi).le) (sq_nonneg _))
  have h := radial_boundary_energy_bound s τ hτ
    (fun i => v i + v (next i)) (fun i => v i - v (next i)) ξ hξ.le
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hQ
  calc
    2 * ξ * (∑ i ∈ s, τ i) ≤
      2 * ξ * (s.card * Real.tanh (Real.pi * ξ / s.card)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring_nf
theorem radial_fourier_square_expand {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (w : ι → ℂ) (v : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, star (w i) * w j *
      Complex.exp ((v * (x j - x i) : ℝ) * Complex.I)) =
      (Complex.normSq (∑ i ∈ s, w i *
        Complex.exp ((v * x i : ℝ) * Complex.I)) : ℂ) := by
  classical
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I]
  have hphase : Complex.exp ((v * (x j - x i) : ℝ) * Complex.I) =
      Complex.exp (-((v * x i : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((v * x j : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hphase]
  simp only [starRingEnd_apply]
  ring_nf
theorem radial_exp_kernel_energy_nonneg {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (w : ι → ℂ) (k : ℝ) (hk : 0 < k) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (w i) * w j *
      Complex.exp (-k * |x j - x i| : ℝ)).re := by
  classical
  let f : ℝ → ℂ := fun v => ∑ i ∈ s, ∑ j ∈ s,
    (star (w i) * w j) *
      (Complex.exp ((v * (x j - x i) : ℝ) * Complex.I) /
        ((k ^ 2 + v ^ 2 : ℝ) : ℂ))
  have hi (i j : ι) : MeasureTheory.Integrable (fun v : ℝ =>
      (star (w i) * w j) *
        (Complex.exp ((v * (x j - x i) : ℝ) * Complex.I) /
          ((k ^ 2 + v ^ 2 : ℝ) : ℂ))) :=
    (radial_cauchy_kernel_phase_integrable k (x j - x i) hk).const_mul _
  have hf : MeasureTheory.Integrable f :=
    MeasureTheory.integrable_finsetSum s (fun i _ =>
      MeasureTheory.integrable_finsetSum s (fun j _ => hi i j))
  have hfi : (∫ v : ℝ, f v) = ((Real.pi / k : ℝ) : ℂ) *
      (∑ i ∈ s, ∑ j ∈ s, star (w i) * w j *
        Complex.exp (-k * |x j - x i| : ℝ)) := by
    dsimp only [f]
    rw [MeasureTheory.integral_finsetSum s (fun i _ =>
      MeasureTheory.integrable_finsetSum s (fun j _ => hi i j))]
    simp_rw [MeasureTheory.integral_finsetSum s (fun j _ => hi _ j),
      MeasureTheory.integral_const_mul,
      radial_cauchy_kernel_inverse k hk]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  have hpos (v : ℝ) : 0 ≤ (f v).re := by
    have heq : f v =
        (Complex.normSq (∑ i ∈ s, w i *
          Complex.exp ((v * x i : ℝ) * Complex.I)) : ℂ) /
            ((k ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      dsimp only [f]
      simp only [← mul_div_assoc, ← Finset.sum_div]
      rw [radial_fourier_square_expand]
    rw [heq, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_nonneg (Complex.normSq_nonneg _) (by positivity)
  have hnonneg : 0 ≤ (∫ v : ℝ, f v).re := by
    rw [← RCLike.re_eq_complex_re]
    rw [← integral_re hf]
    exact MeasureTheory.integral_nonneg hpos
  rw [hfi, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hnonneg
  exact (mul_nonneg_iff_of_pos_left (div_pos Real.pi_pos hk)).mp hnonneg
theorem radial_interval_phase_norm_sq (r θ : ℝ) :
    ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos θ := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]
theorem radial_interval_phase_norm_lower (r θ : ℝ) (hr : 0 ≤ r) :
    1 - r ≤ ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have h := norm_sub_norm_le (1 : ℂ)
    ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  simpa [norm_mul, Complex.norm_of_nonneg hr, Complex.norm_exp_ofReal_mul_I,
    abs_of_nonneg hr] using h
theorem radial_interval_chord_product_lower (r θ φ : ℝ) (hr : 0 ≤ r) :
    2 * r * |Real.cos θ - Real.cos φ| ≤
      ‖1 - (r : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)‖ *
      ‖1 - (r : ℂ) * Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)‖ := by
  let a := ‖1 - (r : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)‖
  let b := ‖1 - (r : ℂ) * Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)‖
  have ha := radial_interval_phase_norm_sq r (θ - φ)
  have hb := radial_interval_phase_norm_sq r (θ + φ)
  change a ^ 2 = _ at ha
  change b ^ 2 = _ at hb
  have hsinθ : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsinφ : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hid : (a * b) ^ 2 = (2 * r * (Real.cos θ - Real.cos φ)) ^ 2 +
      (1 - r) ^ 2 * ((1 + r) ^ 2 - 4 * r * Real.cos θ * Real.cos φ) := by
    rw [mul_pow, ha, hb, Real.cos_sub, Real.cos_add]
    calc
      _ = (2 * r * (Real.cos θ - Real.cos φ)) ^ 2 +
          (1 - r) ^ 2 * ((1 + r) ^ 2 - 4 * r * Real.cos θ * Real.cos φ) +
          4 * r ^ 2 * ((1 - Real.cos θ ^ 2) * (1 - Real.cos φ ^ 2) -
            Real.sin θ ^ 2 * Real.sin φ ^ 2) := by ring
      _ = _ := by rw [hsinθ, hsinφ]; ring
  have hc : Real.cos θ * Real.cos φ ≤ 1 := by
    have h := mul_le_mul (Real.abs_cos_le_one θ) (Real.abs_cos_le_one φ)
      (abs_nonneg (Real.cos φ)) (by norm_num : (0 : ℝ) ≤ 1)
    rw [← abs_mul, one_mul] at h
    exact (le_abs_self _).trans h
  have hbr : 0 ≤ (1 + r) ^ 2 - 4 * r * Real.cos θ * Real.cos φ := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hc), sq_nonneg (1 - r)]
  have hpos := mul_nonneg (sq_nonneg (1 - r)) hbr
  have hab : 0 ≤ a * b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ht : 0 ≤ 2 * r * |Real.cos θ - Real.cos φ| := by positivity
  have hsq : (2 * r * |Real.cos θ - Real.cos φ|) ^ 2 =
      (2 * r * (Real.cos θ - Real.cos φ)) ^ 2 := by
    simp only [mul_pow, sq_abs]
  change _ ≤ a * b
  nlinarith
theorem radial_interval_phase_power_re (r θ : ℝ) (j : ℕ) :
    ((((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ j) / (j : ℂ)).re =
      r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  have he : (j : ℂ) * ((θ : ℂ) * Complex.I) =
      (((j : ℝ) * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, ← Complex.ofReal_pow]
  change (((r ^ j : ℝ) : ℂ) *
    Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I) / ((j : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
    Real.exp_zero, one_mul]
  ring
theorem radial_interval_logTaylor_approx (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (n : ℕ) :
    |-Real.log ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ -
      ∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ)| ≤
        r ^ (n + 1) * (1 - r)⁻¹ := by
  let z : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz : ‖z‖ = r := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hr]
  have h := Complex.norm_log_sub_logTaylor_le n (z := -z) (by simpa [hz] using hr1)
  have ht : Complex.logTaylor (n + 1) (-z) =
      -∑ j ∈ Finset.range (n + 1), z ^ j / (j : ℂ) := by
    simp only [Complex.logTaylor, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hsign : (-1 : ℂ) ^ (j + 1) * (-z) ^ j = -z ^ j := by
      rw [neg_pow, pow_succ]
      calc
        _ = -(((-1 : ℂ) ^ j * (-1) ^ j) * z ^ j) := by ring
        _ = -z ^ j := by rw [← mul_pow]; norm_num
    rw [hsign, neg_div]
  have hre := (Complex.abs_re_le_norm
    (Complex.log (1 + -z) - Complex.logTaylor (n + 1) (-z))).trans h
  rw [ht] at hre
  have hsum : (∑ j ∈ Finset.range (n + 1), z ^ j / (j : ℂ)).re =
      ∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ) := by
    simp only [Complex.re_sum]
    exact Finset.sum_congr rfl (fun j hj => radial_interval_phase_power_re r θ j)
  simp only [Complex.add_re, Complex.log_re, hsum,
    norm_neg, hz, ← sub_eq_add_neg, sub_neg_eq_add] at hre
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hbound : r ^ (n + 1) * (1 - r)⁻¹ / (n + 1) ≤
      r ^ (n + 1) * (1 - r)⁻¹ := by
    exact div_le_self (by positivity) hden
  change |-Real.log ‖1 - z‖ -
    ∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ)| ≤ _
  rw [show -Real.log ‖1 - z‖ -
      (∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ)) =
      -(Real.log ‖1 - z‖ +
        ∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * θ)) by ring,
    abs_neg]
  exact hre.trans hbound
theorem radial_interval_two_phase_sum (r θ φ : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * (θ - φ))) +
      (∑ j ∈ Finset.range (n + 1), r ^ j / (j : ℝ) * Real.cos ((j : ℝ) * (θ + φ))) =
      ∑ j ∈ Finset.range (n + 1),
        2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ) * Real.cos ((j : ℝ) * φ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_sub, mul_add, Real.cos_sub, Real.cos_add]
  ring
theorem radial_interval_cos_moment_nonneg
    (μ : MeasureTheory.ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (θ : Set.Icc (0 : ℝ) 1 → ℝ) (hθ : Continuous θ) (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ ∫ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1,
      (∑ j ∈ Finset.range (n + 1),
        2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ z.1) *
          Real.cos ((j : ℝ) * θ z.2)) ∂(μ.prod μ) := by
  have hi (j : ℕ) : MeasureTheory.Integrable
      (fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 =>
        2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ z.1) *
          Real.cos ((j : ℝ) * θ z.2)) (μ.prod μ) := by
    have hc : Continuous (fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 =>
        2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ z.1) *
          Real.cos ((j : ℝ) * θ z.2)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_finsetSum _ (fun j hj => hi j)]
  apply Finset.sum_nonneg
  intro j hj
  have heq : (∫ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1,
      2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ z.1) *
        Real.cos ((j : ℝ) * θ z.2) ∂(μ.prod μ)) =
      2 * (r ^ j / (j : ℝ)) * (∫ x, Real.cos ((j : ℝ) * θ x) ∂μ) ^ 2 := by
    simp_rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.ProbabilityMeasure.toMeasure_prod,
      MeasureTheory.integral_prod_mul
        (fun x : Set.Icc (0 : ℝ) 1 => Real.cos ((j : ℝ) * θ x))
        (fun x : Set.Icc (0 : ℝ) 1 => Real.cos ((j : ℝ) * θ x))]
    ring
  rw [heq]
  positivity
theorem radial_interval_abel_trunc_le (r θ φ d : ℝ) (N : ℕ)
    (hr : 0 < r) (hr1 : r < 1)
    (hd : |Real.cos θ - Real.cos φ| = 2 * d)
    (hN : 4 * r * Real.exp (-(N : ℝ)) ≤ (1 - r) ^ 2) :
    Real.log 4 - Real.log ‖1 - (r : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)‖ -
      Real.log ‖1 - (r : ℂ) * Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)‖ ≤
      -Real.log (max (Real.exp (-(N : ℝ))) d) - Real.log r := by
  let a := ‖1 - (r : ℂ) * Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)‖
  let b := ‖1 - (r : ℂ) * Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)‖
  have ha : 0 < a := (sub_pos.mpr hr1).trans_le
    (radial_interval_phase_norm_lower r (θ - φ) hr.le)
  have hb : 0 < b := (sub_pos.mpr hr1).trans_le
    (radial_interval_phase_norm_lower r (θ + φ) hr.le)
  have hsmall : (1 - r) ^ 2 ≤ a * b := by
    rw [pow_two]
    exact mul_le_mul (radial_interval_phase_norm_lower r (θ - φ) hr.le)
      (radial_interval_phase_norm_lower r (θ + φ) hr.le)
      (sub_nonneg.mpr hr1.le) (norm_nonneg _)
  have hlarge : 4 * r * d ≤ a * b := by
    have h := radial_interval_chord_product_lower r θ φ hr.le
    rw [hd] at h
    nlinarith
  have hm : 4 * r * max (Real.exp (-(N : ℝ))) d ≤ a * b := by
    by_cases h : d ≤ Real.exp (-(N : ℝ))
    · rw [max_eq_left h]
      exact hN.trans hsmall
    · rw [max_eq_right (le_of_not_ge h)]
      exact hlarge
  have hp : 0 < max (Real.exp (-(N : ℝ))) d :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hlog := Real.log_le_log (mul_pos (mul_pos (by norm_num) hr) hp) hm
  rw [Real.log_mul (mul_ne_zero (by norm_num) hr.ne') hp.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr.ne',
    Real.log_mul ha.ne' hb.ne'] at hlog
  change Real.log 4 - Real.log a - Real.log b ≤ _
  linarith
theorem radial_interval_truncated_energy_bound (c : ℝ) (hc : c < Real.log 4)
    (μ : MeasureTheory.ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    ∃ N : ℕ, c < ∫ z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1,
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ) := by
  let η : ℝ := (Real.log 4 - c) / 4
  have hη : 0 < η := by dsimp [η]; linarith
  let r : ℝ := Real.exp (-η)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hη)
  have hlogr : Real.log r = -η := Real.log_exp _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hη (sub_pos.mpr hr1)) hr1
  let E : ℝ := r ^ (n + 1) * (1 - r)⁻¹
  have hE : E < η := by
    dsimp only [E]
    rw [← div_eq_mul_inv, div_lt_iff₀ (sub_pos.mpr hr1)]
    have hp : r ^ (n + 1) ≤ r ^ n := by
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_left hr1.le (pow_nonneg hr.le n)).trans_eq (mul_one _)
    exact hp.trans_lt hn
  have ht : 0 < (1 - r) ^ 2 / (4 * r) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (-Real.log ((1 - r) ^ 2 / (4 * r)))
  have hNexp : Real.exp (-(N : ℝ)) ≤ (1 - r) ^ 2 / (4 * r) := by
    rw [← Real.exp_log ht]
    exact Real.exp_le_exp.mpr (by linarith)
  have hN' : 4 * r * Real.exp (-(N : ℝ)) ≤ (1 - r) ^ 2 := by
    have h := (le_div_iff₀ (show 0 < 4 * r by positivity)).mp hNexp
    simpa only [mul_comm] using h
  let θ : Set.Icc (0 : ℝ) 1 → ℝ := fun x => Real.arccos (2 * (x : ℝ) - 1)
  have hθ : Continuous θ := by dsimp [θ]; fun_prop
  have hcos (x : Set.Icc (0 : ℝ) 1) : Real.cos (θ x) = 2 * (x : ℝ) - 1 := by
    exact Real.cos_arccos (by linarith [x.property.1]) (by linarith [x.property.2])
  let K : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
    ∑ j ∈ Finset.range (n + 1),
      2 * (r ^ j / (j : ℝ)) * Real.cos ((j : ℝ) * θ z.1) * Real.cos ((j : ℝ) * θ z.2)
  let F : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 → ℝ := fun z =>
    -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2))
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hF : Continuous F := by
    apply Continuous.neg
    apply (continuous_const.max (continuous_fst.dist continuous_snd)).log
    intro z
    exact ((Real.exp_pos _).trans_le (le_max_left _ _)).ne'
  have hKi : MeasureTheory.Integrable K (μ.prod μ) :=
    hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFi : MeasureTheory.Integrable F (μ.prod μ) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) :
      K z ≤ F z + (-Real.log r - Real.log 4 + 2 * E) := by
    have hd : |Real.cos (θ z.1) - Real.cos (θ z.2)| = 2 * dist z.1 z.2 := by
      rw [hcos, hcos, Subtype.dist_eq, Real.dist_eq]
      rw [show 2 * (z.1 : ℝ) - 1 - (2 * (z.2 : ℝ) - 1) =
        2 * ((z.1 : ℝ) - (z.2 : ℝ)) by ring, abs_mul]
      norm_num
    have htr := radial_interval_abel_trunc_le r (θ z.1) (θ z.2)
      (dist z.1 z.2) N hr hr1 hd hN'
    have hminus := (abs_le.mp
      (radial_interval_logTaylor_approx r (θ z.1 - θ z.2) hr.le hr1 n)).1
    have hplus := (abs_le.mp
      (radial_interval_logTaylor_approx r (θ z.1 + θ z.2) hr.le hr1 n)).1
    dsimp only [K]
    rw [← radial_interval_two_phase_sum r (θ z.1) (θ z.2) n]
    dsimp only [F, E]
    linarith
  have hnonneg : 0 ≤ ∫ z, K z ∂(μ.prod μ) :=
    radial_interval_cos_moment_nonneg μ θ hθ r hr.le n
  have hmono := MeasureTheory.integral_mono hKi
    (hFi.add (MeasureTheory.integrable_const (-Real.log r - Real.log 4 + 2 * E))) hpoint
  simp only [Pi.add_apply] at hmono
  rw [MeasureTheory.integral_add hFi (MeasureTheory.integrable_const _)] at hmono
  simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at hmono
  refine ⟨N, ?_⟩
  change c < ∫ z, F z ∂(μ.prod μ)
  have hηeq : 4 * η = Real.log 4 - c := by dsimp [η]; ring
  linarith
theorem radial_fekete_log_bound_of_truncated_energy {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) (M c : ℝ)
    (henergy : (n : ℝ) ^ 2 * c ≤ ∑ i : Fin n, ∑ j : Fin n,
      -Real.log (max (Real.exp (-M)) ‖z i - z j‖)) :
    Real.log (radial_fekete_product z) ≤ -(n : ℝ) ^ 2 * c + n * M := by
  classical
  let K : Fin n → Fin n → ℝ := fun i j =>
    -Real.log (max (Real.exp (-M)) ‖z i - z j‖)
  have hdiag (i : Fin n) : K i i = M := by
    simp [K, (Real.exp_pos (-M)).le, Real.log_exp]
  have hfull : (∑ i : Fin n, ∑ j : Fin n, K i j) =
      (∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, K i j) + n * M := by
    have hrow (i : Fin n) : (∑ j : Fin n, K i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, K i j) + M := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag]
    simp_rw [hrow, Finset.sum_add_distrib]
    simp
  have hne (i j : Fin n) (hij : j ≠ i) : ‖z i - z j‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact fun h => hij (hz h).symm
  have hlog : Real.log (radial_fekete_product z) =
      ∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        Real.log ‖z i - z j‖ := by
    unfold radial_fekete_product
    rw [Real.log_prod (fun i _ => Finset.prod_ne_zero_iff.mpr
      (fun j hj => hne i j (Finset.mem_erase.mp hj).1))]
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.log_prod (fun j hj => hne i j (Finset.mem_erase.mp hj).1)
  have hoff : Real.log (radial_fekete_product z) ≤
      -(∑ i : Fin n, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, K i j) := by
    rw [hlog]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    dsimp only [K]
    rw [neg_neg]
    exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (hne i j (Finset.mem_erase.mp hj).1).symm)
      (le_max_right _ _)
  change (n : ℝ) ^ 2 * c ≤ ∑ i : Fin n, ∑ j : Fin n, K i j at henergy
  rw [hfull] at henergy
  linarith
theorem radial_normalized_fekete_of_truncated_energy
    (A : Finset ℂ) (hA : A.Nonempty) (b : ℝ) (hb : 0 < b) (M c : ℝ)
    (hc : -Real.log b < (A.card : ℝ) * c)
    (henergy : ∀ (n : ℕ) (z : Fin n → ℂ),
      (∀ i, z i ∈ radial_tree_set A 1) →
      (n : ℝ) ^ 2 * c ≤ ∑ i : Fin n, ∑ j : Fin n,
        -Real.log (max (Real.exp (-M)) ‖z i - z j‖)) :
    ∃ n : ℕ, 1 < n ∧ ∀ z : Fin n → ℂ,
      (∀ i, z i ∈ radial_tree_set A 1) →
      radial_fekete_product z ^ A.card ≤ b ^ (n * (n - 1)) := by
  classical
  have hm : 0 < A.card := Finset.card_pos.mpr hA
  have hd : 0 < (A.card : ℝ) * c + Real.log b := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (1 : ℝ) (((A.card : ℝ) * M + Real.log b) /
      ((A.card : ℝ) * c + Real.log b)))
  have hn1 : 1 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlarge : (A.card : ℝ) * M + Real.log b <
      n * ((A.card : ℝ) * c + Real.log b) :=
    (div_lt_iff₀ hd).mp (lt_of_le_of_lt (le_max_right _ _) hn)
  refine ⟨n, hn1, fun z hz => ?_⟩
  by_cases hinj : Function.Injective z
  · have hprod : 0 < radial_fekete_product z := by
      apply Finset.prod_pos
      intro i hi
      apply Finset.prod_pos
      intro j hj
      apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      exact fun heq => (Finset.mem_erase.mp hj).1 (hinj heq).symm
    apply (Real.log_le_log_iff (pow_pos hprod _) (pow_pos hb _)).mp
    rw [Real.log_pow, Real.log_pow]
    have hlog := radial_fekete_log_bound_of_truncated_energy z hinj M c (henergy n z hz)
    have hbound := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ (A.card : ℝ) from Nat.cast_nonneg _)
    have hlarge' := (mul_lt_mul_iff_right₀ hn0).mpr hlarge
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    nlinarith
  · have hzero : radial_fekete_product z = 0 := by
      unfold Function.Injective at hinj
      push Not at hinj
      obtain ⟨i, j, heq, hne⟩ := hinj
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ j⟩)
      simp [heq]
    rw [hzero, zero_pow hm.ne']
    exact (pow_pos hb _).le
theorem radial_exists_strictMono_reindex {m : ℕ} (θ : Fin m → ℝ)
    (hθ : Function.Injective θ) :
    ∃ e : Equiv.Perm (Fin m), StrictMono (θ ∘ e) := by
  exact ⟨Tuple.sort θ,
    (Tuple.monotone_sort θ).strictMono_iff_injective.mpr
      (hθ.comp (Tuple.sort θ).injective)⟩
noncomputable def radial_cyclic_gap {n : ℕ} (L : ℝ)
    (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  x (finRotate (n + 1) i) - x i + if i = Fin.last n then L else 0
theorem radial_cyclic_gap_pos {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hbound : ∀ i, x i ∈ Set.Ico 0 L) (i : Fin (n + 1)) :
    0 < radial_cyclic_gap L x i := by
  classical
  by_cases hi : i = Fin.last n
  · subst i
    simp only [radial_cyclic_gap, finRotate_last, ite_true]
    linarith [(hbound 0).1, (hbound (Fin.last n)).2]
  · have hlt : i < finRotate (n + 1) i := (lt_finRotate_iff_ne_last i).mpr hi
    simpa only [radial_cyclic_gap, if_neg hi, add_zero] using sub_pos.mpr (hx hlt)
theorem radial_cyclic_gap_sum {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ) :
    ∑ i, radial_cyclic_gap L x i = L := by
  classical
  simp only [radial_cyclic_gap, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp, sub_self, zero_add]
  simp
noncomputable def radial_clockwise_distance (L x y : ℝ) : ℝ :=
  if y ≤ x then x - y else L + x - y
theorem radial_cyclic_gap_distance {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (i j : Fin (n + 1)) :
    radial_cyclic_gap L x i + radial_clockwise_distance L (x i) (x j) =
      if j = finRotate (n + 1) i then L
      else radial_clockwise_distance L (x (finRotate (n + 1) i)) (x j) := by
  classical
  by_cases hi : i = Fin.last n
  · subst i
    simp only [radial_cyclic_gap, finRotate_last, ite_true]
    have hjlast : x j ≤ x (Fin.last n) := hx.monotone (Fin.le_last j)
    by_cases hj : j = 0
    · subst j
      simp only [radial_clockwise_distance, if_pos hjlast, ite_true]
      ring_nf
    · have h0j : x 0 < x j := hx (Fin.pos_iff_ne_zero.mpr hj)
      simp only [radial_clockwise_distance, if_pos hjlast, if_neg hj,
        if_neg (not_le.mpr h0j)]
      ring_nf
  · have hnext : i < finRotate (n + 1) i := (lt_finRotate_iff_ne_last i).mpr hi
    have hxn := hx hnext
    simp only [radial_cyclic_gap, if_neg hi, add_zero]
    by_cases hj : j = finRotate (n + 1) i
    · subst j
      simp only [radial_clockwise_distance, if_neg (not_le.mpr hxn), ite_true]
      ring_nf
    · by_cases hji : j ≤ i
      · have hxi := hx.monotone hji
        have hxx := hxi.trans hxn.le
        simp only [radial_clockwise_distance, if_pos hxi, if_pos hxx, if_neg hj]
        ring_nf
      · have hnj : finRotate (n + 1) i < j := by
          have hnval := coe_finRotate_of_ne_last hi
          omega
        have hxj := hx hnj
        have hxi := hxn.trans hxj
        simp only [radial_clockwise_distance, if_neg (not_le.mpr hxi),
          if_neg (not_le.mpr hxj), if_neg hj]
        ring_nf
theorem radial_cyclic_decay_step {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (ξ : ℝ) (i j : Fin (n + 1)) :
    Real.exp (-ξ * radial_clockwise_distance L (x (finRotate (n + 1) i)) (x j)) =
      Real.exp (-ξ * radial_cyclic_gap L x i) *
        Real.exp (-ξ * radial_clockwise_distance L (x i) (x j)) +
      if j = finRotate (n + 1) i then 1 - Real.exp (-ξ * L) else 0 := by
  classical
  rw [← Real.exp_add, ← mul_add, radial_cyclic_gap_distance L x hx]
  by_cases hj : j = finRotate (n + 1) i
  · subst j
    simp only [ite_true, radial_clockwise_distance, le_refl, sub_self, mul_zero,
      Real.exp_zero]
    ring_nf
  · simp only [if_neg hj, add_zero]
theorem radial_cyclic_decay_sum_step {n : ℕ} (L : ℝ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (ξ : ℝ) (w : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    (∑ j, (Real.exp (-ξ * radial_clockwise_distance L
      (x (finRotate (n + 1) i)) (x j)) : ℂ) * w j) =
      (Real.exp (-ξ * radial_cyclic_gap L x i) : ℂ) *
        (∑ j, (Real.exp (-ξ * radial_clockwise_distance L (x i) (x j)) : ℂ) * w j) +
      ((1 - Real.exp (-ξ * L) : ℝ) : ℂ) * w (finRotate (n + 1) i) := by
  classical
  have hcast (j : Fin (n + 1)) :
      ((if j = finRotate (n + 1) i then 1 - Real.exp (-ξ * L) else 0 : ℝ) : ℂ) =
        if j = finRotate (n + 1) i then ((1 - Real.exp (-ξ * L) : ℝ) : ℂ) else 0 := by
    split_ifs <;> rfl
  simp_rw [radial_cyclic_decay_step L x hx ξ i, Complex.ofReal_add,
    Complex.ofReal_mul, hcast, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
theorem radial_tanh_half_exp (t : ℝ) :
    Real.tanh (t / 2) = (1 - Real.exp (-t)) / (1 + Real.exp (-t)) := by
  have he : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [Real.tanh_eq, he, Real.exp_neg]
  have hpos := Real.exp_pos (t / 2)
  field_simp
theorem radial_cosh_periodic_decay (a b : ℝ) (ha : 0 < a) :
    Real.cosh (a - b) / Real.sinh a =
      (Real.exp (-b) + Real.exp (-(2 * a) + b)) / (1 - Real.exp (-(2 * a))) := by
  have hden : 0 < 1 - Real.exp (-(2 * a)) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith : -(2 * a) < 0)
    linarith
  have hsinh : 2 * Real.sinh a * Real.exp (-a) = 1 - Real.exp (-(2 * a)) := by
    calc
      _ = Real.exp a * Real.exp (-a) - Real.exp (-a) * Real.exp (-a) := by
        rw [Real.sinh_eq]
        ring_nf
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
        congr 2
        ring_nf
  have hcosh : 2 * Real.cosh (a - b) * Real.exp (-a) =
      Real.exp (-b) + Real.exp (-(2 * a) + b) := by
    calc
      _ = Real.exp (a - b) * Real.exp (-a) +
          Real.exp (-(a - b)) * Real.exp (-a) := by
        rw [Real.cosh_eq]
        ring_nf
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        rw [show a - b + -a = -b by ring_nf,
          show -(a - b) + -a = -(2 * a) + b by ring_nf]
  apply (div_eq_div_iff (Real.sinh_pos_iff.mpr ha).ne' hden.ne').mpr
  rw [← hsinh, ← hcosh]
  ring_nf
theorem radial_decay_recurrence_energy {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (q : ι → ℝ) (c : ℝ) (a w : ι → ℂ)
    (hrec : ∀ i, a (e i) = (q i : ℂ) * a i + (c : ℂ) * w (e i)) :
    (∑ i, (1 - q i ^ 2) * ‖a i‖ ^ 2) =
      2 * c * (∑ i, star (w i) * a i).re - c ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
  have hlocal (i : ι) : ‖a (e i)‖ ^ 2 - q i ^ 2 * ‖a i‖ ^ 2 =
      2 * c * (star (w (e i)) * a (e i)).re - c ^ 2 * ‖w (e i)‖ ^ 2 := by
    rw [hrec i]
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    _ = ∑ i, (‖a (e i)‖ ^ 2 - q i ^ 2 * ‖a i‖ ^ 2) := by
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      rw [Equiv.sum_comp e (fun i => ‖a i‖ ^ 2)]
    _ = ∑ i, (2 * c * (star (w (e i)) * a (e i)).re - c ^ 2 * ‖w (e i)‖ ^ 2) :=
      Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.re_sum]
      rw [Equiv.sum_comp e (fun i => star (w i) * a i),
        Equiv.sum_comp e (fun i => ‖w i‖ ^ 2)]
theorem radial_symmetric_decay_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H M : ι → ι → ℝ) (hH : ∀ i j, H i j = H j i) (c : ℝ) :
    (∑ i, ∑ j, H i j * (M i j + M j i - if i = j then c else 0)) =
      2 * (∑ i, ∑ j, H i j * M i j) - c * ∑ i, H i i := by
  classical
  have htranspose : (∑ i, ∑ j, H i j * M j i) = ∑ i, ∑ j, H i j * M i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [htranspose]
  have hdiag : (∑ i, ∑ j, H i j * (if i = j then c else 0)) = c * ∑ i, H i i := by
    simp [mul_ite, ← Finset.mul_sum, mul_comm]
  rw [hdiag]
  ring_nf
theorem radial_green_decay_entry (L ξ x y : ℝ) (hL : 0 < L) (hξ : 0 < ξ) :
    (2 * ξ * (1 - Real.exp (-ξ * L))) *
      (Real.cosh (ξ * (L / 2 - |x - y|)) / (2 * ξ * Real.sinh (ξ * L / 2))) =
      Real.exp (-ξ * radial_clockwise_distance L x y) +
        Real.exp (-ξ * radial_clockwise_distance L y x) -
        if x = y then 1 - Real.exp (-ξ * L) else 0 := by
  have hhalf : 0 < ξ * L / 2 := by positivity
  have hs : Real.sinh (ξ * L / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hhalf).ne'
  have hc : 1 - Real.exp (-ξ * L) ≠ 0 := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hξ hL))
    simpa only [neg_mul] using (sub_pos.mpr h).ne'
  have hcosh := radial_cosh_periodic_decay (ξ * L / 2) (ξ * |x - y|) hhalf
  have he₁ : ξ * L / 2 - ξ * |x - y| = ξ * (L / 2 - |x - y|) := by ring_nf
  have he₂ : -(2 * (ξ * L / 2)) + ξ * |x - y| = -ξ * (L - |x - y|) := by ring_nf
  have he₃ : -(2 * (ξ * L / 2)) = -ξ * L := by ring_nf
  rw [he₁, he₂, he₃] at hcosh
  have hcross := (div_eq_div_iff hs hc).mp hcosh
  have hbase : (2 * ξ * (1 - Real.exp (-ξ * L))) *
      (Real.cosh (ξ * (L / 2 - |x - y|)) / (2 * ξ * Real.sinh (ξ * L / 2))) =
      Real.exp (-ξ * |x - y|) + Real.exp (-ξ * (L - |x - y|)) := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (mul_ne_zero (by positivity : (2 : ℝ) * ξ ≠ 0) hs)).mpr
    calc
      _ = (2 * ξ) * (Real.cosh (ξ * (L / 2 - |x - y|)) *
          (1 - Real.exp (-ξ * L))) := by ring_nf
      _ = _ := by rw [hcross]; ring_nf
  rw [hbase]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero, mul_zero, Real.exp_zero, sub_zero, ite_true,
      radial_clockwise_distance, le_refl]
    ring_nf
  · rcases lt_or_gt_of_ne hxy with hlt | hlt
    · simp only [radial_clockwise_distance, if_neg (not_le.mpr hlt), if_pos hlt.le,
        abs_of_neg (sub_neg.mpr hlt), if_neg hxy, sub_zero]
      have he : L - -(x - y) = L + x - y := by ring_nf
      rw [he, neg_sub]
      ring_nf
    · simp only [radial_clockwise_distance, if_pos hlt.le, if_neg (not_le.mpr hlt),
        abs_of_pos (sub_pos.mpr hlt), if_neg hxy, sub_zero]
      rw [show L - (x - y) = L + y - x by ring_nf]
theorem radial_decay_recurrence_cauchy {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i < 1)
    (c : ℝ) (a w : ι → ℂ)
    (hrec : ∀ i, a (e i) = (q i : ℂ) * a i + (c : ℂ) * w (e i)) :
    c ^ 2 * ‖∑ i, w i‖ ^ 2 ≤
      (∑ i, (1 - q i) / (1 + q i)) * ∑ i, (1 - q i ^ 2) * ‖a i‖ ^ 2 := by
  let τ : ι → ℝ := fun i => (1 - q i) / (1 + q i)
  have hden (i : ι) : 0 < 1 + q i := by linarith [(hq i).1]
  have hτ (i : ι) : 0 ≤ τ i := (div_pos (sub_pos.mpr (hq i).2) (hden i)).le
  have hτmul (i : ι) : τ i * (1 + q i) = 1 - q i :=
    div_mul_cancel₀ _ (hden i).ne'
  have hs := congrArg (fun f : ι → ℂ => ∑ i, f i) (funext hrec)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [Equiv.sum_comp e a, Equiv.sum_comp e w] at hs
  have hsum : (∑ i, (τ i : ℂ) * (((1 + q i : ℝ) : ℂ) * a i)) =
      (c : ℂ) * ∑ i, w i := by
    calc
      _ = ∑ i, ((1 - q i : ℝ) : ℂ) * a i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_assoc, ← Complex.ofReal_mul, hτmul]
      _ = (∑ i, a i) - ∑ i, (q i : ℂ) * a i := by
        simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul,
          Finset.sum_sub_distrib]
      _ = _ := by rw [hs]; ring_nf
  have henergy : (∑ i, τ i * ‖((1 + q i : ℝ) : ℂ) * a i‖ ^ 2) =
      ∑ i, (1 - q i ^ 2) * ‖a i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hden i)]
    calc
      _ = (τ i * (1 + q i)) * ((1 + q i) * ‖a i‖ ^ 2) := by ring_nf
      _ = _ := by rw [hτmul]; ring_nf
  have h := radial_weighted_complex_sum_norm_sq_le Finset.univ τ
    (fun i _ => hτ i) (fun i => ((1 + q i : ℝ) : ℂ) * a i)
  rw [hsum, henergy] at h
  simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
noncomputable def radial_periodic_green_kernel (L ξ x y : ℝ) : ℝ :=
  Real.cosh (ξ * (L / 2 - |x - y|)) / (2 * ξ * Real.sinh (ξ * L / 2))
theorem radial_green_decay_quadratic {ι : Type*} [Fintype ι]
    (L ξ : ℝ) (hL : 0 < L) (hξ : 0 < ξ) (x : ι → ℝ)
    (hx : Function.Injective x) (w : ι → ℂ) :
    (2 * ξ * (1 - Real.exp (-ξ * L))) *
      (∑ i, ∑ j, star (w i) * w j * (radial_periodic_green_kernel L ξ (x i) (x j) : ℂ)).re =
      2 * (∑ i, star (w i) *
        ∑ j, (Real.exp (-ξ * radial_clockwise_distance L (x i) (x j)) : ℂ) * w j).re -
      (1 - Real.exp (-ξ * L)) * ∑ i, ‖w i‖ ^ 2 := by
  classical
  let H : ι → ι → ℝ := fun i j => (star (w i) * w j).re
  let M : ι → ι → ℝ := fun i j => Real.exp (-ξ * radial_clockwise_distance L (x i) (x j))
  let c : ℝ := 1 - Real.exp (-ξ * L)
  have hH (i j : ι) : H i j = H j i := by
    simp [H, Complex.mul_re]
    ring_nf
  have hdiag (i : ι) : H i i = ‖w i‖ ^ 2 := by
    simp [H, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]
  have hentry (i j : ι) : (2 * ξ * c) * radial_periodic_green_kernel L ξ (x i) (x j) =
      M i j + M j i - if i = j then c else 0 := by
    simpa only [radial_periodic_green_kernel, M, c, hx.eq_iff] using
      radial_green_decay_entry L ξ (x i) (x j) hL hξ
  have hB : (∑ i, star (w i) * ∑ j, (M i j : ℂ) * w j).re =
      ∑ i, ∑ j, H i j * M i j := by
    simp only [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_comm _ _
  have hQterm (i j : ι) :
      (star (w i) * w j * (radial_periodic_green_kernel L ξ (x i) (x j) : ℂ)).re =
        H i j * radial_periodic_green_kernel L ξ (x i) (x j) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  calc
    _ = ∑ i, ∑ j, H i j * ((2 * ξ * c) * radial_periodic_green_kernel L ξ (x i) (x j)) := by
      simp only [Complex.re_sum, hQterm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [c]
      ring_nf
    _ = 2 * (∑ i, ∑ j, H i j * M i j) - c * ∑ i, H i i := by
      simp_rw [hentry]
      exact radial_symmetric_decay_sum H M hH c
    _ = _ := by
      rw [← hB]
      simp only [hdiag]
      rfl
theorem radial_angular_green_energy_bound_of_strictMono {n : ℕ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hbound : ∀ i, x i ∈ Set.Ico 0 (2 * Real.pi))
    (ξ : ℝ) (hξ : 0 < ξ) (w : Fin (n + 1) → ℂ) :
    ‖∑ i, w i‖ ^ 2 ≤
      (2 * ξ * (n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) *
        (∑ i, ∑ j, star (w i) * w j *
          ((Real.cosh (ξ * (Real.pi - |x i - x j|)) /
            (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ)).re := by
  let L : ℝ := 2 * Real.pi
  let δ : Fin (n + 1) → ℝ := radial_cyclic_gap L x
  let e := finRotate (n + 1)
  let q : Fin (n + 1) → ℝ := fun i => Real.exp (-ξ * δ i)
  let c : ℝ := 1 - Real.exp (-ξ * L)
  let a : Fin (n + 1) → ℂ := fun i =>
    ∑ j, (Real.exp (-ξ * radial_clockwise_distance L (x i) (x j)) : ℂ) * w j
  let Q : ℝ := (∑ i, ∑ j, star (w i) * w j *
    ((Real.cosh (ξ * (Real.pi - |x i - x j|)) /
      (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ)).re
  let E : ℝ := ∑ i, (1 - q i ^ 2) * ‖a i‖ ^ 2
  have hL : 0 < L := mul_pos (by norm_num) Real.pi_pos
  have hc : 0 < c := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hξ) hL))
  have hδ (i : Fin (n + 1)) : 0 < δ i := radial_cyclic_gap_pos L x hx hbound i
  have hq (i : Fin (n + 1)) : 0 ≤ q i ∧ q i < 1 :=
    ⟨(Real.exp_pos _).le,
      Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hξ) (hδ i))⟩
  have hrec (i : Fin (n + 1)) : a (e i) = (q i : ℂ) * a i + (c : ℂ) * w (e i) :=
    radial_cyclic_decay_sum_step L x hx ξ w i
  have hEpos : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg _ (sq_nonneg _)
    have h := mul_nonneg (hq i).1 (sub_nonneg.mpr (hq i).2.le)
    nlinarith [(hq i).2]
  have hker (i j : Fin (n + 1)) : radial_periodic_green_kernel L ξ (x i) (x j) =
      Real.cosh (ξ * (Real.pi - |x i - x j|)) / (2 * ξ * Real.sinh (Real.pi * ξ)) := by
    dsimp only [radial_periodic_green_kernel, L]
    rw [show (2 * Real.pi) / 2 = Real.pi by ring_nf,
      show ξ * (2 * Real.pi) / 2 = Real.pi * ξ by ring_nf]
  have hquadratic := radial_green_decay_quadratic L ξ hL hξ x hx.injective w
  simp_rw [hker] at hquadratic
  change (2 * ξ * c) * Q =
    2 * (∑ i, star (w i) * a i).re - c * ∑ i, ‖w i‖ ^ 2 at hquadratic
  have hE : E = 2 * ξ * c ^ 2 * Q := by
    calc
      _ = 2 * c * (∑ i, star (w i) * a i).re - c ^ 2 * ∑ i, ‖w i‖ ^ 2 :=
        radial_decay_recurrence_energy e q c a w hrec
      _ = c * (2 * (∑ i, star (w i) * a i).re - c * ∑ i, ‖w i‖ ^ 2) := by ring_nf
      _ = c * ((2 * ξ * c) * Q) := by rw [hquadratic]
      _ = _ := by ring_nf
  have hτ (i : Fin (n + 1)) : (1 - q i) / (1 + q i) = Real.tanh (ξ * δ i / 2) := by
    simpa only [q, neg_mul] using (radial_tanh_half_exp (ξ * δ i)).symm
  have hmean : (∑ i, ξ * δ i / 2) = Real.pi * ξ := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [radial_cyclic_gap_sum L x]
    dsimp only [L]
    ring_nf
  have hsum : (∑ i, (1 - q i) / (1 + q i)) ≤
      (n + 1) * Real.tanh (Real.pi * ξ / (n + 1)) := by
    simp_rw [hτ]
    have h := radial_tanh_sum_le (Finset.univ : Finset (Fin (n + 1)))
      Finset.univ_nonempty (fun i => ξ * δ i / 2)
      (fun i _ => (div_pos (mul_pos hξ (hδ i)) (by norm_num)).le)
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one, hmean] using h
  have hCS := radial_decay_recurrence_cauchy e q hq c a w hrec
  have hbound' := hCS.trans (mul_le_mul_of_nonneg_right hsum hEpos)
  change ‖∑ i, w i‖ ^ 2 ≤
    (2 * ξ * (n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) * Q
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hc)).mp
  calc
    ‖∑ i, w i‖ ^ 2 * c ^ 2 = c ^ 2 * ‖∑ i, w i‖ ^ 2 := mul_comm _ _
    _ ≤ ((n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) * E := hbound'
    _ = ((n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) * (2 * ξ * c ^ 2 * Q) :=
      congrArg (fun T : ℝ => ((n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) * T) hE
    _ = ((2 * ξ * (n + 1) * Real.tanh (Real.pi * ξ / (n + 1))) * Q) * c ^ 2 := by ring_nf
theorem radial_angular_green_energy_bound (m : ℕ) (hm : 0 < m)
    (θ : Fin m → ℝ) (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (hinj : Function.Injective θ) (ξ : ℝ) (hξ : 0 < ξ) (w : Fin m → ℂ) :
    ‖∑ i, w i‖ ^ 2 ≤
      (2 * ξ * m * Real.tanh (Real.pi * ξ / m)) *
        (∑ i, ∑ j, star (w i) * w j *
          ((Real.cosh (ξ * (Real.pi - |θ i - θ j|)) /
            (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ)).re := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨e, he⟩ := radial_exists_strictMono_reindex θ hinj
  have h := radial_angular_green_energy_bound_of_strictMono (θ ∘ e) he
    (fun i => hθ (e i)) ξ hξ (w ∘ e)
  simp only [Function.comp_apply] at h
  rw [Equiv.sum_comp e w] at h
  have hsum : (∑ i, ∑ j, star (w (e i)) * w (e j) *
      ((Real.cosh (ξ * (Real.pi - |θ (e i) - θ (e j)|)) /
        (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ)) =
      ∑ i, ∑ j, star (w i) * w j *
        ((Real.cosh (ξ * (Real.pi - |θ i - θ j|)) /
          (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ) := by
    calc
      _ = ∑ i, ∑ j, star (w (e i)) * w j *
          ((Real.cosh (ξ * (Real.pi - |θ (e i) - θ j|)) /
            (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp e (fun j => star (w (e i)) * w j *
          ((Real.cosh (ξ * (Real.pi - |θ (e i) - θ j|)) /
            (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ))
      _ = _ := Equiv.sum_comp e (fun i => ∑ j, star (w i) * w j *
        ((Real.cosh (ξ * (Real.pi - |θ i - θ j|)) /
          (2 * ξ * Real.sinh (Real.pi * ξ)) : ℝ) : ℂ))
  rw [hsum] at h
  exact_mod_cast h
theorem radial_compact_uniform_strict_lower {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (f : ℕ → X → ℝ)
    (hf : ∀ n, Continuous (f n)) (hmono : ∀ x, Monotone (fun n => f n x))
    (c : ℝ) (hpoint : ∀ x, ∃ n, c < f n x) :
    ∃ N : ℕ, ∀ x, c < f N x := by
  classical
  let U : ℕ → Set X := fun n => {x | c < f n x}
  have hopen : ∀ n, IsOpen (U n) := fun n => isOpen_lt continuous_const (hf n)
  have hcover : (Set.univ : Set X) ⊆ ⋃ n, U n := by
    intro x hx
    obtain ⟨n, hn⟩ := hpoint x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨s.sup id, fun x => ?_⟩
  have hx := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion, U, Set.mem_ofPred_eq] at hx
  obtain ⟨n, hn, hcx⟩ := hx
  exact hcx.trans_le (hmono x (Finset.le_sup (f := id) hn))
theorem radial_truncated_log_energy_continuous {E : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace E] [SecondCountableTopology E] (M : ℝ) :
    Continuous (fun μ : MeasureTheory.ProbabilityMeasure E =>
      ∫ z : E × E, -Real.log (max (Real.exp (-M)) (dist z.1 z.2)) ∂(μ.prod μ)) := by
  let K : C(E × E, ℝ) := ⟨fun z => -Real.log (max (Real.exp (-M)) (dist z.1 z.2)),
    ((continuous_const.max (continuous_fst.dist continuous_snd)).log
      (fun z => ne_of_gt ((Real.exp_pos (-M)).trans_le (le_max_left _ _)))).neg⟩
  have hprod : Continuous (fun μ : MeasureTheory.ProbabilityMeasure E => μ.prod μ) :=
    MeasureTheory.ProbabilityMeasure.continuous_prod.comp
      (continuous_id.prodMk continuous_id)
  exact (MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap K).comp hprod
theorem radial_probability_uniform_truncated_energy_of_pointwise {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace E] [SecondCountableTopology E] (c : ℝ)
    (hpoint : ∀ μ : MeasureTheory.ProbabilityMeasure E, ∃ N : ℕ,
      c < ∫ z : E × E,
        -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ)) :
    ∃ N : ℕ, ∀ μ : MeasureTheory.ProbabilityMeasure E,
      c < ∫ z : E × E,
        -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ) := by
  let K (n : ℕ) : C(E × E, ℝ) := ⟨fun z =>
      -Real.log (max (Real.exp (-(n : ℝ))) (dist z.1 z.2)),
    ((continuous_const.max (continuous_fst.dist continuous_snd)).log
      (fun z => ne_of_gt ((Real.exp_pos (-(n : ℝ))).trans_le
        (le_max_left _ _)))).neg⟩
  apply radial_compact_uniform_strict_lower
    (fun n (μ : MeasureTheory.ProbabilityMeasure E) => ∫ z : E × E, K n z ∂(μ.prod μ))
    (fun n => radial_truncated_log_energy_continuous (n : ℝ)) _ c hpoint
  intro μ n m hnm
  apply MeasureTheory.integral_mono
    ((ContinuousMap.equivBoundedOfCompact _ _ (K n)).integrable _)
    ((ContinuousMap.equivBoundedOfCompact _ _ (K m)).integrable _)
  intro z
  apply neg_le_neg
  apply Real.log_le_log ((Real.exp_pos (-(m : ℝ))).trans_le (le_max_left _ _))
  apply max_le_max_right
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (by exact_mod_cast hnm)
theorem radial_empirical_product_integral {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [CompactSpace E]
    {n : ℕ} (hn : 0 < n) (z : Fin n → E) (K : C(E × E, ℝ)) :
    ∃ μ : MeasureTheory.ProbabilityMeasure E,
      (∫ p : E × E, K p ∂(μ.prod μ)) =
        ((n : ℝ)⁻¹) ^ 2 * ∑ i : Fin n, ∑ j : Fin n, K (z i, z j) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let u : PMF (Fin n) := PMF.uniformOfFintype (Fin n)
  let μ : MeasureTheory.ProbabilityMeasure E := ⟨(u.map z).toMeasure, inferInstance⟩
  have hmean (g : C(E, ℝ)) : (∫ x, g x ∂μ) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, g (z i) := by
    change (∫ x, g x ∂(u.map z).toMeasure) = _
    rw [← PMF.toMeasure_map z u (measurable_of_finite z),
      MeasureTheory.integral_map (measurable_of_finite z).aemeasurable
        g.continuous.measurable.aestronglyMeasurable, PMF.integral_eq_sum]
    simp only [u, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  have hinner (x : E) : (∫ y, K (x, y) ∂μ) =
      (n : ℝ)⁻¹ * ∑ j : Fin n, K (x, z j) :=
    hmean ⟨fun y => K (x, y), K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have houter (j : Fin n) : (∫ x, K (x, z j) ∂μ) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, K (z i, z j) :=
    hmean ⟨fun x => K (x, z j), K.continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨μ, ?_⟩
  have hK : MeasureTheory.Integrable (fun p : E × E => K p)
      ((μ : MeasureTheory.Measure E).prod (μ : MeasureTheory.Measure E)) :=
    (ContinuousMap.equivBoundedOfCompact _ _ K).integrable _
  change (∫ p : E × E, K p ∂((μ : MeasureTheory.Measure E).prod
    (μ : MeasureTheory.Measure E))) = _
  rw [MeasureTheory.integral_prod _ hK]
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
  · simp_rw [houter]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring
  · intro j hj
    exact (ContinuousMap.equivBoundedOfCompact _ _
      (⟨fun x => K (x, z j),
        K.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(E, ℝ))).integrable _
theorem radial_finite_truncated_energy_of_probability_bound {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [CompactSpace E]
    (M c : ℝ)
    (hbound : ∀ μ : MeasureTheory.ProbabilityMeasure E,
      c < ∫ p : E × E, -Real.log (max (Real.exp (-M)) (dist p.1 p.2)) ∂(μ.prod μ)) :
    ∀ (n : ℕ) (z : Fin n → E),
      (n : ℝ) ^ 2 * c ≤ ∑ i : Fin n, ∑ j : Fin n,
        -Real.log (max (Real.exp (-M)) (dist (z i) (z j))) := by
  intro n z
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  let K : C(E × E, ℝ) := ⟨fun p =>
      -Real.log (max (Real.exp (-M)) (dist p.1 p.2)),
    ((continuous_const.max (continuous_fst.dist continuous_snd)).log
      (fun p => ne_of_gt ((Real.exp_pos (-M)).trans_le (le_max_left _ _)))).neg⟩
  obtain ⟨μ, hμ⟩ := radial_empirical_product_integral hnpos z K
  have h := hbound μ
  change c < ∫ p : E × E, K p ∂(μ.prod μ) at h
  rw [hμ] at h
  have hmul := mul_lt_mul_of_pos_left h (sq_pos_of_pos hnreal)
  have hcancel : (n : ℝ) ^ 2 * ((n : ℝ)⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hnreal.ne', one_pow]
  rw [← mul_assoc, hcancel, one_mul] at hmul
  exact hmul.le
theorem even_odd_polynomial_decomposition (F : Polynomial ℤ) :
    F = (Polynomial.contract 2 F).comp (Polynomial.X ^ 2) +
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)).comp (Polynomial.X ^ 2) := by
  change F = Polynomial.expand ℤ 2 (Polynomial.contract 2 F) +
    Polynomial.X * Polynomial.expand ℤ 2 (Polynomial.contract 2 (Polynomial.divX F))
  ext n
  rw [Polynomial.coeff_add]
  cases n with
  | zero =>
      simp [Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ)),
        Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  | succ n =>
      rw [Polynomial.coeff_X_mul,
        Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ)),
        Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
      by_cases hn : 2 ∣ n
      · have hs : ¬ 2 ∣ n + 1 := by omega
        simp only [if_neg hs, if_pos hn, zero_add,
          Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
          Polynomial.coeff_divX]
        congr 1
        omega
      · have hs : 2 ∣ n + 1 := by omega
        simp only [if_pos hs, if_neg hn, add_zero,
          Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
        congr 1
        omega
theorem even_odd_power_transform_subst (F : Polynomial ℤ) :
    (((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).comp
        (Polynomial.X ^ 2)) = F * F.comp (-Polynomial.X) := by
  let A := Polynomial.contract 2 F
  let B := Polynomial.contract 2 (Polynomial.divX F)
  have hF : F = A.comp (Polynomial.X ^ 2) +
      Polynomial.X * B.comp (Polynomial.X ^ 2) := even_odd_polynomial_decomposition F
  have hneg : F.comp (-Polynomial.X) = A.comp (Polynomial.X ^ 2) -
      Polynomial.X * B.comp (Polynomial.X ^ 2) := by
    calc
      _ = (A.comp (Polynomial.X ^ 2) +
          Polynomial.X * B.comp (Polynomial.X ^ 2)).comp (-Polynomial.X) :=
        congrArg (fun P : Polynomial ℤ => P.comp (-Polynomial.X)) hF
      _ = _ := by
        simp only [Polynomial.add_comp, Polynomial.mul_comp,
          Polynomial.comp_assoc, Polynomial.pow_comp, Polynomial.X_comp, neg_sq]
        ring
  change (A ^ 2 - Polynomial.X * B ^ 2).comp (Polynomial.X ^ 2) = _
  calc
    _ = (A.comp (Polynomial.X ^ 2) + Polynomial.X * B.comp (Polynomial.X ^ 2)) *
        (A.comp (Polynomial.X ^ 2) - Polynomial.X * B.comp (Polynomial.X ^ 2)) := by
      simp only [Polynomial.sub_comp, Polynomial.pow_comp,
        Polynomial.mul_comp, Polynomial.X_comp]
      ring
    _ = F * F.comp (-Polynomial.X) := congrArg₂ (fun P Q : Polynomial ℤ => P * Q)
      hF.symm hneg.symm
theorem radial_resolvent_int_summable (ξ : ℝ) :
    Summable (fun n : ℤ => 1 / (ξ ^ 2 + (n : ℝ) ^ 2)) := by
  have h := Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))
  apply h.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le
  · exact sq_pos_of_ne_zero (by exact_mod_cast hn)
  · exact le_add_of_nonneg_left (sq_nonneg ξ)
theorem radial_exp_int_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-a * |(n : ℝ)|)) := by
  have h : Summable (fun n : ℕ => Real.exp (-a * (n : ℝ))) := by
    convert summable_geometric_of_lt_one (Real.exp_pos (-a)).le
      (Real.exp_lt_one_iff.mpr (by linarith : -a < 0)) using 1
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  apply Summable.of_nat_of_neg
  · exact h.congr (fun n => by simp)
  · exact h.congr (fun n => by simp)
theorem radial_exp_periodic_norm_summable (a : ℝ) (ha : 0 < a)
    (f : C(ℝ, ℂ)) (hf : ∀ x : ℝ, f x = Complex.exp (-a * |x| : ℝ))
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : ℝ)
  apply ((radial_exp_int_summable a ha).mul_left (Real.exp (a * R))).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => ?_)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro y
  change ‖f ((y : ℝ) + (n : ℝ))‖ ≤ _
  rw [hf, Complex.norm_exp, Complex.ofReal_re, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hy : |(y : ℝ)| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hR y.property
  have hn : |(n : ℝ)| ≤ |(y : ℝ) + (n : ℝ)| + R := by
    calc
      _ = |((y : ℝ) + (n : ℝ)) - (y : ℝ)| := by congr 1; ring
      _ ≤ |(y : ℝ) + (n : ℝ)| + |(y : ℝ)| := by
        simpa using (abs_sub_le ((y : ℝ) + (n : ℝ)) 0 (y : ℝ))
      _ ≤ _ := add_le_add (le_refl _) hy
  nlinarith
theorem radial_exp_abs_fourier_scaled (ξ : ℝ) (hξ : 0 < ξ) (v : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ => Complex.exp (- (2 * Real.pi * ξ) * |x| : ℝ)) v =
      ((ξ / Real.pi : ℝ) : ℂ) / ((ξ ^ 2 + v ^ 2 : ℝ) : ℂ) := by
  rw [radial_exp_abs_fourier (2 * Real.pi * ξ) (by positivity)]
  have hd : (ξ : ℂ) ^ 2 + (v : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < ξ ^ 2 + v ^ 2 by positivity))
  have hd' : (2 * (Real.pi : ℂ) * (ξ : ℂ)) ^ 2 +
      (2 * (Real.pi : ℂ) * (v : ℂ)) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < (2 * Real.pi * ξ) ^ 2 +
      (2 * Real.pi * v) ^ 2 by positivity))
  push_cast
  field_simp [hd, hd', Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
theorem radial_exp_periodization (a x : ℝ) (ha : 0 < a)
    (hx : 0 ≤ x) (hx' : x ≤ 1) :
    (∑' n : ℤ, Real.exp (-a * |x + (n : ℝ)|)) =
      (Real.exp (-a * x) + Real.exp (-a + a * x)) / (1 - Real.exp (-a)) := by
  let q := Real.exp (-a)
  let g : ℤ → ℝ := fun n => Real.exp (-a * |x + (n : ℝ)|)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hnat (n : ℕ) : g n = Real.exp (-a * x) * q ^ n := by
    dsimp only [g, q]
    rw [Int.cast_natCast, abs_of_nonneg (by positivity),
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hneg (n : ℕ) : g (-(n + 1)) = Real.exp (-a + a * x) * q ^ n := by
    dsimp only [g, q]
    push_cast
    rw [abs_of_nonpos (by linarith [show 0 ≤ (n : ℝ) by positivity]),
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hn : Summable (fun n : ℕ => g n) :=
    (hq.mul_left (Real.exp (-a * x))).congr (fun n => (hnat n).symm)
  have hm : Summable (fun n : ℕ => g (-(n + 1))) :=
    (hq.mul_left (Real.exp (-a + a * x))).congr (fun n => (hneg n).symm)
  change (∑' n : ℤ, g n) = _
  rw [tsum_of_nat_of_neg_add_one hn hm]
  simp_rw [hnat, hneg]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  dsimp only [q]
  ring
theorem radial_cos_resolvent_summable (ξ θ : ℝ) (hξ : 0 < ξ) :
    Summable (fun n : ℤ => Real.cos ((n : ℝ) * θ) / (ξ ^ 2 + (n : ℝ) ^ 2)) := by
  apply (radial_resolvent_int_summable ξ).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_div,
    abs_of_pos (show 0 < ξ ^ 2 + (n : ℝ) ^ 2 by positivity)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
theorem radial_resolvent_periodization (ξ x : ℝ) (hξ : 0 < ξ) :
    (ξ / Real.pi) *
      (∑' n : ℤ, Real.cos (2 * Real.pi * (n : ℝ) * x) / (ξ ^ 2 + (n : ℝ) ^ 2)) =
      ∑' n : ℤ, Real.exp (-(2 * Real.pi * ξ) * |x + (n : ℝ)|) := by
  let f : C(ℝ, ℂ) := ⟨fun t : ℝ =>
    Complex.exp (-(2 * Real.pi * ξ) * |t| : ℝ), by fun_prop⟩
  have hcoef (n : ℤ) : FourierTransform.fourier (f : ℝ → ℂ) (n : ℝ) =
      ((ξ / Real.pi : ℝ) : ℂ) / ((ξ ^ 2 + (n : ℝ) ^ 2 : ℝ) : ℂ) :=
    radial_exp_abs_fourier_scaled ξ hξ n
  have hc : Summable (fun n : ℤ => (ξ / Real.pi) / (ξ ^ 2 + (n : ℝ) ^ 2)) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (radial_resolvent_int_summable ξ).mul_left (ξ / Real.pi)
  have hs : Summable (fun n : ℤ => FourierTransform.fourier (f : ℝ → ℂ) (n : ℝ)) := by
    apply hc.of_norm_bounded
    intro n
    rw [hcoef, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hsphase : Summable (fun n : ℤ =>
      FourierTransform.fourier (f : ℝ → ℂ) (n : ℝ) * fourier n (x : UnitAddCircle)) := by
    apply hc.of_norm_bounded
    intro n
    rw [hcoef, norm_mul, fourier_apply, Circle.norm_coe, mul_one,
      ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hpoint (n : ℤ) :
      (FourierTransform.fourier (f : ℝ → ℂ) (n : ℝ) * fourier n (x : UnitAddCircle)).re =
      (ξ / Real.pi) * (Real.cos (2 * Real.pi * (n : ℝ) * x) /
        (ξ ^ 2 + (n : ℝ) ^ 2)) := by
    rw [hcoef, fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]
    have hangle : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) =
        ((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hangle, ← Complex.ofReal_div]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    ring
  have hp := Real.tsum_eq_tsum_fourier (f := f)
    (fun K => radial_exp_periodic_norm_summable (2 * Real.pi * ξ) (by positivity)
      f (fun _ => rfl) K) hs x
  have hre := congrArg Complex.re hp
  have hleft : (∑' n : ℤ, f (x + (n : ℝ))).re =
      ∑' n : ℤ, Real.exp (-(2 * Real.pi * ξ) * |x + (n : ℝ)|) := by
    change (∑' n : ℤ, Complex.exp (-(2 * Real.pi * ξ) * |x + (n : ℝ)| : ℝ)).re = _
    simp_rw [← Complex.ofReal_exp]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hleft, Complex.re_tsum hsphase] at hre
  simp_rw [hpoint] at hre
  rw [tsum_mul_left] at hre
  exact hre.symm
theorem radial_green_fourier_series (ξ θ : ℝ) (hξ : 0 < ξ)
    (hθ : θ ∈ Set.Icc (-2 * Real.pi) (2 * Real.pi)) :
    Summable (fun n : ℤ => Real.cos ((n : ℝ) * θ) / (ξ ^ 2 + (n : ℝ) ^ 2)) ∧
      (∑' n : ℤ, Real.cos ((n : ℝ) * θ) / (ξ ^ 2 + (n : ℝ) ^ 2)) =
        Real.pi * Real.cosh (ξ * (Real.pi - |θ|)) / (ξ * Real.sinh (Real.pi * ξ)) := by
  refine ⟨radial_cos_resolvent_summable ξ θ hξ, ?_⟩
  let x := |θ| / (2 * Real.pi)
  have hx : 0 ≤ x := by positivity
  have hθabs : |θ| ≤ 2 * Real.pi := abs_le.mpr ⟨by nlinarith [hθ.1], hθ.2⟩
  have hx' : x ≤ 1 := (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hθabs
  have hm : (2 * Real.pi * ξ) * x = ξ * |θ| := by
    dsimp only [x]
    field_simp [Real.pi_ne_zero]
  have hrate : 2 * Real.pi * ξ = 2 * (Real.pi * ξ) := by ring
  have hcos (n : ℤ) : Real.cos (2 * Real.pi * (n : ℝ) * x) =
      Real.cos ((n : ℝ) * θ) := by
    have hn : 2 * Real.pi * (n : ℝ) * x = (n : ℝ) * |θ| := by
      dsimp only [x]
      field_simp [Real.pi_ne_zero]
    rw [hn]
    by_cases hθ0 : 0 ≤ θ
    · rw [abs_of_nonneg hθ0]
    · rw [abs_of_neg (lt_of_not_ge hθ0), mul_neg, Real.cos_neg]
  have hp := radial_resolvent_periodization ξ x hξ
  rw [radial_exp_periodization (2 * Real.pi * ξ) x (by positivity) hx hx'] at hp
  simp_rw [hcos] at hp
  have hhyper :
      (Real.exp (-(2 * Real.pi * ξ) * x) +
        Real.exp (-(2 * Real.pi * ξ) + (2 * Real.pi * ξ) * x)) /
          (1 - Real.exp (-(2 * Real.pi * ξ))) =
      Real.cosh (ξ * (Real.pi - |θ|)) / Real.sinh (Real.pi * ξ) := by
    rw [show ξ * (Real.pi - |θ|) = Real.pi * ξ - ξ * |θ| by ring,
      radial_cosh_periodic_decay (Real.pi * ξ) (ξ * |θ|) (by positivity)]
    rw [neg_mul, hm, hrate]
  have hscale := hp.trans hhyper
  have hsinh : Real.sinh (Real.pi * ξ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * ξ)).ne'
  field_simp [hξ.ne', Real.pi_ne_zero, hsinh] at hscale ⊢
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hscale
theorem adjoin_power_degree_le_two {K : Type*} [Field K] [NumberField K] (α : K) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ≤
      2 * Module.finrank ℚ (IntermediateField.adjoin ℚ {α ^ 2}) := by
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {α}
  let F : IntermediateField ℚ K := IntermediateField.adjoin ℚ {α ^ 2}
  let : Algebra ℚ E := E.algebra'
  let : Algebra ℚ F := F.algebra'
  have hFE : F ≤ E := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa only [pow_two] using E.mul_mem
      (IntermediateField.mem_adjoin_simple_self ℚ α)
      (IntermediateField.mem_adjoin_simple_self ℚ α)
  let : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  let : IsScalarTower ℚ F E := IsScalarTower.of_algHom (IntermediateField.inclusion hFE)
  let : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_left E
  let : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_left F
  let : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  let a : E := IntermediateField.AdjoinSimple.gen ℚ α
  let b : F := IntermediateField.AdjoinSimple.gen ℚ (α ^ 2)
  have hprim : IntermediateField.adjoin ℚ {a} = ⊤ := by
    apply IntermediateField.lift_injective E
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  have hquad : Polynomial.aeval a (Polynomial.X ^ 2 - Polynomial.C b) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    apply Subtype.ext
    change α ^ 2 - α ^ 2 = 0
    exact sub_self _
  have hupper : Module.finrank F E ≤ 2 := by
    have hdegree := IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)
    rw [IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ hprim,
      IntermediateField.finrank_top'] at hdegree
    rw [hdegree]
    have hbound := Polynomial.natDegree_le_natDegree
      (minpoly.min F a (Polynomial.monic_X_pow_sub_C b (by decide : (2 : ℕ) ≠ 0)) hquad)
    simpa only [Polynomial.natDegree_X_pow_sub_C] using hbound
  change Module.finrank ℚ E ≤ 2 * Module.finrank ℚ F
  rw [← Module.finrank_mul_finrank ℚ F E]
  calc
    Module.finrank ℚ F * Module.finrank F E ≤ Module.finrank ℚ F * 2 :=
      Nat.mul_le_mul_left _ hupper
    _ = 2 * Module.finrank ℚ F := Nat.mul_comm _ _
theorem even_odd_power_transform_coeff_zero (F : Polynomial ℤ) :
    ((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).coeff 0 =
      F.coeff 0 ^ 2 := by
  simp [pow_two, Polynomial.mul_coeff_zero, Polynomial.coeff_contract]
theorem even_odd_power_transform_mod_two (F : Polynomial ℤ) :
    ∃ H : Polynomial ℤ,
      (Polynomial.contract 2 F) ^ 2 -
        Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2 = F + 2 * H := by
  let T : Polynomial ℤ → Polynomial ℤ := fun P =>
    (Polynomial.contract 2 P) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX P)) ^ 2
  let f := Int.castRingHom (ZMod 2)
  have hneg : -(Polynomial.X : Polynomial (ZMod 2)) = Polynomial.X := by
    ext n
    simp only [Polynomial.coeff_neg]
    exact ZMod.neg_eq_self_mod_two _
  have hsubst := congrArg (fun P : Polynomial ℤ => P.map f)
    (even_odd_power_transform_subst F)
  change ((T F).comp (Polynomial.X ^ 2)).map f = (F * F.comp (-Polynomial.X)).map f
    at hsubst
  simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_neg, hneg, Polynomial.comp_X] at hsubst
  have hmap : (T F).map f = F.map f := by
    apply Polynomial.expand_injective (by norm_num : 0 < (2 : ℕ))
    change ((T F).map f).comp (Polynomial.X ^ 2) =
      (F.map f).comp (Polynomial.X ^ 2)
    rw [hsubst, ← pow_two]
    simpa only [ZMod.frobenius_zmod, Polynomial.map_id,
      Polynomial.expand_eq_comp_X_pow] using
      (Polynomial.map_frobenius_expand 2 (F.map f)).symm
  have hzero : (T F - F).map f = 0 := by
    rw [Polynomial.map_sub, hmap, sub_self]
  have hdiv : Polynomial.C (2 : ℤ) ∣ T F - F := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro n
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ((T F - F).coeff n) 2).mp
    have hc := congrArg (fun P : Polynomial (ZMod 2) => P.coeff n) hzero
    simpa only [Polynomial.coeff_map, f, Int.coe_castRingHom, Polynomial.coeff_zero] using hc
  obtain ⟨H, hH⟩ := hdiv
  refine ⟨H, ?_⟩
  change T F = F + 2 * H
  simpa only [Polynomial.C_ofNat, add_comm] using (sub_eq_iff_eq_add.mp hH)
theorem even_odd_power_transform_add_twice (F H : Polynomial ℤ) :
    let T : Polynomial ℤ → Polynomial ℤ := fun P =>
      (Polynomial.contract 2 P) ^ 2 -
        Polynomial.X * (Polynomial.contract 2 (Polynomial.divX P)) ^ 2
    let A := Polynomial.contract 2 F
    let B := Polynomial.contract 2 (Polynomial.divX F)
    let E := Polynomial.contract 2 H
    let D := Polynomial.contract 2 (Polynomial.divX H)
    T (F + 2 * H) = T F + 4 * (A * E + E ^ 2 - Polynomial.X * (B * D + D ^ 2)) := by
  dsimp only
  have hA : Polynomial.contract 2 (F + 2 * H) =
      Polynomial.contract 2 F + 2 * Polynomial.contract 2 H := by
    ext n
    simp [Polynomial.coeff_contract]
  have hB : Polynomial.contract 2 (Polynomial.divX (F + 2 * H)) =
      Polynomial.contract 2 (Polynomial.divX F) +
        2 * Polynomial.contract 2 (Polynomial.divX H) := by
    ext n
    simp [Polynomial.coeff_contract, Polynomial.coeff_divX]
  rw [hA, hB]
  ring
theorem even_odd_power_transform_mod_four (F : Polynomial ℤ) (hF : F.coeff 0 = 1) :
    let T : Polynomial ℤ → Polynomial ℤ := fun P =>
      (Polynomial.contract 2 P) ^ 2 -
        Polynomial.X * (Polynomial.contract 2 (Polynomial.divX P)) ^ 2
    ∃ Q : Polynomial ℤ, T (T F) = T F + 4 * Q ∧ Q.coeff 0 = 0 := by
  let T : Polynomial ℤ → Polynomial ℤ := fun P =>
    (Polynomial.contract 2 P) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX P)) ^ 2
  change ∃ Q : Polynomial ℤ, T (T F) = T F + 4 * Q ∧ Q.coeff 0 = 0
  obtain ⟨H, hH⟩ := even_odd_power_transform_mod_two F
  change T F = F + 2 * H at hH
  have hH0 : H.coeff 0 = 0 := by
    have hc := congrArg (fun P : Polynomial ℤ => P.coeff 0) hH
    change (T F).coeff 0 = (F + 2 * H).coeff 0 at hc
    rw [even_odd_power_transform_coeff_zero, hF] at hc
    simp only [one_pow, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, hF] at hc
    omega
  let Q := Polynomial.contract 2 F * Polynomial.contract 2 H +
    (Polynomial.contract 2 H) ^ 2 - Polynomial.X *
      (Polynomial.contract 2 (Polynomial.divX F) *
        Polynomial.contract 2 (Polynomial.divX H) +
          (Polynomial.contract 2 (Polynomial.divX H)) ^ 2)
  refine ⟨Q, ?_, ?_⟩
  · calc
      T (T F) = T (F + 2 * H) := congrArg T hH
      _ = T F + 4 * Q := even_odd_power_transform_add_twice F H
  · simp [Q, pow_two, Polynomial.mul_coeff_zero, Polynomial.coeff_contract, hH0]
theorem minpoly_sq_degree_dichotomy {K : Type*} [Field K] [NumberField K] (α : K) :
    (minpoly ℚ α).natDegree = (minpoly ℚ (α ^ 2)).natDegree ∨
      (minpoly ℚ α).natDegree = 2 * (minpoly ℚ (α ^ 2)).natDegree := by
  have hFE : IntermediateField.adjoin ℚ {α ^ 2} ≤ IntermediateField.adjoin ℚ {α} := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa only [pow_two] using (IntermediateField.adjoin ℚ {α}).mul_mem
      (IntermediateField.mem_adjoin_simple_self ℚ α)
      (IntermediateField.mem_adjoin_simple_self ℚ α)
  have hE := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α)
  have hF := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ (α ^ 2))
  have hdvd := IntermediateField.finrank_dvd_of_le_right hFE
  have hbound := adjoin_power_degree_le_two α
  rw [hE, hF] at hdvd hbound
  have hpos := minpoly.natDegree_pos (IsIntegral.of_finite ℚ α)
  have hposSq := minpoly.natDegree_pos (IsIntegral.of_finite ℚ (α ^ 2))
  obtain ⟨r, hr⟩ := hdvd
  have hrpos : 0 < r := by
    by_contra h
    have hrzero : r = 0 := by omega
    rw [hr, hrzero, mul_zero] at hpos
    exact (lt_irrefl (0 : ℕ)) hpos
  have hrle : r ≤ 2 := by
    have hmul : (minpoly ℚ (α ^ 2)).natDegree * r ≤
        (minpoly ℚ (α ^ 2)).natDegree * 2 := by
      simpa only [hr, Nat.mul_comm] using hbound
    exact le_of_mul_le_mul_left hmul hposSq
  have hcases : r = 1 ∨ r = 2 := by omega
  rcases hcases with h | h
  · left
    simpa only [h, mul_one] using hr
  · right
    simpa only [h, Nat.mul_comm] using hr
theorem minpoly_sq_comp_of_degree_drop {K : Type*} [Field K] [NumberField K]
    (α : K) (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree) :
    (minpoly ℚ (α ^ 2)).comp (Polynomial.X ^ 2) = minpoly ℚ α := by
  have hα := IsIntegral.of_finite ℚ α
  have hαsq := IsIntegral.of_finite ℚ (α ^ 2)
  have hdegree : (minpoly ℚ α).natDegree = 2 * (minpoly ℚ (α ^ 2)).natDegree := by
    rcases minpoly_sq_degree_dichotomy α with h | h
    · omega
    · exact h
  have hmonic : ((minpoly ℚ (α ^ 2)).comp (Polynomial.X ^ 2)).Monic :=
    (minpoly.monic hαsq).comp (Polynomial.monic_X_pow 2) (by simp)
  apply minpoly.unique_of_degree_le_degree_minpoly ℚ α hmonic
  · simpa only [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] using
      minpoly.aeval ℚ (α ^ 2)
  · rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero hα),
      Polynomial.natDegree_comp, Polynomial.natDegree_X_pow, hdegree]
    simp only [Nat.mul_comm, le_refl]
theorem exists_embedding_neg_of_degree_drop {K : Type*} [Field K] [NumberField K]
    (α : K) (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree)
    (σ : K →+* ℂ) : ∃ τ : K →+* ℂ, τ α = -(σ α) := by
  have hcomp := minpoly_sq_comp_of_degree_drop α hdrop
  have hroot : Polynomial.aeval (-(σ α)) (minpoly ℚ α) = 0 := by
    have hσ := minpoly.aeval_algHom ℚ σ.toRatAlgHom α
    rw [← hcomp, Polynomial.aeval_comp] at hσ ⊢
    simpa only [map_pow, Polynomial.aeval_X, neg_sq, RingHom.toRatAlgHom_apply] using hσ
  have hmem : -(σ α) ∈ (minpoly ℚ α).rootSet ℂ :=
    Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero (IsIntegral.of_finite ℚ α), hroot⟩
  rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α] at hmem
  exact hmem
theorem angle_card_double_of_antipodal (s : Finset Real.Angle)
    (hclosed : ∀ θ ∈ s, θ + (Real.pi : Real.Angle) ∈ s) :
    2 * (@Finset.image Real.Angle Real.Angle (Classical.decEq _)
      (fun θ => (2 : ℕ) • θ) s).card = s.card := by
  classical
  have hfiber : ∀ β ∈ s.image (fun θ => (2 : ℕ) • θ),
      (s.filter fun θ => (2 : ℕ) • θ = β).card = 2 := by
    intro β hβ
    obtain ⟨θ, hθ, hθβ⟩ := Finset.mem_image.mp hβ
    have hpair : s.filter (fun ψ => (2 : ℕ) • ψ = β) =
        {θ, θ + (Real.pi : Real.Angle)} := by
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hψ⟩
        exact Real.Angle.two_nsmul_eq_iff.mp (hψ.trans hθβ.symm)
      · rintro (rfl | rfl)
        · exact ⟨hθ, hθβ⟩
        · refine ⟨hclosed θ hθ, ?_⟩
          simpa only [smul_add, Real.Angle.two_nsmul_coe_pi, add_zero] using hθβ
    rw [hpair]
    apply Finset.card_pair
    intro h
    apply Real.Angle.pi_ne_zero
    simpa using congrArg (fun ψ : Real.Angle => -θ + ψ) h.symm
  have hcount := Finset.card_eq_sum_card_image (fun θ : Real.Angle => (2 : ℕ) • θ) s
  rw [Finset.sum_const_nat hfiber] at hcount
  simpa only [Nat.mul_comm] using hcount.symm
theorem embedding_angle_card {K : Type*} [Field K] [NumberField K] (α : K) :
    (@Finset.image (K →+* ℂ) Real.Angle (Classical.decEq _)
      (fun σ => ((σ α).arg : Real.Angle)) Finset.univ).card =
      (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card := by
  classical
  have h := Finset.card_image_of_injective
    (Finset.univ.image fun σ : K →+* ℂ => ((σ α).arg : Real.Angle))
    Real.Angle.toReal_injective
  rw [Finset.image_image] at h
  simpa only [Function.comp_def, Complex.arg_coe_angle_toReal_eq_arg] using h.symm
theorem argument_card_sq_of_degree_drop {K : Type*} [Field K] [NumberField K]
    (α : K) (hα : α ≠ 0)
    (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree) :
    2 * (Finset.univ.image fun σ : K →+* ℂ ↦ (σ (α ^ 2)).arg).card =
      (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card := by
  classical
  let s : Finset Real.Angle :=
    Finset.univ.image fun σ : K →+* ℂ => ((σ α).arg : Real.Angle)
  have hclosed : ∀ θ ∈ s, θ + (Real.pi : Real.Angle) ∈ s := by
    intro θ hθ
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨τ, hτ⟩ := exists_embedding_neg_of_degree_drop α hdrop σ
    apply Finset.mem_image.mpr
    refine ⟨τ, Finset.mem_univ τ, ?_⟩
    rw [hτ]
    exact Complex.arg_neg_coe_angle ((map_ne_zero σ).mpr hα)
  have himage :
      (Finset.univ.image fun σ : K →+* ℂ => ((σ (α ^ 2)).arg : Real.Angle)) =
        s.image (fun θ => (2 : ℕ) • θ) := by
    dsimp only [s]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro σ _
    change ((σ (α ^ 2)).arg : Real.Angle) = (2 : ℕ) • ((σ α).arg : Real.Angle)
    rw [map_pow]
    exact Complex.arg_pow_coe_angle (σ α) 2
  have hcount := angle_card_double_of_antipodal s hclosed
  rw [← himage, embedding_angle_card (α ^ 2)] at hcount
  change 2 * (Finset.univ.image fun σ : K →+* ℂ => (σ (α ^ 2)).arg).card =
    (Finset.univ.image fun σ : K →+* ℂ => ((σ α).arg : Real.Angle)).card at hcount
  rw [embedding_angle_card α] at hcount
  exact hcount
theorem polynomial_eq_of_monic_irreducible_mul_eq_sq
    {k : Type*} [Field k] {P Q G : Polynomial k}
    (hP : P.Monic) (hPirr : Irreducible P) (hQ : Q.Monic)
    (hdegree : Q.natDegree = P.natDegree) (hsq : G ^ 2 = P * Q) : Q = P := by
  have hPG : P ∣ G := hPirr.prime.dvd_of_dvd_pow (by
    rw [hsq]
    exact dvd_mul_right P Q)
  have hP2 : P ^ 2 ∣ G ^ 2 := pow_dvd_pow_of_dvd hPG 2
  have hPQ : P ∣ Q := (mul_dvd_mul_iff_left hP.ne_zero).mp (by
    simpa only [pow_two, hsq] using hP2)
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hP hQ hPQ hdegree.le
theorem polynomial_reverse_eq_of_monic_irreducible_mul_eq_sq
    {k : Type*} [Field k] {P Q G : Polynomial k}
    (hP : P.reverse.Monic) (hPirr : Irreducible P.reverse)
    (hQ : Q.reverse.Monic)
    (hdegree : Q.reverse.natDegree = P.reverse.natDegree)
    (hsq : G ^ 2 = P * Q) : Q.reverse = P.reverse := by
  have hreverse : G.reverse ^ 2 = P.reverse * Q.reverse := by
    simpa only [pow_two, Polynomial.reverse_mul_of_domain] using
      congrArg Polynomial.reverse hsq
  exact polynomial_eq_of_monic_irreducible_mul_eq_sq hP hPirr hQ hdegree hreverse
theorem radial_integral_square_root_is_polynomial
    (n : ℕ) (b : Fin (2 * n) → ℂ) (F : Polynomial ℤ) (S : PowerSeries ℤ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : S ^ 2 = (F : PowerSeries ℤ))
    (hF : F.map (Int.castRingHom ℂ) =
      ∏ i : Fin (2 * n), (1 - Polynomial.C (b i) * Polynomial.X))
    (hcontract : ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i : Fin (2 * n), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 → ‖p.eval ((t : ℂ) * b i)‖ ≤ q) :
    ∃ G : Polynomial ℚ, G ^ 2 = F.map (Int.castRingHom ℚ) := by
  classical
  have hSC : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
      ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X) := by
    have hmap : (PowerSeries.map (Int.castRingHom ℂ) S) ^ 2 =
        (F.map (Int.castRingHom ℂ) : PowerSeries ℂ) := by
      simpa only [map_pow, ← Polynomial.polynomial_map_coe] using
        congrArg (PowerSeries.map (Int.castRingHom ℂ)) hS
    rw [hF] at hmap
    have hprod :
        ((∏ i : Fin (2 * n), (1 - Polynomial.C (b i) * Polynomial.X) :
          Polynomial ℂ) : PowerSeries ℂ) =
          ∏ i : Fin (2 * n), (1 - PowerSeries.C (b i) * PowerSeries.X) := by
      change Polynomial.coeToPowerSeries.ringHom (∏ i : Fin (2 * n),
        (1 - Polynomial.C (b i) * Polynomial.X)) = _
      rw [map_prod]
      simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_sub,
        Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
    exact hmap.trans hprod
  obtain ⟨N, hN⟩ :=
    radial_formal_square_root_hankel_eventually_zero n b S hS₀ hSC hcontract
  have hzero : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → Matrix.det
      (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val)
        (PowerSeries.map (Int.castRingHom ℚ) S)) = 0 := by
    refine ⟨N, fun m hm => ?_⟩
    have hdet := (Int.castRingHom ℚ).map_det
      (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val) S)
    rw [hN m hm, map_zero] at hdet
    have hmatrix : (Int.castRingHom ℚ).mapMatrix
        (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val) S) =
        (fun i j : Fin m => PowerSeries.coeff (n + 1 + i.val + j.val)
          (PowerSeries.map (Int.castRingHom ℚ) S)) := by
      ext i j
      exact (PowerSeries.coeff_map (Int.castRingHom ℚ) _ S).symm
    rw [hmatrix] at hdet
    exact hdet.symm
  apply rational_power_series_square_root_is_polynomial
    (PowerSeries.map (Int.castRingHom ℚ) S) (F.map (Int.castRingHom ℚ))
  · simpa only [map_pow, ← Polynomial.polynomial_map_coe] using
      congrArg (PowerSeries.map (Int.castRingHom ℚ)) hS
  · exact shifted_hankel_eventually_zero_rational
      (PowerSeries.map (Int.castRingHom ℚ) S) (n + 1) hzero
theorem radial_integral_factor_eq_of_contraction
    (n : ℕ) (b : Fin (2 * n) → ℂ) (F : Polynomial ℤ) (S : PowerSeries ℤ)
    (P Q : Polynomial ℚ)
    (hS₀ : PowerSeries.constantCoeff S = 1)
    (hS : S ^ 2 = (F : PowerSeries ℤ))
    (hF : F.map (Int.castRingHom ℂ) =
      ∏ i : Fin (2 * n), (1 - Polynomial.C (b i) * Polynomial.X))
    (hcontract : ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i : Fin (2 * n), ∀ t : ℝ,
        0 ≤ t → t ≤ 1 → ‖p.eval ((t : ℂ) * b i)‖ ≤ q)
    (hP : P.Monic) (hPirr : Irreducible P) (hQ : Q.Monic)
    (hdegree : Q.natDegree = P.natDegree)
    (hfactor : F.map (Int.castRingHom ℚ) = P * Q) : Q = P := by
  obtain ⟨G, hG⟩ :=
    radial_integral_square_root_is_polynomial n b F S hS₀ hS hF hcontract
  exact polynomial_eq_of_monic_irreducible_mul_eq_sq
    hP hPirr hQ hdegree (hG.trans hfactor)
theorem radial_angular_resolvent_energy_bound (m : ℕ) (hm : 0 < m)
    (θ : Fin m → ℝ) (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (hinj : Function.Injective θ) (ξ : ℝ) (hξ : 0 < ξ) (w : Fin m → ℂ) :
    Real.pi / ((m : ℝ) * ξ * Real.tanh (Real.pi * ξ / m)) * ‖∑ i, w i‖ ^ 2 ≤
      ∑ i, ∑ j, (star (w i) * w j).re *
        (∑' n : ℤ, Real.cos ((n : ℝ) * (θ i - θ j)) /
          (ξ ^ 2 + (n : ℝ) ^ 2)) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < Real.tanh (Real.pi * ξ / m) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have hsinh : Real.sinh (Real.pi * ξ) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * ξ)).ne'
  have hp (i j : Fin m) : θ i - θ j ∈ Set.Icc (-2 * Real.pi) (2 * Real.pi) :=
    ⟨by linarith [(hθ i).1, (hθ j).2], by linarith [(hθ i).2, (hθ j).1]⟩
  have h := radial_angular_green_energy_bound m hm θ hθ hinj ξ hξ w
  have hbound : ‖∑ i, w i‖ ^ 2 ≤
      (2 * ξ * m * Real.tanh (Real.pi * ξ / m)) *
        (∑ i, ∑ j, (star (w i) * w j).re *
          (Real.cosh (ξ * (Real.pi - |θ i - θ j|)) /
            (2 * ξ * Real.sinh (Real.pi * ξ)))) := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using h
  have heq :
      (∑ i, ∑ j, (star (w i) * w j).re *
        (∑' n : ℤ, Real.cos ((n : ℝ) * (θ i - θ j)) /
          (ξ ^ 2 + (n : ℝ) ^ 2))) =
      (2 * Real.pi) * (∑ i, ∑ j, (star (w i) * w j).re *
        (Real.cosh (ξ * (Real.pi - |θ i - θ j|)) /
          (2 * ξ * Real.sinh (Real.pi * ξ)))) := by
    simp_rw [(radial_green_fourier_series ξ _ hξ (hp _ _)).2]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [heq]
  have hnorm (x : ℝ) :
      Real.pi / ((m : ℝ) * ξ * Real.tanh (Real.pi * ξ / m)) *
        ((2 * ξ * m * Real.tanh (Real.pi * ξ / m)) * x) = (2 * Real.pi) * x := by
    field_simp
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq (hnorm _)
theorem radial_resolvent_lattice_sum (m : ℕ) (hm : 0 < m) (ξ : ℝ) (hξ : 0 < ξ) :
    Summable (fun n : ℤ => 1 / (ξ ^ 2 + ((m : ℝ) * (n : ℝ)) ^ 2)) ∧
      (∑' n : ℤ, 1 / (ξ ^ 2 + ((m : ℝ) * (n : ℝ)) ^ 2)) =
        Real.pi / ((m : ℝ) * ξ * Real.tanh (Real.pi * ξ / m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < ξ / m := div_pos hξ hmR
  have h := radial_green_fourier_series (ξ / m) 0 ha
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have heq (n : ℤ) :
      1 / (ξ ^ 2 + ((m : ℝ) * (n : ℝ)) ^ 2) =
      (m : ℝ)⁻¹ ^ 2 * (Real.cos ((n : ℝ) * 0) / ((ξ / m) ^ 2 + (n : ℝ) ^ 2)) := by
    simp only [mul_zero, Real.cos_zero]
    field_simp
  refine ⟨(h.1.mul_left ((m : ℝ)⁻¹ ^ 2)).congr (fun n => (heq n).symm), ?_⟩
  simp_rw [heq]
  rw [tsum_mul_left, h.2, abs_zero, sub_zero, Real.tanh_eq_sinh_div_cosh]
  have hsinh : Real.sinh (Real.pi * ξ / m) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * ξ / m)).ne'
  rw [show Real.pi * (ξ / m) = Real.pi * ξ / m by ring]
  field_simp
theorem radial_fourier_cosine_square {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (w : ι → ℂ) (v : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re * Real.cos (v * (θ i - θ j))) =
      (‖∑ i ∈ s, w i * Complex.exp (((v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ‖∑ i ∈ s, w i * Complex.exp (((-v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2) / 2 := by
  have hp := congrArg Complex.re (radial_fourier_square_expand s θ w v)
  have hn := congrArg Complex.re (radial_fourier_square_expand s θ w (-v))
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hp hn
  have heq (i j : ι) : (star (w i) * w j).re * Real.cos (v * (θ i - θ j)) =
      (((star (w i) * w j) * Complex.exp (((v * (θ j - θ i) : ℝ) : ℂ) * Complex.I)).re +
        ((star (w i) * w j) * Complex.exp (((-v * (θ j - θ i) : ℝ) : ℂ) * Complex.I)).re) / 2 := by
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, neg_mul, Real.cos_neg, Real.sin_neg]
    rw [show v * (θ i - θ j) = -(v * (θ j - θ i)) by ring, Real.cos_neg]
    ring
  simp_rw [heq]
  simpa only [Finset.sum_div, Finset.sum_add_distrib, add_div] using
    congrArg₂ (fun a b : ℝ => (a + b) / 2) hp hn
theorem radial_even_int_tsum_split (f : ℤ → ℝ) (hf : Summable f)
    (heven : ∀ n : ℤ, f (-n) = f n) :
    (∑' n : ℤ, f n) = f 0 + 2 * ∑' k : ℕ, f ((k : ℤ) + 1) := by
  have hp : Summable (fun k : ℕ => f (k : ℤ)) := hf.comp_injective Nat.cast_injective
  have hn : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) :=
    hf.comp_injective (by
      intro a b h
      change -((a : ℤ) + 1) = -((b : ℤ) + 1) at h
      exact_mod_cast (by omega : (a : ℤ) = b))
  rw [tsum_of_nat_of_neg_add_one hp hn, hp.tsum_eq_zero_add]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  simp_rw [heven]
  ring
theorem radial_cosine_resolvent_tsum {ι : Type*} (s : Finset ι)
    (θ : ι → ℝ) (w : ι → ℂ) (ξ : ℝ) (hξ : 0 < ξ) :
    Summable (fun n : ℤ =>
      (∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re *
        Real.cos ((n : ℝ) * (θ i - θ j))) / (ξ ^ 2 + (n : ℝ) ^ 2)) ∧
    (∑' n : ℤ,
      (∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re *
        Real.cos ((n : ℝ) * (θ i - θ j))) / (ξ ^ 2 + (n : ℝ) ^ 2)) =
      ∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re *
        (∑' n : ℤ, Real.cos ((n : ℝ) * (θ i - θ j)) / (ξ ^ 2 + (n : ℝ) ^ 2)) := by
  classical
  have hs (i j : ι) : Summable (fun n : ℤ => (star (w i) * w j).re *
      (Real.cos ((n : ℝ) * (θ i - θ j)) / (ξ ^ 2 + (n : ℝ) ^ 2))) :=
    (radial_cos_resolvent_summable ξ (θ i - θ j) hξ).mul_left _
  have hpoint (n : ℤ) :
      (∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re *
        Real.cos ((n : ℝ) * (θ i - θ j))) / (ξ ^ 2 + (n : ℝ) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (star (w i) * w j).re *
        (Real.cos ((n : ℝ) * (θ i - θ j)) / (ξ ^ 2 + (n : ℝ) ^ 2)) := by
    simp only [Finset.sum_div, mul_div_assoc]
  refine ⟨(summable_sum (fun i _ => summable_sum (fun j _ => hs i j))).congr
    (fun n => (hpoint n).symm), ?_⟩
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp_rw [tsum_mul_left]
theorem radial_positive_mode_resolvent_bound (m : ℕ) (hm : 0 < m)
    (θ : Fin m → ℝ) (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (hinj : Function.Injective θ) (ξ : ℝ) (hξ : 0 < ξ) (w : Fin m → ℂ) :
    let P : ℝ → ℝ := fun v =>
      (‖∑ i, w i * Complex.exp (((v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ‖∑ i, w i * Complex.exp (((-v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2) / 2
    Summable (fun n : ℕ => P ((n : ℝ) + 1) / (ξ ^ 2 + ((n : ℝ) + 1) ^ 2)) ∧
      ‖∑ i, w i‖ ^ 2 *
        (∑' k : ℕ, 1 / (ξ ^ 2 + ((m : ℝ) * ((k : ℝ) + 1)) ^ 2)) ≤
      ∑' n : ℕ, P ((n : ℝ) + 1) / (ξ ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  classical
  dsimp only
  let Q : ℝ → ℝ := fun v =>
    ∑ i, ∑ j, (star (w i) * w j).re * Real.cos (v * (θ i - θ j))
  have hP (v : ℝ) : Q v =
      (‖∑ i, w i * Complex.exp (((v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2 +
        ‖∑ i, w i * Complex.exp (((-v * θ i : ℝ) : ℂ) * Complex.I)‖ ^ 2) / 2 :=
    radial_fourier_cosine_square Finset.univ θ w v
  simp_rw [← hP]
  have hQ := radial_cosine_resolvent_tsum Finset.univ θ w ξ hξ
  have hQzero : Q 0 = ‖∑ i, w i‖ ^ 2 := by
    rw [hP]
    simp only [zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    ring
  have hQeven (v : ℝ) : Q (-v) = Q v := by
    simp only [Q, neg_mul, Real.cos_neg]
  have hsplitQ := radial_even_int_tsum_split
    (fun n : ℤ => Q (n : ℝ) / (ξ ^ 2 + (n : ℝ) ^ 2)) hQ.1
    (by intro n; simp only [Int.cast_neg, hQeven, neg_sq])
  obtain ⟨hL, hLval⟩ := radial_resolvent_lattice_sum m hm ξ hξ
  have hsplitL := radial_even_int_tsum_split
    (fun n : ℤ => 1 / (ξ ^ 2 + ((m : ℝ) * (n : ℝ)) ^ 2)) hL
    (by intro n; simp only [Int.cast_neg, mul_neg, neg_sq])
  have hpos : Summable (fun n : ℕ => Q ((n : ℝ) + 1) /
      (ξ ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
    have h := hQ.1.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (by
      intro a b h
      change (a : ℤ) + 1 = (b : ℤ) + 1 at h
      exact_mod_cast (add_right_cancel h))
    change Summable (fun n : ℕ => Q (((n : ℤ) + 1 : ℤ) : ℝ) /
      (ξ ^ 2 + (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2)) at h
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using h
  refine ⟨hpos, ?_⟩
  have hbound := radial_angular_resolvent_energy_bound m hm θ hθ hinj ξ hξ w
  rw [← hQ.2, ← hLval, hsplitQ, hsplitL] at hbound
  simp only [Int.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
    hQzero, Int.cast_add, Int.cast_natCast, Int.cast_one] at hbound
  simp only [div_eq_mul_inv, one_mul] at hbound ⊢
  nlinarith only [hbound]
theorem radial_probability_truncated_energy_bound_of_atom {E : Type*}
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace E] [SecondCountableTopology E]
    (μ : MeasureTheory.ProbabilityMeasure E) (a : E)
    (ha : (μ : MeasureTheory.Measure E) {a} ≠ 0)
    (hdiam : ∀ x y : E, dist x y ≤ 2) (c : ℝ) :
    ∃ N : ℕ, c < ∫ z : E × E,
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ) := by
  classical
  let ν : MeasureTheory.Measure (E × E) := μ.prod μ
  let S : Set (E × E) := {(a, a)}
  have hS : MeasurableSet S := measurableSet_singleton _
  have hSpos : ν S ≠ 0 := by
    change (μ : MeasureTheory.Measure E).prod (μ : MeasureTheory.Measure E) {(a, a)} ≠ 0
    rw [← Set.singleton_prod_singleton, MeasureTheory.Measure.prod_prod]
    exact mul_ne_zero ha ha
  have hp : 0 < ν.real S :=
    lt_of_le_of_ne MeasureTheory.measureReal_nonneg
      (Ne.symm ((MeasureTheory.measureReal_ne_zero_iff (μ := ν) (s := S)).mpr hSpos))
  obtain ⟨N, hN⟩ := exists_nat_gt ((c + Real.log 2) / ν.real S)
  have hc : c < ν.real S * (N : ℝ) - Real.log 2 := by
    have := (div_lt_iff₀ hp).mp hN
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let K : C(E × E, ℝ) := ⟨fun z =>
    -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)),
    ((continuous_const.max (continuous_fst.dist continuous_snd)).log
      (fun z => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))).neg⟩
  have hK : MeasureTheory.Integrable K ν :=
    (ContinuousMap.equivBoundedOfCompact _ _ K).integrable _
  have hI : MeasureTheory.Integrable (S.indicator (fun _ : E × E =>
      (N : ℝ) + Real.log 2)) ν :=
    (MeasureTheory.integrable_const _).indicator hS
  have hmono : (fun z : E × E => -Real.log 2 +
      S.indicator (fun _ => (N : ℝ) + Real.log 2) z) ≤ K := by
    intro z
    change -Real.log 2 + S.indicator (fun _ => (N : ℝ) + Real.log 2) z ≤
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2))
    by_cases hz : z ∈ S
    · have hz' : z = (a, a) := Set.mem_singleton_iff.mp hz
      rw [Set.indicator_of_mem hz, hz']
      change -Real.log 2 + ((N : ℝ) + Real.log 2) ≤
        -Real.log (max (Real.exp (-(N : ℝ))) (dist a a))
      rw [dist_self, max_eq_left (Real.exp_pos _).le, Real.log_exp]
      linarith
    · rw [Set.indicator_of_notMem hz, add_zero]
      apply neg_le_neg
      apply Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _))
      exact max_le ((Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))).trans (by norm_num))
        (hdiam z.1 z.2)
  have hbound := MeasureTheory.integral_mono
    ((MeasureTheory.integrable_const _).add hI) hK hmono
  have hval : (∫ z : E × E, -Real.log 2 +
      S.indicator (fun _ => (N : ℝ) + Real.log 2) z ∂ν) =
      -Real.log 2 + ν.real S * ((N : ℝ) + Real.log 2) := by
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) hI,
      MeasureTheory.integral_indicator_const _ hS]
    simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
      smul_eq_mul, one_mul]
  change (∫ z : E × E, -Real.log 2 +
    S.indicator (fun _ => (N : ℝ) + Real.log 2) z ∂ν) ≤ ∫ z : E × E, K z ∂ν at hbound
  rw [hval] at hbound
  refine ⟨N, ?_⟩
  have hstep : ν.real S * (N : ℝ) - Real.log 2 ≤
      -Real.log 2 + ν.real S * ((N : ℝ) + Real.log 2) := by
    nlinarith [mul_nonneg hp.le hlog2]
  exact hc.trans_le (hstep.trans hbound)
theorem radial_tree_set_norm_le_one (A : Finset ℂ) (hA : ∀ a ∈ A, ‖a‖ = 1)
    (z : ℂ) (hz : z ∈ radial_tree_set A 1) : ‖z‖ ≤ 1 := by
  obtain ⟨a, ha, t, ht, ht1, rfl⟩ := (radial_tree_set_mem_iff A 1 z).mp hz
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    hA a ha, mul_one] using ht1
theorem radial_tree_probability_truncated_energy_of_atom (A : Finset ℂ)
    (hA : ∀ a ∈ A, ‖a‖ = 1)
    (μ : MeasureTheory.ProbabilityMeasure (radial_tree_set A 1))
    (a : radial_tree_set A 1)
    (ha : (μ : MeasureTheory.Measure (radial_tree_set A 1)) {a} ≠ 0) (c : ℝ) :
    ∃ N : ℕ, c < ∫ z : (radial_tree_set A 1) × (radial_tree_set A 1),
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ) := by
  let : CompactSpace (radial_tree_set A 1) :=
    isCompact_iff_compactSpace.mp (radial_tree_set_compact A 1)
  apply radial_probability_truncated_energy_bound_of_atom μ a ha _ c
  intro x y
  change dist (x : ℂ) (y : ℂ) ≤ 2
  calc
    dist (x : ℂ) (y : ℂ) ≤ ‖(x : ℂ)‖ + ‖(y : ℂ)‖ := dist_le_norm_add_norm _ _
    _ ≤ 2 := by linarith [radial_tree_set_norm_le_one A hA x x.property,
      radial_tree_set_norm_le_one A hA y y.property]
theorem radial_interval_cutoff_le_abel (s t r : ℝ) (N : ℕ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hmax : 0 < max s t) (hr : 0 < r) (hr1 : r < 1) :
    -Real.log (max (Real.exp (-(N : ℝ))) |s - t|) -
      Real.log (1 + (1 - r) * Real.exp (N : ℝ)) ≤
    -Real.log (max s t - r * min s t) := by
  have hmin : 0 ≤ min s t := le_min hs ht
  have hmin1 : min s t ≤ 1 := (min_le_left _ _).trans hs1
  have hdiff : max s t - min s t = |s - t| := by
    simpa only [abs_sub_comm] using max_sub_min_eq_abs s t
  have hpos : 0 < max s t - r * min s t := by
    have h := mul_pos (sub_pos.mpr hr1) hmax
    have h' := mul_nonneg hr.le (abs_nonneg (s - t))
    nlinarith
  have hcut : 0 < max (Real.exp (-(N : ℝ))) |s - t| :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hexp : Real.exp (N : ℝ) * Real.exp (-(N : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hscale : 1 ≤ Real.exp (N : ℝ) * max (Real.exp (-(N : ℝ))) |s - t| := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
  have hbound : max s t - r * min s t ≤
      (1 + (1 - r) * Real.exp (N : ℝ)) * max (Real.exp (-(N : ℝ))) |s - t| := by
    have h := mul_le_mul_of_nonneg_left hscale (sub_nonneg.mpr hr1.le)
    have h' := mul_le_mul_of_nonneg_left hmin1 (sub_nonneg.mpr hr1.le)
    nlinarith [le_max_right (Real.exp (-(N : ℝ))) |s - t|]
  have hfac : 0 < 1 + (1 - r) * Real.exp (N : ℝ) := by positivity
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_mul hfac.ne' hcut.ne'] at hlog
  linarith
theorem radial_annular_abel_le_cutoff (δ r : ℝ) (z w : ℂ) (N : ℕ)
    (hδ : 0 < δ) (hr : 0 < r) (hr1 : r < 1) (hz : δ ≤ ‖z‖)
    (hwz : ‖w‖ ≤ ‖z‖) (hN : Real.exp (-(N : ℝ)) ≤ (1 - r) * δ) :
    -Real.log ‖z - (r : ℂ) * w‖ ≤
      -Real.log (max (Real.exp (-(N : ℝ))) ‖z - w‖) - Real.log r / 2 := by
  have hrad : (1 - r) * δ ≤ ‖z - (r : ℂ) * w‖ := by
    have h := norm_sub_norm_le z ((r : ℂ) * w)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
    have h' := mul_le_mul_of_nonneg_left hwz hr.le
    have h'' := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hr1.le)
    nlinarith
  have hnorm : 0 < ‖z - (r : ℂ) * w‖ := (mul_pos (sub_pos.mpr hr1) hδ).trans_le hrad
  have hid : ‖z - (r : ℂ) * w‖ ^ 2 - r * ‖z - w‖ ^ 2 =
      (1 - r) * (‖z‖ ^ 2 - r * ‖w‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hww : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hwz
  have hdiff : 0 ≤ (1 - r) * (‖z‖ ^ 2 - r * ‖w‖ ^ 2) := by
    apply mul_nonneg (sub_nonneg.mpr hr1.le)
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (sq_nonneg ‖w‖)]
  have hdist : r * ‖z - w‖ ^ 2 ≤ ‖z - (r : ℂ) * w‖ ^ 2 := by linarith
  have hcut : Real.exp (-(N : ℝ)) ≤ ‖z - (r : ℂ) * w‖ := hN.trans hrad
  have hmax : 0 < max (Real.exp (-(N : ℝ))) ‖z - w‖ :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hsq : r * (max (Real.exp (-(N : ℝ))) ‖z - w‖) ^ 2 ≤
      ‖z - (r : ℂ) * w‖ ^ 2 := by
    rcases le_total (Real.exp (-(N : ℝ))) ‖z - w‖ with h | h
    · simpa only [max_eq_right h] using hdist
    · rw [max_eq_left h]
      have h' := (sq_le_sq₀ (Real.exp_pos _).le (norm_nonneg _)).mpr hcut
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (sq_nonneg (Real.exp (-(N : ℝ))))]
  have hlog := Real.log_le_log (mul_pos hr (sq_pos_of_pos hmax)) hsq
  rw [Real.log_mul hr.ne' (sq_pos_of_pos hmax).ne', Real.log_pow, Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]
theorem radial_probability_fourier_square {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (φ : X → ℝ) :
    (∫ z : X × X, Complex.exp (((φ z.2 - φ z.1 : ℝ) : ℂ) * Complex.I) ∂(μ.prod μ)) =
      (Complex.normSq (∫ z : X, Complex.exp (((φ z : ℝ) : ℂ) * Complex.I) ∂μ) : ℂ) := by
  have hpoint (z : X × X) :
      Complex.exp (((φ z.2 - φ z.1 : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((φ z.1 : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((φ z.2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.ProbabilityMeasure.toMeasure_prod]
  calc
    _ = (∫ z : X, (starRingEnd ℂ) (Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)) ∂μ) *
        (∫ z : X, Complex.exp (((φ z : ℝ) : ℂ) * Complex.I) ∂μ) :=
      MeasureTheory.integral_prod_mul _ _
    _ = _ := by rw [integral_conj, Complex.normSq_eq_conj_mul_self]
theorem radial_probability_cauchy_mode {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x φ : X → ℝ)
    (hx : Measurable x) (hφ : Measurable φ) (k a : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun ξ : ℝ =>
      (Complex.normSq (∫ z : X,
        Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ) : ℂ) /
        ((k ^ 2 + ξ ^ 2 : ℝ) : ℂ)) ∧
    (∫ ξ : ℝ,
      (Complex.normSq (∫ z : X,
        Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ) : ℂ) /
        ((k ^ 2 + ξ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi / k : ℝ) : ℂ) *
        ∫ z : X × X, Complex.exp (-k * |x z.2 - x z.1| : ℝ) *
          Complex.exp (((a * (φ z.2 - φ z.1) : ℝ) : ℂ) * Complex.I) ∂(μ.prod μ) := by
  let ν : MeasureTheory.Measure (X × X) := μ.prod μ
  let F : ℝ × (X × X) → ℂ := fun p =>
    Complex.exp (((p.1 * (x p.2.2 - x p.2.1) + a * (φ p.2.2 - φ p.2.1) : ℝ) : ℂ) *
      Complex.I) / ((k ^ 2 + p.1 ^ 2 : ℝ) : ℂ)
  have hmF : Measurable F := by dsimp only [F]; fun_prop
  have hF : MeasureTheory.Integrable F (MeasureTheory.volume.prod ν) :=
    ((radial_cauchy_kernel_integrable_unscaled k hk).norm.comp_fst ν).mono'
      hmF.aestronglyMeasurable (by
        filter_upwards with p
        simp [F, Complex.norm_exp])
  have hinner (ξ : ℝ) : (∫ z : X × X, F (ξ, z) ∂ν) =
      (Complex.normSq (∫ z : X,
        Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ) : ℂ) /
        ((k ^ 2 + ξ ^ 2 : ℝ) : ℂ) := by
    have hphase (z : X × X) :
        ξ * (x z.2 - x z.1) + a * (φ z.2 - φ z.1) =
        (ξ * x z.2 + a * φ z.2) - (ξ * x z.1 + a * φ z.1) := by ring
    dsimp only [F, ν]
    simp_rw [hphase]
    rw [MeasureTheory.integral_div,
      radial_probability_fourier_square μ (fun z => ξ * x z + a * φ z)]
  have houter (z : X × X) : (∫ ξ : ℝ, F (ξ, z)) =
      ((Real.pi / k : ℝ) : ℂ) * (Complex.exp (-k * |x z.2 - x z.1| : ℝ) *
        Complex.exp (((a * (φ z.2 - φ z.1) : ℝ) : ℂ) * Complex.I)) := by
    have hphase (ξ : ℝ) : F (ξ, z) =
        Complex.exp (((a * (φ z.2 - φ z.1) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((ξ * (x z.2 - x z.1) : ℝ) : ℂ) * Complex.I) /
          ((k ^ 2 + ξ ^ 2 : ℝ) : ℂ)) := by
      dsimp only [F]
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    simp_rw [hphase]
    rw [MeasureTheory.integral_const_mul, radial_cauchy_kernel_inverse k hk]
    ring
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hF.integral_prod_left
  · calc
      _ = ∫ ξ : ℝ, ∫ z : X × X, F (ξ, z) ∂ν := by simp_rw [hinner]
      _ = ∫ z : X × X, (∫ ξ : ℝ, F (ξ, z)) ∂ν :=
        MeasureTheory.integral_integral_swap hF
      _ = _ := by
        simp_rw [houter]
        rw [MeasureTheory.integral_const_mul]
theorem radial_probability_cauchy_cos_mode {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x φ : X → ℝ)
    (hx : Measurable x) (hφ : Measurable φ) (k a : ℝ) (hk : 0 < k) :
    MeasureTheory.Integrable (fun ξ : ℝ =>
      ‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
        (k ^ 2 + ξ ^ 2)) ∧
    (∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) *
      Real.cos (a * (φ z.2 - φ z.1)) ∂(μ.prod μ)) / k =
      (1 / Real.pi) * ∫ ξ : ℝ,
        ‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
          (k ^ 2 + ξ ^ 2) := by
  have hC := radial_probability_cauchy_mode μ x φ hx hφ k a hk
  have hB : MeasureTheory.Integrable (fun z : X × X =>
      Complex.exp (-k * |x z.2 - x z.1| : ℝ) *
        Complex.exp (((a * (φ z.2 - φ z.1) : ℝ) : ℂ) * Complex.I)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound (by fun_prop) 1
    filter_upwards with z
    simp only [norm_mul, Complex.norm_exp, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      Real.exp_zero, mul_one]
    exact Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x z.2 - x z.1)])
  have hL : (∫ ξ : ℝ,
      ‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
        (k ^ 2 + ξ ^ 2)) =
      (∫ ξ : ℝ, (Complex.normSq (∫ z : X,
        Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ) : ℂ) /
          ((k ^ 2 + ξ ^ 2 : ℝ) : ℂ)).re := by
    simpa only [RCLike.re_eq_complex_re, Complex.div_ofReal_re, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq] using integral_re hC.1
  have hR : (∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) *
      Real.cos (a * (φ z.2 - φ z.1)) ∂(μ.prod μ)) =
      (∫ z : X × X, Complex.exp (-k * |x z.2 - x z.1| : ℝ) *
        Complex.exp (((a * (φ z.2 - φ z.1) : ℝ) : ℂ) * Complex.I) ∂(μ.prod μ)).re := by
    simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.exp_ofReal_re,
      Complex.exp_ofReal_im, Complex.exp_ofReal_mul_I_re, zero_mul, sub_zero] using integral_re hB
  refine ⟨?_, ?_⟩
  · simpa only [RCLike.re_eq_complex_re, Complex.div_ofReal_re, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq] using hC.1.re
  · rw [hC.2] at hL
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hL
    rw [hL, ← hR]
    field_simp
theorem radial_probability_cos_mode_nonneg {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x φ : X → ℝ)
    (hx : Measurable x) (hφ : Measurable φ) (k a : ℝ) (hk : 0 < k) :
    0 ≤ ∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) *
      Real.cos (a * (φ z.2 - φ z.1)) ∂(μ.prod μ) := by
  have h := (radial_probability_cauchy_cos_mode μ x φ hx hφ k a hk).2
  have hi : 0 ≤ ∫ ξ : ℝ,
      ‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
        (k ^ 2 + ξ ^ 2) := by
    apply MeasureTheory.integral_nonneg
    intro ξ
    positivity
  have hdiv : 0 ≤ (∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) *
      Real.cos (a * (φ z.2 - φ z.1)) ∂(μ.prod μ)) / k := by
    rw [h]
    exact mul_nonneg (by positivity) hi
  have hmul := mul_nonneg hdiv hk.le
  rwa [div_mul_cancel₀ _ hk.ne'] at hmul
theorem radial_probability_ray_fourier_sum {X : Type*} [MeasurableSpace X]
    (m : ℕ) (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ)
    (label : X → Fin m) (θ : Fin m → ℝ) (hx : Measurable x)
    (hl : Measurable label) (ξ a : ℝ) :
    (∑ i : Fin m, (∫ z : X, {u | label u = i}.indicator
      (fun u => Complex.exp (((ξ * x u : ℝ) : ℂ) * Complex.I)) z ∂μ) *
        Complex.exp (((a * θ i : ℝ) : ℂ) * Complex.I)) =
      ∫ z : X, Complex.exp (((ξ * x z + a * θ (label z) : ℝ) : ℂ) * Complex.I) ∂μ := by
  classical
  have hp : MeasureTheory.Integrable (fun z : X =>
      Complex.exp (((ξ * x z : ℝ) : ℂ) * Complex.I)) μ :=
    MeasureTheory.Integrable.of_bound (by fun_prop) 1
      (by filter_upwards with z; simp [Complex.norm_exp])
  have hi (i : Fin m) : MeasureTheory.Integrable
      ({u | label u = i}.indicator
        (fun u => Complex.exp (((ξ * x u : ℝ) : ℂ) * Complex.I))) μ :=
    hp.indicator (hl (measurableSet_singleton i))
  calc
    _ = ∑ i : Fin m, ∫ z : X, {u | label u = i}.indicator
        (fun u => Complex.exp (((ξ * x u : ℝ) : ℂ) * Complex.I)) z *
          Complex.exp (((a * θ i : ℝ) : ℂ) * Complex.I) ∂μ := by
      simp_rw [MeasureTheory.integral_mul_const]
    _ = ∫ z : X, ∑ i : Fin m, {u | label u = i}.indicator
        (fun u => Complex.exp (((ξ * x u : ℝ) : ℂ) * Complex.I)) z *
          Complex.exp (((a * θ i : ℝ) : ℂ) * Complex.I) ∂μ :=
      (MeasureTheory.integral_finsetSum _ (fun i _ => (hi i).mul_const _)).symm
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [Finset.sum_eq_single (label z)]
      · rw [Set.indicator_of_mem (show z ∈ {u | label u = label z} from rfl),
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
      · intro j _ hj
        rw [Set.indicator_of_notMem (show z ∉ {u | label u = j} from Ne.symm hj), zero_mul]
      · simp
theorem radial_probability_ray_resolvent_bound {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (label : X → Fin m) (θ : Fin m → ℝ)
    (hx : Measurable x) (hl : Measurable label)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (hinj : Function.Injective θ)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    let P : ℝ → ℝ := fun a =>
      (‖∫ z : X, Complex.exp (((ξ * x z + a * θ (label z) : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 +
        ‖∫ z : X, Complex.exp (((ξ * x z + (-a) * θ (label z) : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2) / 2
    Summable (fun n : ℕ => P ((n : ℝ) + 1) / (ξ ^ 2 + ((n : ℝ) + 1) ^ 2)) ∧
      ‖∫ z : X, Complex.exp (((ξ * x z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 *
        (∑' k : ℕ, 1 / (ξ ^ 2 + ((m : ℝ) * ((k : ℝ) + 1)) ^ 2)) ≤
      ∑' n : ℕ, P ((n : ℝ) + 1) / (ξ ^ 2 + ((n : ℝ) + 1) ^ 2) := by
  classical
  let w : Fin m → ℂ := fun i => ∫ z : X, {u | label u = i}.indicator
    (fun u => Complex.exp (((ξ * x u : ℝ) : ℂ) * Complex.I)) z ∂μ
  have hw (a : ℝ) : (∑ i, w i * Complex.exp (((a * θ i : ℝ) : ℂ) * Complex.I)) =
      ∫ z : X, Complex.exp (((ξ * x z + a * θ (label z) : ℝ) : ℂ) * Complex.I) ∂μ :=
    radial_probability_ray_fourier_sum m μ x label θ hx hl ξ a
  have hwzero : (∑ i, w i) =
      ∫ z : X, Complex.exp (((ξ * x z : ℝ) : ℂ) * Complex.I) ∂μ := by
    simpa only [zero_mul, Complex.ofReal_zero, zero_add, add_zero, Complex.exp_zero,
      mul_one] using hw 0
  have h := radial_positive_mode_resolvent_bound m hm θ hθ hinj |ξ| (abs_pos.mpr hξ) w
  dsimp only at h ⊢
  simpa only [sq_abs, hw, hwzero] using h
theorem radial_probability_cauchy_cos_mode_symm {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x φ : X → ℝ)
    (hx : Measurable x) (hφ : Measurable φ) (k a : ℝ) (hk : 0 < k) :
    let P : ℝ → ℝ := fun ξ =>
      (‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 +
        ‖∫ z : X, Complex.exp (((ξ * x z + (-a) * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2) / 2
    MeasureTheory.Integrable (fun ξ : ℝ => P ξ / (k ^ 2 + ξ ^ 2)) ∧
    (∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) *
      Real.cos (a * (φ z.2 - φ z.1)) ∂(μ.prod μ)) / k =
      (1 / Real.pi) * ∫ ξ : ℝ, P ξ / (k ^ 2 + ξ ^ 2) := by
  have hp := radial_probability_cauchy_cos_mode μ x φ hx hφ k a hk
  have hn := radial_probability_cauchy_cos_mode μ x φ hx hφ k (-a) hk
  dsimp only
  have heq (ξ : ℝ) :
      ((‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 +
        ‖∫ z : X, Complex.exp (((ξ * x z + (-a) * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2) / 2) /
        (k ^ 2 + ξ ^ 2) =
      ((‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
        (k ^ 2 + ξ ^ 2)) +
       (‖∫ z : X, Complex.exp (((ξ * x z + (-a) * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2 /
        (k ^ 2 + ξ ^ 2))) / 2 := by ring
  simp_rw [heq]
  refine ⟨(hp.1.add hn.1).div_const 2, ?_⟩
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add hp.1 hn.1]
  have hneg (z : X × X) : Real.cos ((-a) * (φ z.2 - φ z.1)) =
      Real.cos (a * (φ z.2 - φ z.1)) := by rw [neg_mul, Real.cos_neg]
  simp_rw [hneg] at hn
  linarith only [hp.2, hn.2]
theorem radial_nonnegative_mode_integral_comparison
    (L R : ℕ → ℝ → ℝ)
    (hL : ∀ n, MeasureTheory.Integrable (L n))
    (hR : ∀ n, MeasureTheory.Integrable (R n))
    (hLn : ∀ n ξ, 0 ≤ L n ξ) (hRn : ∀ n ξ, 0 ≤ R n ξ)
    (hLs : ∀ᵐ ξ : ℝ, Summable (fun n => L n ξ))
    (hRs : ∀ᵐ ξ : ℝ, Summable (fun n => R n ξ))
    (hbound : ∀ᵐ ξ : ℝ, (∑' n, L n ξ) ≤ ∑' n, R n ξ) :
    (∑' n, ENNReal.ofReal (∫ ξ : ℝ, L n ξ)) ≤
      ∑' n, ENNReal.ofReal (∫ ξ : ℝ, R n ξ) := by
  have hiL (n : ℕ) := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hL n) (Filter.Eventually.of_forall (hLn n))
  have hiR (n : ℕ) := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hR n) (Filter.Eventually.of_forall (hRn n))
  simp_rw [hiL, hiR]
  rw [← MeasureTheory.lintegral_tsum (fun n =>
      (hL n).aestronglyMeasurable.aemeasurable.ennreal_ofReal),
    ← MeasureTheory.lintegral_tsum (fun n =>
      (hR n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [hLs, hRs, hbound] with ξ hls hrs hb
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hLn n ξ) hls,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => hRn n ξ) hrs]
  exact ENNReal.ofReal_le_ofReal hb
theorem radial_probability_ray_mode_sum_bound {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (label : X → Fin m) (θ : Fin m → ℝ)
    (hx : Measurable x) (hl : Measurable label)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (hinj : Function.Injective θ) :
    let C : ℝ → ℝ := fun k => ∫ z : X × X,
      Real.exp (-k * |x z.2 - x z.1|) ∂(μ.prod μ)
    let B : ℝ → ℝ := fun k => ∫ z : X × X,
      Real.exp (-k * |x z.2 - x z.1|) *
        Real.cos (k * (θ (label z.2) - θ (label z.1))) ∂(μ.prod μ)
    (∑' k : ℕ, ENNReal.ofReal (C ((m : ℝ) * ((k : ℝ) + 1)) /
      ((m : ℝ) * ((k : ℝ) + 1)))) ≤
    ∑' n : ℕ, ENNReal.ofReal (B ((n : ℝ) + 1) / ((n : ℝ) + 1)) := by
  classical
  dsimp only
  let φ : X → ℝ := fun z => θ (label z)
  have hφ : Measurable φ := (measurable_of_countable θ).comp hl
  let p : ℝ → ℝ → ℝ := fun a ξ =>
    ‖∫ z : X, Complex.exp (((ξ * x z + a * φ z : ℝ) : ℂ) * Complex.I) ∂μ‖ ^ 2
  let L : ℕ → ℝ → ℝ := fun n ξ =>
    p 0 ξ / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2 + ξ ^ 2)
  let R : ℕ → ℝ → ℝ := fun n ξ =>
    ((p ((n : ℝ) + 1) ξ + p (-((n : ℝ) + 1)) ξ) / 2) /
      (((n : ℝ) + 1) ^ 2 + ξ ^ 2)
  have hk (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hmk (n : ℕ) : 0 < (m : ℝ) * ((n : ℝ) + 1) := by positivity
  have hL (n : ℕ) := radial_probability_cauchy_cos_mode μ x φ hx hφ
    ((m : ℝ) * ((n : ℝ) + 1)) 0 (hmk n)
  have hR (n : ℕ) := radial_probability_cauchy_cos_mode_symm μ x φ hx hφ
    ((n : ℝ) + 1) ((n : ℝ) + 1) (hk n)
  have hLn (n : ℕ) (ξ : ℝ) : 0 ≤ L n ξ := by dsimp only [L, p]; positivity
  have hRn (n : ℕ) (ξ : ℝ) : 0 ≤ R n ξ := by dsimp only [R, p]; positivity
  have hLs (ξ : ℝ) (hξ : ξ ≠ 0) : Summable (fun n => L n ξ) := by
    have hs := ((radial_resolvent_lattice_sum m hm |ξ| (abs_pos.mpr hξ)).1.comp_injective
      (i := fun n : ℕ => (n : ℤ) + 1) (by
        intro a b h
        change (a : ℤ) + 1 = (b : ℤ) + 1 at h
        exact_mod_cast (by omega : (a : ℤ) = b))).mul_left (p 0 ξ)
    simpa only [L, Function.comp_apply, sq_abs, Int.cast_add, Int.cast_natCast,
      Int.cast_one, mul_one_div, add_comm (ξ ^ 2)] using hs
  have hRs (ξ : ℝ) (hξ : ξ ≠ 0) : Summable (fun n => R n ξ) := by
    simpa only [R, p, φ, add_comm (ξ ^ 2)] using
      (radial_probability_ray_resolvent_bound m hm μ x label θ hx hl hθ hinj ξ hξ).1
  have hb (ξ : ℝ) (hξ : ξ ≠ 0) : (∑' n, L n ξ) ≤ ∑' n, R n ξ := by
    have h := (radial_probability_ray_resolvent_bound m hm μ x label θ hx hl hθ hinj ξ hξ).2
    have heq (n : ℕ) : L n ξ = p 0 ξ *
        (1 / (ξ ^ 2 + ((m : ℝ) * ((n : ℝ) + 1)) ^ 2)) := by
      dsimp only [L]
      rw [mul_one_div, add_comm]
    simp_rw [heq]
    rw [tsum_mul_left]
    simpa only [p, φ, zero_mul, add_zero, R, add_comm (ξ ^ 2)] using h
  have hext := radial_nonnegative_mode_integral_comparison L R
    (fun n => (hL n).1) (fun n => (hR n).1) hLn hRn
    ((MeasureTheory.volume.ae_ne 0).mono fun ξ hξ => hLs ξ hξ)
    ((MeasureTheory.volume.ae_ne 0).mono fun ξ hξ => hRs ξ hξ)
    ((MeasureTheory.volume.ae_ne 0).mono fun ξ hξ => hb ξ hξ)
  calc
    _ = ∑' n, ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal (∫ ξ : ℝ, L n ξ) := by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simpa only [L, p, φ, zero_mul, add_zero, Real.cos_zero, mul_one] using (hL n).2
    _ = ENNReal.ofReal (1 / Real.pi) * (∑' n, ENNReal.ofReal (∫ ξ : ℝ, L n ξ)) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (1 / Real.pi) * (∑' n, ENNReal.ofReal (∫ ξ : ℝ, R n ξ)) :=
      mul_le_mul' le_rfl hext
    _ = ∑' n, ENNReal.ofReal (1 / Real.pi) * ENNReal.ofReal (∫ ξ : ℝ, R n ξ) :=
      ENNReal.tsum_mul_left.symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact (hR n).2.symm
theorem radial_log_abel_hasSum (s θ : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    HasSum (fun n : ℕ => s ^ (n + 1) / ((n : ℝ) + 1) *
      Real.cos (((n : ℝ) + 1) * θ))
      (-Real.log ‖1 - (s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖) := by
  have hz : ‖(s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs, Complex.norm_exp_ofReal_mul_I, mul_one] using hs1
  have h := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hz)
  have heq (n : ℕ) :
      ((((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ (n + 1)) /
        ((n : ℂ) + 1)).re =
      s ^ (n + 1) / ((n : ℝ) + 1) * Real.cos (((n : ℝ) + 1) * θ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using radial_interval_phase_power_re s θ (n + 1)
  simp_rw [heq] at h
  simpa only [Complex.neg_re, Complex.log_re] using h
theorem radial_probability_abel_log_expansion {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (q φ : X → ℝ)
    (hq : Measurable q) (hφ : Measurable φ)
    (hq0 : ∀ z, 0 ≤ q z) (hq1 : ∀ z, q z ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ (n + 1) / ((n : ℝ) + 1) *
      ∫ z : X, (q z) ^ (n + 1) * Real.cos (((n : ℝ) + 1) * φ z) ∂μ)
      (∫ z : X, -Real.log ‖1 - ((r * q z : ℝ) : ℂ) *
        Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ ∂μ) := by
  let F : ℕ → X → ℝ := fun n z => (r * q z) ^ (n + 1) / ((n : ℝ) + 1) *
    Real.cos (((n : ℝ) + 1) * φ z)
  have hdom (n : ℕ) (z : X) : ‖F n z‖ ≤ r ^ (n + 1) := by
    have hp : (r * q z) ^ (n + 1) ≤ r ^ (n + 1) :=
      pow_le_pow_left₀ (mul_nonneg hr (hq0 z)) (by nlinarith [hq1 z]) _
    have hqr : 0 ≤ r * q z := mul_nonneg hr (hq0 z)
    have hd : 0 ≤ (r * q z) ^ (n + 1) / ((n : ℝ) + 1) :=
      div_nonneg (pow_nonneg hqr _) (by positivity)
    have hc := Real.abs_cos_le_one (((n : ℝ) + 1) * φ z)
    calc
      ‖F n z‖ = ((r * q z) ^ (n + 1) / ((n : ℝ) + 1)) *
        |Real.cos (((n : ℝ) + 1) * φ z)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
      _ ≤ (r * q z) ^ (n + 1) / ((n : ℝ) + 1) := by nlinarith
      _ ≤ (r * q z) ^ (n + 1) := div_le_self (pow_nonneg hqr _)
        (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ ≤ _ := hp
  have hs : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr hr1).comp_injective (fun a b h => by omega)
  have hi := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := (μ : MeasureTheory.Measure X)) (F := F)
    (fun n (_ : X) => r ^ (n + 1))
    (fun n => by dsimp only [F]; fun_prop)
    (fun n => Filter.Eventually.of_forall (hdom n))
    (Filter.Eventually.of_forall (fun _ => hs))
    (MeasureTheory.integrable_const _)
    (Filter.Eventually.of_forall (fun z => radial_log_abel_hasSum (r * q z) (φ z)
      (mul_nonneg hr (hq0 z)) ((by nlinarith [hq1 z] : r * q z ≤ r).trans_lt hr1)))
  convert hi using 1
  funext n
  have heq (z : X) : F n z = (r ^ (n + 1) / ((n : ℝ) + 1)) *
      ((q z) ^ (n + 1) * Real.cos (((n : ℝ) + 1) * φ z)) := by
    dsimp only [F]
    rw [mul_pow]
    ring
  simp_rw [heq]
  rw [MeasureTheory.integral_const_mul]
theorem radial_probability_log_coordinate_abel_expansion {X : Type*}
    [MeasurableSpace X] (μ : MeasureTheory.ProbabilityMeasure X)
    (x φ : X → ℝ) (hx : Measurable x) (hφ : Measurable φ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ (n + 1) / ((n : ℝ) + 1) *
      ∫ z : X × X, Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) *
        Real.cos (((n : ℝ) + 1) * (φ z.2 - φ z.1)) ∂(μ.prod μ))
      (∫ z : X × X, -Real.log ‖1 -
        ((r * Real.exp (-|x z.2 - x z.1|) : ℝ) : ℂ) *
          Complex.exp (((φ z.2 - φ z.1 : ℝ) : ℂ) * Complex.I)‖ ∂(μ.prod μ)) := by
  have h := radial_probability_abel_log_expansion (μ.prod μ)
    (fun z : X × X => Real.exp (-|x z.2 - x z.1|))
    (fun z : X × X => φ z.2 - φ z.1) (by fun_prop) (by fun_prop)
    (fun z => (Real.exp_pos _).le)
    (fun z => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))) r hr hr1
  have heq (n : ℕ) (z : X × X) :
      Real.exp (-|x z.2 - x z.1|) ^ (n + 1) =
        Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simpa only [heq] using h
theorem radial_abel_weighted_sum_gt (b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hb1 : ∀ n, b n ≤ 1) (c : ℝ)
    (hc : c < 0 ∨ ENNReal.ofReal c < ∑' n, ENNReal.ofReal (b n)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ Summable (fun n => r ^ (n + 1) * b n) ∧
      c < (∑' n, r ^ (n + 1) * b n) + Real.log r / 2 := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, c < ∑ n ∈ s, b n := by
    rcases hc with hc | hc
    · exact ⟨∅, by simpa using hc⟩
    · rw [ENNReal.tsum_eq_iSup_sum] at hc
      obtain ⟨s, hs⟩ := lt_iSup_iff.mp hc
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hb n)] at hs
      exact ⟨s, (ENNReal.ofReal_lt_ofReal_iff'.mp hs).1⟩
  let f : ℝ → ℝ := fun r => (∑ n ∈ s, r ^ (n + 1) * b n) + Real.log r / 2
  have hf : ContinuousAt f 1 := by dsimp only [f]; fun_prop (disch := norm_num)
  have hf1 : c < f 1 := by simpa [f] using hs
  have hevent : ∀ᶠ r in nhds (1 : ℝ), c < f r :=
    continuousAt_const.eventually_lt hf hf1
  obtain ⟨l, u, hlu, hsub⟩ := hevent.exists_Ioo_subset
  let r : ℝ := (max l 0 + 1) / 2
  have hmax : max l 0 < 1 := max_lt hlu.1 (by norm_num)
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right l 0]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hlr : l < r := by dsimp [r]; linarith [le_max_left l 0]
  have hfgt := hsub ⟨hlr, hr1.trans hlu.2⟩
  have hg : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_geometric_of_lt_one hr.le hr1).comp_injective (fun a b h => by omega)
  have hbnd (n : ℕ) : r ^ (n + 1) * b n ≤ r ^ (n + 1) :=
    mul_le_of_le_one_right (pow_nonneg hr.le _) (hb1 n)
  have hsumm : Summable (fun n : ℕ => r ^ (n + 1) * b n) :=
    hg.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg hr.le _) (hb n)) hbnd
  refine ⟨r, hr, hr1, hsumm, ?_⟩
  have hsum := hsumm.sum_le_tsum s (fun n _ => mul_nonneg (pow_nonneg hr.le _) (hb n))
  change c < (∑ n ∈ s, r ^ (n + 1) * b n) + Real.log r / 2 at hfgt
  linarith only [hfgt, hsum]
theorem radial_interval_truncated_energy_bound_map {X : Type*}
    [MeasurableSpace X] (μ : MeasureTheory.ProbabilityMeasure X)
    (s : X → Set.Icc (0 : ℝ) 1) (hs : Measurable s)
    (c : ℝ) (hc : c < Real.log 4) :
    ∃ N : ℕ, c < ∫ z : X × X,
      -Real.log (max (Real.exp (-(N : ℝ))) |(s z.1 : ℝ) - (s z.2 : ℝ)|) ∂(μ.prod μ) := by
  obtain ⟨N, hN⟩ := radial_interval_truncated_energy_bound c hc (μ.map s)
  refine ⟨N, ?_⟩
  have hcont : Continuous (fun z : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1 =>
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2))) :=
    ((continuous_const.max (continuous_fst.dist continuous_snd)).log
      (fun z => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))).neg
  rw [MeasureTheory.ProbabilityMeasure.map_prod_map μ μ hs hs,
    MeasureTheory.ProbabilityMeasure.toMeasure_map,
    MeasureTheory.integral_map (hs.prodMap hs).aemeasurable
      hcont.stronglyMeasurable.aestronglyMeasurable] at hN
  simpa only [Prod.map_fst, Prod.map_snd, Subtype.dist_eq, Real.dist_eq] using hN
theorem radial_exp_interval_abel_factor (a b k r : ℝ) (hk : 0 ≤ k) :
    max (Real.exp (-k * a)) (Real.exp (-k * b)) -
      r * min (Real.exp (-k * a)) (Real.exp (-k * b)) =
      Real.exp (-k * min a b) * (1 - r * Real.exp (-k * |b - a|)) := by
  rcases le_total a b with hab | hba
  · have he : Real.exp (-k * b) ≤ Real.exp (-k * a) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hprod : Real.exp (-k * a) * Real.exp (-k * (b - a)) = Real.exp (-k * b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [max_eq_left he, min_eq_right he, min_eq_left hab,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    calc
      _ = Real.exp (-k * a) - r * (Real.exp (-k * a) * Real.exp (-k * (b - a))) := by
        rw [hprod]
      _ = _ := by ring
  · have he : Real.exp (-k * a) ≤ Real.exp (-k * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hprod : Real.exp (-k * b) * Real.exp (-k * -(b - a)) = Real.exp (-k * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [max_eq_right he, min_eq_left he, min_eq_right hba,
      abs_of_nonpos (sub_nonpos.mpr hba)]
    calc
      _ = Real.exp (-k * b) - r * (Real.exp (-k * b) * Real.exp (-k * -(b - a))) := by
        rw [hprod]
      _ = _ := by ring
theorem radial_exp_interval_log_abel_factor (a b k r : ℝ)
    (hk : 0 ≤ k) (hr : 0 ≤ r) (hr1 : r < 1) :
    -Real.log (max (Real.exp (-k * a)) (Real.exp (-k * b)) -
      r * min (Real.exp (-k * a)) (Real.exp (-k * b))) =
      k * min a b - Real.log (1 - r * Real.exp (-k * |b - a|)) := by
  have hq : Real.exp (-k * |b - a|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (b - a)])
  have hp : 0 < 1 - r * Real.exp (-k * |b - a|) := by
    nlinarith [mul_le_mul_of_nonneg_left hq hr]
  rw [radial_exp_interval_abel_factor a b k r hk,
    Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
  ring
theorem radial_probability_real_abel_integrable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (q : X → ℝ) (hq : Measurable q)
    (hq0 : ∀ z, 0 ≤ q z) (hq1 : ∀ z, q z ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    MeasureTheory.Integrable (fun z => -Real.log (1 - r * q z)) μ := by
  have hp (z : X) : 0 < 1 - r * q z := by
    nlinarith [mul_le_mul_of_nonneg_left (hq1 z) hr]
  apply MeasureTheory.Integrable.of_bound
    ((measurable_const.sub (measurable_const.mul hq)).log.neg.aestronglyMeasurable)
    (-Real.log (1 - r))
  filter_upwards with z
  change ‖-Real.log (1 - r * q z)‖ ≤ -Real.log (1 - r)
  have hlog : Real.log (1 - r * q z) ≤ 0 :=
    Real.log_nonpos (hp z).le (by nlinarith [mul_nonneg hr (hq0 z)])
  rw [Real.norm_eq_abs, abs_of_nonneg (neg_nonneg.mpr hlog)]
  exact neg_le_neg (Real.log_le_log (by linarith) (by
    nlinarith [mul_le_mul_of_nonneg_left (hq1 z) hr]))
theorem radial_interval_log_coordinate_cutoff_le_abel_of_integrable {X : Type*}
    [MeasurableSpace X] (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (hx : Measurable x) (k r : ℝ)
    (hx0 : ∀ z, 0 ≤ x z)
    (hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ))
    (hk : 0 ≤ k) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    (∫ z : X × X, -Real.log (max (Real.exp (-(N : ℝ)))
      |Real.exp (-k * x z.1) - Real.exp (-k * x z.2)|) ∂(μ.prod μ)) ≤
    k * (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
      (∫ z : X × X, -Real.log (1 - r *
        Real.exp (-k * |x z.2 - x z.1|)) ∂(μ.prod μ)) +
      Real.log (1 + (1 - r) * Real.exp (N : ℝ)) := by
  let s : X → ℝ := fun z => Real.exp (-k * x z)
  have hs0 (z : X) : 0 < s z := Real.exp_pos _
  have hs1 (z : X) : s z ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hx0 z])
  have hlog := radial_probability_real_abel_integrable (μ.prod μ)
    (fun z : X × X => Real.exp (-k * |x z.2 - x z.1|)) (by fun_prop)
    (fun z => (Real.exp_pos _).le)
    (fun z => Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x z.2 - x z.1)]))
    r hr.le hr1
  have hcut : MeasureTheory.Integrable (fun z : X × X =>
      -Real.log (max (Real.exp (-(N : ℝ))) |s z.1 - s z.2|)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound
      ((show Measurable (fun z : X × X =>
        max (Real.exp (-(N : ℝ))) |s z.1 - s z.2|) by dsimp [s]; fun_prop).log.neg.aestronglyMeasurable)
      (N : ℝ)
    filter_upwards with z
    change ‖-Real.log (max (Real.exp (-(N : ℝ))) |s z.1 - s z.2|)‖ ≤ (N : ℝ)
    have hpos : 0 < max (Real.exp (-(N : ℝ))) |s z.1 - s z.2| :=
      (Real.exp_pos _).trans_le (le_max_left _ _)
    have hle : max (Real.exp (-(N : ℝ))) |s z.1 - s z.2| ≤ 1 := by
      apply max_le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N)))
      exact abs_le.mpr ⟨by linarith [hs0 z.1, hs1 z.2], by linarith [hs1 z.1, hs0 z.2]⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (neg_nonneg.mpr (Real.log_nonpos hpos.le hle))]
    have h := Real.log_le_log (Real.exp_pos (-(N : ℝ)))
      (le_max_left (Real.exp (-(N : ℝ))) |s z.1 - s z.2|)
    rw [Real.log_exp] at h
    linarith
  have hi := MeasureTheory.integral_mono hcut
    (((hmin.const_mul k).add hlog).add (MeasureTheory.integrable_const
      (Real.log (1 + (1 - r) * Real.exp (N : ℝ))))) (fun z => ?_)
  · dsimp only [Pi.add_apply] at hi
    have houter := MeasureTheory.integral_add ((hmin.const_mul k).add hlog)
      (MeasureTheory.integrable_const (Real.log (1 + (1 - r) * Real.exp (N : ℝ))))
    have hinner := MeasureTheory.integral_add (hmin.const_mul k) hlog
    dsimp only [Pi.add_apply] at houter hinner
    rw [houter, hinner,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
      at hi
    exact hi
  · have h := radial_interval_cutoff_le_abel (s z.1) (s z.2) r N
      (hs0 _).le (hs1 _) (hs0 _).le (hs1 _)
      ((hs0 _).trans_le (le_max_left _ _)) hr hr1
    change -Real.log (max (Real.exp (-(N : ℝ))) |s z.1 - s z.2|) - _ ≤
      -Real.log (max (Real.exp (-k * x z.1)) (Real.exp (-k * x z.2)) -
        r * min (Real.exp (-k * x z.1)) (Real.exp (-k * x z.2))) at h
    rw [radial_exp_interval_log_abel_factor (x z.1) (x z.2) k r hk hr.le hr1] at h
    dsimp only [Pi.add_apply]
    linarith only [h]
theorem radial_interval_log_coordinate_cutoff_le_abel {X : Type*}
    [MeasurableSpace X] (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (hx : Measurable x) (L k r : ℝ)
    (hx0 : ∀ z, 0 ≤ x z) (hxL : ∀ z, x z ≤ L)
    (hk : 0 ≤ k) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    (∫ z : X × X, -Real.log (max (Real.exp (-(N : ℝ)))
      |Real.exp (-k * x z.1) - Real.exp (-k * x z.2)|) ∂(μ.prod μ)) ≤
    k * (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
      (∫ z : X × X, -Real.log (1 - r *
        Real.exp (-k * |x z.2 - x z.1|)) ∂(μ.prod μ)) +
      Real.log (1 + (1 - r) * Real.exp (N : ℝ)) := by
  have hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound (by fun_prop) L
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hx0 _) (hx0 _))]
    exact (min_le_left _ _).trans (hxL _)
  exact radial_interval_log_coordinate_cutoff_le_abel_of_integrable μ x hx k r hx0 hmin hk hr hr1 N
theorem radial_probability_real_abel_expansion {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (q : X → ℝ) (hq : Measurable q)
    (hq0 : ∀ z, 0 ≤ q z) (hq1 : ∀ z, q z ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ (n + 1) / ((n : ℝ) + 1) *
      ∫ z : X, (q z) ^ (n + 1) ∂μ)
      (∫ z : X, -Real.log (1 - r * q z) ∂μ) := by
  have h := radial_probability_abel_log_expansion μ q (fun _ => 0) hq measurable_const
    hq0 hq1 r hr hr1
  have hp (z : X) : 0 < 1 - r * q z := by
    nlinarith [mul_le_mul_of_nonneg_left (hq1 z) hr]
  have hnorm (z : X) : ‖(1 : ℂ) - ((r * q z : ℝ) : ℂ)‖ = 1 - r * q z := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hp z)]
  simpa only [mul_zero, Real.cos_zero, mul_one, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, hnorm] using h
theorem radial_interval_log_coordinate_series_bound_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ) (hx : Measurable x)
    (k : ℝ) (hx0 : ∀ z, 0 ≤ x z)
    (hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ)) (hk : 0 < k)
    (hs : Summable (fun n : ℕ =>
      (∫ z : X × X, Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
        (k * ((n : ℝ) + 1)))) :
    Real.log 4 / k ≤
      (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
      ∑' n : ℕ, (∫ z : X × X,
        Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
          (k * ((n : ℝ) + 1)) := by
  let I : ℝ := ∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)
  let b : ℕ → ℝ := fun n =>
    (∫ z : X × X, Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
      (k * ((n : ℝ) + 1))
  have hb (n : ℕ) : 0 ≤ b n := by
    apply div_nonneg
    · exact MeasureTheory.integral_nonneg (fun _ => (Real.exp_pos _).le)
    · positivity
  have hs' : Summable b := hs
  have hsum : Real.log 4 ≤ k * (I + ∑' n, b n) := by
    apply le_of_forall_lt
    intro c hc
    let s : X → Set.Icc (0 : ℝ) 1 := fun z => ⟨Real.exp (-k * x z),
      (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [hx0 z])⟩
    have hsm : Measurable s := by
      apply Measurable.subtype_mk
      fun_prop
    obtain ⟨N, hN⟩ := radial_interval_truncated_energy_bound_map μ s hsm c hc
    have hbound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
        (∫ z : X × X, -Real.log (max (Real.exp (-(N : ℝ)))
          |Real.exp (-k * x z.1) - Real.exp (-k * x z.2)|) ∂(μ.prod μ)) ≤
        k * (I + ∑' n, b n) + Real.log (1 + (1 - r) * Real.exp (N : ℝ)) := by
      have hAb := radial_probability_real_abel_expansion (μ.prod μ)
        (fun z : X × X => Real.exp (-k * |x z.2 - x z.1|)) (by fun_prop)
        (fun _ => (Real.exp_pos _).le)
        (fun z => Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x z.2 - x z.1)]))
        r hr.le hr1
      have heq (n : ℕ) :
          r ^ (n + 1) / ((n : ℝ) + 1) *
            (∫ z : X × X, Real.exp (-k * |x z.2 - x z.1|) ^ (n + 1) ∂(μ.prod μ)) =
          r ^ (n + 1) * (k * b n) := by
        have hpow (z : X × X) : Real.exp (-k * |x z.2 - x z.1|) ^ (n + 1) =
            Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        simp_rw [hpow]
        dsimp only [b]
        field_simp
      simp_rw [heq] at hAb
      have hle := hAb.summable.tsum_le_tsum
        (fun n => mul_le_of_le_one_left (mul_nonneg hk.le (hb n))
          (pow_le_one₀ hr.le hr1.le)) (hs'.mul_left k)
      rw [tsum_mul_left, hAb.tsum_eq] at hle
      have h := radial_interval_log_coordinate_cutoff_le_abel_of_integrable μ x hx k r hx0 hmin
        hk.le hr hr1 N
      change _ ≤ k * I + _ + _ at h
      nlinarith only [h, hle]
    by_contra hbad
    have hbad' : k * (I + ∑' n, b n) ≤ c := le_of_not_gt hbad
    have hcont : ContinuousAt (fun r : ℝ =>
        k * (I + ∑' n, b n) + Real.log (1 + (1 - r) * Real.exp (N : ℝ))) 1 := by
      fun_prop (disch := norm_num)
    have hgap : k * (I + ∑' n, b n) <
        ∫ z : X × X, -Real.log (max (Real.exp (-(N : ℝ)))
          |Real.exp (-k * x z.1) - Real.exp (-k * x z.2)|) ∂(μ.prod μ) :=
      hbad'.trans_lt hN
    have hevent := hcont.eventually_lt continuousAt_const (by simpa only
      [sub_self, zero_mul, add_zero, Real.log_one] using hgap)
    obtain ⟨l, u, hlu, hsub⟩ := hevent.exists_Ioo_subset
    let r : ℝ := (max l 0 + 1) / 2
    have hmax : max l 0 < 1 := max_lt hlu.1 (by norm_num)
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right l 0]
    have hr1 : r < 1 := by dsimp [r]; linarith
    have hlr : l < r := by dsimp [r]; linarith [le_max_left l 0]
    exact (not_lt_of_ge (hbound r hr hr1)) (hsub ⟨hlr, hr1.trans hlu.2⟩)
  exact (div_le_iff₀ hk).mpr (by nlinarith only [hsum])
theorem radial_interval_log_coordinate_series_bound {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ) (hx : Measurable x)
    (L k : ℝ) (hx0 : ∀ z, 0 ≤ x z) (hxL : ∀ z, x z ≤ L) (hk : 0 < k)
    (hs : Summable (fun n : ℕ =>
      (∫ z : X × X, Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
        (k * ((n : ℝ) + 1)))) :
    Real.log 4 / k ≤
      (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
      ∑' n : ℕ, (∫ z : X × X,
        Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
          (k * ((n : ℝ) + 1)) := by
  have hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound (by fun_prop) L
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hx0 _) (hx0 _))]
    exact (min_le_left _ _).trans (hxL _)
  exact radial_interval_log_coordinate_series_bound_of_integrable μ x hx k hx0 hmin hk hs
theorem radial_interval_log_coordinate_mode_sum_bound_of_integrable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ) (hx : Measurable x)
    (k : ℝ) (hx0 : ∀ z, 0 ≤ x z)
    (hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ)) (hk : 0 < k) :
    ENNReal.ofReal (Real.log 4 / k) ≤
      ENNReal.ofReal (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
        ∑' n : ℕ, ENNReal.ofReal ((∫ z : X × X,
          Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
            (k * ((n : ℝ) + 1))) := by
  let b : ℕ → ℝ := fun n => (∫ z : X × X,
    Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
      (k * ((n : ℝ) + 1))
  have hb (n : ℕ) : 0 ≤ b n := by
    exact div_nonneg (MeasureTheory.integral_nonneg (fun _ => (Real.exp_pos _).le))
      (by positivity)
  have hI : 0 ≤ ∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ) :=
    MeasureTheory.integral_nonneg (fun z => le_min (hx0 _) (hx0 _))
  by_cases htop : (∑' n, ENNReal.ofReal (b n)) = ⊤
  · change _ ≤ _ + ∑' n, ENNReal.ofReal (b n)
    simp only [htop, add_top, le_top]
  have hs : Summable b := by
    simpa only [ENNReal.toReal_ofReal (hb _)] using ENNReal.summable_toReal htop
  change _ ≤ _ + ∑' n, ENNReal.ofReal (b n)
  rw [← ENNReal.ofReal_tsum_of_nonneg hb hs,
    ← ENNReal.ofReal_add hI (tsum_nonneg hb)]
  exact ENNReal.ofReal_le_ofReal
    (radial_interval_log_coordinate_series_bound_of_integrable μ x hx k hx0 hmin hk hs)
theorem radial_interval_log_coordinate_mode_sum_bound {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ) (hx : Measurable x)
    (L k : ℝ) (hx0 : ∀ z, 0 ≤ x z) (hxL : ∀ z, x z ≤ L) (hk : 0 < k) :
    ENNReal.ofReal (Real.log 4 / k) ≤
      ENNReal.ofReal (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
        ∑' n : ℕ, ENNReal.ofReal ((∫ z : X × X,
          Real.exp (-(k * ((n : ℝ) + 1)) * |x z.2 - x z.1|) ∂(μ.prod μ)) /
            (k * ((n : ℝ) + 1))) := by
  have hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound (by fun_prop) L
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hx0 _) (hx0 _))]
    exact (min_le_left _ _).trans (hxL _)
  exact radial_interval_log_coordinate_mode_sum_bound_of_integrable μ x hx k hx0 hmin hk
theorem radial_probability_ray_abel_energy_gap_of_integrable {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (label : X → Fin m) (θ : Fin m → ℝ)
    (hx : Measurable x) (hl : Measurable label)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (hinj : Function.Injective θ)
    (hx0 : ∀ z, 0 ≤ x z)
    (hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ))
    (c : ℝ) (hc : c < Real.log 4 / (m : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      c < (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
        (∫ z : X × X, -Real.log ‖1 -
          ((r * Real.exp (-|x z.2 - x z.1|) : ℝ) : ℂ) *
            Complex.exp (((θ (label z.2) - θ (label z.1) : ℝ) : ℂ) *
              Complex.I)‖ ∂(μ.prod μ)) + Real.log r / 2 := by
  let I : ℝ := ∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)
  let b : ℕ → ℝ := fun n => (∫ z : X × X,
    Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) *
      Real.cos (((n : ℝ) + 1) * (θ (label z.2) - θ (label z.1))) ∂(μ.prod μ)) /
        ((n : ℝ) + 1)
  have hφ : Measurable (fun z => θ (label z)) := (measurable_of_countable θ).comp hl
  have hb (n : ℕ) : 0 ≤ b n :=
    div_nonneg (radial_probability_cos_mode_nonneg μ x _ hx hφ _ _ (by positivity))
      (by positivity)
  have hb1 (n : ℕ) : b n ≤ 1 := by
    have hpoint (z : X × X) :
        ‖Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) *
          Real.cos (((n : ℝ) + 1) * (θ (label z.2) - θ (label z.1)))‖ ≤ 1 := by
      have he : Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x z.2 - x z.1)])
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le).trans
        (by simpa only [mul_one] using he)
    have hInt : (∫ z : X × X, Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) *
        Real.cos (((n : ℝ) + 1) * (θ (label z.2) - θ (label z.1))) ∂(μ.prod μ)) ≤ 1 :=
      (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using
          MeasureTheory.norm_integral_le_of_norm_le_const
            (μ := (μ.prod μ : MeasureTheory.Measure (X × X)))
            (Filter.Eventually.of_forall hpoint))
    exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      (by simpa only [one_mul] using hInt.trans (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hI : 0 ≤ I := MeasureTheory.integral_nonneg (fun _ => le_min (hx0 _) (hx0 _))
  have hbound : ENNReal.ofReal (Real.log 4 / (m : ℝ)) ≤
      ENNReal.ofReal I + ∑' n, ENNReal.ofReal (b n) :=
    (radial_interval_log_coordinate_mode_sum_bound_of_integrable μ x hx (m : ℝ) hx0 hmin
      (by positivity)).trans (add_le_add le_rfl
        (radial_probability_ray_mode_sum_bound m hm μ x label θ hx hl hθ hinj))
  have hc' : c - I < 0 ∨ ENNReal.ofReal (c - I) < ∑' n, ENNReal.ofReal (b n) := by
    by_cases htop : (∑' n, ENNReal.ofReal (b n)) = ⊤
    · exact Or.inr (by rw [htop]; exact ENNReal.ofReal_lt_top)
    have hs : Summable b := by
      simpa only [ENNReal.toReal_ofReal (hb _)] using ENNReal.summable_toReal htop
    rw [← ENNReal.ofReal_tsum_of_nonneg hb hs,
      ← ENNReal.ofReal_add hI (tsum_nonneg hb),
      ENNReal.ofReal_le_ofReal_iff (add_nonneg hI (tsum_nonneg hb))] at hbound
    have hlt : c - I < ∑' n, b n := by linarith only [hc, hbound]
    by_cases hneg : c - I < 0
    · exact Or.inl hneg
    · exact Or.inr (by
        rw [← ENNReal.ofReal_tsum_of_nonneg hb hs]
        exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hlt, lt_of_le_of_lt (le_of_not_gt hneg) hlt⟩)
  obtain ⟨r, hr, hr1, _, hgap⟩ := radial_abel_weighted_sum_gt b hb hb1 (c - I) hc'
  have hAb := radial_probability_log_coordinate_abel_expansion μ x (fun z => θ (label z))
    hx hφ r hr.le hr1
  have heq (n : ℕ) : r ^ (n + 1) / ((n : ℝ) + 1) *
      (∫ z : X × X, Real.exp (-((n : ℝ) + 1) * |x z.2 - x z.1|) *
        Real.cos (((n : ℝ) + 1) * (θ (label z.2) - θ (label z.1))) ∂(μ.prod μ)) =
      r ^ (n + 1) * b n := by dsimp only [b]; ring
  simp_rw [heq] at hAb
  rw [hAb.tsum_eq] at hgap
  exact ⟨r, hr, hr1, by linarith only [hgap]⟩
theorem radial_probability_ray_abel_energy_gap {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (μ : MeasureTheory.ProbabilityMeasure X)
    (x : X → ℝ) (label : X → Fin m) (θ : Fin m → ℝ)
    (hx : Measurable x) (hl : Measurable label)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (hinj : Function.Injective θ)
    (L : ℝ) (hx0 : ∀ z, 0 ≤ x z) (hxL : ∀ z, x z ≤ L)
    (c : ℝ) (hc : c < Real.log 4 / (m : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      c < (∫ z : X × X, min (x z.1) (x z.2) ∂(μ.prod μ)) +
        (∫ z : X × X, -Real.log ‖1 -
          ((r * Real.exp (-|x z.2 - x z.1|) : ℝ) : ℂ) *
            Complex.exp (((θ (label z.2) - θ (label z.1) : ℝ) : ℂ) *
              Complex.I)‖ ∂(μ.prod μ)) + Real.log r / 2 := by
  have hmin : MeasureTheory.Integrable (fun z : X × X =>
      min (x z.1) (x z.2)) (μ.prod μ) := by
    apply MeasureTheory.Integrable.of_bound (by fun_prop) L
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hx0 _) (hx0 _))]
    exact (min_le_left _ _).trans (hxL _)
  exact radial_probability_ray_abel_energy_gap_of_integrable m hm μ x label θ hx hl hθ hinj hx0 hmin c hc
theorem radial_probability_complex_abel_integrable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (q φ : X → ℝ)
    (hq : Measurable q) (hφ : Measurable φ)
    (hq0 : ∀ z, 0 ≤ q z) (hq1 : ∀ z, q z ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    MeasureTheory.Integrable (fun z => -Real.log ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖) μ := by
  have hm : Measurable (fun z => ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖) := by fun_prop
  apply MeasureTheory.Integrable.of_bound hm.log.neg.aestronglyMeasurable
    (-Real.log (1 - r) + Real.log 2)
  filter_upwards with z
  change ‖-Real.log ‖1 - ((r * q z : ℝ) : ℂ) *
    Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖‖ ≤ _
  have hq' : 0 ≤ r * q z := mul_nonneg hr (hq0 z)
  have hq'' : r * q z ≤ r := by nlinarith [hq1 z]
  have hlower := radial_interval_phase_norm_lower (r * q z) (φ z) hq'
  have hpos : 0 < ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ := by linarith
  have hupper : ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I))
    simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr, abs_of_nonneg (hq0 z),
      Complex.norm_exp_ofReal_mul_I, mul_one] at h
    linarith
  have hlogL := Real.log_le_log (by linarith : 0 < 1 - r)
    (show 1 - r ≤ ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ by linarith only [hlower, hq''])
  have hlogU := Real.log_le_log hpos hupper
  have hrlog : Real.log (1 - r) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem radial_log_coordinate_abel_le_cutoff (u q θ r : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) :
    u - Real.log ‖1 - ((r * q : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤
      -Real.log (max (Real.exp (-(N : ℝ)))
        (Real.exp (-u) * ‖1 - (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖)) -
      Real.log r / 2 + max 0 (u - Real.log (1 - r) - (N : ℝ)) := by
  let A : ℝ := ‖1 - ((r * q : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖
  let D : ℝ := ‖1 - (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖
  have hA : 0 < A := by
    have h := radial_interval_phase_norm_lower (r * q) θ (mul_nonneg hr.le hq)
    have hqr : r * q ≤ r := by nlinarith
    dsimp only [A]
    linarith
  have hD : 0 ≤ D := norm_nonneg _
  have hsq : r * D ^ 2 ≤ A ^ 2 := by
    have h := radial_interval_phase_norm_sq (r * q) θ
    have h' := radial_interval_phase_norm_sq q θ
    have hq2 : q ^ 2 ≤ 1 := by nlinarith
    have hdiff : 0 ≤ (1 - r) * (1 - r * q ^ 2) := by
      apply mul_nonneg (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hq2 hr.le]
    dsimp only [A, D]
    rw [h, h']
    nlinarith only [hdiff]
  have hrlog : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1.le
  rcases le_total (Real.exp (-(N : ℝ))) (Real.exp (-u) * D) with hd | hd
  · rw [max_eq_right hd]
    have hdp : 0 < D := (mul_pos_iff_of_pos_left (Real.exp_pos (-u))).mp
      ((Real.exp_pos _).trans_le hd)
    have hlog := Real.log_le_log (mul_pos hr (sq_pos_of_pos hdp)) hsq
    rw [Real.log_mul hr.ne' (sq_pos_of_pos hdp).ne', Real.log_pow, Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    rw [Real.log_mul (Real.exp_pos _).ne' hdp.ne', Real.log_exp]
    change u - Real.log A ≤ _
    nlinarith only [hlog, le_max_left 0 (u - Real.log (1 - r) - (N : ℝ))]
  · rw [max_eq_left hd, Real.log_exp]
    have hlow : 1 - r ≤ A := by
      have h := radial_interval_phase_norm_lower (r * q) θ (mul_nonneg hr.le hq)
      have hqr : r * q ≤ r := by nlinarith
      dsimp only [A]
      linarith
    have hlog := Real.log_le_log (by linarith : 0 < 1 - r) hlow
    change u - Real.log A ≤ _
    linarith [le_max_right 0 (u - Real.log (1 - r) - (N : ℝ))]
theorem radial_probability_abel_tail_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (u : X → ℝ)
    (hu : Measurable u) (hu0 : ∀ z, 0 ≤ u z) (hui : MeasureTheory.Integrable u μ)
    (C : ℝ) (hC : 0 ≤ C) :
    Filter.Tendsto (fun N : ℕ => ∫ z : X, max 0 (u z + C - (N : ℝ)) ∂μ)
      Filter.atTop (nhds 0) := by
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (μ : MeasureTheory.Measure X))
    (F := fun N : ℕ => fun z : X => max 0 (u z + C - (N : ℝ)))
    (f := fun _ => (0 : ℝ)) (fun z => u z + C)
    (fun N => ((measurable_const.max ((hu.add_const C).sub measurable_const))).aestronglyMeasurable)
    (hui.add (MeasureTheory.integrable_const C))
    (fun N => Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      apply max_le (add_nonneg (hu0 z) hC)
      linarith [Nat.cast_nonneg (α := ℝ) N]))
    (Filter.Eventually.of_forall (fun z => by
      apply tendsto_const_nhds.congr'
      obtain ⟨M, hM⟩ := exists_nat_ge (u z + C)
      filter_upwards [Filter.eventually_ge_atTop M] with N hN
      have hMN : (M : ℝ) ≤ N := by exact_mod_cast hN
      rw [max_eq_left (by linarith : u z + C - (N : ℝ) ≤ 0)]))
  simpa only [MeasureTheory.integral_zero] using h
theorem radial_probability_cutoff_integrable {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.ProbabilityMeasure X) (d : X → ℝ) (hd : Measurable d)
    (hd2 : ∀ z, d z ≤ 2) (N : ℕ) :
    MeasureTheory.Integrable (fun z => -Real.log (max (Real.exp (-(N : ℝ))) (d z))) μ := by
  apply MeasureTheory.Integrable.of_bound
    ((measurable_const.max hd).log.neg.aestronglyMeasurable) ((N : ℝ) + Real.log 2)
  filter_upwards with z
  change ‖-Real.log (max (Real.exp (-(N : ℝ))) (d z))‖ ≤ (N : ℝ) + Real.log 2
  have hp : 0 < max (Real.exp (-(N : ℝ))) (d z) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hl := Real.log_le_log (Real.exp_pos (-(N : ℝ)))
    (le_max_left (Real.exp (-(N : ℝ))) (d z))
  rw [Real.log_exp] at hl
  have hu := Real.log_le_log hp (max_le
    ((Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))).trans (by norm_num)) (hd2 z))
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) N], by linarith⟩
theorem radial_min_coordinate_le_cutoff (u d : ℝ) (hdu : d ≤ 2 * Real.exp (-u)) (N : ℕ) :
    min (N : ℝ) u - Real.log 2 ≤ -Real.log (max (Real.exp (-(N : ℝ))) d) := by
  have heN : Real.exp (-(N : ℝ)) ≤ Real.exp (-min (N : ℝ) u) :=
    Real.exp_le_exp.mpr (neg_le_neg (min_le_left _ _))
  have heu : Real.exp (-u) ≤ Real.exp (-min (N : ℝ) u) :=
    Real.exp_le_exp.mpr (neg_le_neg (min_le_right _ _))
  have hmax : max (Real.exp (-(N : ℝ))) d ≤ 2 * Real.exp (-min (N : ℝ) u) :=
    max_le (by linarith [Real.exp_pos (-min (N : ℝ) u)]) (by linarith only [hdu, heu])
  have hlog := Real.log_le_log
    ((Real.exp_pos (-(N : ℝ))).trans_le (le_max_left _ _)) hmax
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith only [hlog]
theorem radial_probability_coordinate_integrable_of_cutoff_bound {X : Type*}
    [MeasurableSpace X] (μ : MeasureTheory.ProbabilityMeasure X)
    (u d : X → ℝ) (hu : Measurable u) (hd : Measurable d)
    (hu0 : ∀ z, 0 ≤ u z) (hd2 : ∀ z, d z ≤ 2)
    (hdu : ∀ᵐ z ∂(μ : MeasureTheory.Measure X), d z ≤ 2 * Real.exp (-u z))
    (c : ℝ) (hc : ∀ N : ℕ,
      (∫ z : X, -Real.log (max (Real.exp (-(N : ℝ))) (d z)) ∂μ) ≤ c) :
    MeasureTheory.Integrable u μ := by
  have hmin (N : ℕ) : MeasureTheory.Integrable (fun z => min (N : ℝ) (u z)) μ := by
    apply MeasureTheory.Integrable.of_bound (measurable_const.min hu).aestronglyMeasurable (N : ℝ)
    filter_upwards with z
    change ‖min (N : ℝ) (u z)‖ ≤ (N : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg N) (hu0 z))]
    exact min_le_left _ _
  have hInt (N : ℕ) : (∫ z, min (N : ℝ) (u z) ∂μ) ≤ c + Real.log 2 := by
    have h := MeasureTheory.integral_mono_ae
      ((hmin N).sub (MeasureTheory.integrable_const (Real.log 2)))
      (radial_probability_cutoff_integrable μ d hd hd2 N)
      (hdu.mono (fun z hz => radial_min_coordinate_le_cutoff (u z) (d z) hz N))
    dsimp only [Pi.sub_apply] at h
    rw [MeasureTheory.integral_sub (hmin N) (MeasureTheory.integrable_const _),
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] at h
    linarith only [h, hc N]
  have hlim := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (μ := (μ : MeasureTheory.Measure X))
    (f := fun N : ℕ => fun z => ENNReal.ofReal (min (N : ℝ) (u z)))
    (F := fun z => ENNReal.ofReal (u z))
    (fun N => (measurable_const.min hu).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun z a b hab =>
      ENNReal.ofReal_le_ofReal (min_le_min_right (u z) (by exact_mod_cast hab))))
    (Filter.Eventually.of_forall (fun z => by
      apply tendsto_const_nhds.congr'
      obtain ⟨M, hM⟩ := exists_nat_ge (u z)
      filter_upwards [Filter.eventually_ge_atTop M] with N hN
      have hMN : (M : ℝ) ≤ N := by exact_mod_cast hN
      rw [min_eq_right (hM.trans hMN)]))
  have hfinite : (∫⁻ z, ENNReal.ofReal (u z) ∂μ) ≤ ENNReal.ofReal (c + Real.log 2) := by
    apply le_of_tendsto' hlim
    intro N
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmin N)
      (Filter.Eventually.of_forall (fun z => le_min (Nat.cast_nonneg N) (hu0 z)))]
    exact ENNReal.ofReal_le_ofReal (hInt N)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hu.aestronglyMeasurable
    (Filter.Eventually.of_forall hu0)).mp (ne_of_lt (hfinite.trans_lt ENNReal.ofReal_lt_top))
theorem radial_phase_norm_upper (q θ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖1 - (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 2 := by
  have h := norm_sub_le (1 : ℂ) ((q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hq, Complex.norm_exp_ofReal_mul_I, mul_one] at h
  linarith only [h, hq1]
theorem radial_probability_ray_truncated_energy_of_factor {X : Type*}
    [MeasurableSpace X] (m : ℕ) (hm : 0 < m)
    (μ : MeasureTheory.ProbabilityMeasure X) (x : X → ℝ)
    (label : X → Fin m) (θ : Fin m → ℝ)
    (hx : Measurable x) (hl : Measurable label)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (hinj : Function.Injective θ)
    (hx0 : ∀ z, 0 ≤ x z) (d : X × X → ℝ) (hd : Measurable d)
    (hd2 : ∀ z, d z ≤ 2)
    (hfactor : ∀ᵐ z ∂(μ.prod μ : MeasureTheory.Measure (X × X)),
      d z = Real.exp (-min (x z.1) (x z.2)) *
        ‖1 - ((Real.exp (-|x z.2 - x z.1|) : ℝ) : ℂ) *
          Complex.exp (((θ (label z.2) - θ (label z.1) : ℝ) : ℂ) * Complex.I)‖)
    (c : ℝ) (hc : c < Real.log 4 / (m : ℝ)) :
    ∃ N : ℕ, c < ∫ z : X × X,
      -Real.log (max (Real.exp (-(N : ℝ))) (d z)) ∂(μ.prod μ) := by
  by_contra hbad
  push_neg at hbad
  let u : X × X → ℝ := fun z => min (x z.1) (x z.2)
  let q : X × X → ℝ := fun z => Real.exp (-|x z.2 - x z.1|)
  let φ : X × X → ℝ := fun z => θ (label z.2) - θ (label z.1)
  have hφ' : Measurable (fun z => θ (label z)) := (measurable_of_countable θ).comp hl
  have hu : Measurable u := by dsimp only [u]; fun_prop
  have hu0 (z : X × X) : 0 ≤ u z := le_min (hx0 _) (hx0 _)
  have hq : Measurable q := by dsimp only [q]; fun_prop
  have hφ : Measurable φ := by dsimp only [φ]; fun_prop
  have hq0 (z : X × X) : 0 ≤ q z := (Real.exp_pos _).le
  have hq1 (z : X × X) : q z ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hdu : ∀ᵐ z ∂(μ.prod μ : MeasureTheory.Measure (X × X)),
      d z ≤ 2 * Real.exp (-u z) := by
    filter_upwards [hfactor] with z hz
    rw [hz]
    have h := radial_phase_norm_upper (q z) (φ z) (hq0 z) (hq1 z)
    change Real.exp (-u z) * _ ≤ 2 * Real.exp (-u z)
    nlinarith only [h, Real.exp_pos (-u z)]
  have hui := radial_probability_coordinate_integrable_of_cutoff_bound
    (μ.prod μ) u d hu hd hu0 hd2 hdu c hbad
  obtain ⟨r, hr, hr1, hgap⟩ := radial_probability_ray_abel_energy_gap_of_integrable
    m hm μ x label θ hx hl hθ hinj hx0 hui c hc
  have hlog := radial_probability_complex_abel_integrable (μ.prod μ) q φ hq hφ hq0 hq1
    r hr.le hr1
  let J : ℝ := (∫ z : X × X, u z ∂(μ.prod μ)) +
    (∫ z : X × X, -Real.log ‖1 - ((r * q z : ℝ) : ℂ) *
      Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ ∂(μ.prod μ)) + Real.log r / 2
  have hJ : c < J := hgap
  have hC : 0 ≤ -Real.log (1 - r) := neg_nonneg.mpr
    (Real.log_nonpos (by linarith) (by linarith))
  have ht := radial_probability_abel_tail_tendsto_zero (μ.prod μ) u hu hu0 hui
    (-Real.log (1 - r)) hC
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      (∫ z : X × X, max 0 (u z - Real.log (1 - r) - (N : ℝ)) ∂(μ.prod μ)) < J - c := by
    simpa only [sub_eq_add_neg] using ht.eventually (gt_mem_nhds (sub_pos.mpr hJ))
  obtain ⟨N, hN⟩ := hevent.exists
  have htail : MeasureTheory.Integrable
      (fun z : X × X => max 0 (u z - Real.log (1 - r) - (N : ℝ))) (μ.prod μ) := by
    apply (hui.sub (MeasureTheory.integrable_const (Real.log (1 - r)))).mono'
      (measurable_const.max ((hu.sub_const _).sub_const _)).aestronglyMeasurable
    filter_upwards with z
    change ‖max 0 (u z - Real.log (1 - r) - (N : ℝ))‖ ≤ u z - Real.log (1 - r)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    apply max_le (by linarith [hu0 z])
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hcut := radial_probability_cutoff_integrable (μ.prod μ) d hd hd2 N
  have hmono := MeasureTheory.integral_mono_ae (hui.add hlog)
    ((hcut.sub (MeasureTheory.integrable_const (Real.log r / 2))).add htail) (by
      filter_upwards [hfactor] with z hz
      have h := radial_log_coordinate_abel_le_cutoff (u z) (q z) (φ z) r
        (hq0 z) (hq1 z) hr hr1 N
      change u z + -Real.log ‖1 - ((r * q z : ℝ) : ℂ) *
        Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ ≤ _
      change d z = Real.exp (-u z) * ‖1 - ((q z : ℝ) : ℂ) *
        Complex.exp (((φ z : ℝ) : ℂ) * Complex.I)‖ at hz
      rw [← hz] at h
      exact h)
  have hleft := MeasureTheory.integral_add hui hlog
  have hright := MeasureTheory.integral_add
    (hcut.sub (MeasureTheory.integrable_const (Real.log r / 2))) htail
  have hright' := MeasureTheory.integral_sub hcut
    (MeasureTheory.integrable_const (Real.log r / 2))
  dsimp only [Pi.add_apply, Pi.sub_apply] at hmono hleft hright hright'
  rw [hleft, hright, hright', MeasureTheory.integral_const,
    MeasureTheory.probReal_univ, one_smul] at hmono
  dsimp only [J] at hN
  linarith only [hmono, hN, hbad N]
theorem radial_phase_norm_neg (q θ : ℝ) :
    ‖1 - (q : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ =
      ‖1 - (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have h := radial_interval_phase_norm_sq q (-θ)
  have h' := radial_interval_phase_norm_sq q θ
  rw [Real.cos_neg] at h
  nlinarith [norm_nonneg (1 - (q : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)),
    norm_nonneg (1 - (q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))]
theorem radial_polar_distance_factor_of_le (a b φ ψ : ℝ) (hab : a ≤ b) :
    ‖(Real.exp (-a) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) -
      (Real.exp (-b) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ =
      Real.exp (-a) * ‖1 - (Real.exp (-(b - a)) : ℂ) *
        Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I)‖ := by
  have hrad : (Real.exp (-a) : ℂ) * (Real.exp (-(b - a)) : ℂ) =
      (Real.exp (-b) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hphase : Complex.exp ((φ : ℂ) * Complex.I) *
      Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((ψ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hprod : ((Real.exp (-a) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) *
      ((Real.exp (-(b - a)) : ℂ) * Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I)) =
      (Real.exp (-b) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
    calc
      _ = ((Real.exp (-a) : ℂ) * (Real.exp (-(b - a)) : ℂ)) *
          (Complex.exp ((φ : ℂ) * Complex.I) *
            Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [hrad, hphase]
  calc
    _ = ‖((Real.exp (-a) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) *
        (1 - (Real.exp (-(b - a)) : ℂ) *
          Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I))‖ := by
      rw [mul_sub, mul_one, hprod]
    _ = _ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]
theorem radial_polar_distance_factor (a b φ ψ : ℝ) :
    ‖(Real.exp (-a) : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) -
      (Real.exp (-b) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖ =
      Real.exp (-min a b) * ‖1 - (Real.exp (-|b - a|) : ℂ) *
        Complex.exp (((ψ - φ : ℝ) : ℂ) * Complex.I)‖ := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact radial_polar_distance_factor_of_le a b φ ψ hab
  · rw [norm_sub_rev, radial_polar_distance_factor_of_le b a ψ φ hba,
      min_eq_right hba, abs_of_nonpos (sub_nonpos.mpr hba)]
    have hsub : a - b = -(b - a) := by ring
    have hphase : φ - ψ = -(ψ - φ) := by ring
    rw [hsub, hphase, radial_phase_norm_neg]
theorem radial_unit_phase_choice (a : ℂ) (ha : ‖a‖ = 1) :
    ∃ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧
      Complex.exp ((θ : ℂ) * Complex.I) = a := by
  have hexp : Complex.exp ((a.arg : ℂ) * Complex.I) = a := by
    simpa only [ha, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I a
  by_cases harg : a.arg < 0
  · refine ⟨a.arg + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · linarith [Complex.neg_pi_lt_arg a, Real.pi_pos]
    · linarith
    · rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      have hperiod : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
        simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using Complex.exp_two_pi_mul_I
      rw [hperiod, mul_one, hexp]
  · exact ⟨a.arg, ⟨le_of_not_gt harg, by linarith [Complex.arg_le_pi a, Real.pi_pos]⟩, hexp⟩
theorem radial_tree_direction_mem (A : Finset ℂ) (hA : ∀ a ∈ A, ‖a‖ = 1)
    (a₀ : ℂ) (ha₀ : a₀ ∈ A) (z : radial_tree_set A 1) :
    (if (z : ℂ) = 0 then a₀ else (z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ∈ A := by
  classical
  by_cases hz : (z : ℂ) = 0
  · simpa only [if_pos hz] using ha₀
  · rw [if_neg hz]
    obtain ⟨a, ha, t, ht, ht1, hta⟩ := (radial_tree_set_mem_iff A 1 z).mp z.property
    have htn : ‖(z : ℂ)‖ = t := by
      rw [hta, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, hA a ha, mul_one]
    have htne : t ≠ 0 := by
      intro h
      apply hz
      rw [hta, h, Complex.ofReal_zero, zero_mul]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast htne
    rw [htn, hta, mul_div_cancel_left₀ a htC]
    exact ha
theorem radial_tree_measurable_polar_coordinates (A : Finset ℂ) (hA₀ : A.Nonempty)
    (hA : ∀ a ∈ A, ‖a‖ = 1) :
    ∃ (x : radial_tree_set A 1 → ℝ) (label : radial_tree_set A 1 → Fin A.card)
      (θ : Fin A.card → ℝ), Measurable x ∧ Measurable label ∧
      (∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) ∧ Function.Injective θ ∧
      (∀ z, 0 ≤ x z) ∧ ∀ z : radial_tree_set A 1, (z : ℂ) ≠ 0 →
        (Real.exp (-x z) : ℂ) * Complex.exp (((θ (label z) : ℝ) : ℂ) * Complex.I) = z := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA₀
  let e := A.equivFin
  have hunit (i : Fin A.card) : ‖((e.symm i : A) : ℂ)‖ = 1 := hA _ (e.symm i).property
  choose θ hθ hexp using fun i : Fin A.card => radial_unit_phase_choice (e.symm i) (hunit i)
  have hinj : Function.Injective θ := by
    intro i j hij
    have h := (hexp i).symm.trans ((congrArg (fun t : ℝ =>
      Complex.exp ((t : ℂ) * Complex.I)) hij).trans (hexp j))
    exact e.symm.injective (Subtype.ext h)
  let dir : radial_tree_set A 1 → A := fun z =>
    ⟨if (z : ℂ) = 0 then a₀ else (z : ℂ) / (‖(z : ℂ)‖ : ℂ),
      radial_tree_direction_mem A hA a₀ ha₀ z⟩
  have hdir : Measurable dir := by
    apply Measurable.subtype_mk
    apply Measurable.ite (measurable_subtype_coe (measurableSet_singleton 0)) measurable_const
    exact measurable_subtype_coe.div measurable_subtype_coe.norm.complex_ofReal
  let label : radial_tree_set A 1 → Fin A.card := fun z => e (dir z)
  have hl : Measurable label := (measurable_of_finite e).comp hdir
  let x : radial_tree_set A 1 → ℝ := fun z => -Real.log ‖(z : ℂ)‖
  have hx : Measurable x := measurable_subtype_coe.norm.log.neg
  have hx0 (z : radial_tree_set A 1) : 0 ≤ x z :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (radial_tree_set_norm_le_one A hA z z.property))
  refine ⟨x, label, θ, hx, hl, hθ, hinj, hx0, ?_⟩
  intro z hz
  have hp : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz
  have hrad : Real.exp (-x z) = ‖(z : ℂ)‖ := by
    dsimp only [x]
    rw [neg_neg, Real.exp_log hp]
  have hphase : Complex.exp (((θ (label z) : ℝ) : ℂ) * Complex.I) =
      (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
    rw [hexp]
    change ((e.symm (e (dir z)) : A) : ℂ) = _
    rw [e.symm_apply_apply]
    exact if_neg hz
  rw [hrad, hphase]
  have hn : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
theorem radial_probability_truncated_energy_bound (A : Finset ℂ) (hA₀ : A.Nonempty)
    (hA : ∀ a ∈ A, ‖a‖ = 1) (c : ℝ) (hc : c < Real.log 4 / (A.card : ℝ))
    (μ : MeasureTheory.ProbabilityMeasure (radial_tree_set A 1)) :
    ∃ N : ℕ, c < ∫ z : (radial_tree_set A 1) × (radial_tree_set A 1),
      -Real.log (max (Real.exp (-(N : ℝ))) (dist z.1 z.2)) ∂(μ.prod μ) := by
  classical
  by_cases hatom : ∃ a : radial_tree_set A 1,
      (μ : MeasureTheory.Measure (radial_tree_set A 1)) {a} ≠ 0
  · obtain ⟨a, ha⟩ := hatom
    exact radial_tree_probability_truncated_energy_of_atom A hA μ a ha c
  push_neg at hatom
  obtain ⟨x, label, θ, hx, hl, hθ, hinj, hx0, hpolar⟩ :=
    radial_tree_measurable_polar_coordinates A hA₀ hA
  have hzero : (0 : ℂ) ∈ radial_tree_set A 1 := by
    obtain ⟨a, ha⟩ := hA₀
    apply (radial_tree_set_mem_iff A 1 0).mpr
    exact ⟨a, ha, 0, le_rfl, by norm_num, by simp⟩
  let o : radial_tree_set A 1 := ⟨0, hzero⟩
  have hne : ∀ᵐ (z : radial_tree_set A 1) ∂(μ : MeasureTheory.Measure (radial_tree_set A 1)),
      (z : ℂ) ≠ 0 := by
    have h : ∀ᵐ (z : radial_tree_set A 1)
        ∂(μ : MeasureTheory.Measure (radial_tree_set A 1)), z ≠ o := by
      rw [MeasureTheory.ae_iff]
      simpa using hatom o
    filter_upwards [h] with z hz
    intro hz0
    exact hz (Subtype.ext hz0)
  have hpairs : ∀ᵐ (z : (radial_tree_set A 1) × (radial_tree_set A 1)) ∂(μ.prod μ : MeasureTheory.Measure
      ((radial_tree_set A 1) × (radial_tree_set A 1))), (z.1 : ℂ) ≠ 0 ∧ (z.2 : ℂ) ≠ 0 := by
    change ∀ᵐ z ∂((μ : MeasureTheory.Measure (radial_tree_set A 1)).prod
      (μ : MeasureTheory.Measure (radial_tree_set A 1))), _
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [hne] with a ha
    exact hne.mono (fun b hb => ⟨ha, hb⟩)
  apply radial_probability_ray_truncated_energy_of_factor A.card (Finset.card_pos.mpr hA₀)
    μ x label θ hx hl hθ hinj hx0 (fun z => dist z.1 z.2) (by fun_prop) _ _ c hc
  · intro z
    change dist (z.1 : ℂ) (z.2 : ℂ) ≤ 2
    exact (dist_le_norm_add_norm _ _).trans (by
      linarith [radial_tree_set_norm_le_one A hA z.1 z.1.property,
        radial_tree_set_norm_le_one A hA z.2 z.2.property])
  · filter_upwards [hpairs] with z hz
    rw [Subtype.dist_eq, dist_eq_norm]
    rw [← hpolar z.1 hz.1, ← hpolar z.2 hz.2]
    exact radial_polar_distance_factor _ _ _ _
theorem radial_uniform_truncated_energy (A : Finset ℂ) (hA₀ : A.Nonempty)
    (hA : ∀ a ∈ A, ‖a‖ = 1) (c : ℝ) (hc : c < Real.log 4 / (A.card : ℝ)) :
    ∃ M : ℝ, ∀ (n : ℕ) (z : Fin n → ℂ),
      (∀ i, z i ∈ radial_tree_set A 1) →
      (n : ℝ) ^ 2 * c ≤ ∑ i : Fin n, ∑ j : Fin n,
        -Real.log (max (Real.exp (-M)) ‖z i - z j‖) := by
  letI : CompactSpace (radial_tree_set A 1) :=
    isCompact_iff_compactSpace.mp (radial_tree_set_compact A 1)
  obtain ⟨N, hN⟩ := radial_probability_uniform_truncated_energy_of_pointwise c
    (radial_probability_truncated_energy_bound A hA₀ hA c hc)
  refine ⟨(N : ℝ), fun n z hz => ?_⟩
  have h := radial_finite_truncated_energy_of_probability_bound (N : ℝ) c hN
    n (fun i => (⟨z i, hz i⟩ : radial_tree_set A 1))
  simpa only [Subtype.dist_eq, dist_eq_norm] using h
theorem normalized_radial_fekete_estimate (A : Finset ℂ) (hA₀ : A.Nonempty)
    (hA : ∀ a ∈ A, ‖a‖ = 1) (b : ℝ) (hb : (1 : ℝ) / 4 < b) :
    ∃ n : ℕ, 1 < n ∧ ∀ z : Fin n → ℂ,
      (∀ i, z i ∈ (⋃ a ∈ A, (fun t : ℝ => (t : ℂ) * a) '' Set.Icc 0 (1 : ℝ))) →
      (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, ‖z i - z j‖) ^
        A.card ≤ b ^ (n * (n - 1)) := by
  have hm : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA₀
  have hb₀ : 0 < b := by linarith
  have hlog : -Real.log b < Real.log 4 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) hb
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at h
    linarith
  obtain ⟨c, hc₀, hc₁⟩ := exists_between (div_lt_div_of_pos_right hlog hm)
  obtain ⟨M, hM⟩ := radial_uniform_truncated_energy A hA₀ hA c hc₁
  have hc : -Real.log b < (A.card : ℝ) * c := by
    have h := (div_lt_iff₀ hm).mp hc₀
    linarith
  simpa only [radial_tree_set, radial_fekete_product] using
    radial_normalized_fekete_of_truncated_energy A hA₀ b hb₀ M c hc hM
theorem radial_tree_contracting_monic (A : Finset ℂ) (T : ℝ)
    (hA₀ : A.Nonempty) (hA : ∀ a ∈ A, ‖a‖ = 1)
    (hT : 0 ≤ T) (hpower : T ^ A.card < 4) :
    ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
      ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ a ∈ A, ∀ t : ℝ,
        0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q := by
  exact radial_tree_contracting_monic_of_normalized_fekete_estimate_expanded
    A T hA₀ hA hT hpower (normalized_radial_fekete_estimate A hA₀ hA)
theorem integration_reverse_square {P Q F G : Polynomial ℚ} (hP : P.Monic) (hirr : Irreducible P)
    (hQ : Q.Monic) (hd : Q.natDegree = P.natDegree)
    (hsq : G ^ 2 = F) (hf : F.reverse = P * Q) : Q = P := by
  have hs : G.reverse ^ 2 = F.reverse := by
    simpa only [pow_two, Polynomial.reverse_mul_of_domain] using
      congrArg Polynomial.reverse hsq
  exact Submission.Helpers.polynomial_eq_of_monic_irreducible_mul_eq_sq
    hP hirr hQ hd (hs.trans hf)
theorem integration_root_enumeration {K : Type*} [Field K] [NumberField K] (α : K) :
    Nonempty ((minpoly ℚ α).rootSet ℂ ≃ Fin (minpoly ℚ α).natDegree) := by
  classical
  have hsep := (minpoly.irreducible (IsIntegral.of_finite ℚ α)).separable
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep
    (IsAlgClosed.splits ((minpoly ℚ α).map (algebraMap ℚ ℂ)))
  exact ⟨Fintype.equivFinOfCardEq hcard⟩
theorem integration_degree_drop_exponent {K : Type*} [Field K] [NumberField K] (α : K) (hα : α ≠ 0)
    (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree)
    (hih : (2 : ℝ) ≤ NumberField.house (α ^ 2) ^
      (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ (α ^ 2)).arg).card)) :
    (2 : ℝ) ≤ NumberField.house α ^
      (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) := by
  have hc := Submission.Helpers.argument_card_sq_of_degree_drop α hα hdrop
  rw [NumberField.house_pow, ← pow_mul] at hih
  have he : 2 * (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ (α ^ 2)).arg).card) =
      4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card := by omega
  rwa [he] at hih
theorem integration_radius_exponent (H : ℝ) (m a : ℕ) (hH : 1 ≤ H) (ha : a ≤ 2 * m)
    (hlt : H ^ (4 * m) < 2) : (H ^ 4) ^ a < 4 := by
  have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH
  have hp : 0 ≤ H ^ (4 * m) := pow_nonneg (by linarith) _
  calc
    (H ^ 4) ^ a ≤ (H ^ 4) ^ (2 * m) := pow_le_pow_right₀ hH4 ha
    _ = (H ^ (4 * m)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ < 4 := by nlinarith
theorem integration_second_drop {P R G : Polynomial ℚ} (hP : P.Monic) (hirr : Irreducible P)
    (hR : R.Monic) (hd : 2 * R.natDegree = P.natDegree)
    (hsq : G ^ 2 = P * R ^ 2) : False := by
  have heq : R ^ 2 = P :=
    Submission.Helpers.polynomial_eq_of_monic_irreducible_mul_eq_sq
      hP hirr (hR.pow 2) (by rw [Polynomial.natDegree_pow]; omega) hsq
  exact not_irreducible_pow (by decide : (2 : ℕ) ≠ 1) (heq.symm ▸ hirr)
theorem integration_distinct_root_product (P : Polynomial ℚ) (hM : P.Monic) (hS : P.Separable) :
    P.map (algebraMap ℚ ℂ) =
      ∏ z : P.rootSet ℂ, (Polynomial.X - Polynomial.C (z : ℂ)) := by
  classical
  let g := P.map (algebraMap ℚ ℂ)
  have hnd := Polynomial.nodup_roots (hS.map (f := algebraMap ℚ ℂ))
  change g = ∏ z : g.roots.toFinset, (Polynomial.X - Polynomial.C (z : ℂ))
  rw [Finset.prod_coe_sort g.roots.toFinset (fun z : ℂ => Polynomial.X - Polynomial.C z)]
  change g = (g.roots.toFinset.val.map (fun z => Polynomial.X - Polynomial.C z)).prod
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  exact (IsAlgClosed.splits g).eq_prod_roots_of_monic (hM.map _)
theorem integration_reciprocal_unique {K : Type*} [Field K] [NumberField K]
    (β : K) (hβ : β ≠ 0) (A : Polynomial ℚ)
    (hA : A.coeff 0 = 1) (hd : A.natDegree ≤ (minpoly ℚ β).natDegree)
    (hr : Polynomial.aeval (β⁻¹) A = 0) : A = (minpoly ℚ β).reverse := by
  let d := (minpoly ℚ β).natDegree
  let R := Polynomial.reflect d A
  have hdeg : R.natDegree ≤ d := by
    exact Polynomial.natDegree_reflect_le.trans (max_le (le_refl _) hd)
  have hc : R.coeff d = 1 := by
    simpa only [R, Polynomial.coeff_reflect, Polynomial.revAt_le (le_refl d),
      Nat.sub_self] using hA
  have hM : R.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hdeg hc
  letI : Invertible (β⁻¹) := invertibleOfNonzero (inv_ne_zero hβ)
  have hroot : Polynomial.aeval β R = 0 := by
    simpa only [invOf_eq_inv, inv_inv, Polynomial.aeval_def, R] using
      (Polynomial.eval₂_reflect_eq_zero_iff (algebraMap ℚ K) (β⁻¹) d A hd).mpr hr
  have he : R = minpoly ℚ β := by
    apply minpoly.unique_of_degree_le_degree_minpoly ℚ β hM hroot
    rw [Polynomial.degree_eq_natDegree hM.ne_zero,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite ℚ β))]
    exact_mod_cast hdeg
  simpa only [R, d, Polynomial.reflect_reflect, Polynomial.reverse] using
    congrArg (Polynomial.reflect d) he
theorem integration_transform_bound (F : Polynomial ℤ) :
    ((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).natDegree ≤
        F.natDegree := by
  have hs := congrArg Polynomial.natDegree
    (Submission.Helpers.even_odd_power_transform_subst F)
  have hm := Polynomial.natDegree_mul_le (p := F) (q := F.comp (-Polynomial.X))
  simp only [Polynomial.natDegree_comp, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one] at hs hm
  omega
theorem integration_transform_preserved {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α) (hα : α ≠ 0)
    (hdegree : (minpoly ℚ α).natDegree = (minpoly ℚ (α ^ 2)).natDegree) :
    let F := (minpoly ℤ α).reverse
    ((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).map
        (Int.castRingHom ℚ) = (minpoly ℚ (α ^ 2)).reverse := by
  let F := (minpoly ℤ α).reverse
  let A := (Polynomial.contract 2 F) ^ 2 -
    Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2
  change A.map (Int.castRingHom ℚ) = (minpoly ℚ (α ^ 2)).reverse
  apply integration_reciprocal_unique (α ^ 2) (pow_ne_zero 2 hα)
  · change (A.map (Int.castRingHom ℚ)).coeff 0 = 1
    rw [Polynomial.coeff_map]
    change (Int.castRingHom ℚ) (((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).coeff 0) = 1
    rw [Submission.Helpers.even_odd_power_transform_coeff_zero]
    simp [F, (minpoly.monic hInt).leadingCoeff]
  · have hn : (minpoly ℤ α).natDegree = (minpoly ℚ α).natDegree := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hInt]
      exact ((minpoly.monic hInt).natDegree_map _).symm
    calc
      (A.map (Int.castRingHom ℚ)).natDegree ≤ A.natDegree := Polynomial.natDegree_map_le
      _ ≤ F.natDegree := integration_transform_bound F
      _ ≤ (minpoly ℤ α).natDegree := Polynomial.reverse_natDegree_le _
      _ = (minpoly ℚ α).natDegree := hn
      _ = (minpoly ℚ (α ^ 2)).natDegree := hdegree
  · have hrF : Polynomial.aeval (α⁻¹) F = 0 := by
      letI : Invertible α := invertibleOfNonzero hα
      simpa only [F, Polynomial.aeval_def, invOf_eq_inv] using
        (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap ℤ K) α (minpoly ℤ α)).mpr
          (minpoly.aeval ℤ α)
    have hrA : Polynomial.aeval ((α ^ 2)⁻¹) A = 0 := by
      have hs := congrArg (Polynomial.aeval (α⁻¹))
        (Submission.Helpers.even_odd_power_transform_subst F)
      change Polynomial.aeval (α⁻¹) (A.comp (Polynomial.X ^ 2)) = _ at hs
      rw [Polynomial.aeval_comp, map_mul, hrF, zero_mul] at hs
      simpa only [map_pow, Polynomial.aeval_X, inv_pow] using hs
    have hc : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = algebraMap ℤ K := by
      ext n
      simp
    exact (Polynomial.aeval_eq_aeval_map hc A ((α ^ 2)⁻¹)).symm.trans hrA
theorem integration_power_ray_cover {K : Type*} [Field K] [NumberField K]
    (α : K) (hH : 1 ≤ NumberField.house α)
    (hlt : NumberField.house α ^
      (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) < 2) :
    ∃ A : Finset ℂ, A.Nonempty ∧ (∀ a ∈ A, ‖a‖ = 1) ∧
      (NumberField.house α ^ 4) ^ A.card < 4 ∧
      ∀ (σ : K →+* ℂ) (k : ℕ), k = 2 ∨ k = 4 →
        σ (α ^ k) ∈ Submission.Helpers.radial_tree_set A (NumberField.house α ^ 4) := by
  classical
  let s := Finset.univ.image fun σ : K →+* ℂ => (σ α).arg
  let e : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * Complex.I)
  let A := s.image (fun θ => e θ ^ 2) ∪ s.image (fun θ => e θ ^ 4)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  have hAn : A.Nonempty := (hs.image (fun θ => e θ ^ 2)).mono Finset.subset_union_left
  have hcard : A.card ≤ 2 * s.card := by
    calc
      A.card ≤ (s.image (fun θ => e θ ^ 2)).card +
        (s.image (fun θ => e θ ^ 4)).card := Finset.card_union_le _ _
      _ ≤ s.card + s.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * s.card := by omega
  refine ⟨A, hAn, ?_, integration_radius_exponent _ _ _ hH hcard hlt, ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨θ, _, rfl⟩ := Finset.mem_image.mp ha
      simp [e, Complex.norm_exp_ofReal_mul_I]
    · obtain ⟨θ, _, rfl⟩ := Finset.mem_image.mp ha
      simp [e, Complex.norm_exp_ofReal_mul_I]
  · intro σ k hk
    have hm : e (σ α).arg ^ k ∈ A := by
      rcases hk with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(σ α).arg, Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(σ α).arg, Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩, rfl⟩)
    apply (Submission.Helpers.radial_tree_set_mem_iff A (NumberField.house α ^ 4) _).mpr
    refine ⟨e (σ α).arg ^ k, hm, ‖σ α‖ ^ k, pow_nonneg (norm_nonneg _) _, ?_, ?_⟩
    · calc
        ‖σ α‖ ^ k ≤ NumberField.house α ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) (NumberField.norm_embedding_le_house α σ) k
        _ ≤ NumberField.house α ^ 4 := pow_le_pow_right₀ hH (by omega)
    · simpa only [e, map_pow, Complex.ofReal_pow, mul_pow] using
        (congrArg (fun z : ℂ => z ^ k) (Complex.norm_mul_exp_arg_mul_I (σ α))).symm
theorem integration_reverse_comp_sq (F : Polynomial ℤ) :
    (F.comp (Polynomial.X ^ 2)).reverse = F.reverse.comp (Polynomial.X ^ 2) := by
  ext n
  simp only [Polynomial.coeff_reverse, ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.natDegree_expand, Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : n ≤ F.natDegree * 2
  · rw [Polynomial.revAt_le hn]
    by_cases hd : 2 ∣ n
    · have hd' : 2 ∣ F.natDegree * 2 - n := by omega
      simp only [ite_eq_left hd', ite_eq_left hd]
      rw [Polynomial.revAt_le (by omega : n / 2 ≤ F.natDegree)]
      congr 1
      omega
    · have hd' : ¬ 2 ∣ F.natDegree * 2 - n := by omega
      simp only [ite_eq_right hd', ite_eq_right hd]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]
    by_cases hd : 2 ∣ n
    · simp only [ite_eq_left hd]
      rw [Polynomial.revAt_eq_self_of_lt (by omega : F.natDegree < n / 2)]
    · simp only [ite_eq_right hd]
theorem integration_integral_comp_drop {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α)
    (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree) :
    (minpoly ℤ (α ^ 2)).comp (Polynomial.X ^ 2) = minpoly ℤ α := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  have h0 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hInt
  have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (hInt.pow 2)
  change ((minpoly ℤ (α ^ 2)).map (algebraMap ℤ ℚ)).comp (Polynomial.X ^ 2) =
    (minpoly ℤ α).map (algebraMap ℤ ℚ)
  rw [← h0, ← h1]
  exact Submission.Helpers.minpoly_sq_comp_of_degree_drop α hdrop
theorem integration_transform_even (F : Polynomial ℤ) :
    let E := F.comp (Polynomial.X ^ 2)
    (Polynomial.contract 2 E) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX E)) ^ 2 = F ^ 2 := by
  dsimp only
  apply Polynomial.expand_injective (by norm_num : 0 < (2 : ℕ))
  change (((Polynomial.contract 2 (F.comp (Polynomial.X ^ 2))) ^ 2 -
    Polynomial.X * (Polynomial.contract 2 (Polynomial.divX
      (F.comp (Polynomial.X ^ 2)))) ^ 2).comp (Polynomial.X ^ 2)) =
    (F ^ 2).comp (Polynomial.X ^ 2)
  rw [Submission.Helpers.even_odd_power_transform_subst]
  simp only [Polynomial.comp_assoc, Polynomial.pow_comp,
    Polynomial.X_comp, neg_sq]
  ring
theorem integration_transform_drop {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α)
    (hdrop : (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree) :
    let F := (minpoly ℤ α).reverse
    (Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2 =
        (minpoly ℤ (α ^ 2)).reverse ^ 2 := by
  dsimp only
  rw [← integration_integral_comp_drop α hInt hdrop, integration_reverse_comp_sq]
  exact integration_transform_even _
theorem integration_map_reverse {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (hf : Function.Injective f) (P : Polynomial R) :
    P.reverse.map f = (P.map f).reverse := by
  unfold Polynomial.reverse
  rw [Polynomial.natDegree_map_eq_of_injective hf]
  exact (Polynomial.reflect_map f P _).symm
theorem integration_reverse_reverse {R : Type*} [Semiring R]
    (P : Polynomial R) (hP : P.coeff 0 ≠ 0) : P.reverse.reverse = P := by
  have ht : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  change Polynomial.reflect P.reverse.natDegree (Polynomial.reflect P.natDegree P) = P
  rw [Polynomial.reverse_natDegree, ht, Nat.sub_zero]
  exact Polynomial.reflect_reflect
theorem integration_house_eq_of_minpoly_eq {K : Type*} [Field K] [NumberField K]
    (α β : K) (h : minpoly ℚ α = minpoly ℚ β) : NumberField.house α = NumberField.house β := by
  classical
  have aux (x y : K) (hm : minpoly ℚ x = minpoly ℚ y) :
      Finset.univ.sup' Finset.univ_nonempty (fun σ : K →+* ℂ => ‖σ x‖₊) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun σ : K →+* ℂ => ‖σ y‖₊) := by
    apply Finset.sup'_le
    intro σ _
    have hx : σ x ∈ (minpoly ℚ y).rootSet ℂ := by
      rw [← hm, ← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ x]
      exact ⟨σ, rfl⟩
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ y] at hx
    obtain ⟨τ, hτ⟩ := hx
    rw [← hτ]
    exact Finset.le_sup' (fun φ : K →+* ℂ => ‖φ y‖₊) (Finset.mem_univ τ)
  rw [NumberField.house_eq_sup' α, NumberField.house_eq_sup' β]
  exact congrArg (fun x : NNReal => (x : ℝ)) (le_antisymm (aux α β h) (aux β α h.symm))
theorem integration_reverse_prod (n : ℕ) (b : Fin n → ℂ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (b i))).reverse =
      ∏ i : Fin n, (1 - Polynomial.C (b i) * Polynomial.X) := by
  classical
  have he (z : ℂ) : (Polynomial.X - Polynomial.C z).reverse =
      1 - Polynomial.C z * Polynomial.X := by
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.reverse_add_C]
    simp [Polynomial.reverse, sub_eq_add_neg]
  let rev : Polynomial ℂ →* Polynomial ℂ :=
    { toFun := Polynomial.reverse
      map_one' := by simp [Polynomial.reverse]
      map_mul' := Polynomial.reverse_mul_of_domain }
  change rev (∏ i : Fin n, (Polynomial.X - Polynomial.C (b i))) = _
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => he (b i))
theorem integration_transform_product (n : ℕ) (b : Fin n → ℂ) (F : Polynomial ℤ)
    (hF : F.map (Int.castRingHom ℂ) =
      ∏ i : Fin n, (1 - Polynomial.C (b i) * Polynomial.X)) :
    ((Polynomial.contract 2 F) ^ 2 -
      Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).map
        (Int.castRingHom ℂ) =
          ∏ i : Fin n, (1 - Polynomial.C (b i ^ 2) * Polynomial.X) := by
  classical
  have hs := congrArg (Polynomial.map (Int.castRingHom ℂ))
    (Submission.Helpers.even_odd_power_transform_subst F)
  simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_neg] at hs
  apply Polynomial.expand_injective (by norm_num : 0 < (2 : ℕ))
  change (((Polynomial.contract 2 F) ^ 2 -
    Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2).map
      (Int.castRingHom ℂ)).comp (Polynomial.X ^ 2) =
    (∏ i : Fin n, (1 - Polynomial.C (b i ^ 2) * Polynomial.X)).comp (Polynomial.X ^ 2)
  rw [hs]
  simp only [hF, Polynomial.prod_comp]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.C_pow, Polynomial.pow_comp]
  ring
noncomputable def integration_power_transform (F : Polynomial ℤ) : Polynomial ℤ :=
  (Polynomial.contract 2 F) ^ 2 -
    Polynomial.X * (Polynomial.contract 2 (Polynomial.divX F)) ^ 2
theorem integration_minpoly_map (K : Type*) [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α) :
    (minpoly ℤ α).map (Int.castRingHom ℚ) = minpoly ℚ α := by
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hInt).symm
theorem integration_distinct_conjugates {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α) :
    ∃ c : Fin (minpoly ℚ α).natDegree → ℂ,
      Function.Injective c ∧
      (∀ i, ∃ σ : K →+* ℂ, c i = σ α) ∧
      (minpoly ℤ α).reverse.map (Int.castRingHom ℂ) =
        ∏ i, (1 - Polynomial.C (c i) * Polynomial.X) := by
  classical
  obtain ⟨e⟩ := integration_root_enumeration α
  let c : Fin (minpoly ℚ α).natDegree → ℂ := fun i => e.symm i
  have hc : Function.Injective c := Subtype.val_injective.comp e.symm.injective
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have hi : c i ∈ (minpoly ℚ α).rootSet ℂ := (e.symm i).property
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α] at hi
    obtain ⟨σ, hσ⟩ := hi
    exact ⟨σ, hσ.symm⟩
  · have hprod := integration_distinct_root_product (minpoly ℚ α)
      (minpoly.monic (IsIntegral.of_finite ℚ α))
      (minpoly.irreducible (IsIntegral.of_finite ℚ α)).separable
    have he : (∏ i, (Polynomial.X - Polynomial.C (c i))) =
        ∏ z : (minpoly ℚ α).rootSet ℂ, (Polynomial.X - Polynomial.C (z : ℂ)) :=
      e.symm.prod_comp (fun z => Polynomial.X - Polynomial.C (z : ℂ))
    have hmap : (minpoly ℤ α).map (Int.castRingHom ℂ) =
        (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
      rw [← integration_minpoly_map K α hInt, Polynomial.map_map]
      congr 1
    rw [integration_map_reverse _ Int.cast_injective, hmap, hprod, ← he]
    exact integration_reverse_prod _ c
theorem integration_join_products (n : ℕ) (u v : Fin n → ℂ) :
    ∃ b : Fin (2 * n) → ℂ,
      (∀ i, (∃ j, b i = u j) ∨ (∃ j, b i = v j)) ∧
      (∏ i, (1 - Polynomial.C (u i) * Polynomial.X)) *
        (∏ i, (1 - Polynomial.C (v i) * Polynomial.X)) =
          ∏ i, (1 - Polynomial.C (b i) * Polynomial.X) := by
  classical
  let e : Fin 2 × Fin n ≃ Fin (2 * n) := finProdFinEquiv
  let b : Fin (2 * n) → ℂ := fun i =>
    if (e.symm i).1 = 0 then u (e.symm i).2 else v (e.symm i).2
  refine ⟨b, ?_, ?_⟩
  · intro i
    by_cases hi : (e.symm i).1 = 0
    · exact Or.inl ⟨(e.symm i).2, if_pos hi⟩
    · exact Or.inr ⟨(e.symm i).2, if_neg hi⟩
  · have he := e.prod_comp (fun i => (1 - Polynomial.C (b i) * Polynomial.X))
    simp only [b, Equiv.symm_apply_apply] at he
    rw [Fintype.prod_prod_type, Fin.prod_univ_two] at he
    simpa using he
theorem integration_formal_square_root (F : Polynomial ℤ) (hF : F.coeff 0 = 1) :
    ∃ S : PowerSeries ℤ, PowerSeries.constantCoeff S = 1 ∧
      S ^ 2 = ((integration_power_transform F *
        integration_power_transform (integration_power_transform F) : Polynomial ℤ) :
          PowerSeries ℤ) := by
  obtain ⟨Q, hQ, hQ₀⟩ := even_odd_power_transform_mod_four F hF
  change integration_power_transform (integration_power_transform F) =
    integration_power_transform F + 4 * Q at hQ
  have hU : PowerSeries.constantCoeff
      (integration_power_transform F : PowerSeries ℤ) = 1 := by
    change (integration_power_transform F).coeff 0 = 1
    rw [integration_power_transform, even_odd_power_transform_coeff_zero, hF, one_pow]
  have hQ' : PowerSeries.constantCoeff (Q : PowerSeries ℤ) = 0 := hQ₀
  obtain ⟨S, hS₀, hS⟩ := integral_square_root_mod_four
    (integration_power_transform F : PowerSeries ℤ) Q hU hQ'
  refine ⟨S, hS₀, ?_⟩
  have h4 : ((4 : Polynomial ℤ) : PowerSeries ℤ) = 4 := by
    have h : (4 : Polynomial ℤ) = 1 + 1 + 1 + 1 := by norm_num
    rw [h, Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_one]
    norm_num
  rw [hQ]
  simpa only [Polynomial.coe_mul, Polynomial.coe_add, h4] using hS
theorem integration_preserved_integral {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α) (hα : α ≠ 0)
    (hdegree : (minpoly ℚ α).natDegree = (minpoly ℚ (α ^ 2)).natDegree) :
    integration_power_transform (minpoly ℤ α).reverse =
      (minpoly ℤ (α ^ 2)).reverse := by
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [integration_map_reverse _ Int.cast_injective, integration_minpoly_map K _ (hInt.pow 2)]
  exact integration_transform_preserved α hInt hα hdegree
theorem integration_square_obstruction {K : Type*} [Field K] [NumberField K]
    (α : K) (hInt : IsIntegral ℤ α) (hα : α ≠ 0) (hH : 1 < NumberField.house α)
    (hsquare : ∃ G : Polynomial ℚ, G ^ 2 =
      (integration_power_transform (minpoly ℤ α).reverse *
        integration_power_transform (integration_power_transform
          (minpoly ℤ α).reverse)).map (Int.castRingHom ℚ)) :
    (minpoly ℚ (α ^ 2)).natDegree < (minpoly ℚ α).natDegree := by
  by_contra hdrop
  have hdegree : (minpoly ℚ α).natDegree = (minpoly ℚ (α ^ 2)).natDegree := by
    rcases minpoly_sq_degree_dichotomy α with h | h
    · exact h
    · have hp := minpoly.natDegree_pos (IsIntegral.of_finite ℚ (α ^ 2))
      omega
  let β := α ^ 2
  have hβ : β ≠ 0 := pow_ne_zero 2 hα
  have hβInt : IsIntegral ℤ β := hInt.pow 2
  have hU := integration_preserved_integral α hInt hα hdegree
  obtain ⟨G, hG⟩ := hsquare
  rw [hU] at hG
  let P := minpoly ℚ β
  let R := minpoly ℚ (β ^ 2)
  have hP : P.Monic := minpoly.monic (IsIntegral.of_finite ℚ β)
  have hiP : Irreducible P := minpoly.irreducible (IsIntegral.of_finite ℚ β)
  have hR : R.Monic := minpoly.monic (IsIntegral.of_finite ℚ (β ^ 2))
  have hcP : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero
    (IsIntegral.of_finite ℚ β) hβ
  have hcR : R.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero
    (IsIntegral.of_finite ℚ (β ^ 2)) (pow_ne_zero 2 hβ)
  have hmapP : (minpoly ℤ β).reverse.map (Int.castRingHom ℚ) = P.reverse := by
    rw [integration_map_reverse _ Int.cast_injective, integration_minpoly_map K β hβInt]
  change G ^ 2 = ((minpoly ℤ β).reverse *
    integration_power_transform (minpoly ℤ β).reverse).map (Int.castRingHom ℚ) at hG
  rcases minpoly_sq_degree_dichotomy β with hd | hd
  · have hmapR : (integration_power_transform (minpoly ℤ β).reverse).map
        (Int.castRingHom ℚ) = R.reverse :=
      integration_transform_preserved β hβInt hβ hd
    have hsq : G.reverse ^ 2 = P * R := by
      rw [Polynomial.map_mul, hmapP, hmapR] at hG
      simpa only [pow_two, Polynomial.reverse_mul_of_domain,
        integration_reverse_reverse P hcP, integration_reverse_reverse R hcR] using
          congrArg Polynomial.reverse hG
    have heq : R = P := polynomial_eq_of_monic_irreducible_mul_eq_sq
      hP hiP hR hd.symm hsq
    have hhouse := integration_house_eq_of_minpoly_eq β (β ^ 2) heq.symm
    rw [NumberField.house_pow β 2] at hhouse
    have hβH : 1 < NumberField.house β := by
      dsimp [β]
      rw [NumberField.house_pow]
      nlinarith
    nlinarith
  · have hdropβ : (minpoly ℚ (β ^ 2)).natDegree < (minpoly ℚ β).natDegree := by
      have hp := minpoly.natDegree_pos (IsIntegral.of_finite ℚ (β ^ 2))
      omega
    have hV : integration_power_transform (minpoly ℤ β).reverse =
        (minpoly ℤ (β ^ 2)).reverse ^ 2 :=
      integration_transform_drop β hβInt hdropβ
    have hmapR : (minpoly ℤ (β ^ 2)).reverse.map (Int.castRingHom ℚ) = R.reverse := by
      rw [integration_map_reverse _ Int.cast_injective,
        integration_minpoly_map K _ (hβInt.pow 2)]
    have hsq : G.reverse ^ 2 = P * R ^ 2 := by
      rw [hV, Polynomial.map_mul, Polynomial.map_pow, hmapP, hmapR] at hG
      simpa only [pow_two, Polynomial.reverse_mul_of_domain,
        integration_reverse_reverse P hcP, integration_reverse_reverse R hcR] using
          congrArg Polynomial.reverse hG
    exact integration_second_drop hP hiP hR hd.symm hsq
theorem integration_square_from_contraction
    (hcontract : ∀ (A : Finset ℂ) (T : ℝ), A.Nonempty →
      (∀ a ∈ A, ‖a‖ = 1) → 0 ≤ T → T ^ A.card < 4 →
      ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
        ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ a ∈ A, ∀ t : ℝ,
          0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q)
    {K : Type*} [Field K] [NumberField K] (α : K)
    (hInt : IsIntegral ℤ α) (hH : 1 ≤ NumberField.house α)
    (hlt : NumberField.house α ^
      (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) < 2) :
    ∃ G : Polynomial ℚ, G ^ 2 =
      (integration_power_transform (minpoly ℤ α).reverse *
        integration_power_transform (integration_power_transform
          (minpoly ℤ α).reverse)).map (Int.castRingHom ℚ) := by
  classical
  let F := (minpoly ℤ α).reverse
  let U := integration_power_transform F
  let V := integration_power_transform U
  obtain ⟨c, _, hc, hF⟩ := integration_distinct_conjugates α hInt
  have hU : U.map (Int.castRingHom ℂ) =
      ∏ i, (1 - Polynomial.C (c i ^ 2) * Polynomial.X) :=
    integration_transform_product _ c F hF
  have hV : V.map (Int.castRingHom ℂ) =
      ∏ i, (1 - Polynomial.C (c i ^ 4) * Polynomial.X) := by
    have hv := integration_transform_product _ (fun i => c i ^ 2) U hU
    change V.map (Int.castRingHom ℂ) =
      ∏ i, (1 - Polynomial.C ((c i ^ 2) ^ 2) * Polynomial.X) at hv
    rw [hv]
    simp only [← pow_mul, Nat.reduceMul]
  obtain ⟨b, hb, hprod⟩ := integration_join_products _
    (fun i => c i ^ 2) (fun i => c i ^ 4)
  have hUV : (U * V).map (Int.castRingHom ℂ) =
      ∏ i, (1 - Polynomial.C (b i) * Polynomial.X) := by
    rw [Polynomial.map_mul, hU, hV, hprod]
  obtain ⟨A, hA, hunit, hrad, hcover⟩ := integration_power_ray_cover α hH hlt
  have hpoint : ∀ i, b i ∈ radial_tree_set A (NumberField.house α ^ 4) := by
    intro i
    rcases hb i with ⟨j, hj⟩ | ⟨j, hj⟩
    · obtain ⟨σ, hσ⟩ := hc j
      rw [hj, hσ, ← map_pow]
      exact hcover σ 2 (Or.inl rfl)
    · obtain ⟨σ, hσ⟩ := hc j
      rw [hj, hσ, ← map_pow]
      exact hcover σ 4 (Or.inr rfl)
  have hF₀ : F.coeff 0 = 1 := by
    simp [F, (minpoly.monic hInt).leadingCoeff]
  obtain ⟨S, hS₀, hS⟩ := integration_formal_square_root F hF₀
  change S ^ 2 = ((U * V : Polynomial ℤ) : PowerSeries ℤ) at hS
  apply radial_integral_square_root_is_polynomial
    (minpoly ℚ α).natDegree b (U * V) S hS₀ hS hUV
  obtain ⟨p, hp, hpd, q, hq₀, hq₁, hpq⟩ := hcontract A (NumberField.house α ^ 4)
    hA hunit (pow_nonneg (by linarith) 4) hrad
  refine ⟨p, hp, hpd, q, hq₀, hq₁, ?_⟩
  intro i t ht ht₁
  obtain ⟨a, ha, r, hr, hrT, hbr⟩ :=
    (radial_tree_set_mem_iff A (NumberField.house α ^ 4) (b i)).mp (hpoint i)
  have htr : t * r ≤ NumberField.house α ^ 4 := by
    calc
      t * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht₁ hr
      _ ≤ NumberField.house α ^ 4 := by simpa using hrT
  have he : (t : ℂ) * b i = ((t * r : ℝ) : ℂ) * a := by
    rw [hbr, Complex.ofReal_mul, mul_assoc]
  rw [he]
  exact hpq a ha (t * r) (mul_nonneg ht hr) htr
theorem house_power_lower_bound_of_radial_contraction
    (hcontract : ∀ (A : Finset ℂ) (T : ℝ), A.Nonempty →
      (∀ a ∈ A, ‖a‖ = 1) → 0 ≤ T → T ^ A.card < 4 →
      ∃ p : Polynomial ℂ, p.Monic ∧ 0 < p.natDegree ∧
        ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ a ∈ A, ∀ t : ℝ,
          0 ≤ t → t ≤ T → ‖p.eval ((t : ℂ) * a)‖ ≤ q) :
    ∀ {K : Type*} [Field K] [NumberField K] (α : K),
      IsIntegral ℤ α → α ≠ 0 → ¬ IsOfFinOrder α →
        (2 : ℝ) ≤ NumberField.house α ^
          (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) := by
  intro K _ _
  classical
  have main : ∀ n : ℕ, ∀ α : K, (minpoly ℚ α).natDegree = n →
      IsIntegral ℤ α → α ≠ 0 → ¬ IsOfFinOrder α →
      (2 : ℝ) ≤ NumberField.house α ^
        (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro α hn hInt hα hnot
      by_contra hlt
      have hH := house_gt_one α hInt hα hnot
      have hs := integration_square_from_contraction hcontract α hInt hH.le
        (lt_of_not_ge hlt)
      have hd := integration_square_obstruction α hInt hα hH hs
      have hnotSq : ¬ IsOfFinOrder (α ^ 2) := by
        intro h
        exact hnot ((isOfFinOrder_pow.mp h).resolve_right (by decide))
      have hind := ih (minpoly ℚ (α ^ 2)).natDegree (by omega)
        (α ^ 2) rfl (hInt.pow 2) (pow_ne_zero 2 hα) hnotSq
      exact hlt (integration_degree_drop_exponent α hα hd hind)
  intro α
  exact main _ α rfl
theorem house_power_lower_bound {K : Type*} [Field K] [NumberField K]
    (α : K) (α_int : IsIntegral ℤ α) (α_ne_zero : α ≠ 0)
    (α_not_rootOfUnity : ¬ IsOfFinOrder α) :
    (2 : ℝ) ≤ NumberField.house α ^
      (4 * (Finset.univ.image fun σ : K →+* ℂ => (σ α).arg).card) := by
  exact house_power_lower_bound_of_radial_contraction radial_tree_contracting_monic
    α α_int α_ne_zero α_not_rootOfUnity
end Submission.Helpers
