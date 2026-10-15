import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import ChallengeDeps
import Submission.Helpers

open RademacherEnfloType
open Function MeasureTheory ProbabilityTheory Measure NNReal
open scoped ENNReal

set_option autoImplicit false
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace Submission

theorem theorem_1_1 (p : ℝ) (h1p : 1 ≤ p) (hp2 : p ≤ 2) :
    TR X p ≤ TE X p ∧ TE X p ≤ (pi / sqrt 2) * TR X p := by
  have rademacher_product_probability (n : ℕ) :
      IsProbabilityMeasure (rademacherProductDistribution (Fin n)) := by
    unfold rademacherProductDistribution
    haveI : IsProbabilityMeasure rademacherDistribution := by
      unfold rademacherDistribution
      infer_instance
    infer_instance
  have linear_cube_odd
      
      (n : ℕ) (x : Fin n → X) (ε : Fin n → ({-1, 1} : Set ℤ)) :
      (∑ j : Fin n, (((-ε) j) : ℝ) • x j) =
        -(∑ j : Fin n, ((ε j) : ℝ) • x j) := by
    change (∑ j : Fin n, (Int.cast (-(ε j : ℤ)) : ℝ) • x j) =
      -(∑ j : Fin n, ((ε j : ℤ) : ℝ) • x j)
    simp only [Int.cast_neg, neg_smul, Finset.sum_neg_distrib]
  have linear_cube_antipodal_half
      
      (n : ℕ) (x : Fin n → X) (ε : Fin n → ({-1, 1} : Set ℤ)) :
      (1 / (2 : ℝ)) • ((∑ j : Fin n, ((ε j) : ℝ) • x j) -
        (∑ j : Fin n, (((-ε) j) : ℝ) • x j)) =
        ∑ j : Fin n, ((ε j) : ℝ) • x j := by
    rw [linear_cube_odd n x ε, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
  have linear_cube_derivative
      
      (n : ℕ) (x : Fin n → X) (j : Fin n) (ε : Fin n → ({-1, 1} : Set ℤ)) :
      D j (fun δ ↦ ∑ k : Fin n, ((δ k) : ℝ) • x k) ε =
        ((ε j) : ℝ) • x j := by
    classical
    unfold D
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    rw [Finset.sum_eq_single j]
    · simp only [Function.update_self]
      change (1 / (2 : ℝ)) •
        (((ε j : ℤ) : ℝ) • x j - (Int.cast (-(ε j : ℤ)) : ℝ) • x j) =
        ((ε j : ℤ) : ℝ) • x j
      rw [Int.cast_neg, neg_smul, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
      norm_num
    · intro k hk hkj
      simp [Function.update_of_ne hkj]
    · simp
  have rademacher_sign_enorm
      
      (x : X) (ε : ({-1, 1} : Set ℤ)) :
      ‖((ε : ℤ) : ℝ) • x‖ₑ = ‖x‖ₑ := by
    rcases ε with ⟨ε, hε⟩
    have h : ε = -1 ∨ ε = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hε
    rcases h with h | h <;> subst ε <;> simp
  have linear_cube_derivative_integral
      
      (n : ℕ) (x : Fin n → X) (j : Fin n) (p : ℝ) :
      (∫⁻ ε, ‖D j (fun δ ↦ ∑ k : Fin n, ((δ k) : ℝ) • x k) ε‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n)) = ‖x j‖ₑ ^ p := by
    haveI := rademacher_product_probability n
    simp only [linear_cube_derivative, rademacher_sign_enorm]
    rw [lintegral_const, measure_univ, mul_one]
  have enflo_implies_rademacher :
      ∀ (p : ℝ) (C : ℝ≥0∞),
        1 ≤ p → p ≤ 2 →
        RademacherEnfloType.IsEnfloType X C p →
        RademacherEnfloType.IsRademacherType X C p := by
    intro p C h1p hp2 hC n hn x
    have h := hC n hn (fun ε ↦ ∑ j : Fin n, ((ε j) : ℝ) • x j)
    simpa only [linear_cube_antipodal_half, linear_cube_derivative_integral] using h
  have bernoulli_difference_moment_eq (p : ℝ) (q : Set.Icc (0 : ℝ) 1)
      (hp : 0 < p) :
      (∫⁻ ξ : (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)),
        ‖((ξ.1 : ℤ) : ℝ) - ((ξ.2 : ℤ) : ℝ)‖ₑ ^ p
        ∂(bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
          ⟨-1, by decide⟩ q).prod
          (bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
            ⟨-1, by decide⟩ q)) =
        (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) := by
    simp only [bernoulliMeasure_def, Measure.add_prod, Measure.prod_add,
      Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
      lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
    norm_num [ENNReal.zero_rpow_of_pos hp]
    have htwo : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by
      simp [enorm_eq_nnnorm]
    rw [htwo]
    change (unitInterval.toNNReal q : ℝ≥0∞) *
        ((unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) * 2 ^ p) +
        (unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) *
        ((unitInterval.toNNReal q : ℝ≥0∞) * 2 ^ p) = _
    have hq : (unitInterval.toNNReal q : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
      rw [← unitInterval.coe_toNNReal q, ENNReal.ofReal_coe_nnreal]
    have hq' : (unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) =
        ENNReal.ofReal (1 - (q : ℝ)) := by
      rw [← unitInterval.coe_symm_eq q, ← unitInterval.coe_toNNReal (unitInterval.symm q),
        ENNReal.ofReal_coe_nnreal]
    rw [hq, hq', ENNReal.ofReal_mul (mul_nonneg (by norm_num) q.property.1),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    ring
  have bernoulli_difference_moment_le :
      ∀ (p : ℝ) (q : Set.Icc (0 : ℝ) 1), 1 ≤ p → p ≤ 2 →
      (∫⁻ ξ : (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)),
        ‖((ξ.1 : ℤ) : ℝ) - ((ξ.2 : ℤ) : ℝ)‖ₑ ^ p
        ∂(bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
          ⟨-1, by decide⟩ q).prod
          (bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
            ⟨-1, by decide⟩ q)) ≤
        (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) := by
    intro p q h1p hp2
    have hp : 0 < p := by linarith
    have hp_half : 0 ≤ p / 2 := by linarith
    by_cases hq0 : (q : ℝ) = 0
    · rw [bernoulli_difference_moment_eq p q hp]
      simp [hq0, ENNReal.zero_rpow_of_pos (show 0 < p / 2 by linarith)]
    by_cases hq1 : (q : ℝ) = 1
    · rw [bernoulli_difference_moment_eq p q hp]
      simp [hq1, ENNReal.zero_rpow_of_pos (show 0 < p / 2 by linarith)]
    have ha : ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) ≤ 1 := by
      apply ENNReal.ofReal_le_one.mpr
      nlinarith [sq_nonneg ((q : ℝ) - 1 / 2)]
    have ha_pow : ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) ≤
        (ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) := by
      simpa only [ENNReal.rpow_one] using
        (ENNReal.rpow_le_rpow_of_exponent_ge ha (show p / 2 ≤ 1 by linarith) :
          (ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ)))) ^ (1 : ℝ) ≤ _)
    have hvariance : ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ))) =
        4 * ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) := by
      rw [show 8 * (q : ℝ) * (1 - (q : ℝ)) =
        4 * (2 * (q : ℝ) * (1 - (q : ℝ))) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hfour : (4 : ℝ≥0∞) ^ (p / 2) = (2 : ℝ≥0∞) ^ p := by
      calc
        (4 : ℝ≥0∞) ^ (p / 2) = ((2 : ℝ≥0∞) ^ (2 : ℝ)) ^ (p / 2) := by
          norm_num [ENNReal.rpow_natCast]
        _ = (2 : ℝ≥0∞) ^ (2 * (p / 2)) := (ENNReal.rpow_mul _ _ _).symm
        _ = (2 : ℝ≥0∞) ^ p := by congr 1; ring
    rw [bernoulli_difference_moment_eq p q hp, hvariance,
      ENNReal.mul_rpow_of_nonneg _ _ hp_half, hfour]
    gcongr
  have probability_integral_enorm_rpow_le :
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (p : ℝ) (f : Ω → X),
        1 ≤ p → MeasureTheory.AEStronglyMeasurable f μ →
        ‖∫ ω, f ω ∂μ‖ₑ ^ p ≤ ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ := by
    intro Ω _ μ _ p f hp hf
    have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
    have hL1 : (∫⁻ ω, ‖f ω‖ₑ ∂μ) = eLpNorm' f 1 μ := by
      simp [eLpNorm'_eq_lintegral_enorm]
    have hLp : ‖∫ ω, f ω ∂μ‖ₑ ≤ eLpNorm' f p μ := by
      calc
        ‖∫ ω, f ω ∂μ‖ₑ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm f
        _ = eLpNorm' f 1 μ := hL1
        _ ≤ eLpNorm' f p μ :=
          eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) hp μ hf
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp_pos]
    exact ENNReal.rpow_le_rpow hLp hp_pos.le
  have cube_flip_involutive (n : ℕ) (j : Fin n) :
      Function.Involutive (fun δ : Fin n → ({-1, 1} : Set ℤ) ↦
        Function.update δ j (-δ j)) := by
    intro δ
    funext k
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self]
      apply Subtype.ext
      change -(-(δ j : ℤ)) = (δ j : ℤ)
      exact neg_neg _
    · simp [Function.update_of_ne hk]
  have sign_noise_scalar_identity (t : ℝ) (a : ({-1, 1} : Set ℤ)) :
      (1 + t * ((a : ℤ) : ℝ)) * (((a : ℤ) : ℝ) - t) =
        (1 - t ^ 2) * ((a : ℤ) : ℝ) := by
    rcases a with ⟨a, ha⟩
    have h : a = -1 ∨ a = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    rcases h with h | h <;> subst a <;> norm_num <;> ring
  have cube_erased_weight_flip (n : ℕ) (j : Fin n) (t : ℝ)
      (δ : Fin n → ({-1, 1} : Set ℤ)) :
      ((((Function.update δ j (-δ j)) j) : ℤ) : ℝ) *
        (∏ k ∈ Finset.univ.erase j,
          (1 + t * ((((Function.update δ j (-δ j)) k) : ℤ) : ℝ))) =
        -(((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) := by
    have hprod : (∏ k ∈ Finset.univ.erase j,
        (1 + t * ((((Function.update δ j (-δ j)) k) : ℤ) : ℝ))) =
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
    rw [hprod, Function.update_self]
    change (Int.cast (-(δ j : ℤ)) : ℝ) * _ = _
    simp only [Int.cast_neg, neg_mul]
  have cube_noise_weight_coefficient (n : ℕ) (j : Fin n) (t : ℝ)
      (δ : Fin n → ({-1, 1} : Set ℤ)) :
      (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) * (((δ j : ℤ) : ℝ) - t) =
        (1 - t ^ 2) * (((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k : Fin n ↦ 1 + t * ((δ k : ℤ) : ℝ)) (Finset.mem_univ j)]
    calc
      ((1 + t * ((δ j : ℤ) : ℝ)) *
          (∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)))) *
            (((δ j : ℤ) : ℝ) - t) =
        ((1 + t * ((δ j : ℤ) : ℝ)) * (((δ j : ℤ) : ℝ) - t)) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)) := by ring
      _ = _ := by rw [sign_noise_scalar_identity]; ring
  have cube_flip_weighted_difference
      
      (n : ℕ) (j : Fin n) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (w : (Fin n → ({-1, 1} : Set ℤ)) → ℝ)
      (hw : ∀ δ, w (Function.update δ j (-δ j)) = -w δ) :
      (∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • D j f δ) =
        ∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ := by
    have hflip : (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        w δ • f (Function.update δ j (-δ j))) =
        -(∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ) := by
      calc
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
            w δ • f (Function.update δ j (-δ j))) =
          ∑ δ : Fin n → ({-1, 1} : Set ℤ),
            w (Function.update δ j (-δ j)) • f δ := by
          refine Fintype.sum_bijective (fun δ ↦ Function.update δ j (-δ j))
            (cube_flip_involutive n j).bijective _ _ ?_
          intro δ
          have hδ : Function.update (Function.update δ j (-δ j)) j
              (-(Function.update δ j (-δ j)) j) = δ := cube_flip_involutive n j δ
          rw [hδ]
        _ = _ := by simp only [hw, neg_smul, Finset.sum_neg_distrib]
    calc
      (∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • D j f δ) =
        (1 / (2 : ℝ)) • ((∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ) -
          (∑ δ : Fin n → ({-1, 1} : Set ℤ),
            w δ • f (Function.update δ j (-δ j)))) := by
        simp only [D, smul_sub, smul_smul, Finset.smul_sum, Finset.sum_sub_distrib,
          mul_comm]
      _ = _ := by
        rw [hflip, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
        norm_num
  have weighted_cube_derivative_identity :
      ∀ (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X) (t : ℝ),
        (1 - t ^ 2) • (∑ δ : (Fin n → ({-1, 1} : Set ℤ)),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • f δ) =
        ∑ δ : (Fin n → ({-1, 1} : Set ℤ)),
          (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) •
            (∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • RademacherEnfloType.D j f δ) := by
    intro n f t
    symm
    calc
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) •
            (∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • D j f δ)) =
        ∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          ((∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) *
            (((δ j : ℤ) : ℝ) - t)) • D j f δ := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
      _ = (1 - t ^ 2) •
        (∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • D j f δ) := by
        simp only [cube_noise_weight_coefficient, Finset.smul_sum, smul_smul]
      _ = (1 - t ^ 2) •
        (∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • f δ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact cube_flip_weighted_difference n j f
          (fun δ ↦ ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)))
          (fun δ ↦ cube_erased_weight_flip n j t δ)
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
  let centeredBernoulliMeasure (q : Set.Icc (0 : ℝ) 1) :
      Measure ({-1, 1} : Set ℤ) :=
    bernoulliMeasure ⟨1, by decide⟩ ⟨-1, by decide⟩ q
  letI centeredBernoulliMeasure_probability (q : Set.Icc (0 : ℝ) 1) :
      IsProbabilityMeasure (centeredBernoulliMeasure q) := by
    unfold centeredBernoulliMeasure
    infer_instance
  let centeredBernoulliCube (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
      Measure (Fin n → ({-1, 1} : Set ℤ)) :=
    Measure.pi (fun _ : Fin n ↦ centeredBernoulliMeasure q)
  letI centeredBernoulliCube_probability (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
      IsProbabilityMeasure (centeredBernoulliCube n q) := by
    unfold centeredBernoulliCube
    infer_instance
  let cubeTranslate (n : ℕ) (δ ε : Fin n → ({-1, 1} : Set ℤ)) :
      Fin n → ({-1, 1} : Set ℤ) :=
    fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k
  have rademacher_sign_neg_preserving :
      MeasurePreserving (fun a : ({-1, 1} : Set ℤ) ↦ -a)
        rademacherDistribution rademacherDistribution := by
    constructor
    · exact measurable_of_countable _
    · unfold rademacherDistribution
      rw [map_bernoulliMeasure]
      simp only [bernoulliMeasure_def]
      have hp : (-(⟨1, by decide⟩ : ({-1, 1} : Set ℤ))) = ⟨-1, by decide⟩ := by rfl
      have hm : (-(⟨-1, by decide⟩ : ({-1, 1} : Set ℤ))) = ⟨1, by decide⟩ := by
        apply Subtype.ext
        change -(-1 : ℤ) = 1
        norm_num
      rw [hp, hm]
      have hq : unitInterval.symm (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) =
          ⟨1 / 2, by norm_num⟩ := by
        apply Subtype.ext
        norm_num [unitInterval.coe_symm_eq]
      rw [hq, add_comm]
  have cubeTranslate_preserving (n : ℕ) (δ : Fin n → ({-1, 1} : Set ℤ)) :
      MeasurePreserving (cubeTranslate n δ)
        (rademacherProductDistribution (Fin n)) (rademacherProductDistribution (Fin n)) := by
    haveI : IsProbabilityMeasure rademacherDistribution := by
      unfold rademacherDistribution
      infer_instance
    unfold rademacherProductDistribution
    rw [Measure.infinitePi_eq_pi]
    unfold cubeTranslate
    refine measurePreserving_pi (fun _ : Fin n ↦ rademacherDistribution)
      (fun _ : Fin n ↦ rademacherDistribution)
      (f := fun j a ↦ if (δ j : ℤ) = 1 then a else -a) ?_
    intro j
    by_cases hj : (δ j : ℤ) = 1
    · simp only [hj, if_true]
      exact ⟨measurable_id, by simp⟩
    · simpa only [hj, if_false] using rademacher_sign_neg_preserving
  have cubeTranslate_lintegral (n : ℕ) (δ : Fin n → ({-1, 1} : Set ℤ))
      (g : (Fin n → ({-1, 1} : Set ℤ)) → ℝ≥0∞) :
      (∫⁻ ε, g (cubeTranslate n δ ε) ∂rademacherProductDistribution (Fin n)) =
        ∫⁻ ε, g ε ∂rademacherProductDistribution (Fin n) := by
    exact (cubeTranslate_preserving n δ).lintegral_comp (measurable_of_countable _)
  have centeredBernoulli_sign_mean (q : Set.Icc (0 : ℝ) 1) :
      (∫ a : ({-1, 1} : Set ℤ), ((a : ℤ) : ℝ) ∂centeredBernoulliMeasure q) =
        2 * (q : ℝ) - 1 := by
    unfold centeredBernoulliMeasure
    rw [integral_bernoulliMeasure]
    norm_num
    ring
  have centeredBernoulli_coordinate_mean (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
      (j : Fin n) :
      (∫ δ : Fin n → ({-1, 1} : Set ℤ), ((δ j : ℤ) : ℝ)
        ∂centeredBernoulliCube n q) = 2 * (q : ℝ) - 1 := by
    unfold centeredBernoulliCube
    rw [integral_comp_eval (μ := fun _ : Fin n ↦ centeredBernoulliMeasure q)
      (i := j) (f := fun a : ({-1, 1} : Set ℤ) ↦ ((a : ℤ) : ℝ))
      StronglyMeasurable.of_discrete.aestronglyMeasurable]
    exact centeredBernoulli_sign_mean q
  let centeredBernoulliPairs (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
      Measure (Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) :=
    Measure.pi (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
  letI centeredBernoulliPairs_probability (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
      IsProbabilityMeasure (centeredBernoulliPairs n q) := by
    unfold centeredBernoulliPairs
    infer_instance
  let bernoulliPairSwap (n : ℕ) (σ : Fin n → ({-1, 1} : Set ℤ))
      (ξ : Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) :
      Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)) :=
    fun j ↦ if (σ j : ℤ) = 1 then ξ j else (ξ j).swap
  have bernoulliPairSwap_preserving (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
      (σ : Fin n → ({-1, 1} : Set ℤ)) :
      MeasurePreserving (bernoulliPairSwap n σ)
        (centeredBernoulliPairs n q) (centeredBernoulliPairs n q) := by
    unfold centeredBernoulliPairs bernoulliPairSwap
    refine measurePreserving_pi
      (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
      (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
      (f := fun j (a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)) ↦
        if (σ j : ℤ) = 1 then a else a.swap) ?_
    intro j
    by_cases hj : (σ j : ℤ) = 1
    · simp only [hj, if_true]
      exact ⟨measurable_id, by simp⟩
    · simpa only [hj, if_false] using
        (Measure.measurePreserving_swap (μ := centeredBernoulliMeasure q)
          (ν := centeredBernoulliMeasure q))
  have bernoulliPairSwap_difference (n : ℕ)
      (σ : Fin n → ({-1, 1} : Set ℤ))
      (ξ : Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) (j : Fin n) :
      (((bernoulliPairSwap n σ ξ j).1 : ℤ) : ℝ) -
          (((bernoulliPairSwap n σ ξ j).2 : ℤ) : ℝ) =
        ((σ j : ℤ) : ℝ) * ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) := by
    have h : (σ j : ℤ) = -1 ∨ (σ j : ℤ) = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (σ j).property
    rcases h with h | h <;> simp [bernoulliPairSwap, h]
  have centeredBernoulliPairs_sign_integral
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (x : Fin n → X)
      (σ : Fin n → ({-1, 1} : Set ℤ)) :
      (∫⁻ ξ, ‖∑ j : Fin n, ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂centeredBernoulliPairs n q) =
      (∫⁻ ξ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
        (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂centeredBernoulliPairs n q) := by
    have h := (bernoulliPairSwap_preserving n q σ).lintegral_comp
      (measurable_of_countable (fun ξ ↦
        ‖∑ j : Fin n, ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p))
    symm
    convert h using 1
    apply lintegral_congr
    intro ξ
    simp only [bernoulliPairSwap_difference, smul_smul]
  have centeredBernoulli_copy_integral
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (δ : Fin n → ({-1, 1} : Set ℤ))
      (x : Fin n → X) :
      (∫ δ' : Fin n → ({-1, 1} : Set ℤ),
        ∑ j : Fin n, (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j
        ∂centeredBernoulliCube n q) =
        ∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j := by
    rw [integral_finsetSum Finset.univ (fun j hj ↦ Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_const, integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const, probReal_univ, one_smul, centeredBernoulli_coordinate_mean]
  have centeredBernoulli_copy_jensen
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) (x : Fin n → X) :
      (∫⁻ δ, ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j‖ₑ ^ p
        ∂centeredBernoulliCube n q) ≤
      (∫⁻ ξ, ‖∑ j : Fin n,
        ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂centeredBernoulliPairs n q) := by
    calc
      _ ≤ ∫⁻ δ, ∫⁻ δ', ‖∑ j : Fin n,
          (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j‖ₑ ^ p
          ∂centeredBernoulliCube n q ∂centeredBernoulliCube n q := by
        apply lintegral_mono
        intro δ
        have h := probability_integral_enorm_rpow_le
          (Fin n → ({-1, 1} : Set ℤ)) (centeredBernoulliCube n q) p
          (fun δ' ↦ ∑ j : Fin n, (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j)
          hp StronglyMeasurable.of_discrete.aestronglyMeasurable
        rwa [centeredBernoulli_copy_integral] at h
      _ = ∫⁻ z, ‖∑ j : Fin n,
          (((z.1 j : ℤ) : ℝ) - ((z.2 j : ℤ) : ℝ)) • x j‖ₑ ^ p
          ∂(centeredBernoulliCube n q).prod (centeredBernoulliCube n q) :=
        lintegral_lintegral (measurable_of_countable _).aemeasurable
      _ = _ := by
        unfold centeredBernoulliCube centeredBernoulliPairs
        exact (measurePreserving_arrowProdEquivProdArrow
          ({-1, 1} : Set ℤ) ({-1, 1} : Set ℤ) (Fin n)
          (fun _ ↦ centeredBernoulliMeasure q) (fun _ ↦ centeredBernoulliMeasure q)
          |>.lintegral_comp (measurable_of_countable _)).symm
  have centeredBernoulliPairs_symmetrization
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (x : Fin n → X) :
      (∫⁻ ξ, ‖∑ j : Fin n,
        ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂centeredBernoulliPairs n q) =
      (∫⁻ ξ, ∫⁻ σ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
        (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliPairs n q) := by
    haveI := rademacher_product_probability n
    calc
      _ = ∫⁻ σ : Fin n → ({-1, 1} : Set ℤ),
          (∫⁻ ξ, ‖∑ j : Fin n,
            ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
            ∂centeredBernoulliPairs n q)
          ∂rademacherProductDistribution (Fin n) := by
        rw [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ σ, ∫⁻ ξ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
          (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
          ∂centeredBernoulliPairs n q ∂rademacherProductDistribution (Fin n) := by
        apply lintegral_congr
        intro σ
        exact centeredBernoulliPairs_sign_integral n q p x σ
      _ = _ := lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
  have centeredBernoulliPairs_scaled_moment_le
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
      (j : Fin n) (v : X) :
      (∫⁻ ξ, ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • v)‖ₑ ^ p
        ∂centeredBernoulliPairs n q) ≤
        (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) * ‖v‖ₑ ^ p := by
    calc
      _ = (∫⁻ ξ, ‖((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ))‖ₑ ^ p
          ∂centeredBernoulliPairs n q) * ‖v‖ₑ ^ p := by
        simp only [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ p by linarith)]
        exact lintegral_mul_const _ (measurable_of_countable _)
      _ = (∫⁻ a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ),
          ‖((a.1 : ℤ) : ℝ) - ((a.2 : ℤ) : ℝ)‖ₑ ^ p
          ∂(centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q)) * ‖v‖ₑ ^ p := by
        congr 1
        unfold centeredBernoulliPairs
        exact (measurePreserving_eval
          (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q)) j
          |>.lintegral_comp (measurable_of_countable
            (fun a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ) ↦
              ‖((a.1 : ℤ) : ℝ) - ((a.2 : ℤ) : ℝ)‖ₑ ^ p)))
      _ ≤ _ := mul_le_mul' (bernoulli_difference_moment_le p q hp hp2) le_rfl
  have centeredBernoulli_cube_bound
      
      (n : ℕ) (p : ℝ) (C : ℝ≥0∞) (q : Set.Icc (0 : ℝ) 1) (x : Fin n → X)
      (hn : 1 ≤ n) (hp : 1 ≤ p) (hp2 : p ≤ 2)
      (hC : IsRademacherType X C p) :
      (∫⁻ δ, ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j‖ₑ ^ p
        ∂centeredBernoulliCube n q) ≤
        (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
          C ^ p * ∑ j : Fin n, ‖x j‖ₑ ^ p := by
    calc
      _ ≤ ∫⁻ ξ, ‖∑ j : Fin n,
          ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
          ∂centeredBernoulliPairs n q := centeredBernoulli_copy_jensen n q p hp x
      _ = ∫⁻ ξ, ∫⁻ σ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
          (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliPairs n q :=
        centeredBernoulliPairs_symmetrization n q p x
      _ ≤ ∫⁻ ξ, C ^ p * ∑ j : Fin n,
          ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
          ∂centeredBernoulliPairs n q := by
        apply lintegral_mono
        intro ξ
        exact hC n hn _
      _ = C ^ p * ∑ j : Fin n, ∫⁻ ξ,
          ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
          ∂centeredBernoulliPairs n q := by
        rw [lintegral_const_mul _ (measurable_of_countable _),
          lintegral_finsetSum Finset.univ (fun j hj ↦ measurable_of_countable _)]
      _ ≤ C ^ p * ∑ j : Fin n,
          (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) * ‖x j‖ₑ ^ p := by
        refine mul_le_mul' le_rfl ?_
        apply Finset.sum_le_sum
        intro j hj
        exact centeredBernoulliPairs_scaled_moment_le n q p hp hp2 j (x j)
      _ = _ := by rw [← Finset.mul_sum]; ac_rfl
  have centered_bernoulli_cube_joint_bound :
      ∀ (n : ℕ) (p : ℝ) (C : ℝ≥0∞) (q : Set.Icc (0 : ℝ) 1)
        (x : (Fin n → ({-1, 1} : Set ℤ)) → Fin n → X),
        1 ≤ n → 1 ≤ p → p ≤ 2 →
        RademacherEnfloType.IsRademacherType X C p →
        (∫⁻ ε : Fin n → ({-1, 1} : Set ℤ),
          (∫⁻ δ : Fin n → ({-1, 1} : Set ℤ),
            ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
              x (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k) j‖ₑ ^ p
            ∂MeasureTheory.Measure.infinitePi (fun _ : Fin n ↦
              ProbabilityTheory.bernoulliMeasure
                (⟨1, by decide⟩ : ({-1, 1} : Set ℤ)) ⟨-1, by decide⟩ q))
          ∂RademacherEnfloType.rademacherProductDistribution (Fin n)) ≤
          (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
            C ^ p * ∑ j : Fin n,
              (∫⁻ ε : Fin n → ({-1, 1} : Set ℤ), ‖x ε j‖ₑ ^ p
                ∂RademacherEnfloType.rademacherProductDistribution (Fin n)) := by
    intro n p C q x hn hp hp2 hC
    haveI := rademacher_product_probability n
    rw [Measure.infinitePi_eq_pi]
    change (∫⁻ ε, ∫⁻ δ,
      ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
        x (cubeTranslate n δ ε) j‖ₑ ^ p
      ∂centeredBernoulliCube n q ∂rademacherProductDistribution (Fin n)) ≤ _
    calc
      _ = ∫⁻ δ, ∫⁻ ε,
          ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
            x (cubeTranslate n δ ε) j‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliCube n q :=
        lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
      _ = ∫⁻ δ, ∫⁻ ε,
          ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliCube n q := by
        apply lintegral_congr
        intro δ
        exact cubeTranslate_lintegral n δ
          (fun ε ↦ ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p)
      _ = ∫⁻ ε, ∫⁻ δ,
          ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p
          ∂centeredBernoulliCube n q ∂rademacherProductDistribution (Fin n) :=
        lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
      _ ≤ ∫⁻ ε, (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
          C ^ p * ∑ j : Fin n, ‖x ε j‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n) := by
        apply lintegral_mono
        intro ε
        exact centeredBernoulli_cube_bound n p C q (x ε) hn hp hp2 hC
      _ = _ := by
        rw [lintegral_const_mul _ (measurable_of_countable _),
          lintegral_finsetSum Finset.univ (fun j hj ↦ measurable_of_countable _)]
  have arcsine_kernel_mass :
      IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
        MeasureTheory.volume (-1 : ℝ) (1 : ℝ) ∧
      (∫ t in (-1 : ℝ)..(1 : ℝ), (Real.sqrt (1 - t ^ 2))⁻¹) = Real.pi := by
    have hint : IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
        MeasureTheory.volume (-1 : ℝ) (1 : ℝ) := by
      simpa only [Real.sqrt_inv] using
        Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    refine ⟨hint, ?_⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := Real.arcsin) (f' := fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
      (show (-1 : ℝ) ≤ 1 by norm_num) Real.continuous_arcsin.continuousOn
      (by
        intro t ht
        simpa only [one_div] using
          Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)) hint
    calc
      (∫ t in (-1 : ℝ)..(1 : ℝ), (Real.sqrt (1 - t ^ 2))⁻¹) =
          Real.arcsin 1 - Real.arcsin (-1) := hFTC
      _ = Real.pi := by rw [Real.arcsin_one, Real.arcsin_neg_one]; ring
  have noise_product_deriv (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
      HasDerivAt (fun s : ℝ => ∏ k : Fin n, (1 + s * a k))
        (∑ j : Fin n, a j * ∏ k ∈ Finset.univ.erase j, (1 + t * a k)) t := by
    have h := HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => fun s : ℝ => 1 + s * a i) (f' := a) (x := t) (by
          intro i hi
          simpa [add_comm, mul_comm] using
            HasDerivAt.add_const 1 ((hasDerivAt_id' t).mul_const (a i)))
    have hder : HasDerivAt (∏ i : Fin n, fun s : ℝ => 1 + s * a i)
        (∑ j : Fin n, a j * ∏ k ∈ Finset.univ.erase j, (1 + t * a k)) t :=
      h.congr_deriv (by simp [smul_eq_mul, mul_comm])
    exact hder.congr_of_eventuallyEq (by
      filter_upwards [] with s
      simp only [Finset.prod_apply])
  have noise_polynomial_antipodal_integral
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) :
      (1 / (2 : ℝ)) • (f ε - f (-ε)) =
      ∫ t in (-1 : ℝ)..(1 : ℝ),
        (1 / (2 * (2 : ℝ) ^ n)) •
          (∑ δ : Fin n → ({-1, 1} : Set ℤ),
            (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
              ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) •
            f (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k)) := by
    classical
    let g : (Fin n → ({-1, 1} : Set ℤ)) → X :=
      fun δ => f (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k)
    let c : ℝ := 1 / (2 * (2 : ℝ) ^ n)
    let P : ℝ → X := fun t =>
      c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) • g δ
    have hPderiv : ∀ t : ℝ, HasDerivAt P
        (c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ) t := by
      intro t
      have hsum : HasDerivAt
          (fun s : ℝ => ∑ δ : Fin n → ({-1, 1} : Set ℤ),
            (∏ k : Fin n, (1 + s * ((δ k : ℤ) : ℝ))) • g δ)
          (∑ δ : Fin n → ({-1, 1} : Set ℤ),
            (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
              ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ) t := by
        apply HasDerivAt.fun_sum
        intro δ hδ
        have hp := noise_product_deriv n (fun k ↦ ((δ k : ℤ) : ℝ)) t
        have hs := hp.smul_const (g δ)
        simpa [smul_eq_mul, mul_comm] using hs
      have hc := hsum.const_smul c
      change HasDerivAt (fun s : ℝ => c •
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + s * ((δ k : ℤ) : ℝ))) • g δ)) _ t
      convert hc using 1 <;> funext s <;> rfl
    have hPcont : ContinuousOn P (Set.Icc (-1 : ℝ) 1) := by
      fun_prop
    have hPint : IntervalIntegrable
        (fun t => c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
        MeasureTheory.volume (-1 : ℝ) 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      fun_prop
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := (-1 : ℝ)) (b := (1 : ℝ)) (f := P)
      (f' := fun t => c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
      (by norm_num) hPcont (fun t ht => hPderiv t) hPint
    change (1 / (2 : ℝ)) • (f ε - f (-ε)) =
      ∫ t in (-1 : ℝ)..(1 : ℝ),
        c • (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
    let δp : Fin n → ({-1, 1} : Set ℤ) := fun _ => ⟨1, by simp⟩
    let δm : Fin n → ({-1, 1} : Set ℤ) := fun _ => ⟨-1, by simp⟩
    have hsum1 :
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + (1 : ℝ) * ((δ k : ℤ) : ℝ))) • g δ) =
        (2 : ℝ) ^ n • f ε := by
      rw [Finset.sum_eq_single δp]
      · simp [δp, g]
        congr 1
        norm_num
      · intro δ hδ hne
        by_cases heq : δ = δp
        · exact (hne heq).elim
        · obtain ⟨k, hk⟩ : ∃ k : Fin n, δ k ≠ δp k := by
            by_contra hno
            apply heq
            funext k
            exact not_not.mp (fun h => hno ⟨k, h⟩)
          have hδk : (δ k : ℤ) = -1 := by
            have hv' : (δ k : ℤ) = -1 ∨ (δ k : ℤ) = 1 := by
              simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ k).property
            rcases hv' with hv' | hv'
            · exact hv'
            · exfalso
              apply hk
              apply Subtype.ext
              simpa [δp] using hv'
          have hz : (∏ k : Fin n, (1 + (1 : ℝ) * ((δ k : ℤ) : ℝ))) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [hδk]
          rw [hz]
          simp
      · simp
    have hsumm :
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + (-1 : ℝ) * ((δ k : ℤ) : ℝ))) • g δ) =
        (2 : ℝ) ^ n • f (-ε) := by
      rw [Finset.sum_eq_single δm]
      · simp [δm, g]
        congr 1
        norm_num
      · intro δ hδ hne
        by_cases heq : δ = δm
        · exact (hne heq).elim
        · obtain ⟨k, hk⟩ : ∃ k : Fin n, δ k ≠ δm k := by
            by_contra hno
            apply heq
            funext k
            exact not_not.mp (fun h => hno ⟨k, h⟩)
          have hδk : (δ k : ℤ) = 1 := by
            have hv' : (δ k : ℤ) = -1 ∨ (δ k : ℤ) = 1 := by
              simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ k).property
            rcases hv' with hv' | hv'
            · exfalso
              apply hk
              apply Subtype.ext
              simpa [δm] using hv'
            · exact hv'
          have hz : (∏ k : Fin n, (1 + (-1 : ℝ) * ((δ k : ℤ) : ℝ))) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [hδk]
          rw [hz]
          simp
      · simp
    rw [hFTC]
    simp only [P, c]
    rw [hsum1, hsumm]
    rw [smul_sub, smul_smul, smul_smul]
    congr 1 <;> field_simp
  let enfloArcsineDensity (t : ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)
  let enfloArcsineMeasure : MeasureTheory.Measure ℝ :=
    (MeasureTheory.volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity enfloArcsineDensity
  have enfloArcsineDensity_measurable : Measurable enfloArcsineDensity := by
    unfold enfloArcsineDensity
    fun_prop
  have enfloArcsineDensity_toReal (t : ℝ) :
      (enfloArcsineDensity t).toReal = (Real.pi * Real.sqrt (1 - t ^ 2))⁻¹ := by
    dsimp only [enfloArcsineDensity]
    rw [ENNReal.toReal_ofReal]
    positivity
  have enfloArcsineMeasure_probability :
      MeasureTheory.IsProbabilityMeasure enfloArcsineMeasure := by
    have hmass := arcsine_kernel_mass
    have hi : Integrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
        (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
      rw [restrict_Ioo_eq_restrict_Ioc]
      exact hmass.1.1
    have hi' : Integrable (fun t : ℝ ↦ (Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)
        (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
      simpa only [mul_inv_rev, mul_comm] using hi.const_mul Real.pi⁻¹
    constructor
    dsimp only [enfloArcsineMeasure]
    rw [withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    change (∫⁻ t in Set.Ioo (-1 : ℝ) 1,
      ENNReal.ofReal ((Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall (by
      intro t; positivity))]
    simp only [mul_inv_rev]
    rw [integral_mul_const, restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), hmass.2]
    rw [mul_inv_cancel₀ Real.pi_ne_zero]
    norm_num
  have enfloArcsineMeasure_ae_mem :
      ∀ᵐ t ∂enfloArcsineMeasure, t ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem measurableSet_Ioo)
  have enfloArcsineDensity_sqrt_cancel (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
      (enfloArcsineDensity t).toReal * Real.sqrt (2 * (1 - t ^ 2)) =
        Real.sqrt 2 / Real.pi := by
    have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    rw [enfloArcsineDensity_toReal, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hz := (Real.sqrt_pos.2 hs).ne'
    field_simp
  have enfloArcsineMeasure_integral_recovery
      
      (g : ℝ → X) :
      (∫ t in (-1 : ℝ)..(1 : ℝ), g t) =
        (Real.pi / Real.sqrt 2) •
          (∫ t, Real.sqrt (2 * (1 - t ^ 2)) • g t ∂enfloArcsineMeasure) := by
    dsimp only [enfloArcsineMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul
      enfloArcsineDensity_measurable (Filter.Eventually.of_forall (by
        intro t; exact ENNReal.ofReal_lt_top))]
    rw [integral_congr_ae (Filter.Eventually.mono
      (ae_restrict_mem measurableSet_Ioo) (by
        intro t ht
        rw [smul_smul, enfloArcsineDensity_sqrt_cancel t ht]))]
    rw [integral_smul, smul_smul]
    have hc : Real.pi / Real.sqrt 2 * (Real.sqrt 2 / Real.pi) = 1 := by
      have hz : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
      field_simp
    rw [hc, one_smul, restrict_Ioo_eq_restrict_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have centeredBernoulliMeasure_singleton_real
      (q : Set.Icc (0 : ℝ) 1) (a : ({-1, 1} : Set ℤ)) :
      (centeredBernoulliMeasure q).real {a} =
        (1 + (2 * (q : ℝ) - 1) * ((a : ℤ) : ℝ)) / 2 := by
    rcases a with ⟨a, ha⟩
    have h : a = -1 ∨ a = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    rcases h with h | h <;> subst a
    · simp [centeredBernoulliMeasure, bernoulliMeasure_def, Measure.real,
        unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      ring
    · simp [centeredBernoulliMeasure, bernoulliMeasure_def, Measure.real,
        unitInterval.coe_toNNReal]
  have centeredBernoulliCube_singleton_real
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (δ : Fin n → ({-1, 1} : Set ℤ)) :
      (centeredBernoulliCube n q).real {δ} =
        (1 / (2 : ℝ) ^ n) *
          ∏ k : Fin n, (1 + (2 * (q : ℝ) - 1) * ((δ k : ℤ) : ℝ)) := by
    rw [Measure.real]
    dsimp only [centeredBernoulliCube]
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    change (∏ k : Fin n, (centeredBernoulliMeasure q).real {δ k}) = _
    simp only [centeredBernoulliMeasure_singleton_real, div_eq_mul_inv,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]
    ring
  have centeredBernoulliCube_integral_eq
      
      (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
      (g : (Fin n → ({-1, 1} : Set ℤ)) → X) :
      (∫ δ, g δ ∂centeredBernoulliCube n q) =
        (1 / (2 : ℝ) ^ n) •
          ∑ δ : Fin n → ({-1, 1} : Set ℤ),
            (∏ k : Fin n, (1 + (2 * (q : ℝ) - 1) * ((δ k : ℤ) : ℝ))) • g δ := by
    rw [integral_fintype Integrable.of_finite]
    simp only [centeredBernoulliCube_singleton_real, Finset.smul_sum, smul_smul]
  have cubeTranslate_update (n : ℕ) (δ ε : Fin n → ({-1, 1} : Set ℤ)) (j : Fin n) :
      cubeTranslate n (Function.update δ j (-δ j)) ε =
        Function.update (cubeTranslate n δ ε) j (-(cubeTranslate n δ ε j)) := by
    classical
    funext k
    by_cases hk : k = j
    · subst k
      simp only [Function.update_self, cubeTranslate]
      change (if -(δ j : ℤ) = 1 then ε j else -ε j) =
        -(if (δ j : ℤ) = 1 then ε j else -ε j)
      have hj : (δ j : ℤ) = -1 ∨ (δ j : ℤ) = 1 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ j).property
      rcases hj with hj | hj
      · simp only [hj]
        norm_num
        apply Subtype.ext
        change (ε j : ℤ) = -(-(ε j : ℤ))
        simp
      · simp only [hj]
        norm_num
    · simp only [cubeTranslate, Function.update_of_ne hk]
  have cubeTranslate_derivative
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (δ ε : Fin n → ({-1, 1} : Set ℤ)) (j : Fin n) :
      D j (fun η ↦ f (cubeTranslate n η ε)) δ = D j f (cubeTranslate n δ ε) := by
    unfold D
    dsimp only
    rw [cubeTranslate_update]
  let enfloNoiseDerivative
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ) : X :=
    (1 / (2 * (2 : ℝ) ^ n)) •
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) •
        f (cubeTranslate n δ ε))
  let enfloNormalizedNoise
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ) : X :=
    Real.sqrt (2 * (1 - t ^ 2)) • enfloNoiseDerivative n f ε t
  have enfloNormalizedNoise_continuous
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) :
      Continuous (enfloNormalizedNoise n f ε) := by
    unfold enfloNormalizedNoise enfloNoiseDerivative
    fun_prop
  have enflo_antipodal_kernel_expectation
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) :
      (1 / (2 : ℝ)) • (f ε - f (-ε)) =
        (Real.pi / Real.sqrt 2) •
          (∫ t, enfloNormalizedNoise n f ε t ∂enfloArcsineMeasure) := by
    rw [noise_polynomial_antipodal_integral n f ε]
    exact enfloArcsineMeasure_integral_recovery (enfloNoiseDerivative n f ε)
  have enfloNoiseDerivative_centered_integral
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ)
      (q : Set.Icc (0 : ℝ) 1) (hq : 2 * (q : ℝ) - 1 = t) :
      (1 - t ^ 2) • enfloNoiseDerivative n f ε t =
        (1 / (2 : ℝ)) •
          (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
            D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q) := by
    have hw := weighted_cube_derivative_identity n (fun δ ↦ f (cubeTranslate n δ ε)) t
    simp only [cubeTranslate_derivative] at hw
    rw [centeredBernoulliCube_integral_eq, hq]
    unfold enfloNoiseDerivative
    rw [smul_comm (1 - t ^ 2), hw, smul_smul]
    congr 1
    field_simp
  have enfloNormalizedNoise_centered_expectation
      
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ)
      (ht : t ∈ Set.Ioo (-1 : ℝ) 1)
      (q : Set.Icc (0 : ℝ) 1) (hq : 2 * (q : ℝ) - 1 = t) :
      enfloNormalizedNoise n f ε t =
        (Real.sqrt (2 * (1 - t ^ 2)))⁻¹ •
          (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
            D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q) := by
    have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hs' : 0 < 2 * (1 - t ^ 2) := by positivity
    have heq : enfloNoiseDerivative n f ε t =
        (1 - t ^ 2)⁻¹ • ((1 / (2 : ℝ)) •
          (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
            D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q)) := by
      rw [← enfloNoiseDerivative_centered_integral n f ε t q hq,
        smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    unfold enfloNormalizedNoise
    rw [heq, smul_smul, smul_smul]
    congr 1
    have hz : Real.sqrt (2 * (1 - t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 hs').ne'
    have hsq := Real.sq_sqrt hs'.le
    field_simp
    nlinarith
  have enflo_sqrt_inv_moment_cancel (s p : ℝ) (hs : 0 < s) :
      (ENNReal.ofReal ((Real.sqrt s)⁻¹)) ^ p *
        (ENNReal.ofReal s) ^ (p / 2) = 1 := by
    have hz : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
    have he : ENNReal.ofReal (Real.sqrt s) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hs)).ne'
    have he' : ENNReal.ofReal (Real.sqrt s) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpow : (ENNReal.ofReal s) ^ (p / 2) =
        (ENNReal.ofReal (Real.sqrt s)) ^ p := by
      calc
        (ENNReal.ofReal s) ^ (p / 2) =
            ((ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℝ)) ^ (p / 2) := by
          have hsq : (ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℝ) = ENNReal.ofReal s := by
            calc
              _ = (ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℕ) := by
                simpa using ENNReal.rpow_natCast (ENNReal.ofReal (Real.sqrt s)) 2
              _ = ENNReal.ofReal ((Real.sqrt s) ^ (2 : ℕ)) :=
                (ENNReal.ofReal_pow (Real.sqrt_nonneg s) 2).symm
              _ = ENNReal.ofReal s := by rw [Real.sq_sqrt hs.le]
          rw [hsq]
        _ = (ENNReal.ofReal (Real.sqrt s)) ^ (2 * (p / 2)) :=
          (ENNReal.rpow_mul _ _ _).symm
        _ = _ := by congr 1; ring
    rw [hpow, ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 hs), ENNReal.inv_rpow]
    exact ENNReal.inv_mul_cancel (by simp [he, he'])
      (ENNReal.rpow_ne_top_of_ne_zero he he')
  have enflo_finite_lintegral_swap
      (n : ℕ) (μ : MeasureTheory.Measure ℝ)
      (g : ℝ → (Fin n → ({-1, 1} : Set ℤ)) → ℝ≥0∞)
      (hg : ∀ ε, Measurable (fun t ↦ g t ε)) :
      (∫⁻ ε, (∫⁻ t, g t ε ∂μ) ∂rademacherProductDistribution (Fin n)) =
        ∫⁻ t, (∫⁻ ε, g t ε ∂rademacherProductDistribution (Fin n)) ∂μ := by
    simp only [lintegral_fintype]
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ε hε
      exact (lintegral_mul_const _ (hg ε)).symm
    · intro ε hε
      exact (hg ε).mul_const _
  have enfloNormalizedNoise_cube_moment_le
      
      (n : ℕ) (p : ℝ) (C : ℝ≥0∞)
      (f : (Fin n → ({-1, 1} : Set ℤ)) → X) (t : ℝ)
      (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hn : 1 ≤ n) (h1p : 1 ≤ p) (hp2 : p ≤ 2)
      (hC : RademacherEnfloType.IsRademacherType X C p) :
      (∫⁻ ε, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n)) ≤
        C ^ p * ∑ j : Fin n,
          (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n)) := by
    let q : Set.Icc (0 : ℝ) 1 := ⟨(1 + t) / 2, by
      constructor <;> linarith [ht.1, ht.2]⟩
    have hq : 2 * (q : ℝ) - 1 = t := by dsimp [q]; ring
    have hs : 0 < 2 * (1 - t ^ 2) := by nlinarith [ht.1, ht.2]
    have hp : 0 ≤ p := by linarith
    let a : ℝ≥0∞ := (ENNReal.ofReal ((Real.sqrt (2 * (1 - t ^ 2)))⁻¹)) ^ p
    let S : (Fin n → ({-1, 1} : Set ℤ)) →
        (Fin n → ({-1, 1} : Set ℤ)) → X :=
      fun ε δ ↦ ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • D j f (cubeTranslate n δ ε)
    have hjensen : ∀ ε, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p ≤
        a * (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q) := by
      intro ε
      have hj := probability_integral_enorm_rpow_le
        (Fin n → ({-1, 1} : Set ℤ)) (centeredBernoulliCube n q) p (S ε)
        h1p StronglyMeasurable.of_discrete.aestronglyMeasurable
      rw [enfloNormalizedNoise_centered_expectation n f ε t ht q hq,
        enorm_smul, Real.enorm_of_nonneg (by positivity),
        ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact mul_le_mul' le_rfl hj
    have hfirst :
        (∫⁻ ε, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n)) ≤
        a * (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
          ∂rademacherProductDistribution (Fin n)) := by
      calc
        _ ≤ ∫⁻ ε, a * (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
            ∂rademacherProductDistribution (Fin n) := lintegral_mono hjensen
        _ = _ := lintegral_const_mul a (measurable_of_countable _)
    have hvariance : 8 * (q : ℝ) * (1 - (q : ℝ)) = 2 * (1 - t ^ 2) := by
      dsimp [q]
      ring
    have hjoint :
        (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
          ∂rademacherProductDistribution (Fin n)) ≤
        (ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
          ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
            ∂rademacherProductDistribution (Fin n)) := by
      have h := centered_bernoulli_cube_joint_bound n p C q (fun ε j ↦ D j f ε)
        hn h1p hp2 hC
      rw [Measure.infinitePi_eq_pi, hq, hvariance] at h
      change (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
        ∂rademacherProductDistribution (Fin n)) ≤
        (ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
          ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
            ∂rademacherProductDistribution (Fin n)) at h
      exact h
    calc
      _ ≤ a * (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
          ∂rademacherProductDistribution (Fin n)) := hfirst
      _ ≤ a * ((ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
          ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
            ∂rademacherProductDistribution (Fin n))) := mul_le_mul' le_rfl hjoint
      _ = _ := by
        dsimp only [a]
        rw [← mul_assoc, ← mul_assoc, enflo_sqrt_inv_moment_cancel _ p hs, one_mul]
  have enflo_type_constant_eq :
      ENNReal.ofReal (Real.pi / Real.sqrt 2) =
        (NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by norm_num))]
    have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
      rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    have hs : ENNReal.ofReal (Real.sqrt 2) = (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) := by
      simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using
        (show ENNReal.ofReal ((NNReal.sqrt (2 : ℝ≥0)) : ℝ) =
          (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
    rw [hpi, hs]
  have rademacher_implies_enflo :
      ∀ (p : ℝ) (C : ℝ≥0∞),
        1 ≤ p → p ≤ 2 →
        RademacherEnfloType.IsRademacherType X C p →
        RademacherEnfloType.IsEnfloType X
          (((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) * C) p := by
    intro p C h1p hp2 hC n hn f
    letI := enfloArcsineMeasure_probability
    have hp : 0 ≤ p := by linarith
    have hscalar : 0 ≤ Real.pi / Real.sqrt 2 := by positivity
    have hJ : ∀ ε, ‖(1 / (2 : ℝ)) • (f ε - f (-ε))‖ₑ ^ p ≤
        (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
          (∫⁻ t, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p ∂enfloArcsineMeasure) := by
      intro ε
      rw [enflo_antipodal_kernel_expectation n f ε, enorm_smul,
        Real.enorm_of_nonneg hscalar, ENNReal.mul_rpow_of_nonneg _ _ hp]
      exact mul_le_mul' le_rfl
        (probability_integral_enorm_rpow_le ℝ enfloArcsineMeasure p
          (enfloNormalizedNoise n f ε) h1p
          (enfloNormalizedNoise_continuous n f ε).aestronglyMeasurable)
    have hswap := enflo_finite_lintegral_swap n enfloArcsineMeasure
      (fun t ε ↦ ‖enfloNormalizedNoise n f ε t‖ₑ ^ p)
      (fun ε ↦ (enfloNormalizedNoise_continuous n f ε).enorm.measurable.pow_const p)
    have hmoment :
        (∫⁻ t, (∫⁻ ε, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n)) ∂enfloArcsineMeasure) ≤
        C ^ p * ∑ j : Fin n,
          (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n)) := by
      calc
        _ ≤ ∫⁻ _t : ℝ,
            C ^ p * ∑ j : Fin n,
              (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
            ∂enfloArcsineMeasure := lintegral_mono_ae (enfloArcsineMeasure_ae_mem.mono
              (fun t ht ↦ enfloNormalizedNoise_cube_moment_le n p C f t ht hn h1p hp2 hC))
        _ = _ := by rw [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ ∫⁻ ε, (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
          (∫⁻ t, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p ∂enfloArcsineMeasure)
          ∂rademacherProductDistribution (Fin n) := lintegral_mono hJ
      _ = (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
          (∫⁻ t, (∫⁻ ε, ‖enfloNormalizedNoise n f ε t‖ₑ ^ p
            ∂rademacherProductDistribution (Fin n)) ∂enfloArcsineMeasure) := by
        rw [lintegral_const_mul _ (measurable_of_countable _), hswap]
      _ ≤ (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
          (C ^ p * ∑ j : Fin n,
            (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))) :=
        mul_le_mul' le_rfl hmoment
      _ = _ := by
        rw [enflo_type_constant_eq, ENNReal.mul_rpow_of_nonneg _ _ hp, mul_assoc]
  have type_constants_of_reverse_conversion :
      ∀ (p : ℝ),
        1 ≤ p → p ≤ 2 →
        (∀ C : ℝ≥0∞, RademacherEnfloType.IsRademacherType X C p →
          RademacherEnfloType.IsEnfloType X
            (((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) * C) p) →
        RademacherEnfloType.TR X p ≤ RademacherEnfloType.TE X p ∧
          RademacherEnfloType.TE X p ≤
            ((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) *
              RademacherEnfloType.TR X p := by
    intro p h1p hp2 hconvert
    let k : ℝ≥0∞ :=
      (NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)
    have hsqrt : 0 < NNReal.sqrt (2 : ℝ≥0) :=
      NNReal.sqrt_pos.mpr (by norm_num)
    have hkcoe : k = ((NNReal.pi / NNReal.sqrt (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) :=
      (ENNReal.coe_div (ne_of_gt hsqrt)).symm
    have hk0 : k ≠ 0 := by
      rw [hkcoe, ENNReal.coe_ne_zero]
      exact ne_of_gt (div_pos NNReal.pi_pos hsqrt)
    have hktop : k ≠ ∞ := by
      rw [hkcoe]
      exact ENNReal.coe_ne_top
    constructor
    · unfold RademacherEnfloType.TR RademacherEnfloType.TE
      apply le_sInf
      intro C hC
      exact sInf_le (enflo_implies_rademacher p C h1p hp2 hC)
    · change RademacherEnfloType.TE X p ≤ k * RademacherEnfloType.TR X p
      apply (ENNReal.div_le_iff' hk0 hktop).mp
      unfold RademacherEnfloType.TR
      apply le_sInf
      intro C hC
      apply (ENNReal.div_le_iff' hk0 hktop).mpr
      exact sInf_le (hconvert C hC)
  exact type_constants_of_reverse_conversion p h1p hp2
    (fun C hC ↦ rademacher_implies_enflo p C h1p hp2 hC)
theorem rademacher_product_probability (n : ℕ) :
    IsProbabilityMeasure (rademacherProductDistribution (Fin n)) := by
  unfold rademacherProductDistribution
  haveI : IsProbabilityMeasure rademacherDistribution := by
    unfold rademacherDistribution
    infer_instance
  infer_instance
theorem linear_cube_odd
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (x : Fin n → X) (ε : Fin n → ({-1, 1} : Set ℤ)) :
    (∑ j : Fin n, (((-ε) j) : ℝ) • x j) =
      -(∑ j : Fin n, ((ε j) : ℝ) • x j) := by
  change (∑ j : Fin n, (Int.cast (-(ε j : ℤ)) : ℝ) • x j) =
    -(∑ j : Fin n, ((ε j : ℤ) : ℝ) • x j)
  simp only [Int.cast_neg, neg_smul, Finset.sum_neg_distrib]
theorem linear_cube_antipodal_half
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (x : Fin n → X) (ε : Fin n → ({-1, 1} : Set ℤ)) :
    (1 / (2 : ℝ)) • ((∑ j : Fin n, ((ε j) : ℝ) • x j) -
      (∑ j : Fin n, (((-ε) j) : ℝ) • x j)) =
      ∑ j : Fin n, ((ε j) : ℝ) • x j := by
  rw [linear_cube_odd X n x ε, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num
theorem linear_cube_derivative
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (x : Fin n → X) (j : Fin n) (ε : Fin n → ({-1, 1} : Set ℤ)) :
    D j (fun δ ↦ ∑ k : Fin n, ((δ k) : ℝ) • x k) ε =
      ((ε j) : ℝ) • x j := by
  classical
  unfold D
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  rw [Finset.sum_eq_single j]
  · simp only [Function.update_self]
    change (1 / (2 : ℝ)) •
      (((ε j : ℤ) : ℝ) • x j - (Int.cast (-(ε j : ℤ)) : ℝ) • x j) =
      ((ε j : ℤ) : ℝ) • x j
    rw [Int.cast_neg, neg_smul, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
  · intro k hk hkj
    simp [Function.update_of_ne hkj]
  · simp
theorem rademacher_sign_enorm
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (x : X) (ε : ({-1, 1} : Set ℤ)) :
    ‖((ε : ℤ) : ℝ) • x‖ₑ = ‖x‖ₑ := by
  rcases ε with ⟨ε, hε⟩
  have h : ε = -1 ∨ ε = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hε
  rcases h with h | h <;> subst ε <;> simp
theorem linear_cube_derivative_integral
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (x : Fin n → X) (j : Fin n) (p : ℝ) :
    (∫⁻ ε, ‖D j (fun δ ↦ ∑ k : Fin n, ((δ k) : ℝ) • x k) ε‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n)) = ‖x j‖ₑ ^ p := by
  haveI := rademacher_product_probability n
  simp only [linear_cube_derivative, rademacher_sign_enorm]
  rw [lintegral_const, measure_univ, mul_one]
theorem enflo_implies_rademacher :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (p : ℝ) (C : ℝ≥0∞),
      1 ≤ p → p ≤ 2 →
      RademacherEnfloType.IsEnfloType X C p →
      RademacherEnfloType.IsRademacherType X C p := by
  intro X _ _ _ p C h1p hp2 hC n hn x
  have h := hC n hn (fun ε ↦ ∑ j : Fin n, ((ε j) : ℝ) • x j)
  simpa only [linear_cube_antipodal_half, linear_cube_derivative_integral] using h
theorem bernoulli_difference_moment_eq (p : ℝ) (q : Set.Icc (0 : ℝ) 1)
    (hp : 0 < p) :
    (∫⁻ ξ : (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)),
      ‖((ξ.1 : ℤ) : ℝ) - ((ξ.2 : ℤ) : ℝ)‖ₑ ^ p
      ∂(bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
        ⟨-1, by decide⟩ q).prod
        (bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
          ⟨-1, by decide⟩ q)) =
      (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) := by
  simp only [bernoulliMeasure_def, Measure.add_prod, Measure.prod_add,
    Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]
  norm_num [ENNReal.zero_rpow_of_pos hp]
  have htwo : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by
    simp [enorm_eq_nnnorm]
  rw [htwo]
  change (unitInterval.toNNReal q : ℝ≥0∞) *
      ((unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) * 2 ^ p) +
      (unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) *
      ((unitInterval.toNNReal q : ℝ≥0∞) * 2 ^ p) = _
  have hq : (unitInterval.toNNReal q : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
    rw [← unitInterval.coe_toNNReal q, ENNReal.ofReal_coe_nnreal]
  have hq' : (unitInterval.toNNReal (unitInterval.symm q) : ℝ≥0∞) =
      ENNReal.ofReal (1 - (q : ℝ)) := by
    rw [← unitInterval.coe_symm_eq q, ← unitInterval.coe_toNNReal (unitInterval.symm q),
      ENNReal.ofReal_coe_nnreal]
  rw [hq, hq', ENNReal.ofReal_mul (mul_nonneg (by norm_num) q.property.1),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  ring
theorem bernoulli_difference_moment_le :
    ∀ (p : ℝ) (q : Set.Icc (0 : ℝ) 1), 1 ≤ p → p ≤ 2 →
    (∫⁻ ξ : (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)),
      ‖((ξ.1 : ℤ) : ℝ) - ((ξ.2 : ℤ) : ℝ)‖ₑ ^ p
      ∂(bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
        ⟨-1, by decide⟩ q).prod
        (bernoulliMeasure (⟨1, by decide⟩ : ({-1, 1} : Set ℤ))
          ⟨-1, by decide⟩ q)) ≤
      (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) := by
  intro p q h1p hp2
  have hp : 0 < p := by linarith
  have hp_half : 0 ≤ p / 2 := by linarith
  by_cases hq0 : (q : ℝ) = 0
  · rw [bernoulli_difference_moment_eq p q hp]
    simp [hq0, ENNReal.zero_rpow_of_pos (show 0 < p / 2 by linarith)]
  by_cases hq1 : (q : ℝ) = 1
  · rw [bernoulli_difference_moment_eq p q hp]
    simp [hq1, ENNReal.zero_rpow_of_pos (show 0 < p / 2 by linarith)]
  have ha : ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    nlinarith [sq_nonneg ((q : ℝ) - 1 / 2)]
  have ha_pow : ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) ≤
      (ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) := by
    simpa only [ENNReal.rpow_one] using
      (ENNReal.rpow_le_rpow_of_exponent_ge ha (show p / 2 ≤ 1 by linarith) :
        (ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ)))) ^ (1 : ℝ) ≤ _)
  have hvariance : ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ))) =
      4 * ENNReal.ofReal (2 * (q : ℝ) * (1 - (q : ℝ))) := by
    rw [show 8 * (q : ℝ) * (1 - (q : ℝ)) =
      4 * (2 * (q : ℝ) * (1 - (q : ℝ))) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hfour : (4 : ℝ≥0∞) ^ (p / 2) = (2 : ℝ≥0∞) ^ p := by
    calc
      (4 : ℝ≥0∞) ^ (p / 2) = ((2 : ℝ≥0∞) ^ (2 : ℝ)) ^ (p / 2) := by
        norm_num [ENNReal.rpow_natCast]
      _ = (2 : ℝ≥0∞) ^ (2 * (p / 2)) := (ENNReal.rpow_mul _ _ _).symm
      _ = (2 : ℝ≥0∞) ^ p := by congr 1; ring
  rw [bernoulli_difference_moment_eq p q hp, hvariance,
    ENNReal.mul_rpow_of_nonneg _ _ hp_half, hfour]
  gcongr
theorem probability_integral_enorm_rpow_le :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (p : ℝ) (f : Ω → X),
      1 ≤ p → MeasureTheory.AEStronglyMeasurable f μ →
      ‖∫ ω, f ω ∂μ‖ₑ ^ p ≤ ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ := by
  intro X _ _ _ Ω _ μ _ p f hp hf
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hL1 : (∫⁻ ω, ‖f ω‖ₑ ∂μ) = eLpNorm' f 1 μ := by
    simp [eLpNorm'_eq_lintegral_enorm]
  have hLp : ‖∫ ω, f ω ∂μ‖ₑ ≤ eLpNorm' f p μ := by
    calc
      ‖∫ ω, f ω ∂μ‖ₑ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm f
      _ = eLpNorm' f 1 μ := hL1
      _ ≤ eLpNorm' f p μ :=
        eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) hp μ hf
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp_pos]
  exact ENNReal.rpow_le_rpow hLp hp_pos.le
theorem cube_flip_involutive (n : ℕ) (j : Fin n) :
    Function.Involutive (fun δ : Fin n → ({-1, 1} : Set ℤ) ↦
      Function.update δ j (-δ j)) := by
  intro δ
  funext k
  by_cases hk : k = j
  · subst k
    simp only [Function.update_self]
    apply Subtype.ext
    change -(-(δ j : ℤ)) = (δ j : ℤ)
    exact neg_neg _
  · simp [Function.update_of_ne hk]
theorem sign_noise_scalar_identity (t : ℝ) (a : ({-1, 1} : Set ℤ)) :
    (1 + t * ((a : ℤ) : ℝ)) * (((a : ℤ) : ℝ) - t) =
      (1 - t ^ 2) * ((a : ℤ) : ℝ) := by
  rcases a with ⟨a, ha⟩
  have h : a = -1 ∨ a = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  rcases h with h | h <;> subst a <;> norm_num <;> ring
theorem cube_erased_weight_flip (n : ℕ) (j : Fin n) (t : ℝ)
    (δ : Fin n → ({-1, 1} : Set ℤ)) :
    ((((Function.update δ j (-δ j)) j) : ℤ) : ℝ) *
      (∏ k ∈ Finset.univ.erase j,
        (1 + t * ((((Function.update δ j (-δ j)) k) : ℤ) : ℝ))) =
      -(((δ j : ℤ) : ℝ) *
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) := by
  have hprod : (∏ k ∈ Finset.univ.erase j,
      (1 + t * ((((Function.update δ j (-δ j)) k) : ℤ) : ℝ))) =
      ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [hprod, Function.update_self]
  change (Int.cast (-(δ j : ℤ)) : ℝ) * _ = _
  simp only [Int.cast_neg, neg_mul]
theorem cube_noise_weight_coefficient (n : ℕ) (j : Fin n) (t : ℝ)
    (δ : Fin n → ({-1, 1} : Set ℤ)) :
    (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) * (((δ j : ℤ) : ℝ) - t) =
      (1 - t ^ 2) * (((δ j : ℤ) : ℝ) *
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k : Fin n ↦ 1 + t * ((δ k : ℤ) : ℝ)) (Finset.mem_univ j)]
  calc
    ((1 + t * ((δ j : ℤ) : ℝ)) *
        (∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)))) *
          (((δ j : ℤ) : ℝ) - t) =
      ((1 + t * ((δ j : ℤ) : ℝ)) * (((δ j : ℤ) : ℝ) - t)) *
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)) := by ring
    _ = _ := by rw [sign_noise_scalar_identity]; ring
theorem cube_flip_weighted_difference
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (j : Fin n) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (w : (Fin n → ({-1, 1} : Set ℤ)) → ℝ)
    (hw : ∀ δ, w (Function.update δ j (-δ j)) = -w δ) :
    (∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • D j f δ) =
      ∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ := by
  have hflip : (∑ δ : Fin n → ({-1, 1} : Set ℤ),
      w δ • f (Function.update δ j (-δ j))) =
      -(∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ) := by
    calc
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          w δ • f (Function.update δ j (-δ j))) =
        ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          w (Function.update δ j (-δ j)) • f δ := by
        refine Fintype.sum_bijective (fun δ ↦ Function.update δ j (-δ j))
          (cube_flip_involutive n j).bijective _ _ ?_
        intro δ
        have hδ : Function.update (Function.update δ j (-δ j)) j
            (-(Function.update δ j (-δ j)) j) = δ := cube_flip_involutive n j δ
        rw [hδ]
      _ = _ := by simp only [hw, neg_smul, Finset.sum_neg_distrib]
  calc
    (∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • D j f δ) =
      (1 / (2 : ℝ)) • ((∑ δ : Fin n → ({-1, 1} : Set ℤ), w δ • f δ) -
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          w δ • f (Function.update δ j (-δ j)))) := by
      simp only [D, smul_sub, smul_smul, Finset.smul_sum, Finset.sum_sub_distrib,
        mul_comm]
    _ = _ := by
      rw [hflip, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
      norm_num
theorem weighted_cube_derivative_identity :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X) (t : ℝ),
      (1 - t ^ 2) • (∑ δ : (Fin n → ({-1, 1} : Set ℤ)),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • f δ) =
      ∑ δ : (Fin n → ({-1, 1} : Set ℤ)),
        (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) •
          (∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • RademacherEnfloType.D j f δ) := by
  intro X _ _ _ n f t
  symm
  calc
    (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) •
          (∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • D j f δ)) =
      ∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        ((∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) *
          (((δ j : ℤ) : ℝ) - t)) • D j f δ := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
    _ = (1 - t ^ 2) •
      (∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • D j f δ) := by
      simp only [cube_noise_weight_coefficient, Finset.smul_sum, smul_smul]
    _ = (1 - t ^ 2) •
      (∑ j : Fin n, ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • f δ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact cube_flip_weighted_difference X n j f
        (fun δ ↦ ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ)))
        (fun δ ↦ cube_erased_weight_flip n j t δ)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
noncomputable def centeredBernoulliMeasure (q : Set.Icc (0 : ℝ) 1) :
    Measure ({-1, 1} : Set ℤ) :=
  bernoulliMeasure ⟨1, by decide⟩ ⟨-1, by decide⟩ q
instance centeredBernoulliMeasure_probability (q : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (centeredBernoulliMeasure q) := by
  unfold centeredBernoulliMeasure
  infer_instance
noncomputable def centeredBernoulliCube (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
    Measure (Fin n → ({-1, 1} : Set ℤ)) :=
  Measure.pi (fun _ : Fin n ↦ centeredBernoulliMeasure q)
instance centeredBernoulliCube_probability (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (centeredBernoulliCube n q) := by
  unfold centeredBernoulliCube
  infer_instance
def cubeTranslate (n : ℕ) (δ ε : Fin n → ({-1, 1} : Set ℤ)) :
    Fin n → ({-1, 1} : Set ℤ) :=
  fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k
theorem rademacher_sign_neg_preserving :
    MeasurePreserving (fun a : ({-1, 1} : Set ℤ) ↦ -a)
      rademacherDistribution rademacherDistribution := by
  constructor
  · exact measurable_of_countable _
  · unfold rademacherDistribution
    rw [map_bernoulliMeasure]
    simp only [bernoulliMeasure_def]
    have hp : (-(⟨1, by decide⟩ : ({-1, 1} : Set ℤ))) = ⟨-1, by decide⟩ := by rfl
    have hm : (-(⟨-1, by decide⟩ : ({-1, 1} : Set ℤ))) = ⟨1, by decide⟩ := by
      apply Subtype.ext
      change -(-1 : ℤ) = 1
      norm_num
    rw [hp, hm]
    have hq : unitInterval.symm (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨1 / 2, by norm_num⟩ := by
      apply Subtype.ext
      norm_num [unitInterval.coe_symm_eq]
    rw [hq, add_comm]
theorem cubeTranslate_preserving (n : ℕ) (δ : Fin n → ({-1, 1} : Set ℤ)) :
    MeasurePreserving (cubeTranslate n δ)
      (rademacherProductDistribution (Fin n)) (rademacherProductDistribution (Fin n)) := by
  haveI : IsProbabilityMeasure rademacherDistribution := by
    unfold rademacherDistribution
    infer_instance
  unfold rademacherProductDistribution
  rw [Measure.infinitePi_eq_pi]
  unfold cubeTranslate
  refine measurePreserving_pi (fun _ : Fin n ↦ rademacherDistribution)
    (fun _ : Fin n ↦ rademacherDistribution)
    (f := fun j a ↦ if (δ j : ℤ) = 1 then a else -a) ?_
  intro j
  by_cases hj : (δ j : ℤ) = 1
  · simp only [hj, if_true]
    exact ⟨measurable_id, by simp⟩
  · simpa only [hj, if_false] using rademacher_sign_neg_preserving
theorem cubeTranslate_lintegral (n : ℕ) (δ : Fin n → ({-1, 1} : Set ℤ))
    (g : (Fin n → ({-1, 1} : Set ℤ)) → ℝ≥0∞) :
    (∫⁻ ε, g (cubeTranslate n δ ε) ∂rademacherProductDistribution (Fin n)) =
      ∫⁻ ε, g ε ∂rademacherProductDistribution (Fin n) := by
  exact (cubeTranslate_preserving n δ).lintegral_comp (measurable_of_countable _)
theorem centeredBernoulli_sign_mean (q : Set.Icc (0 : ℝ) 1) :
    (∫ a : ({-1, 1} : Set ℤ), ((a : ℤ) : ℝ) ∂centeredBernoulliMeasure q) =
      2 * (q : ℝ) - 1 := by
  unfold centeredBernoulliMeasure
  rw [integral_bernoulliMeasure]
  norm_num
  ring
theorem centeredBernoulli_coordinate_mean (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
    (j : Fin n) :
    (∫ δ : Fin n → ({-1, 1} : Set ℤ), ((δ j : ℤ) : ℝ)
      ∂centeredBernoulliCube n q) = 2 * (q : ℝ) - 1 := by
  unfold centeredBernoulliCube
  rw [integral_comp_eval (μ := fun _ : Fin n ↦ centeredBernoulliMeasure q)
    (i := j) (f := fun a : ({-1, 1} : Set ℤ) ↦ ((a : ℤ) : ℝ))
    StronglyMeasurable.of_discrete.aestronglyMeasurable]
  exact centeredBernoulli_sign_mean q
noncomputable def centeredBernoulliPairs (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
    Measure (Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) :=
  Measure.pi (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
instance centeredBernoulliPairs_probability (n : ℕ) (q : Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (centeredBernoulliPairs n q) := by
  unfold centeredBernoulliPairs
  infer_instance
def bernoulliPairSwap (n : ℕ) (σ : Fin n → ({-1, 1} : Set ℤ))
    (ξ : Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) :
    Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)) :=
  fun j ↦ if (σ j : ℤ) = 1 then ξ j else (ξ j).swap
theorem bernoulliPairSwap_preserving (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
    (σ : Fin n → ({-1, 1} : Set ℤ)) :
    MeasurePreserving (bernoulliPairSwap n σ)
      (centeredBernoulliPairs n q) (centeredBernoulliPairs n q) := by
  unfold centeredBernoulliPairs bernoulliPairSwap
  refine measurePreserving_pi
    (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
    (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q))
    (f := fun j (a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ)) ↦
      if (σ j : ℤ) = 1 then a else a.swap) ?_
  intro j
  by_cases hj : (σ j : ℤ) = 1
  · simp only [hj, if_true]
    exact ⟨measurable_id, by simp⟩
  · simpa only [hj, if_false] using
      (Measure.measurePreserving_swap (μ := centeredBernoulliMeasure q)
        (ν := centeredBernoulliMeasure q))
theorem bernoulliPairSwap_difference (n : ℕ)
    (σ : Fin n → ({-1, 1} : Set ℤ))
    (ξ : Fin n → (({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ))) (j : Fin n) :
    (((bernoulliPairSwap n σ ξ j).1 : ℤ) : ℝ) -
        (((bernoulliPairSwap n σ ξ j).2 : ℤ) : ℝ) =
      ((σ j : ℤ) : ℝ) * ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) := by
  have h : (σ j : ℤ) = -1 ∨ (σ j : ℤ) = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (σ j).property
  rcases h with h | h <;> simp [bernoulliPairSwap, h]
theorem centeredBernoulliPairs_sign_integral
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (x : Fin n → X)
    (σ : Fin n → ({-1, 1} : Set ℤ)) :
    (∫⁻ ξ, ‖∑ j : Fin n, ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
      ∂centeredBernoulliPairs n q) =
    (∫⁻ ξ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
      (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
      ∂centeredBernoulliPairs n q) := by
  have h := (bernoulliPairSwap_preserving n q σ).lintegral_comp
    (measurable_of_countable (fun ξ ↦
      ‖∑ j : Fin n, ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p))
  symm
  convert h using 1
  apply lintegral_congr
  intro ξ
  simp only [bernoulliPairSwap_difference, smul_smul]
theorem centeredBernoulli_copy_integral
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (δ : Fin n → ({-1, 1} : Set ℤ))
    (x : Fin n → X) :
    (∫ δ' : Fin n → ({-1, 1} : Set ℤ),
      ∑ j : Fin n, (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j
      ∂centeredBernoulliCube n q) =
      ∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j := by
  rw [integral_finsetSum Finset.univ (fun j hj ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_const, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, probReal_univ, one_smul, centeredBernoulli_coordinate_mean]
theorem centeredBernoulli_copy_jensen
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) (x : Fin n → X) :
    (∫⁻ δ, ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j‖ₑ ^ p
      ∂centeredBernoulliCube n q) ≤
    (∫⁻ ξ, ‖∑ j : Fin n,
      ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
      ∂centeredBernoulliPairs n q) := by
  calc
    _ ≤ ∫⁻ δ, ∫⁻ δ', ‖∑ j : Fin n,
        (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂centeredBernoulliCube n q ∂centeredBernoulliCube n q := by
      apply lintegral_mono
      intro δ
      have h := probability_integral_enorm_rpow_le X
        (Fin n → ({-1, 1} : Set ℤ)) (centeredBernoulliCube n q) p
        (fun δ' ↦ ∑ j : Fin n, (((δ j : ℤ) : ℝ) - ((δ' j : ℤ) : ℝ)) • x j)
        hp StronglyMeasurable.of_discrete.aestronglyMeasurable
      rwa [centeredBernoulli_copy_integral] at h
    _ = ∫⁻ z, ‖∑ j : Fin n,
        (((z.1 j : ℤ) : ℝ) - ((z.2 j : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂(centeredBernoulliCube n q).prod (centeredBernoulliCube n q) :=
      lintegral_lintegral (measurable_of_countable _).aemeasurable
    _ = _ := by
      unfold centeredBernoulliCube centeredBernoulliPairs
      exact (measurePreserving_arrowProdEquivProdArrow
        ({-1, 1} : Set ℤ) ({-1, 1} : Set ℤ) (Fin n)
        (fun _ ↦ centeredBernoulliMeasure q) (fun _ ↦ centeredBernoulliMeasure q)
        |>.lintegral_comp (measurable_of_countable _)).symm
theorem centeredBernoulliPairs_symmetrization
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (x : Fin n → X) :
    (∫⁻ ξ, ‖∑ j : Fin n,
      ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
      ∂centeredBernoulliPairs n q) =
    (∫⁻ ξ, ∫⁻ σ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
      (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliPairs n q) := by
  haveI := rademacher_product_probability n
  calc
    _ = ∫⁻ σ : Fin n → ({-1, 1} : Set ℤ),
        (∫⁻ ξ, ‖∑ j : Fin n,
          ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
          ∂centeredBernoulliPairs n q)
        ∂rademacherProductDistribution (Fin n) := by
      rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ σ, ∫⁻ ξ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
        (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂centeredBernoulliPairs n q ∂rademacherProductDistribution (Fin n) := by
      apply lintegral_congr
      intro σ
      exact centeredBernoulliPairs_sign_integral X n q p x σ
    _ = _ := lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
theorem centeredBernoulliPairs_scaled_moment_le
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (j : Fin n) (v : X) :
    (∫⁻ ξ, ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • v)‖ₑ ^ p
      ∂centeredBernoulliPairs n q) ≤
      (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) * ‖v‖ₑ ^ p := by
  calc
    _ = (∫⁻ ξ, ‖((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ))‖ₑ ^ p
        ∂centeredBernoulliPairs n q) * ‖v‖ₑ ^ p := by
      simp only [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ p by linarith)]
      exact lintegral_mul_const _ (measurable_of_countable _)
    _ = (∫⁻ a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ),
        ‖((a.1 : ℤ) : ℝ) - ((a.2 : ℤ) : ℝ)‖ₑ ^ p
        ∂(centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q)) * ‖v‖ₑ ^ p := by
      congr 1
      unfold centeredBernoulliPairs
      exact (measurePreserving_eval
        (fun _ : Fin n ↦ (centeredBernoulliMeasure q).prod (centeredBernoulliMeasure q)) j
        |>.lintegral_comp (measurable_of_countable
          (fun a : ({-1, 1} : Set ℤ) × ({-1, 1} : Set ℤ) ↦
            ‖((a.1 : ℤ) : ℝ) - ((a.2 : ℤ) : ℝ)‖ₑ ^ p)))
    _ ≤ _ := mul_le_mul' (bernoulli_difference_moment_le p q hp hp2) le_rfl
theorem centeredBernoulli_cube_bound
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (p : ℝ) (C : ℝ≥0∞) (q : Set.Icc (0 : ℝ) 1) (x : Fin n → X)
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hC : IsRademacherType X C p) :
    (∫⁻ δ, ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x j‖ₑ ^ p
      ∂centeredBernoulliCube n q) ≤
      (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
        C ^ p * ∑ j : Fin n, ‖x j‖ₑ ^ p := by
  calc
    _ ≤ ∫⁻ ξ, ‖∑ j : Fin n,
        ((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j‖ₑ ^ p
        ∂centeredBernoulliPairs n q := centeredBernoulli_copy_jensen X n q p hp x
    _ = ∫⁻ ξ, ∫⁻ σ, ‖∑ j : Fin n, ((σ j : ℤ) : ℝ) •
        (((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliPairs n q :=
      centeredBernoulliPairs_symmetrization X n q p x
    _ ≤ ∫⁻ ξ, C ^ p * ∑ j : Fin n,
        ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂centeredBernoulliPairs n q := by
      apply lintegral_mono
      intro ξ
      exact hC n hn _
    _ = C ^ p * ∑ j : Fin n, ∫⁻ ξ,
        ‖(((((ξ j).1 : ℤ) : ℝ) - (((ξ j).2 : ℤ) : ℝ)) • x j)‖ₑ ^ p
        ∂centeredBernoulliPairs n q := by
      rw [lintegral_const_mul _ (measurable_of_countable _),
        lintegral_finsetSum Finset.univ (fun j hj ↦ measurable_of_countable _)]
    _ ≤ C ^ p * ∑ j : Fin n,
        (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) * ‖x j‖ₑ ^ p := by
      refine mul_le_mul' le_rfl ?_
      apply Finset.sum_le_sum
      intro j hj
      exact centeredBernoulliPairs_scaled_moment_le X n q p hp hp2 j (x j)
    _ = _ := by rw [← Finset.mul_sum]; ac_rfl
theorem centered_bernoulli_cube_joint_bound :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (n : ℕ) (p : ℝ) (C : ℝ≥0∞) (q : Set.Icc (0 : ℝ) 1)
      (x : (Fin n → ({-1, 1} : Set ℤ)) → Fin n → X),
      1 ≤ n → 1 ≤ p → p ≤ 2 →
      RademacherEnfloType.IsRademacherType X C p →
      (∫⁻ ε : Fin n → ({-1, 1} : Set ℤ),
        (∫⁻ δ : Fin n → ({-1, 1} : Set ℤ),
          ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
            x (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k) j‖ₑ ^ p
          ∂MeasureTheory.Measure.infinitePi (fun _ : Fin n ↦
            ProbabilityTheory.bernoulliMeasure
              (⟨1, by decide⟩ : ({-1, 1} : Set ℤ)) ⟨-1, by decide⟩ q))
        ∂RademacherEnfloType.rademacherProductDistribution (Fin n)) ≤
        (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
          C ^ p * ∑ j : Fin n,
            (∫⁻ ε : Fin n → ({-1, 1} : Set ℤ), ‖x ε j‖ₑ ^ p
              ∂RademacherEnfloType.rademacherProductDistribution (Fin n)) := by
  intro X _ _ _ n p C q x hn hp hp2 hC
  haveI := rademacher_product_probability n
  rw [Measure.infinitePi_eq_pi]
  change (∫⁻ ε, ∫⁻ δ,
    ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
      x (cubeTranslate n δ ε) j‖ₑ ^ p
    ∂centeredBernoulliCube n q ∂rademacherProductDistribution (Fin n)) ≤ _
  calc
    _ = ∫⁻ δ, ∫⁻ ε,
        ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) •
          x (cubeTranslate n δ ε) j‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliCube n q :=
      lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
    _ = ∫⁻ δ, ∫⁻ ε,
        ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) ∂centeredBernoulliCube n q := by
      apply lintegral_congr
      intro δ
      exact cubeTranslate_lintegral n δ
        (fun ε ↦ ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p)
    _ = ∫⁻ ε, ∫⁻ δ,
        ‖∑ j : Fin n, (((δ j : ℤ) : ℝ) - (2 * (q : ℝ) - 1)) • x ε j‖ₑ ^ p
        ∂centeredBernoulliCube n q ∂rademacherProductDistribution (Fin n) :=
      lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
    _ ≤ ∫⁻ ε, (ENNReal.ofReal (8 * (q : ℝ) * (1 - (q : ℝ)))) ^ (p / 2) *
        C ^ p * ∑ j : Fin n, ‖x ε j‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n) := by
      apply lintegral_mono
      intro ε
      exact centeredBernoulli_cube_bound X n p C q (x ε) hn hp hp2 hC
    _ = _ := by
      rw [lintegral_const_mul _ (measurable_of_countable _),
        lintegral_finsetSum Finset.univ (fun j hj ↦ measurable_of_countable _)]
theorem Helpers.arcsine_kernel_mass :
    IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
      MeasureTheory.volume (-1 : ℝ) (1 : ℝ) ∧
    (∫ t in (-1 : ℝ)..(1 : ℝ), (Real.sqrt (1 - t ^ 2))⁻¹) = Real.pi := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
      MeasureTheory.volume (-1 : ℝ) (1 : ℝ) := by
    simpa only [Real.sqrt_inv] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  refine ⟨hint, ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := Real.arcsin) (f' := fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
    (show (-1 : ℝ) ≤ 1 by norm_num) Real.continuous_arcsin.continuousOn
    (by
      intro t ht
      simpa only [one_div] using
        Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)) hint
  calc
    (∫ t in (-1 : ℝ)..(1 : ℝ), (Real.sqrt (1 - t ^ 2))⁻¹) =
        Real.arcsin 1 - Real.arcsin (-1) := hFTC
    _ = Real.pi := by rw [Real.arcsin_one, Real.arcsin_neg_one]; ring
theorem noise_product_deriv (n : ℕ) (a : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∏ k : Fin n, (1 + s * a k))
      (∑ j : Fin n, a j * ∏ k ∈ Finset.univ.erase j, (1 + t * a k)) t := by
  have h := HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => fun s : ℝ => 1 + s * a i) (f' := a) (x := t) (by
        intro i hi
        simpa [add_comm, mul_comm] using
          HasDerivAt.add_const 1 ((hasDerivAt_id' t).mul_const (a i)))
  have hder : HasDerivAt (∏ i : Fin n, fun s : ℝ => 1 + s * a i)
      (∑ j : Fin n, a j * ∏ k ∈ Finset.univ.erase j, (1 + t * a k)) t :=
    h.congr_deriv (by simp [smul_eq_mul, mul_comm])
  exact hder.congr_of_eventuallyEq (by
    filter_upwards [] with s
    simp only [Finset.prod_apply])
theorem noise_polynomial_antipodal_integral
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) :
    (1 / (2 : ℝ)) • (f ε - f (-ε)) =
    ∫ t in (-1 : ℝ)..(1 : ℝ),
      (1 / (2 * (2 : ℝ) ^ n)) •
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) •
          f (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k)) := by
  classical
  let g : (Fin n → ({-1, 1} : Set ℤ)) → X :=
    fun δ => f (fun k ↦ if (δ k : ℤ) = 1 then ε k else -ε k)
  let c : ℝ := 1 / (2 * (2 : ℝ) ^ n)
  let P : ℝ → X := fun t =>
    c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
      (∏ k : Fin n, (1 + t * ((δ k : ℤ) : ℝ))) • g δ
  have hPderiv : ∀ t : ℝ, HasDerivAt P
      (c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ) t := by
    intro t
    have hsum : HasDerivAt
        (fun s : ℝ => ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + s * ((δ k : ℤ) : ℝ))) • g δ)
        (∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
            ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ) t := by
      apply HasDerivAt.fun_sum
      intro δ hδ
      have hp := noise_product_deriv n (fun k ↦ ((δ k : ℤ) : ℝ)) t
      have hs := hp.smul_const (g δ)
      simpa [smul_eq_mul, mul_comm] using hs
    have hc := hsum.const_smul c
    change HasDerivAt (fun s : ℝ => c •
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∏ k : Fin n, (1 + s * ((δ k : ℤ) : ℝ))) • g δ)) _ t
    convert hc using 1 <;> funext s <;> rfl
  have hPcont : ContinuousOn P (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hPint : IntervalIntegrable
      (fun t => c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
      MeasureTheory.volume (-1 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (f := P)
    (f' := fun t => c • ∑ δ : Fin n → ({-1, 1} : Set ℤ),
      (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
    (by norm_num) hPcont (fun t ht => hPderiv t) hPint
  change (1 / (2 : ℝ)) • (f ε - f (-ε)) =
    ∫ t in (-1 : ℝ)..(1 : ℝ),
      c • (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
          ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) • g δ)
  let δp : Fin n → ({-1, 1} : Set ℤ) := fun _ => ⟨1, by simp⟩
  let δm : Fin n → ({-1, 1} : Set ℤ) := fun _ => ⟨-1, by simp⟩
  have hsum1 :
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∏ k : Fin n, (1 + (1 : ℝ) * ((δ k : ℤ) : ℝ))) • g δ) =
      (2 : ℝ) ^ n • f ε := by
    rw [Finset.sum_eq_single δp]
    · simp [δp, g]
      congr 1
      norm_num
    · intro δ hδ hne
      by_cases heq : δ = δp
      · exact (hne heq).elim
      · obtain ⟨k, hk⟩ : ∃ k : Fin n, δ k ≠ δp k := by
          by_contra hno
          apply heq
          funext k
          exact not_not.mp (fun h => hno ⟨k, h⟩)
        have hδk : (δ k : ℤ) = -1 := by
          have hv' : (δ k : ℤ) = -1 ∨ (δ k : ℤ) = 1 := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ k).property
          rcases hv' with hv' | hv'
          · exact hv'
          · exfalso
            apply hk
            apply Subtype.ext
            simpa [δp] using hv'
        have hz : (∏ k : Fin n, (1 + (1 : ℝ) * ((δ k : ℤ) : ℝ))) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          simp [hδk]
        rw [hz]
        simp
    · simp
  have hsumm :
      (∑ δ : Fin n → ({-1, 1} : Set ℤ),
        (∏ k : Fin n, (1 + (-1 : ℝ) * ((δ k : ℤ) : ℝ))) • g δ) =
      (2 : ℝ) ^ n • f (-ε) := by
    rw [Finset.sum_eq_single δm]
    · simp [δm, g]
      congr 1
      norm_num
    · intro δ hδ hne
      by_cases heq : δ = δm
      · exact (hne heq).elim
      · obtain ⟨k, hk⟩ : ∃ k : Fin n, δ k ≠ δm k := by
          by_contra hno
          apply heq
          funext k
          exact not_not.mp (fun h => hno ⟨k, h⟩)
        have hδk : (δ k : ℤ) = 1 := by
          have hv' : (δ k : ℤ) = -1 ∨ (δ k : ℤ) = 1 := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ k).property
          rcases hv' with hv' | hv'
          · exfalso
            apply hk
            apply Subtype.ext
            simpa [δm] using hv'
          · exact hv'
        have hz : (∏ k : Fin n, (1 + (-1 : ℝ) * ((δ k : ℤ) : ℝ))) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          simp [hδk]
        rw [hz]
        simp
    · simp
  rw [hFTC]
  simp only [P, c]
  rw [hsum1, hsumm]
  rw [smul_sub, smul_smul, smul_smul]
  congr 1 <;> field_simp
theorem type_constants_of_reverse_conversion :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (p : ℝ),
      1 ≤ p → p ≤ 2 →
      (∀ C : ℝ≥0∞, RademacherEnfloType.IsRademacherType X C p →
        RademacherEnfloType.IsEnfloType X
          (((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) * C) p) →
      RademacherEnfloType.TR X p ≤ RademacherEnfloType.TE X p ∧
        RademacherEnfloType.TE X p ≤
          ((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) *
            RademacherEnfloType.TR X p := by
  intro X _ _ _ p h1p hp2 hconvert
  let k : ℝ≥0∞ :=
    (NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)
  have hsqrt : 0 < NNReal.sqrt (2 : ℝ≥0) :=
    NNReal.sqrt_pos.mpr (by norm_num)
  have hkcoe : k = ((NNReal.pi / NNReal.sqrt (2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.coe_div (ne_of_gt hsqrt)).symm
  have hk0 : k ≠ 0 := by
    rw [hkcoe, ENNReal.coe_ne_zero]
    exact ne_of_gt (div_pos NNReal.pi_pos hsqrt)
  have hktop : k ≠ ∞ := by
    rw [hkcoe]
    exact ENNReal.coe_ne_top
  constructor
  · unfold RademacherEnfloType.TR RademacherEnfloType.TE
    apply le_sInf
    intro C hC
    exact sInf_le (enflo_implies_rademacher X p C h1p hp2 hC)
  · change RademacherEnfloType.TE X p ≤ k * RademacherEnfloType.TR X p
    apply (ENNReal.div_le_iff' hk0 hktop).mp
    unfold RademacherEnfloType.TR
    apply le_sInf
    intro C hC
    apply (ENNReal.div_le_iff' hk0 hktop).mpr
    exact sInf_le (hconvert C hC)
noncomputable def enfloArcsineDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)
noncomputable def enfloArcsineMeasure : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity enfloArcsineDensity
theorem enfloArcsineDensity_measurable : Measurable enfloArcsineDensity := by
  unfold enfloArcsineDensity
  fun_prop
theorem enfloArcsineDensity_toReal (t : ℝ) :
    (enfloArcsineDensity t).toReal = (Real.pi * Real.sqrt (1 - t ^ 2))⁻¹ := by
  rw [enfloArcsineDensity, ENNReal.toReal_ofReal]
  positivity
theorem enfloArcsineMeasure_probability :
    MeasureTheory.IsProbabilityMeasure enfloArcsineMeasure := by
  have hmass := Helpers.arcsine_kernel_mass
  have hi : Integrable (fun t : ℝ ↦ (Real.sqrt (1 - t ^ 2))⁻¹)
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact hmass.1.1
  have hi' : Integrable (fun t : ℝ ↦ (Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)) := by
    simpa only [mul_inv_rev, mul_comm] using hi.const_mul Real.pi⁻¹
  constructor
  rw [enfloArcsineMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫⁻ t in Set.Ioo (-1 : ℝ) 1,
    ENNReal.ofReal ((Real.pi * Real.sqrt (1 - t ^ 2))⁻¹)) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall (by
    intro t; positivity))]
  simp only [mul_inv_rev]
  rw [integral_mul_const, restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), hmass.2]
  rw [mul_inv_cancel₀ Real.pi_ne_zero]
  norm_num
theorem enfloArcsineMeasure_ae_mem :
    ∀ᵐ t ∂enfloArcsineMeasure, t ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Ioo)
theorem enfloArcsineDensity_sqrt_cancel (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    (enfloArcsineDensity t).toReal * Real.sqrt (2 * (1 - t ^ 2)) =
      Real.sqrt 2 / Real.pi := by
  have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  rw [enfloArcsineDensity_toReal, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hz := (Real.sqrt_pos.2 hs).ne'
  field_simp
theorem enfloArcsineMeasure_integral_recovery
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (g : ℝ → X) :
    (∫ t in (-1 : ℝ)..(1 : ℝ), g t) =
      (Real.pi / Real.sqrt 2) •
        (∫ t, Real.sqrt (2 * (1 - t ^ 2)) • g t ∂enfloArcsineMeasure) := by
  rw [enfloArcsineMeasure, integral_withDensity_eq_integral_toReal_smul
    enfloArcsineDensity_measurable (Filter.Eventually.of_forall (by
      intro t; exact ENNReal.ofReal_lt_top))]
  rw [integral_congr_ae (Filter.Eventually.mono
    (ae_restrict_mem measurableSet_Ioo) (by
      intro t ht
      rw [smul_smul, enfloArcsineDensity_sqrt_cancel t ht]))]
  rw [integral_smul, smul_smul]
  have hc : Real.pi / Real.sqrt 2 * (Real.sqrt 2 / Real.pi) = 1 := by
    have hz : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp
  rw [hc, one_smul, restrict_Ioo_eq_restrict_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
theorem centeredBernoulliMeasure_singleton_real
    (q : Set.Icc (0 : ℝ) 1) (a : ({-1, 1} : Set ℤ)) :
    (centeredBernoulliMeasure q).real {a} =
      (1 + (2 * (q : ℝ) - 1) * ((a : ℤ) : ℝ)) / 2 := by
  rcases a with ⟨a, ha⟩
  have h : a = -1 ∨ a = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  rcases h with h | h <;> subst a
  · simp [centeredBernoulliMeasure, bernoulliMeasure_def, Measure.real,
      unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    ring
  · simp [centeredBernoulliMeasure, bernoulliMeasure_def, Measure.real,
      unitInterval.coe_toNNReal]
theorem centeredBernoulliCube_singleton_real
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1) (δ : Fin n → ({-1, 1} : Set ℤ)) :
    (centeredBernoulliCube n q).real {δ} =
      (1 / (2 : ℝ) ^ n) *
        ∏ k : Fin n, (1 + (2 * (q : ℝ) - 1) * ((δ k : ℤ) : ℝ)) := by
  rw [Measure.real, centeredBernoulliCube, Measure.pi_singleton, ENNReal.toReal_prod]
  change (∏ k : Fin n, (centeredBernoulliMeasure q).real {δ k}) = _
  simp only [centeredBernoulliMeasure_singleton_real, div_eq_mul_inv,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← inv_pow]
  ring
theorem centeredBernoulliCube_integral_eq
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (q : Set.Icc (0 : ℝ) 1)
    (g : (Fin n → ({-1, 1} : Set ℤ)) → X) :
    (∫ δ, g δ ∂centeredBernoulliCube n q) =
      (1 / (2 : ℝ) ^ n) •
        ∑ δ : Fin n → ({-1, 1} : Set ℤ),
          (∏ k : Fin n, (1 + (2 * (q : ℝ) - 1) * ((δ k : ℤ) : ℝ))) • g δ := by
  rw [integral_fintype Integrable.of_finite]
  simp only [centeredBernoulliCube_singleton_real, Finset.smul_sum, smul_smul]
theorem cubeTranslate_update (n : ℕ) (δ ε : Fin n → ({-1, 1} : Set ℤ)) (j : Fin n) :
    cubeTranslate n (Function.update δ j (-δ j)) ε =
      Function.update (cubeTranslate n δ ε) j (-(cubeTranslate n δ ε j)) := by
  classical
  funext k
  by_cases hk : k = j
  · subst k
    simp only [Function.update_self, cubeTranslate]
    change (if -(δ j : ℤ) = 1 then ε j else -ε j) =
      -(if (δ j : ℤ) = 1 then ε j else -ε j)
    have hj : (δ j : ℤ) = -1 ∨ (δ j : ℤ) = 1 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (δ j).property
    rcases hj with hj | hj
    · simp only [hj]
      norm_num
      apply Subtype.ext
      change (ε j : ℤ) = -(-(ε j : ℤ))
      simp
    · simp only [hj]
      norm_num
  · simp only [cubeTranslate, Function.update_of_ne hk]
theorem cubeTranslate_derivative
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (δ ε : Fin n → ({-1, 1} : Set ℤ)) (j : Fin n) :
    D j (fun η ↦ f (cubeTranslate n η ε)) δ = D j f (cubeTranslate n δ ε) := by
  unfold D
  dsimp only
  rw [cubeTranslate_update]
noncomputable def enfloNoiseDerivative
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ) : X :=
  (1 / (2 * (2 : ℝ) ^ n)) •
    (∑ δ : Fin n → ({-1, 1} : Set ℤ),
      (∑ j : Fin n, ((δ j : ℤ) : ℝ) *
        ∏ k ∈ Finset.univ.erase j, (1 + t * ((δ k : ℤ) : ℝ))) •
      f (cubeTranslate n δ ε))
noncomputable def enfloNormalizedNoise
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ) : X :=
  Real.sqrt (2 * (1 - t ^ 2)) • enfloNoiseDerivative X n f ε t
theorem enfloNormalizedNoise_continuous
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) :
    Continuous (enfloNormalizedNoise X n f ε) := by
  unfold enfloNormalizedNoise enfloNoiseDerivative
  fun_prop
theorem enflo_antipodal_kernel_expectation
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) :
    (1 / (2 : ℝ)) • (f ε - f (-ε)) =
      (Real.pi / Real.sqrt 2) •
        (∫ t, enfloNormalizedNoise X n f ε t ∂enfloArcsineMeasure) := by
  rw [noise_polynomial_antipodal_integral X n f ε]
  exact enfloArcsineMeasure_integral_recovery X (enfloNoiseDerivative X n f ε)
theorem enfloNoiseDerivative_centered_integral
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ)
    (q : Set.Icc (0 : ℝ) 1) (hq : 2 * (q : ℝ) - 1 = t) :
    (1 - t ^ 2) • enfloNoiseDerivative X n f ε t =
      (1 / (2 : ℝ)) •
        (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
          D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q) := by
  have hw := weighted_cube_derivative_identity X n (fun δ ↦ f (cubeTranslate n δ ε)) t
  simp only [cubeTranslate_derivative] at hw
  rw [centeredBernoulliCube_integral_eq, hq]
  unfold enfloNoiseDerivative
  rw [smul_comm (1 - t ^ 2), hw, smul_smul]
  congr 1
  field_simp
theorem enfloNormalizedNoise_centered_expectation
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
    (ε : Fin n → ({-1, 1} : Set ℤ)) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 2 * (q : ℝ) - 1 = t) :
    enfloNormalizedNoise X n f ε t =
      (Real.sqrt (2 * (1 - t ^ 2)))⁻¹ •
        (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
          D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q) := by
  have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hs' : 0 < 2 * (1 - t ^ 2) := by positivity
  have heq : enfloNoiseDerivative X n f ε t =
      (1 - t ^ 2)⁻¹ • ((1 / (2 : ℝ)) •
        (∫ δ, ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) •
          D j f (cubeTranslate n δ ε) ∂centeredBernoulliCube n q)) := by
    rw [← enfloNoiseDerivative_centered_integral X n f ε t q hq,
      smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  unfold enfloNormalizedNoise
  rw [heq, smul_smul, smul_smul]
  congr 1
  have hz : Real.sqrt (2 * (1 - t ^ 2)) ≠ 0 := (Real.sqrt_pos.2 hs').ne'
  have hsq := Real.sq_sqrt hs'.le
  field_simp
  nlinarith
theorem enflo_sqrt_inv_moment_cancel (s p : ℝ) (hs : 0 < s) :
    (ENNReal.ofReal ((Real.sqrt s)⁻¹)) ^ p *
      (ENNReal.ofReal s) ^ (p / 2) = 1 := by
  have hz : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  have he : ENNReal.ofReal (Real.sqrt s) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hs)).ne'
  have he' : ENNReal.ofReal (Real.sqrt s) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpow : (ENNReal.ofReal s) ^ (p / 2) =
      (ENNReal.ofReal (Real.sqrt s)) ^ p := by
    calc
      (ENNReal.ofReal s) ^ (p / 2) =
          ((ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℝ)) ^ (p / 2) := by
        have hsq : (ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℝ) = ENNReal.ofReal s := by
          calc
            _ = (ENNReal.ofReal (Real.sqrt s)) ^ (2 : ℕ) := by
              simpa using ENNReal.rpow_natCast (ENNReal.ofReal (Real.sqrt s)) 2
            _ = ENNReal.ofReal ((Real.sqrt s) ^ (2 : ℕ)) :=
              (ENNReal.ofReal_pow (Real.sqrt_nonneg s) 2).symm
            _ = ENNReal.ofReal s := by rw [Real.sq_sqrt hs.le]
        rw [hsq]
      _ = (ENNReal.ofReal (Real.sqrt s)) ^ (2 * (p / 2)) :=
        (ENNReal.rpow_mul _ _ _).symm
      _ = _ := by congr 1; ring
  rw [hpow, ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.2 hs), ENNReal.inv_rpow]
  exact ENNReal.inv_mul_cancel (by simp [he, he'])
    (ENNReal.rpow_ne_top_of_ne_zero he he')
theorem enflo_finite_lintegral_swap
    (n : ℕ) (μ : MeasureTheory.Measure ℝ)
    (g : ℝ → (Fin n → ({-1, 1} : Set ℤ)) → ℝ≥0∞)
    (hg : ∀ ε, Measurable (fun t ↦ g t ε)) :
    (∫⁻ ε, (∫⁻ t, g t ε ∂μ) ∂rademacherProductDistribution (Fin n)) =
      ∫⁻ t, (∫⁻ ε, g t ε ∂rademacherProductDistribution (Fin n)) ∂μ := by
  simp only [lintegral_fintype]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ε hε
    exact (lintegral_mul_const _ (hg ε)).symm
  · intro ε hε
    exact (hg ε).mul_const _
theorem enfloNormalizedNoise_cube_moment_le
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (n : ℕ) (p : ℝ) (C : ℝ≥0∞)
    (f : (Fin n → ({-1, 1} : Set ℤ)) → X) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hn : 1 ≤ n) (h1p : 1 ≤ p) (hp2 : p ≤ 2)
    (hC : RademacherEnfloType.IsRademacherType X C p) :
    (∫⁻ ε, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p
      ∂rademacherProductDistribution (Fin n)) ≤
      C ^ p * ∑ j : Fin n,
        (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n)) := by
  let q : Set.Icc (0 : ℝ) 1 := ⟨(1 + t) / 2, by
    constructor <;> linarith [ht.1, ht.2]⟩
  have hq : 2 * (q : ℝ) - 1 = t := by dsimp [q]; ring
  have hs : 0 < 2 * (1 - t ^ 2) := by nlinarith [ht.1, ht.2]
  have hp : 0 ≤ p := by linarith
  let a : ℝ≥0∞ := (ENNReal.ofReal ((Real.sqrt (2 * (1 - t ^ 2)))⁻¹)) ^ p
  let S : (Fin n → ({-1, 1} : Set ℤ)) →
      (Fin n → ({-1, 1} : Set ℤ)) → X :=
    fun ε δ ↦ ∑ j : Fin n, (((δ j : ℤ) : ℝ) - t) • D j f (cubeTranslate n δ ε)
  have hjensen : ∀ ε, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p ≤
      a * (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q) := by
    intro ε
    have hj := probability_integral_enorm_rpow_le X
      (Fin n → ({-1, 1} : Set ℤ)) (centeredBernoulliCube n q) p (S ε)
      h1p StronglyMeasurable.of_discrete.aestronglyMeasurable
    rw [enfloNormalizedNoise_centered_expectation X n f ε t ht q hq,
      enorm_smul, Real.enorm_of_nonneg (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ hp]
    exact mul_le_mul' le_rfl hj
  have hfirst :
      (∫⁻ ε, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n)) ≤
      a * (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
        ∂rademacherProductDistribution (Fin n)) := by
    calc
      _ ≤ ∫⁻ ε, a * (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
          ∂rademacherProductDistribution (Fin n) := lintegral_mono hjensen
      _ = _ := lintegral_const_mul a (measurable_of_countable _)
  have hvariance : 8 * (q : ℝ) * (1 - (q : ℝ)) = 2 * (1 - t ^ 2) := by
    dsimp [q]
    ring
  have hjoint :
      (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
        ∂rademacherProductDistribution (Fin n)) ≤
      (ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
        ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n)) := by
    have h := centered_bernoulli_cube_joint_bound X n p C q (fun ε j ↦ D j f ε)
      hn h1p hp2 hC
    rw [Measure.infinitePi_eq_pi, hq, hvariance] at h
    change (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
      ∂rademacherProductDistribution (Fin n)) ≤
      (ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
        ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n)) at h
    exact h
  calc
    _ ≤ a * (∫⁻ ε, (∫⁻ δ, ‖S ε δ‖ₑ ^ p ∂centeredBernoulliCube n q)
        ∂rademacherProductDistribution (Fin n)) := hfirst
    _ ≤ a * ((ENNReal.ofReal (2 * (1 - t ^ 2))) ^ (p / 2) * C ^ p *
        ∑ j : Fin n, (∫⁻ ε, ‖D j f ε‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n))) := mul_le_mul' le_rfl hjoint
    _ = _ := by
      dsimp only [a]
      rw [← mul_assoc, ← mul_assoc, enflo_sqrt_inv_moment_cancel _ p hs, one_mul]
theorem enflo_type_constant_eq :
    ENNReal.ofReal (Real.pi / Real.sqrt 2) =
      (NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by norm_num))]
  have hpi : ENNReal.ofReal Real.pi = (NNReal.pi : ℝ≥0∞) := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hs : ENNReal.ofReal (Real.sqrt 2) = (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) := by
    simpa only [Real.coe_sqrt, NNReal.coe_ofNat] using
      (show ENNReal.ofReal ((NNReal.sqrt (2 : ℝ≥0)) : ℝ) =
        (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  rw [hpi, hs]
theorem rademacher_implies_enflo :
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (p : ℝ) (C : ℝ≥0∞),
      1 ≤ p → p ≤ 2 →
      RademacherEnfloType.IsRademacherType X C p →
      RademacherEnfloType.IsEnfloType X
        (((NNReal.pi : ℝ≥0∞) / (NNReal.sqrt (2 : ℝ≥0) : ℝ≥0∞)) * C) p := by
  intro X _ _ _ p C h1p hp2 hC n hn f
  letI := enfloArcsineMeasure_probability
  have hp : 0 ≤ p := by linarith
  have hscalar : 0 ≤ Real.pi / Real.sqrt 2 := by positivity
  have hJ : ∀ ε, ‖(1 / (2 : ℝ)) • (f ε - f (-ε))‖ₑ ^ p ≤
      (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
        (∫⁻ t, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p ∂enfloArcsineMeasure) := by
    intro ε
    rw [enflo_antipodal_kernel_expectation X n f ε, enorm_smul,
      Real.enorm_of_nonneg hscalar, ENNReal.mul_rpow_of_nonneg _ _ hp]
    exact mul_le_mul' le_rfl
      (probability_integral_enorm_rpow_le X ℝ enfloArcsineMeasure p
        (enfloNormalizedNoise X n f ε) h1p
        (enfloNormalizedNoise_continuous X n f ε).aestronglyMeasurable)
  have hswap := enflo_finite_lintegral_swap n enfloArcsineMeasure
    (fun t ε ↦ ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p)
    (fun ε ↦ (enfloNormalizedNoise_continuous X n f ε).enorm.measurable.pow_const p)
  have hmoment :
      (∫⁻ t, (∫⁻ ε, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p
        ∂rademacherProductDistribution (Fin n)) ∂enfloArcsineMeasure) ≤
      C ^ p * ∑ j : Fin n,
        (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n)) := by
    calc
      _ ≤ ∫⁻ _t : ℝ,
          C ^ p * ∑ j : Fin n,
            (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))
          ∂enfloArcsineMeasure := lintegral_mono_ae (enfloArcsineMeasure_ae_mem.mono
            (fun t ht ↦ enfloNormalizedNoise_cube_moment_le X n p C f t ht hn h1p hp2 hC))
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  calc
    _ ≤ ∫⁻ ε, (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
        (∫⁻ t, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p ∂enfloArcsineMeasure)
        ∂rademacherProductDistribution (Fin n) := lintegral_mono hJ
    _ = (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
        (∫⁻ t, (∫⁻ ε, ‖enfloNormalizedNoise X n f ε t‖ₑ ^ p
          ∂rademacherProductDistribution (Fin n)) ∂enfloArcsineMeasure) := by
      rw [lintegral_const_mul _ (measurable_of_countable _), hswap]
    _ ≤ (ENNReal.ofReal (Real.pi / Real.sqrt 2)) ^ p *
        (C ^ p * ∑ j : Fin n,
          (∫⁻ ε, ‖D j f ε‖ₑ ^ p ∂rademacherProductDistribution (Fin n))) :=
      mul_le_mul' le_rfl hmoment
    _ = _ := by
      rw [enflo_type_constant_eq, ENNReal.mul_rpow_of_nonneg _ _ hp, mul_assoc]
end Submission
