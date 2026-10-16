import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import ChallengeDeps
namespace Submission.Helpers

theorem same_sign_of_abs_sub_lt (a b : ℝ) (h : |b - a| < |a|) : 0 < a * b := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h
    have hb : b < 0 := by have := (abs_lt.mp h).2; linarith
    exact mul_pos_of_neg_of_neg ha hb
  · subst a
    simp only [sub_zero, abs_zero] at h
    exact False.elim ((not_lt_of_ge (abs_nonneg b)) h)
  · rw [abs_of_pos ha] at h
    have hb : 0 < b := by have := (abs_lt.mp h).1; linarith
    exact mul_pos ha hb
theorem exists_root_of_eval_perturbation
    (p q : Polynomial ℝ) (a b : ℝ) (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b)
    (hea : |q.eval a - p.eval a| < |p.eval a|)
    (heb : |q.eval b - p.eval b| < |p.eval b|) :
    ∃ x ∈ Set.Ioo a b, q.eval x = 0 := by
  rw [abs_of_neg ha] at hea
  rw [abs_of_pos hb] at heb
  have hqa : q.eval a < 0 := by
    have h := (abs_lt.mp hea).2
    linarith
  have hqb : 0 < q.eval b := by
    have h := (abs_lt.mp heb).1
    linarith
  exact intermediate_value_Ioo hab.le q.continuousOn ⟨hqa, hqb⟩
theorem finite_rounding_error_bound {ι : Type*} (s : Finset ι) (c v : ι → ℝ) :
    |∑ i ∈ s, (c i - (round (c i) : ℤ)) * v i| ≤
      (1 / 2 : ℝ) * ∑ i ∈ s, |v i| := by
  calc
    _ ≤ ∑ i ∈ s, |(c i - (round (c i) : ℤ)) * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (1 / 2 : ℝ) * |v i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_sub_round (c i)) (abs_nonneg (v i))
    _ = _ := (Finset.mul_sum s (fun i => |v i|) (1 / 2 : ℝ)).symm
theorem rounded_integer_polynomial_eval_bound
    (s : Finset ℕ) (b : ℕ → Polynomial ℤ) (c : ℕ → ℝ) (r : Polynomial ℤ) :
    ∃ p : Polynomial ℤ,
      p = r + ∑ i ∈ s, Polynomial.C (round (c i)) * b i ∧
      ∀ x : ℝ,
        |((r.map (Int.castRingHom ℝ) +
          ∑ i ∈ s, Polynomial.C (c i) * (b i).map (Int.castRingHom ℝ)).eval x) -
          (p.map (Int.castRingHom ℝ)).eval x| ≤
        (1 / 2 : ℝ) * ∑ i ∈ s, |((b i).map (Int.castRingHom ℝ)).eval x| := by
  refine ⟨r + ∑ i ∈ s, Polynomial.C (round (c i)) * b i, rfl, ?_⟩
  intro x
  have heq :
      ((r.map (Int.castRingHom ℝ) +
        ∑ i ∈ s, Polynomial.C (c i) * (b i).map (Int.castRingHom ℝ)).eval x) -
        ((r + ∑ i ∈ s, Polynomial.C (round (c i)) * b i).map
          (Int.castRingHom ℝ)).eval x =
      ∑ i ∈ s, (c i - (round (c i) : ℤ)) *
        ((b i).map (Int.castRingHom ℝ)).eval x := by
    simp only [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Int.coe_castRingHom]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  exact finite_rounding_error_bound s c
    (fun i => ((b i).map (Int.castRingHom ℝ)).eval x)
theorem roots_between_alternating_eval
    (p : Polynomial ℝ) (n : ℕ) (hp : p ≠ 0) (hd : p.natDegree = n)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hs : ∀ i : Fin n, p.eval (x i.castSucc) * p.eval (x i.succ) < 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧
      (∀ i, x i.castSucc < y i ∧ y i < x i.succ ∧ p.eval (y i) = 0) ∧
      p.roots = (Finset.univ.image y).val := by
  classical
  have hroot : ∀ i : Fin n, ∃ z ∈ Set.Ioo (x i.castSucc) (x i.succ), p.eval z = 0 := by
    intro i
    have hab : x i.castSucc < x i.succ := hx (by exact Nat.lt_succ_self i.val)
    rcases mul_neg_iff.mp (hs i) with h | h
    · exact intermediate_value_Ioo' hab.le p.continuousOn ⟨h.2, h.1⟩
    · exact intermediate_value_Ioo hab.le p.continuousOn ⟨h.1, h.2⟩
  choose y hy using hroot
  have hmono : StrictMono y := by
    intro i j hij
    have hindex : i.succ ≤ j.castSucc := by exact Nat.succ_le_of_lt hij
    exact ((hy i).1.2.trans_le (hx.monotone hindex)).trans (hy j).1.1
  refine ⟨y, hmono, fun i => ⟨(hy i).1.1, (hy i).1.2, (hy i).2⟩, ?_⟩
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (hy i).2
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ,
      Fintype.card_fin, hd]
  · exact hp
theorem lambda_SSS_le_of_infinite :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (c : ℝ), 0 ≤ c →
      Set.Infinite { α : ℂ | IsIntegral ℤ α ∧
        AlgebraicIntegers.IsTotallyPositive α ∧
        AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α } →
      AlgebraicIntegers.lambda_SSS ≤ c := by
  intro c hc hinfinite
  unfold AlgebraicIntegers.lambda_SSS
  apply Real.sSup_le ?_ hc
  intro lam hlam
  apply le_of_not_gt
  intro hcl
  have hfinite := hlam (lam - c) (sub_pos.mpr hcl)
  exact hinfinite (by simpa only [Complex.ofReal_sub, sub_sub_cancel] using hfinite)
theorem trace_lt_mul_of_trace_le :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (α : ℂ) (a b : ℝ),
      AlgebraicIntegers.IsTotallyPositive α → a < b →
      AlgebraicIntegers.trace α ≤ (a : ℂ) * AlgebraicIntegers.degree α →
      AlgebraicIntegers.trace α < (b : ℂ) * AlgebraicIntegers.degree α := by
  let : PartialOrder ℂ := Complex.partialOrder
  intro α a b hα hab htrace
  have hdeg : 0 < (AlgebraicIntegers.degree α : ℝ) := by
    exact_mod_cast minpoly.natDegree_pos hα.1.isIntegral
  apply lt_of_le_of_lt htrace
  rw [Complex.lt_def]
  constructor
  · simpa using mul_lt_mul_of_pos_right hab hdeg
  · simp
theorem infinite_small_trace_of_injective :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (a b : ℝ) (f : ℕ → ℂ), a < b → Function.Injective f →
      (∀ n, IsIntegral ℤ (f n)) →
      (∀ n, AlgebraicIntegers.IsTotallyPositive (f n)) →
      (∀ n, AlgebraicIntegers.trace (f n) ≤
        (a : ℂ) * AlgebraicIntegers.degree (f n)) →
      Set.Infinite {α : ℂ | IsIntegral ℤ α ∧
        AlgebraicIntegers.IsTotallyPositive α ∧
        AlgebraicIntegers.trace α < (b : ℂ) * AlgebraicIntegers.degree α} := by
  let : PartialOrder ℂ := Complex.partialOrder
  intro a b f hab hinj hint hpos htrace
  apply Set.infinite_of_injective_forall_mem hinj
  intro n
  exact ⟨hint n, hpos n, trace_lt_mul_of_trace_le (f n) a b (hpos n) hab (htrace n)⟩
theorem exists_small_trace_infinite_family_of_sequence :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (f : ℕ → ℂ), Function.Injective f →
      (∀ n, IsIntegral ℤ (f n)) →
      (∀ n, AlgebraicIntegers.IsTotallyPositive (f n)) →
      (∀ n, AlgebraicIntegers.trace (f n) ≤
        (1.898305 : ℂ) * AlgebraicIntegers.degree (f n)) →
      ∃ (c : ℝ), 0 ≤ c ∧ c < (1.89831 : ℝ) ∧
        Set.Infinite {α : ℂ | IsIntegral ℤ α ∧
          AlgebraicIntegers.IsTotallyPositive α ∧
          AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α} := by
  let : PartialOrder ℂ := Complex.partialOrder
  intro f hinj hint hpos htrace
  refine ⟨1.8983075, by norm_num, by norm_num, ?_⟩
  apply infinite_small_trace_of_injective (1.898305 : ℝ) 1.8983075 f
    (by norm_num) hinj hint hpos
  simpa using htrace
theorem exists_small_trace_infinite_family_of_tendsto :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (L : ℝ) (f : ℕ → ℂ) (a : ℕ → ℝ), 0 ≤ L → L < 1.89831 →
      Function.Injective f →
      (∀ n, IsIntegral ℤ (f n)) →
      (∀ n, AlgebraicIntegers.IsTotallyPositive (f n)) →
      (∀ n, AlgebraicIntegers.trace (f n) ≤
        (a n : ℂ) * AlgebraicIntegers.degree (f n)) →
      Filter.Tendsto a Filter.atTop (nhds L) →
      ∃ (c : ℝ), 0 ≤ c ∧ c < (1.89831 : ℝ) ∧
        Set.Infinite {α : ℂ | IsIntegral ℤ α ∧
          AlgebraicIntegers.IsTotallyPositive α ∧
          AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α} := by
  let : PartialOrder ℂ := Complex.partialOrder
  intro L f a hL hbound hinj hint hpos htrace hlim
  let c : ℝ := (L + 1.89831) / 2
  have hLc : L < c := by dsimp [c]; linarith
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc : c < 1.89831 := by dsimp [c]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hlim).2 c hLc)
  refine ⟨c, hc0, hc, ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => f (n + N))
  · intro n m h
    exact Nat.add_right_cancel (hinj h)
  · intro n
    exact ⟨hint (n + N), hpos (n + N),
      trace_lt_mul_of_trace_le (f (n + N)) (a (n + N)) c (hpos (n + N))
        (hN (n + N) (Nat.le_add_left N n)) (htrace (n + N))⟩
theorem monic_int_lift_of_dvd_rat {p : Polynomial ℤ} (hp : p.Monic)
    {q : Polynomial ℚ} (hq : q.Monic) (hd : q ∣ p.map (algebraMap ℤ ℚ)) :
    ∃ r : Polynomial ℤ, r.Monic ∧ r.map (algebraMap ℤ ℚ) = q := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hp hd
  have heq : r.map (algebraMap ℤ ℚ) = q := by
    simpa only [hq.leadingCoeff, Polynomial.C_1, mul_one] using hr
  refine ⟨r, ?_, heq⟩
  exact (IsFractionRing.injective ℤ ℚ).monic_map_iff.mpr (heq.symm ▸ hq)
theorem squarefree_map_rat_of_monic {p : Polynomial ℤ} (hp : p.Monic)
    (hs : Squarefree p) : Squarefree (p.map (algebraMap ℤ ℚ)) := by
  classical
  intro q hqq
  have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero (hp.map (algebraMap ℤ ℚ)).ne_zero
    ((dvd_mul_right q q).trans hqq)
  have hnorm : normalize q * normalize q ∣ p.map (algebraMap ℤ ℚ) :=
    (mul_dvd_mul (normalize_associated q).dvd (normalize_associated q).dvd).trans hqq
  obtain ⟨r, hr, heq⟩ := monic_int_lift_of_dvd_rat hp
    (Polynomial.monic_normalize hq0) ((dvd_mul_right _ _).trans hnorm)
  have hrr : r * r ∣ p := hp.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) (hr.mul hr)
    (by simpa only [Polynomial.map_mul, heq] using hnorm)
  have hu : IsUnit (normalize q) := heq ▸ (hs r hrr).map (Polynomial.mapRingHom (algebraMap ℤ ℚ))
  exact (normalize_associated q).isUnit_iff.mp hu
theorem sum_aroots_eq_neg_nextCoeff {q : Polynomial ℚ} (hq : q.Monic) :
    (q.aroots ℂ).sum = -algebraMap ℚ ℂ q.nextCoeff := by
  have h := (IsAlgClosed.splits (q.map (algebraMap ℚ ℂ))).nextCoeff_eq_neg_sum_roots_of_monic
    (hq.map (algebraMap ℚ ℂ))
  rw [Polynomial.nextCoeff_map (algebraMap ℚ ℂ).injective] at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm
theorem irreducible_factor_root_data {p : Polynomial ℤ} (hp : p.Monic)
    {q : Polynomial ℚ} (hi : Irreducible q) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap ℤ ℚ)) :
    ∃ a : ℂ, IsIntegral ℤ a ∧ a ∈ p.aroots ℂ ∧ q = minpoly ℚ a := by
  have hdeg : 0 < q.natDegree := hq.natDegree_pos_of_not_isUnit hi.not_isUnit
  have hcard : 0 < (q.aroots ℂ).card := by
    rw [IsAlgClosed.card_aroots_eq_natDegree]
    exact hdeg
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hae : Polynomial.aeval a q = 0 := (Polynomial.mem_aroots.mp ha).2
  have hpa : a ∈ p.aroots ℂ := by
    rw [← Polynomial.aroots_map ℂ ℚ p]
    exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd ((hp.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).ne_zero
      (Polynomial.map_dvd (algebraMap ℚ ℂ) hd)) ha
  refine ⟨a, ⟨p, hp, (Polynomial.mem_aroots.mp hpa).2⟩, hpa,
    minpoly.eq_of_irreducible_of_monic hi hae hq⟩
theorem factor_total_positive {p : Polynomial ℤ} (hp : p.Monic)
    (hpos : letI : PartialOrder ℂ := Complex.partialOrder
      ∀ z : ℂ, z ∈ p.aroots ℂ → 0 < z)
    {q : Polynomial ℚ} (hi : Irreducible q) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap ℤ ℚ)) :
    ∃ a : ℂ, IsIntegral ℤ a ∧ AlgebraicIntegers.IsTotallyPositive a ∧
      q = minpoly ℚ a := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨a, ha, hpa, heq⟩ := irreducible_factor_root_data hp hi hq hd
  refine ⟨a, ha, ⟨ha.tower_top.isAlgebraic, ?_⟩, heq⟩
  intro b hb
  apply hpos b
  rw [← heq] at hb
  rw [← Polynomial.aroots_map ℂ ℚ p]
  exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd
    ((hp.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).ne_zero
    (Polynomial.map_dvd (algebraMap ℚ ℂ) hd)) hb
theorem factor_trace_real {q : Polynomial ℚ} (hq : q.Monic) {a : ℂ}
    (heq : q = minpoly ℚ a) :
    AlgebraicIntegers.trace a = ((-(q.nextCoeff : ℚ) : ℚ) : ℂ) := by
  rw [AlgebraicIntegers.trace, ← heq, sum_aroots_eq_neg_nextCoeff hq]
  simp
theorem finite_exception_weight_bound {ι : Type*} [DecidableEq ι]
    (F T : Finset ι) (d t : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hd : ∀ i, 0 ≤ d i) (ht : ∀ i ∈ F, 0 ≤ t i)
    (hlower : ∀ i ∈ F, i ∉ T → c * d i ≤ t i) :
    c * (∑ i ∈ F, d i) ≤ (∑ i ∈ F, t i) + c * (∑ i ∈ T, d i) := by
  have hpoint : ∀ i ∈ F, c * d i ≤ t i + if i ∈ T then c * d i else 0 := by
    intro i hi
    by_cases hm : i ∈ T
    · simp only [ite_eq_left hm]
      linarith [ht i hi]
    · simpa only [ite_eq_right hm, add_zero] using hlower i hi hm
  have hsum := Finset.sum_le_sum hpoint
  have hsub : (∑ i ∈ F, if i ∈ T then c * d i else 0) ≤ c * (∑ i ∈ T, d i) := by
    rw [← Finset.sum_filter]
    simpa only [Finset.mul_sum] using
      (Finset.sum_le_sum_of_subset_of_nonneg
        (show F.filter (fun i => i ∈ T) ⊆ T by simp only [Finset.subset_iff, Finset.mem_filter]; tauto)
        (fun i _ _ => mul_nonneg hc (hd i)))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith
theorem squarefree_rat_factor_sums {r : Polynomial ℚ} (hr : r.Monic)
    (hs : Squarefree r) :
    (∑ q ∈ (UniqueFactorizationMonoid.normalizedFactors r).toFinset, q.natDegree) = r.natDegree ∧
    (∑ q ∈ (UniqueFactorizationMonoid.normalizedFactors r).toFinset, q.nextCoeff) = r.nextCoeff := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors r
  have hn : M.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hr.ne_zero).mp hs
  have hprod : M.prod = r := by
    simpa only [hr.leadingCoeff, Polynomial.C_1, one_mul] using
      Polynomial.leadingCoeff_mul_prod_normalizedFactors r
  have hmonic : ∀ q ∈ M, q.Monic := fun q hq =>
    ((Polynomial.mem_normalizedFactors_iff hr.ne_zero).mp hq).2.1
  have hnd : (M.map Polynomial.natDegree).sum = r.natDegree := by
    rw [← Polynomial.natDegree_multiset_prod M
      (UniqueFactorizationMonoid.zero_notMem_normalizedFactors r), hprod]
  have hnc : (M.map Polynomial.nextCoeff).sum = r.nextCoeff := by
    have h := Polynomial.Monic.nextCoeff_multiset_prod M id hmonic
    simp only [Multiset.map_id', id_eq] at h
    rw [hprod] at h
    exact h.symm
  constructor
  · change (M.toFinset.val.map Polynomial.natDegree).sum = _
    rw [Multiset.toFinset_val, hn.dedup]
    exact hnd
  · change (M.toFinset.val.map Polynomial.nextCoeff).sum = _
    rw [Multiset.toFinset_val, hn.dedup]
    exact hnc
theorem factor_nextCoeff_nonneg {p : Polynomial ℤ} (hp : p.Monic)
    (hpos : letI : PartialOrder ℂ := Complex.partialOrder
      ∀ z : ℂ, z ∈ p.aroots ℂ → 0 < z)
    {q : Polynomial ℚ} (_hi : Irreducible q) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap ℤ ℚ)) : 0 ≤ -(q.nextCoeff : ℝ) := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  have hsum : 0 ≤ ((q.aroots ℂ).map Complex.re).sum := by
    apply Multiset.sum_nonneg
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
    have hwpos : 0 < w := hpos w (by
      rw [← Polynomial.aroots_map ℂ ℚ p]
      exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd
        ((hp.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).ne_zero
        (Polynomial.map_dvd (algebraMap ℚ ℂ) hd)) hw)
    exact (Complex.lt_def.mp hwpos).1.le
  have hreal := congrArg Complex.re (sum_aroots_eq_neg_nextCoeff hq)
  change (q.aroots ℂ).sum.re = -((q.nextCoeff : ℂ).re) at hreal
  have hre : (q.aroots ℂ).sum.re = ((q.aroots ℂ).map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom (q.aroots ℂ)
  rw [hre] at hreal
  rw [hreal] at hsum
  simpa only [Complex.ratCast_re] using hsum
theorem factor_trace_lt_of_real {q : Polynomial ℚ} (hq : q.Monic) {a : ℂ}
    (heq : q = minpoly ℚ a) {c : ℝ}
    (ht : -(q.nextCoeff : ℝ) < c * q.natDegree) :
    letI : PartialOrder ℂ := Complex.partialOrder
    AlgebraicIntegers.trace a < (c : ℂ) * AlgebraicIntegers.degree a := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  rw [factor_trace_real hq heq, AlgebraicIntegers.degree, ← heq]
  rw [Complex.lt_def]
  simpa only [Complex.ratCast_re, Complex.neg_re, Rat.cast_neg,
    Complex.mul_re, Complex.ofReal_re, Complex.natCast_re, Complex.ofReal_im,
    Complex.natCast_im, mul_zero, sub_zero, Complex.ratCast_im, Complex.neg_im,
    neg_zero, Complex.mul_im, zero_mul, add_zero, and_true] using ht
theorem finite_low_trace_polynomial_bound (c : ℝ) (hc : 0 ≤ c)
    (S : Set ℂ) (hS : S.Finite)
    (hcontain : letI : PartialOrder ℂ := Complex.partialOrder
      ∀ a : ℂ, IsIntegral ℤ a → AlgebraicIntegers.IsTotallyPositive a →
        AlgebraicIntegers.trace a < (c : ℂ) * AlgebraicIntegers.degree a → a ∈ S)
    {p : Polynomial ℤ} (hp : p.Monic) (hs : Squarefree p)
    (hpos : letI : PartialOrder ℂ := Complex.partialOrder
      ∀ z : ℂ, z ∈ p.aroots ℂ → 0 < z) :
    c * (p.natDegree : ℝ) ≤ -(p.nextCoeff : ℝ) +
      c * (∑ q ∈ hS.toFinset.image (minpoly ℚ), (q.natDegree : ℝ)) := by
  classical
  let _ : PartialOrder ℂ := Complex.partialOrder
  let r := p.map (algebraMap ℤ ℚ)
  let F := (UniqueFactorizationMonoid.normalizedFactors r).toFinset
  let T := hS.toFinset.image (minpoly ℚ)
  have hr : r.Monic := hp.map _
  have hrs : Squarefree r := squarefree_map_rat_of_monic hp hs
  have hdata : ∀ q ∈ F, Irreducible q ∧ q.Monic ∧ q ∣ r := by
    intro q hq
    exact (Polynomial.mem_normalizedFactors_iff hr.ne_zero).mp
      (Multiset.mem_toFinset.mp hq)
  have ht : ∀ q ∈ F, 0 ≤ -(q.nextCoeff : ℝ) := by
    intro q hq
    exact factor_nextCoeff_nonneg hp hpos (hdata q hq).1
      (hdata q hq).2.1 (hdata q hq).2.2
  have hlower : ∀ q ∈ F, q ∉ T → c * (q.natDegree : ℝ) ≤ -(q.nextCoeff : ℝ) := by
    intro q hq hqT
    by_contra hbad
    have hlt : -(q.nextCoeff : ℝ) < c * (q.natDegree : ℝ) := lt_of_not_ge hbad
    obtain ⟨a, ha, hpa, heq⟩ := factor_total_positive hp hpos
      (hdata q hq).1 (hdata q hq).2.1 (hdata q hq).2.2
    have hamem : a ∈ S := hcontain a ha hpa
      (factor_trace_lt_of_real (hdata q hq).2.1 heq hlt)
    exact hqT (Finset.mem_image.mpr ⟨a, hS.mem_toFinset.mpr hamem, heq.symm⟩)
  have hb := finite_exception_weight_bound F T
    (fun q => (q.natDegree : ℝ)) (fun q => -(q.nextCoeff : ℝ)) c hc
    (fun _ => Nat.cast_nonneg _) ht hlower
  obtain ⟨hdeg, hnext⟩ := squarefree_rat_factor_sums hr hrs
  have hdegreal : (∑ q ∈ F, (q.natDegree : ℝ)) = (r.natDegree : ℝ) := by
    exact_mod_cast hdeg
  have hnextreal : (∑ q ∈ F, -(q.nextCoeff : ℝ)) = -(r.nextCoeff : ℝ) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    exact_mod_cast hnext
  rw [hdegreal, hnextreal] at hb
  have hmapdeg : r.natDegree = p.natDegree := hp.natDegree_map _
  have hmapnext : r.nextCoeff = (p.nextCoeff : ℚ) :=
    Polynomial.nextCoeff_map (IsFractionRing.injective ℤ ℚ) p
  simpa only [hmapdeg, hmapnext, Rat.cast_intCast] using hb
theorem infinite_of_squarefree_polynomials :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (c0 c : ℝ), 0 ≤ c0 → c0 < c →
      (∀ (N : ℕ), ∃ (p : Polynomial ℤ), p.Monic ∧ Squarefree p ∧
        N < p.natDegree ∧ (∀ (z : ℂ), z ∈ p.aroots ℂ → 0 < z) ∧
        -((p.coeff (p.natDegree - 1) : ℤ) : ℝ) < c0 * (p.natDegree : ℝ)) →
      Set.Infinite { α : ℂ | IsIntegral ℤ α ∧
        AlgebraicIntegers.IsTotallyPositive α ∧
        AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α } := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  classical
  intro c0 c hc0 hcc hpolys
  by_contra hnot
  have hf := Set.not_infinite.mp hnot
  let S := { α : ℂ | IsIntegral ℤ α ∧ AlgebraicIntegers.IsTotallyPositive α ∧
    AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α }
  have hS : S.Finite := hf
  let B : ℝ := ∑ q ∈ hS.toFinset.image (minpoly ℚ), (q.natDegree : ℝ)
  have hc : 0 ≤ c := le_trans hc0 hcc.le
  have hgap : 0 < c - c0 := sub_pos.mpr hcc
  obtain ⟨N, hN⟩ := exists_nat_gt (c * B / (c - c0))
  obtain ⟨p, hp, hs, hdegree, hpos, htrace⟩ := hpolys N
  have hpd : 0 < p.natDegree := lt_of_le_of_lt (Nat.zero_le N) hdegree
  have hbound : c * (p.natDegree : ℝ) ≤ -(p.nextCoeff : ℝ) + c * B :=
    finite_low_trace_polynomial_bound c hc S hS
      (fun a ha hpa hta => ⟨ha, hpa, hta⟩) hp hs hpos
  have ht : -(p.nextCoeff : ℝ) < c0 * (p.natDegree : ℝ) := by
    simpa only [Polynomial.nextCoeff_of_natDegree_pos hpd] using htrace
  have hlarge : c * B < (c - c0) * (p.natDegree : ℝ) := by
    have hN' : c * B / (c - c0) < (p.natDegree : ℝ) :=
      lt_trans hN (Nat.cast_lt.mpr hdegree)
    simpa only [mul_comm] using (div_lt_iff₀ hgap).mp hN'
  nlinarith
theorem exists_small_trace_infinite_family_of_squarefree_polynomials :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (c0 : ℝ), 0 ≤ c0 → c0 < (1.89831 : ℝ) →
      (∀ (N : ℕ), ∃ (p : Polynomial ℤ), p.Monic ∧ Squarefree p ∧
        N < p.natDegree ∧ (∀ (z : ℂ), z ∈ p.aroots ℂ → 0 < z) ∧
        -((p.coeff (p.natDegree - 1) : ℤ) : ℝ) < c0 * (p.natDegree : ℝ)) →
      ∃ (c : ℝ), 0 ≤ c ∧ c < (1.89831 : ℝ) ∧
        Set.Infinite { α : ℂ | IsIntegral ℤ α ∧
          AlgebraicIntegers.IsTotallyPositive α ∧
          AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α } := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  intro c0 hc0 hbound hpolys
  refine ⟨(c0 + 1.89831) / 2, by linarith, by linarith, ?_⟩
  exact infinite_of_squarefree_polynomials c0 ((c0 + 1.89831) / 2) hc0
    (by linarith) hpolys
theorem rounded_monic_basis_coeff_bound
    (n : ℕ) (b : ℕ → Polynomial ℤ) (c : ℕ → ℝ) (hn : 0 < n)
    (hb : ∀ k, k ≤ n → (b k).Monic ∧ (b k).natDegree = k) :
    let h : Polynomial ℝ := (b n).map (Int.castRingHom ℝ) +
      ∑ k ∈ Finset.range n, Polynomial.C (c k) * (b k).map (Int.castRingHom ℝ)
    let p : Polynomial ℤ := b n +
      ∑ k ∈ Finset.range n, Polynomial.C (round (c k)) * b k
    p.Monic ∧ p.natDegree = n ∧
      |((p.coeff (n - 1) : ℤ) : ℝ) - h.coeff (n - 1)| ≤ (1 / 2 : ℝ) := by
  classical
  dsimp only
  let p : Polynomial ℤ := b n +
    ∑ k ∈ Finset.range n, Polynomial.C (round (c k)) * b k
  have hbn : (b n).coeff n = 1 := by
    simpa only [(hb n le_rfl).2] using (hb n le_rfl).1.coeff_natDegree
  have htop : p.coeff n = 1 := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
    have hzero : (∑ k ∈ Finset.range n,
        (Polynomial.C (round (c k)) * b k).coeff n) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [(hb k (Finset.mem_range.mp hk).le).2]
      exact Finset.mem_range.mp hk
    rw [hzero, add_zero, hbn]
  have hdeg : p.natDegree ≤ n := by
    apply le_trans (Polynomial.natDegree_add_le _ _)
    apply max_le
    · exact (hb n le_rfl).2.le
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((hb k (Finset.mem_range.mp hk).le).2.le.trans (Finset.mem_range.mp hk).le)
  have hprev : n - 1 < n := by omega
  have hbprev : (b (n - 1)).coeff (n - 1) = 1 := by
    simpa only [(hb (n - 1) hprev.le).2] using
      (hb (n - 1) hprev.le).1.coeff_natDegree
  have hzero : ∀ k ∈ Finset.range n, k ≠ n - 1 → (b k).coeff (n - 1) = 0 := by
    intro k hk hne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [(hb k (Finset.mem_range.mp hk).le).2]
    have := Finset.mem_range.mp hk
    omega
  have hpnext : p.coeff (n - 1) = (b n).coeff (n - 1) + round (c (n - 1)) := by
    dsimp only [p]
    rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single (n - 1)]
    · rw [Polynomial.coeff_C_mul, hbprev, mul_one]
    · intro k hk hne
      rw [Polynomial.coeff_C_mul, hzero k hk hne, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hprev))
  have hhnext : ((b n).map (Int.castRingHom ℝ) +
        ∑ k ∈ Finset.range n, Polynomial.C (c k) * (b k).map (Int.castRingHom ℝ)).coeff
        (n - 1) = ((b n).coeff (n - 1) : ℝ) + c (n - 1) := by
    rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single (n - 1)]
    · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
        Int.coe_castRingHom, hbprev, Int.cast_one, mul_one]
    · intro k hk hne
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
        Int.coe_castRingHom, hzero k hk hne, Int.cast_zero, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hprev))
  refine ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg htop,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [htop]; exact one_ne_zero), ?_⟩
  change |((p.coeff (n - 1) : ℤ) : ℝ) - _| ≤ _
  rw [hpnext, hhnext, Int.cast_add, add_sub_add_left_eq_sub, abs_sub_comm]
  exact abs_sub_round (c (n - 1))
theorem squarefree_positive_of_alternating_eval :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (n : ℕ) (p : Polynomial ℤ) (x : Fin (n + 1) → ℝ),
      p.Monic → p.natDegree = n → StrictMono x → (∀ j, 0 < x j) →
      (∀ i : Fin n,
        (p.map (Int.castRingHom ℝ)).eval (x i.castSucc) *
          (p.map (Int.castRingHom ℝ)).eval (x i.succ) < 0) →
      Squarefree p ∧ ∀ z ∈ p.aroots ℂ, 0 < z := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  classical
  intro n p x hp hd hx hxpos hs
  let q := p.map (Int.castRingHom ℝ)
  have hq : q.Monic := hp.map _
  have hqd : q.natDegree = n := (hp.natDegree_map _).trans hd
  obtain ⟨y, hy, hxy, hroots⟩ := roots_between_alternating_eval q n hq.ne_zero hqd x hx hs
  have hcard : q.roots.card = q.natDegree := by
    rw [hroots, Finset.card_val, Finset.card_image_of_injective _ hy.injective,
      Finset.card_univ, Fintype.card_fin, hqd]
  have hsplit : q.Splits := Polynomial.splits_iff_card_roots.mpr hcard
  have hsq : Squarefree q := ((Polynomial.nodup_roots_iff_of_splits hq.ne_zero hsplit).mp
    (by rw [hroots]; exact Finset.nodup _)).squarefree
  constructor
  · intro r hrr
    apply Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map (Int.castRingHom ℝ)
      (hp.isUnit_leadingCoeff_of_dvd ((dvd_mul_right r r).trans hrr))
    apply hsq (r.map (Int.castRingHom ℝ))
    simpa only [Polynomial.map_mul] using Polynomial.map_dvd (Int.castRingHom ℝ) hrr
  · intro z hz
    have hmapeq : q.map (algebraMap ℝ ℂ) = p.map (algebraMap ℤ ℂ) := by
      ext k
      simp [q]
    change z ∈ (p.map (algebraMap ℤ ℂ)).roots at hz
    rw [← hmapeq, hsplit.roots_map, hroots] at hz
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hr)
    rw [Complex.lt_def]
    simpa using (hxpos i.castSucc).trans (hxy i).1
theorem exists_positive_squarefree_of_rounding_certificate :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (n : ℕ) (b : ℕ → Polynomial ℤ) (c : ℕ → ℝ) (x : Fin (n + 1) → ℝ),
      0 < n →
      (∀ k, k ≤ n → (b k).Monic ∧ (b k).natDegree = k) →
      StrictMono x → (∀ j, 0 < x j) →
      let h : Polynomial ℝ := (b n).map (Int.castRingHom ℝ) +
        ∑ k ∈ Finset.range n, Polynomial.C (c k) * (b k).map (Int.castRingHom ℝ)
      (∀ i : Fin n, h.eval (x i.castSucc) * h.eval (x i.succ) < 0) →
      (∀ j : Fin (n + 1), (1 / 2 : ℝ) *
        (∑ k ∈ Finset.range n, |((b k).map (Int.castRingHom ℝ)).eval (x j)|) <
          |h.eval (x j)|) →
      ∃ p : Polynomial ℤ, p.Monic ∧ p.natDegree = n ∧ Squarefree p ∧
        (∀ z ∈ p.aroots ℂ, 0 < z) ∧
        |((p.coeff (n - 1) : ℤ) : ℝ) - h.coeff (n - 1)| ≤ (1 / 2 : ℝ) := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  classical
  intro n b c x hn hb hx hxpos h hs hwidth
  obtain ⟨p, hpeq, heval⟩ := rounded_integer_polynomial_eval_bound
    (Finset.range n) b c (b n)
  have hpdata := rounded_monic_basis_coeff_bound n b c hn hb
  dsimp only at hpdata
  rw [← hpeq] at hpdata
  obtain ⟨hp, hpd, hpcoeff⟩ := hpdata
  have herr : ∀ j : Fin (n + 1),
      |(p.map (Int.castRingHom ℝ)).eval (x j) - h.eval (x j)| < |h.eval (x j)| := by
    intro j
    rw [abs_sub_comm]
    exact (heval (x j)).trans_lt (hwidth j)
  have hsign : ∀ j : Fin (n + 1),
      0 < h.eval (x j) * (p.map (Int.castRingHom ℝ)).eval (x j) := by
    intro j
    exact same_sign_of_abs_sub_lt _ _ (herr j)
  have halt : ∀ i : Fin n,
      (p.map (Int.castRingHom ℝ)).eval (x i.castSucc) *
        (p.map (Int.castRingHom ℝ)).eval (x i.succ) < 0 := by
    intro i
    have hmul := mul_pos (hsign i.castSucc) (hsign i.succ)
    have hreorder :
        (h.eval (x i.castSucc) * (p.map (Int.castRingHom ℝ)).eval (x i.castSucc)) *
          (h.eval (x i.succ) * (p.map (Int.castRingHom ℝ)).eval (x i.succ)) =
        (h.eval (x i.castSucc) * h.eval (x i.succ)) *
          ((p.map (Int.castRingHom ℝ)).eval (x i.castSucc) *
            (p.map (Int.castRingHom ℝ)).eval (x i.succ)) := by ring
    rw [hreorder] at hmul
    exact neg_of_mul_pos_right hmul (hs i).le
  obtain ⟨hsq, hpos⟩ := squarefree_positive_of_alternating_eval n p x hp hpd hx hxpos halt
  exact ⟨p, hp, hpd, hsq, hpos, hpcoeff⟩
noncomputable def scaledChebyshev (d c : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C (d^n) * (Polynomial.Chebyshev.C ℝ (n : ℤ)).comp
    (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c))
theorem scaledChebyshev_zero (d c : ℝ) : scaledChebyshev d c 0 = 2 := by
  simp [scaledChebyshev]
theorem scaledChebyshev_one (d c : ℝ) (hd : d ≠ 0) :
    scaledChebyshev d c 1 = Polynomial.X - Polynomial.C c := by
  simp [scaledChebyshev, ← mul_assoc, ← Polynomial.C_mul, hd]
theorem scaledChebyshev_add_two (d c : ℝ) (hd : d ≠ 0) (n : ℕ) :
    scaledChebyshev d c (n+2) =
      (Polynomial.X - Polynomial.C c) * scaledChebyshev d c (n+1) -
        Polynomial.C (d^2) * scaledChebyshev d c n := by
  simp only [scaledChebyshev, Nat.cast_add, Nat.cast_ofNat,
    Polynomial.Chebyshev.C_add_two, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.X_comp]
  have hpow : Polynomial.C (d^(n+2)) * Polynomial.C d⁻¹ =
      Polynomial.C (d^(n+1)) := by
    rw [← Polynomial.C_mul]
    congr 1
    simp [pow_succ, mul_assoc, hd]
  have hpow' : Polynomial.C (d^(n+2)) =
      Polynomial.C (d^2) * Polynomial.C (d^n) := by
    rw [← Polynomial.C_mul, pow_add, mul_comm]
  linear_combination (norm := ring_nf)
    hpow * (Polynomial.X - Polynomial.C c) *
      (Polynomial.Chebyshev.C ℝ ((n : ℤ)+1)).comp
        (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c)) -
    hpow' * (Polynomial.Chebyshev.C ℝ (n : ℤ)).comp
      (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c))
theorem scaledChebyshev_data (d c : ℝ) (hd : d ≠ 0) (n : ℕ) :
    (scaledChebyshev d c n).natDegree = n ∧
      (0 < n → (scaledChebyshev d c n).Monic ∧
        (scaledChebyshev d c n).coeff (n-1) = -(n : ℝ)*c) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [scaledChebyshev_zero]
  | one =>
    rw [scaledChebyshev_one d c hd]
    simp [Polynomial.monic_X_sub_C]
  | more n ih0 ih1 =>
    have hp := (ih1.2 (Nat.succ_pos n)).1
    have hq := (Polynomial.monic_X_sub_C c).mul hp
    have hdeg : ((Polynomial.X - Polynomial.C c) *
        scaledChebyshev d c (n+1)).natDegree = n+2 := by
      rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C c).ne_zero hp.ne_zero,
        Polynomial.natDegree_X_sub_C, ih1.1]
      omega
    have hsmall : (Polynomial.C (d^2) * scaledChebyshev d c n).natDegree < n+1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans_lt (by rw [ih0.1]; omega)
    have hlt : (Polynomial.C (d^2) * scaledChebyshev d c n).natDegree <
        ((Polynomial.X - Polynomial.C c) * scaledChebyshev d c (n+1)).natDegree := by
      rw [hdeg]; omega
    rw [scaledChebyshev_add_two d c hd n]
    refine ⟨(Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt).trans hdeg, ?_⟩
    intro _
    refine ⟨hq.sub_of_left (Polynomial.degree_lt_degree hlt), ?_⟩
    rw [show n+2-1=n+1 by omega, Polynomial.coeff_sub,
      Polynomial.coeff_eq_zero_of_natDegree_lt hsmall, sub_zero,
      mul_comm (Polynomial.X - Polynomial.C c), Polynomial.coeff_mul_X_sub_C,
      show n+1-1=n by omega] at *
    rw [(ih1.2 (Nat.succ_pos n)).2]
    have htop : (scaledChebyshev d c (n+1)).coeff (n+1) = 1 := by
      simpa only [ih1.1] using hp.coeff_natDegree
    rw [htop]
    push_cast
    ring
theorem weightedChebyshev_data (d c a : ℝ) (n m : ℕ)
    (hd : d ≠ 0) (hm : m < n) :
    let H := ∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*a^j) * scaledChebyshev d c (n-j)
    H.Monic ∧ H.natDegree = n ∧ H.coeff (n-1) = -(n : ℝ)*c + (m : ℝ)*a := by
  classical
  intro H
  have hn : 0 < n := by omega
  have hdegree : H.natDegree ≤ n := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((scaledChebyshev_data d c hd (n-j)).1.le.trans (Nat.sub_le _ _))
  have htop : H.coeff n = 1 := by
    change (∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*a^j) * scaledChebyshev d c (n-j)).coeff n = 1
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simpa only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
        Polynomial.C_1, one_mul, Nat.sub_zero, (scaledChebyshev_data d c hd n).1]
        using ((scaledChebyshev_data d c hd n).2 hn).1.coeff_natDegree
    · intro j hj hj0
      rw [Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [(scaledChebyshev_data d c hd (n-j)).1]; omega), mul_zero]
    · simp
  have hmonic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdegree htop
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegree
    (by rw [htop]; exact one_ne_zero)
  refine ⟨hmonic, hdeg, ?_⟩
  change (∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*a^j) * scaledChebyshev d c (n-j)).coeff (n-1) = _
  rw [Polynomial.finsetSum_coeff,
    ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega) : 0 ∈ Finset.range (m+1))]
  have hz : (Polynomial.C ((Nat.choose m 0 : ℝ)*a^0) *
      scaledChebyshev d c (n-0)).coeff (n-1) = -(n : ℝ)*c := by
    simpa using ((scaledChebyshev_data d c hd n).2 hn).2
  rw [hz]
  congr 1
  rw [Finset.sum_eq_single 1]
  · by_cases hm0 : m = 0
    · subst m
      simp
    · have hn1 : 0 < n-1 := by omega
      have h := ((scaledChebyshev_data d c hd (n-1)).2 hn1).1.coeff_natDegree
      rw [(scaledChebyshev_data d c hd (n-1)).1] at h
      rw [Polynomial.coeff_C_mul, h]
      simp
  · intro j hj hj1
    have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
    have hjm : j < m+1 := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [(scaledChebyshev_data d c hd (n-j)).1]; omega), mul_zero]
  · intro hnot
    have hm0 : m = 0 := by
      by_contra h
      apply hnot
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    subst m
    simp
theorem explicit_weighted_chebyshev_algebraic :
    ∀ (u v : ℝ) (k : ℕ), 0 < u → u < v → 0 < k →
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let c := s^2+r^2
    let R : ℕ → Polynomial ℝ := fun j =>
      Polynomial.C (d^j) * (Polynomial.Chebyshev.C ℝ (j : ℤ)).comp
        (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c))
    let H := ∑ j ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j) * R (14*k-j)
    H.Monic ∧ H.natDegree = 14*k ∧
      H.coeff (14*k-1) = -(14*k : ℝ)*c + (6*k : ℝ)*r^2 := by
  intro u v k hu huv hk s r d c R H
  have hs : 0 < s := by dsimp [s]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  simpa only [H, R, scaledChebyshev, Nat.cast_mul, Nat.cast_ofNat] using weightedChebyshev_data d c (r^2) (14*k) (6*k)
    (ne_of_gt (mul_pos hs hr)) (by omega)
theorem chebyshev_C_eval_add_inv (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    (Polynomial.Chebyshev.C ℂ (n : ℤ)).eval (w+w⁻¹) =
      w^n + (w⁻¹)^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n ih0 ih1 =>
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Polynomial.Chebyshev.C_add_two,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at *
    rw [ih1, ih0]
    simp only [pow_succ]
    field_simp
    ring
theorem scaledChebyshev_eval_laurent (d c : ℝ) (hd : d ≠ 0)
    (w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    ((scaledChebyshev d c n).map (algebraMap ℝ ℂ)).eval
      ((c : ℂ) + (d : ℂ)*(w+w⁻¹)) =
      (d : ℂ)^n*(w^n+(w⁻¹)^n) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hx : (d : ℂ)⁻¹ * ((c : ℂ) + (d : ℂ)*(w+w⁻¹) - (c : ℂ)) = w+w⁻¹ := by
    field_simp
    ring
  simp only [scaledChebyshev, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.Chebyshev.map_C, Polynomial.map_pow, map_pow, map_inv₀,
    Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]
  change (d : ℂ)^n * (Polynomial.Chebyshev.C ℂ (n : ℤ)).eval
    ((d : ℂ)⁻¹ * ((c : ℂ)+(d : ℂ)*(w+w⁻¹)-(c : ℂ))) = _
  rw [hx, chebyshev_C_eval_add_inv w hw n]
theorem binomial_weighted_sum (d a z : ℂ) (n m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ Finset.range (m+1), (Nat.choose m j : ℂ)*a^j*d^(n-j)*z^(n-j)) =
      (d*z)^(n-m)*(a+d*z)^m := by
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : n-j = (n-m)+(m-j) := by omega
  rw [hpow, pow_add, pow_add, mul_pow, mul_pow]
  ring
theorem weightedChebyshev_eval_laurent (d c a : ℝ) (hd : d ≠ 0)
    (n m : ℕ) (hm : m ≤ n) (w : ℂ) (hw : w ≠ 0) :
    let H := ∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*a^j) * scaledChebyshev d c (n-j)
    (H.map (algebraMap ℝ ℂ)).eval ((c : ℂ)+(d : ℂ)*(w+w⁻¹)) =
      ((d : ℂ)*w)^(n-m)*((a : ℂ)+(d : ℂ)*w)^m +
      ((d : ℂ)*w⁻¹)^(n-m)*((a : ℂ)+(d : ℂ)*w⁻¹)^m := by
  intro H
  dsimp only [H]
  simp only [Polynomial.map_sum, Polynomial.eval_finsetSum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
    scaledChebyshev_eval_laurent d c hd w hw]
  change (∑ j ∈ Finset.range (m+1),
    (((Nat.choose m j : ℝ)*a^j : ℝ) : ℂ) *
      ((d : ℂ)^(n-j)*(w^(n-j)+(w⁻¹)^(n-j)))) = _
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  have hterm (z : ℂ) :
      (∑ j ∈ Finset.range (m+1),
        ((Nat.choose m j : ℂ)*(a : ℂ)^j)*((d : ℂ)^(n-j)*z^(n-j))) =
        ((d : ℂ)*z)^(n-m)*((a : ℂ)+(d : ℂ)*z)^m := by
    simpa only [mul_assoc] using binomial_weighted_sum (d : ℂ) (a : ℂ) z n m hm
  rw [hterm w, hterm w⁻¹]
theorem continuous_ordered_preimages (n : ℕ) (F : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hF : ContinuousOn F (Set.Icc a b))
    (t : Fin (n+2) → ℝ) (ht : StrictMono t)
    (ha : F a = t 0) (hb : F b = t (Fin.last (n+1))) :
    ∃ y : Fin (n+2) → ℝ, StrictMono y ∧ y 0 = a ∧
      y (Fin.last (n+1)) = b ∧
      (∀ j, y j ∈ Set.Icc a b ∧ F (y j) = t j) := by
  induction n generalizing a b with
  | zero =>
    refine ⟨Fin.cons a (fun _ : Fin 1 => b), ?_, rfl, ?_, ?_⟩
    · rw [Fin.strictMono_cons]
      exact ⟨fun _ => hab, fun i j hij => False.elim (by omega)⟩
    · simp
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ⟨⟨le_refl _, hab.le⟩, ha⟩
      · have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact ⟨⟨hab.le, le_refl _⟩, hb⟩
  | succ n ih =>
    have h1 : F a < t (Fin.succ 0) := by rw [ha]; exact ht (by simp)
    have h2 : t (Fin.succ 0) < F b := by
      rw [hb]
      apply ht
      change (0 : ℕ)+1 < n+1+1
      omega
    obtain ⟨c, hc, hFc⟩ := intermediate_value_Ioo hab.le hF ⟨h1, h2⟩
    have hcont : ContinuousOn F (Set.Icc c b) :=
      hF.mono (fun x hx => ⟨hc.1.le.trans hx.1, hx.2⟩)
    obtain ⟨y, hy, hy0, hyb, hyval⟩ := ih c b hc.2 hcont
      (fun j => t j.succ) (fun i j hij => ht (by simpa using hij)) hFc hb
    refine ⟨Fin.cons a y, ?_, rfl, ?_, ?_⟩
    · rw [Fin.strictMono_cons]
      exact ⟨fun j => hc.1.trans_le (hy0 ▸ hy.monotone (Fin.zero_le j)), hy⟩
    · simpa using hyb
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ⟨⟨le_refl _, hab.le⟩, ha⟩
      · exact ⟨⟨hc.1.le.trans (hyval i).1.1, (hyval i).1.2⟩, (hyval i).2⟩
theorem complex_polar_product (d θ : ℝ) (z : ℂ) (l m : ℕ) :
    ((d : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^l*z^m =
      ((d^l*‖z‖^m : ℝ) : ℂ) * Complex.exp
        ((((l : ℝ)*θ+(m : ℝ)*z.arg : ℝ) : ℂ)*Complex.I) := by
  have hpow : z^m = (‖z‖ : ℂ)^m * (Complex.exp ((z.arg : ℂ)*Complex.I))^m := by
    rw [← mul_pow, Complex.norm_mul_exp_arg_mul_I]
  rw [hpow, mul_pow]
  calc
    _ = (d : ℂ)^l*(‖z‖ : ℂ)^m *
        ((Complex.exp ((θ : ℂ)*Complex.I))^l *
          (Complex.exp ((z.arg : ℂ)*Complex.I))^m) := by ring
    _ = _ := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      push_cast
      congr 2
      ring
theorem circle_exp_inv (θ : ℝ) :
    (Complex.exp ((θ : ℂ)*Complex.I))⁻¹ = Complex.exp (((-θ : ℝ) : ℂ)*Complex.I) := by
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring
theorem circle_exp_conj (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((θ : ℂ)*Complex.I)) =
      (Complex.exp ((θ : ℂ)*Complex.I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp
theorem weightedChebyshev_eval_phase (d c a θ : ℝ) (hd : d ≠ 0)
    (n m : ℕ) (hm : m ≤ n) :
    let H := ∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*a^j) * scaledChebyshev d c (n-j)
    let z := (a : ℂ)+(d : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)
    H.eval (c+2*d*Real.cos θ) =
      2*d^(n-m)*‖z‖^m *
        Real.cos ((n-m : ℕ)*θ+(m : ℝ)*z.arg) := by
  intro H z
  let w := Complex.exp ((θ : ℂ)*Complex.I)
  have hconj : (starRingEnd ℂ) w = w⁻¹ := circle_exp_conj θ
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hsum : w+w⁻¹ = ((2*Real.cos θ : ℝ) : ℂ) := by
    rw [← hconj]
    apply Complex.ext
    · change w.re+w.re = 2*Real.cos θ
      rw [show w.re = Real.cos θ from Complex.exp_ofReal_mul_I_re θ]
      ring
    · simp
  have harg : ((c+2*d*Real.cos θ : ℝ) : ℂ) =
      (c : ℂ)+(d : ℂ)*(w+w⁻¹) := by rw [hsum]; push_cast; ring
  have hl := weightedChebyshev_eval_laurent d c a hd n m hm w hw
  dsimp only at hl
  change (H.map (algebraMap ℝ ℂ)).eval _ = _ at hl
  rw [← harg] at hl
  have hev : (H.map (algebraMap ℝ ℂ)).eval ((c+2*d*Real.cos θ : ℝ) : ℂ) =
      ((H.eval (c+2*d*Real.cos θ) : ℝ) : ℂ) :=
    Polynomial.eval_map_apply (algebraMap ℝ ℂ) _
  rw [hev] at hl
  let P := ((d : ℂ)*w)^(n-m)*z^m
  have hpconj : ((d : ℂ)*w⁻¹)^(n-m)*((a : ℂ)+(d : ℂ)*w⁻¹)^m =
      (starRingEnd ℂ) P := by
    simp only [P, z, w, map_mul, map_pow, map_add, Complex.conj_ofReal,
      circle_exp_conj]
  change _ = P + _ at hl
  rw [hpconj] at hl
  have hre := congrArg Complex.re hl
  simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at hre
  have hp := complex_polar_product d θ z (n-m) m
  change P = _ at hp
  have hpr := congrArg Complex.re hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_ofReal_mul_I_re] at hpr
  rw [hpr] at hre
  linarith
theorem weighted_circle_norm_sq (s r θ : ℝ) :
    ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)‖^2 =
      r^2*(s^2+r^2+2*s*r*Real.cos θ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, zero_add, add_zero, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  linear_combination (norm := ring_nf) (s*r)^2*(Real.cos_sq_add_sin_sq θ)
theorem weighted_circle_pos (s r θ : ℝ) (hr : 0 < r) (hrs : r < s) :
    0 < s^2+r^2+2*s*r*Real.cos θ := by
  have hsr : 0 < s*r := mul_pos (hr.trans hrs) hr
  have hcos := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hsr.le
  have hgap := sq_pos_of_pos (sub_pos.mpr hrs)
  nlinarith
theorem weighted_circle_ne_zero (s r θ : ℝ) (hr : 0 < r) (hrs : r < s) :
    ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) ≠ 0 := by
  have hp := weighted_circle_pos s r θ hr hrs
  have hn := weighted_circle_norm_sq s r θ
  intro hz
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
  have := mul_pos (sq_pos_of_pos hr) hp
  linarith
theorem weighted_phase_continuous (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (l m : ℕ) :
    ContinuousOn (fun θ : ℝ => (l : ℝ)*θ + (m : ℝ)*
      (((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)).arg)
      (Set.Icc 0 Real.pi) := by
  let z : ℝ → ℂ := fun θ =>
    ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)
  have hzcont : Continuous z := by dsimp [z]; fun_prop
  have harg : ∀ θ ∈ Set.Icc 0 Real.pi,
      (z θ).arg = Real.arccos ((z θ).re/‖z θ‖) := by
    intro θ hθ
    apply Complex.arg_of_im_nonneg_of_ne_zero
    · dsimp [z]
      simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add, Complex.exp_ofReal_mul_I_im]
      exact mul_nonneg (mul_pos (hr.trans hrs) hr).le (Real.sin_nonneg_of_mem_Icc hθ)
    · exact weighted_circle_ne_zero s r θ hr hrs
  have hcont : ContinuousOn (fun θ => Real.arccos ((z θ).re/‖z θ‖))
      (Set.Icc 0 Real.pi) := by
    exact Real.continuous_arccos.comp_continuousOn
      ((Complex.continuous_re.comp hzcont).continuousOn.div hzcont.norm.continuousOn
        (fun θ _ => norm_ne_zero_iff.mpr (weighted_circle_ne_zero s r θ hr hrs)))
  apply ((continuous_const.mul continuous_id).continuousOn.add
    (continuousOn_const.mul hcont)).congr
  intro θ hθ
  exact congrArg (fun t : ℝ => (l : ℝ)*θ+(m : ℝ)*t) (harg θ hθ)
theorem weightedChebyshev_amplitude (s r θ : ℝ) (hs : s ≠ 0) (k : ℕ) :
    (s*r)^(8*k) *
      ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)‖^(6*k) =
      ((s*r)^14/s^6)^k*(s^2+r^2+2*s*r*Real.cos θ)^(3*k) := by
  let z := ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)
  let x := s^2+r^2+2*s*r*Real.cos θ
  have hnorm : ‖z‖^2 = r^2*x := weighted_circle_norm_sq s r θ
  calc
    _ = ((s*r)^8 * (‖z‖^2)^3)^k := by
      simp only [mul_pow, ← pow_mul]
      congr 1
    _ = ((s*r)^8*(r^2*x)^3)^k := by rw [hnorm]
    _ = (((s*r)^14/s^6)*x^3)^k := by
      congr 1
      field_simp
    _ = _ := by simp only [mul_pow, ← pow_mul]; rfl
theorem weightedChebyshev_exact_eval (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (k : ℕ) (θ : ℝ) :
    let H := ∑ j ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j) *
        scaledChebyshev (s*r) (s^2+r^2) (14*k-j)
    let x := s^2+r^2+2*s*r*Real.cos θ
    let z := ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)
    H.eval x = 2*((s*r)^14/s^6)^k*x^(3*k)*
      Real.cos ((8*k : ℕ)*θ+(6*k : ℕ)*z.arg) := by
  intro H x z
  have hs : 0 < s := hr.trans hrs
  have hp := weightedChebyshev_eval_phase (s*r) (s^2+r^2) (r^2) θ
    (ne_of_gt (mul_pos hs hr)) (14*k) (6*k) (by omega)
  dsimp only at hp
  rw [show 14*k-6*k=8*k by omega] at hp
  have hx : s^2+r^2+2*(s*r)*Real.cos θ = x := by dsimp [x]; ring
  rw [hx] at hp
  change H.eval x = 2*(s*r)^(8*k)*‖z‖^(6*k)*
    Real.cos ((8*k : ℕ)*θ+(6*k : ℕ)*z.arg) at hp
  calc
    _ = 2*((s*r)^(8*k)*‖z‖^(6*k))*
        Real.cos ((8*k : ℕ)*θ+(6*k : ℕ)*z.arg) := by
      convert hp using 1
      ring
    _ = _ := by
      rw [weightedChebyshev_amplitude s r θ (ne_of_gt hs) k]
      dsimp [x]
      ring
theorem continuous_ordered_preimages_pos (N : ℕ) (hN : 0 < N)
    (F : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hF : ContinuousOn F (Set.Icc a b))
    (t : Fin (N+1) → ℝ) (ht : StrictMono t)
    (ha : F a = t 0) (hb : F b = t (Fin.last N)) :
    ∃ y : Fin (N+1) → ℝ, StrictMono y ∧ y 0 = a ∧
      y (Fin.last N) = b ∧ (∀ j, y j ∈ Set.Icc a b ∧ F (y j) = t j) := by
  cases N with
  | zero => omega
  | succ n => exact continuous_ordered_preimages n F a b hab hF t ht ha hb
theorem weighted_phase_endpoints (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (l m : ℕ) :
    let F := fun θ : ℝ => (l : ℝ)*θ + (m : ℝ)*
      (((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)).arg
    F 0 = 0 ∧ F Real.pi = ((l+m : ℕ) : ℝ)*Real.pi := by
  intro F
  have hs := hr.trans hrs
  have hplus : 0 ≤ r^2+s*r := by positivity
  have hminus : r^2-s*r < 0 := by nlinarith
  constructor
  · dsimp only [F]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      ← Complex.ofReal_add, Complex.arg_ofReal_of_nonneg hplus, mul_zero, add_zero]
  · dsimp only [F]
    have hz : ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((Real.pi : ℂ)*Complex.I) =
        ((r^2-s*r : ℝ) : ℂ) := by
      rw [Complex.exp_pi_mul_I]
      push_cast
      ring
    rw [hz, Complex.arg_ofReal_of_neg hminus]
    push_cast
    ring
theorem weightedChebyshev_alternating_nodes (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (k : ℕ) (hk : 0 < k) :
    let H := ∑ j ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j) *
        scaledChebyshev (s*r) (s^2+r^2) (14*k-j)
    ∃ x : Fin (14*k+1) → ℝ, StrictMono x ∧
      x 0 = (s-r)^2 ∧ x (Fin.last (14*k)) = (s+r)^2 ∧
      ∀ j, H.eval (x j) = (-1 : ℝ)^j.val*2*((s*r)^14/s^6)^k*(x j)^(3*k) := by
  classical
  intro H
  let F := fun θ : ℝ => (8*k : ℕ)*θ + (6*k : ℕ)*
      (((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)).arg
  have hF : ContinuousOn F (Set.Icc 0 Real.pi) :=
    weighted_phase_continuous s r hr hrs (8*k) (6*k)
  have hend := weighted_phase_endpoints s r hr hrs (8*k) (6*k)
  change F 0 = 0 ∧ F Real.pi = _ at hend
  let t : Fin (14*k+1) → ℝ := fun j => (j.val : ℝ)*Real.pi
  have ht : StrictMono t := by
    intro i j hij
    exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) Real.pi_pos
  have hstart : F 0 = t 0 := by simpa [t] using hend.1
  have hfinish : F Real.pi = t (Fin.last (14*k)) := by
    rw [hend.2]
    change ((8*k+6*k : ℕ) : ℝ)*Real.pi = ((14*k : ℕ) : ℝ)*Real.pi
    congr 1
    exact_mod_cast (by omega : 8*k+6*k=14*k)
  obtain ⟨θ, hθ, hθ0, hθπ, hθval⟩ := continuous_ordered_preimages_pos
    (14*k) (by omega) F 0 Real.pi Real.pi_pos hF t ht hstart hfinish
  let x : Fin (14*k+1) → ℝ := fun j =>
    s^2+r^2+2*s*r*Real.cos (θ j.rev)
  have hxmono : StrictMono x := by
    intro i j hij
    have hθlt : θ j.rev < θ i.rev := hθ (Fin.rev_lt_rev.mpr hij)
    have hcos := Real.strictAntiOn_cos (hθval j.rev).1 (hθval i.rev).1 hθlt
    dsimp only [x]
    have hs := hr.trans hrs
    have hcoef : 0 < 2*s*r := by positivity
    have hmul := mul_lt_mul_of_pos_left hcos hcoef
    linarith
  refine ⟨x, hxmono, ?_, ?_, ?_⟩
  · dsimp only [x]
    rw [Fin.rev_zero, hθπ, Real.cos_pi]
    ring
  · dsimp only [x]
    rw [Fin.rev_last, hθ0, Real.cos_zero]
    ring
  · intro j
    have hp := weightedChebyshev_exact_eval s r hr hrs k (θ j.rev)
    change H.eval (x j) = 2*((s*r)^14/s^6)^k*(x j)^(3*k)*Real.cos (F (θ j.rev)) at hp
    rw [(hθval j.rev).2] at hp
    dsimp only [t] at hp
    rw [Real.cos_nat_mul_pi] at hp
    have hsum : j.rev.val+j.val = 14*k := by
      dsimp [Fin.rev]
      omega
    have hparity : (-1 : ℝ)^j.rev.val = (-1 : ℝ)^j.val := by
      apply mul_right_cancel₀ (pow_ne_zero j.val (by norm_num : (-1 : ℝ) ≠ 0))
      rw [← pow_add, hsum]
      have heven : (-1 : ℝ)^(14*k) = 1 := by rw [pow_mul]; norm_num
      rw [heven, ← mul_pow]
      norm_num
    rw [hparity] at hp
    calc
      _ = _ := hp
      _ = _ := by ring
theorem explicit_weighted_chebyshev_target :
    ∀ (u v : ℝ) (k : ℕ), 0 < u → u < v → 0 < k →
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let c := s^2+r^2
    let R : ℕ → Polynomial ℝ := fun j =>
      Polynomial.C (d^j) * (Polynomial.Chebyshev.C ℝ (j : ℤ)).comp
        (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c))
    let H := ∑ j ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j) * R (14*k-j)
    H.Monic ∧ H.natDegree = 14*k ∧
      H.coeff (14*k-1) = -(14*k : ℝ)*c + (6*k : ℝ)*r^2 ∧
      ∃ x : Fin (14*k+1) → ℝ, StrictMono x ∧
        x 0 = u^2 ∧ x (Fin.last (14*k)) = v^2 ∧
        ∀ j, H.eval (x j) = (-1 : ℝ)^j.val*2*(d^14/s^6)^k*(x j)^(3*k) := by
  intro u v k hu huv hk s r d c R H
  have hs : 0 < s := by dsimp [s]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hrs : r < s := by dsimp [r, s]; linarith
  have hdata := explicit_weighted_chebyshev_algebraic u v k hu huv hk
  change H.Monic ∧ H.natDegree = 14*k ∧
    H.coeff (14*k-1) = -(14*k : ℝ)*c+(6*k : ℝ)*r^2 at hdata
  obtain ⟨x, hx, hx0, hxlast, hxeval⟩ :=
    weightedChebyshev_alternating_nodes s r hr hrs k hk
  have hleft : s-r = u := by dsimp [s, r]; ring
  have hright : s+r = v := by dsimp [s, r]; ring
  rw [hleft] at hx0
  rw [hright] at hxlast
  refine ⟨hdata.1, hdata.2.1, hdata.2.2, x, hx, hx0, hxlast, ?_⟩
  intro j
  exact hxeval j
theorem log_norm_multiset_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    Real.log ‖s.prod‖ = (s.map (fun z => Real.log ‖z‖)).sum := by
  rw [Multiset.norm_prod, Real.log_multiset_prod]
  · simp only [Multiset.map_map, Function.comp_def]
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
    exact norm_ne_zero_iff.mpr (hs z hz)
theorem ae_complex_avoid_multiset (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.NullSingletonClass μ] (s : Multiset ℂ) :
    ∀ᵐ (x : ℝ) ∂μ, ∀ z ∈ s, (x : ℂ) ≠ z := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    filter_upwards [μ.ae_ne z.re, ih] with x hx hs
    intro w hw
    rcases Multiset.mem_cons.mp hw with rfl | hw
    · intro h
      exact hx (congrArg Complex.re h)
    · exact hs w hw
theorem root_log_sum_integral (μ : MeasureTheory.Measure ℝ)
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ) (s : Multiset ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ => (s.map (fun z => Real.log ‖z - (x : ℂ)‖)).sum) μ ∧
    MeasureTheory.integral μ
      (fun x : ℝ => (s.map (fun z => Real.log ‖z - (x : ℂ)‖)).sum) =
      (s.map (fun z => MeasureTheory.integral μ
        (fun x : ℝ => Real.log ‖z - (x : ℂ)‖))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ⟨(hroot z).add ih.1, (MeasureTheory.integral_add (hroot z) ih.1).trans
      (congrArg (fun y => MeasureTheory.integral μ
        (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) + y) ih.2)⟩
theorem complex_log_eval_integral (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    MeasureTheory.Integrable (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) μ ∧
    MeasureTheory.integral μ (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) =
      Real.log ‖p.leadingCoeff‖ +
      (p.roots.map (fun z => MeasureTheory.integral μ
        (fun x : ℝ => Real.log ‖z - (x : ℂ)‖))).sum := by
  have heq : (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) =ᵐ[μ]
      (fun x : ℝ => Real.log ‖p.leadingCoeff‖ +
        (p.roots.map (fun z => Real.log ‖z - (x : ℂ)‖)).sum) := by
    filter_upwards [ae_complex_avoid_multiset μ p.roots] with x hx
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))]
    · rw [log_norm_multiset_prod]
      · congr 1
        simp only [Multiset.map_map, Function.comp_def]
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro z hz
        rw [norm_sub_rev]
      · intro a ha
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
        exact sub_ne_zero.mpr (hx z hz)
    · apply norm_ne_zero_iff.mpr
      intro hz
      have hmem := Multiset.prod_eq_zero_iff.mp hz
      obtain ⟨z, hz, he⟩ := Multiset.mem_map.mp hmem
      exact sub_ne_zero.mpr (hx z hz) he
  have hs := root_log_sum_integral μ hroot p.roots
  refine ⟨((MeasureTheory.integrable_const _).add hs.1).congr heq.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae heq,
    MeasureTheory.integral_add (MeasureTheory.integrable_const _) hs.1, hs.2]
  simp
theorem complex_log_eval_lower_bound_of_coeff (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (t C : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ)
    (hpotential : ∀ z : ℂ, z ≠ 0 → t * Real.log ‖z‖ + C ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log ‖z - (x : ℂ)‖))
    (p : Polynomial ℂ) (hp : p ≠ 0) (h0 : p.coeff 0 ≠ 0)
    (hlc : 0 ≤ Real.log ‖p.leadingCoeff‖) (hconst : 0 ≤ Real.log ‖p.coeff 0‖) :
    C * (p.natDegree : ℝ) ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) := by
  have hr0 : (0 : ℂ) ∉ p.roots := by
    intro hz
    have he := (Polynomial.mem_roots hp).mp hz
    apply h0
    rwa [Polynomial.coeff_zero_eq_eval_zero]
  have hr : ∀ z ∈ p.roots, z ≠ 0 := by
    intro z hz he
    exact hr0 (he ▸ hz)
  have hcoeff : ‖p.coeff 0‖ = ‖p.leadingCoeff‖ * ‖p.roots.prod‖ := by
    rw [(IsAlgClosed.splits p).coeff_zero_eq_leadingCoeff_mul_prod_roots]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hlogcoeff : Real.log ‖p.coeff 0‖ = Real.log ‖p.leadingCoeff‖ +
      (p.roots.map (fun z => Real.log ‖z‖)).sum := by
    rw [hcoeff, Real.log_mul
      (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
      (norm_ne_zero_iff.mpr (Multiset.prod_ne_zero hr0)), log_norm_multiset_prod p.roots hr]
  have hsum := Multiset.sum_map_le_sum_map
    (fun z : ℂ => t * Real.log ‖z‖ + C)
    (fun z : ℂ => MeasureTheory.integral μ (fun x : ℝ => Real.log ‖z - (x : ℂ)‖))
    (fun z hz => hpotential z (hr z hz))
  have hsum_eq : (p.roots.map (fun z => t * Real.log ‖z‖ + C)).sum =
      t * (p.roots.map (fun z => Real.log ‖z‖)).sum + (p.roots.card : ℝ) * C := by
    induction p.roots using Multiset.induction_on with
    | empty => simp
    | cons z s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
        Nat.cast_one] at *
      rw [ih]
      ring
  rw [hsum_eq, ← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hsum
  rw [(complex_log_eval_integral μ hroot p hp).2]
  have hlead := mul_nonneg (sub_nonneg.mpr ht1) hlc
  have hconstant := mul_nonneg ht hconst
  nlinarith
theorem integer_log_eval_eq_complex (p : Polynomial ℤ) (x : ℝ) :
    Real.log |Polynomial.aeval x p| =
      Real.log ‖(p.map (Int.castRingHom ℂ)).eval (x : ℂ)‖ := by
  change Real.log |Polynomial.aeval x p| =
    Real.log ‖(p.map (algebraMap ℤ ℂ)).eval ((algebraMap ℝ ℂ) x)‖
  rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply ℂ x p]
  change Real.log |Polynomial.aeval x p| = Real.log ‖((Polynomial.aeval x p : ℝ) : ℂ)‖
  rw [Complex.norm_real, Real.norm_eq_abs]
theorem integer_log_eval_integrable (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ)
    (p : Polynomial ℤ) (hp : p ≠ 0) :
    MeasureTheory.Integrable (fun x : ℝ => Real.log |Polynomial.aeval x p|) μ := by
  have hp' : p.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hp
  simpa only [integer_log_eval_eq_complex] using (complex_log_eval_integral μ hroot _ hp').1
theorem exists_X_pow_mul_coeff_zero_ne (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∃ (r : ℕ) (q : Polynomial ℤ), p = Polynomial.X ^ r * q ∧ q ≠ 0 ∧
      q.coeff 0 ≠ 0 ∧ p.natDegree = r + q.natDegree := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases h0 : p.coeff 0 = 0
    · obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
      have hq0 : q ≠ 0 := by intro hz; simp [hz] at hq; exact hp hq
      have hdegree : p.natDegree = q.natDegree + 1 := by rw [hq, Polynomial.natDegree_X_mul hq0]
      obtain ⟨r, Q, hQ, hQ0, hQconst, hdQ⟩ :=
        ih q.natDegree (by omega) q hq0 rfl
      refine ⟨r+1, Q, ?_, hQ0, hQconst, ?_⟩
      · rw [hq, hQ, pow_succ]
        ring
      · omega
    · exact ⟨0, p, by simp, hp, h0, by simpa only [zero_add] using hn.symm⟩
theorem nonneg_log_norm_intCast (a : ℤ) (ha : a ≠ 0) :
    0 ≤ Real.log ‖(a : ℂ)‖ := by
  apply Real.log_nonneg
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs ha
theorem integer_log_eval_lower_bound_of_coeff (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (t C : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ)
    (hpotential : ∀ z : ℂ, z ≠ 0 → t * Real.log ‖z‖ + C ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log ‖z - (x : ℂ)‖))
    (p : Polynomial ℤ) (hp : p ≠ 0) (h0 : p.coeff 0 ≠ 0) :
    C * (p.natDegree : ℝ) ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log |Polynomial.aeval x p|) := by
  have hp' : p.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hp
  have h0' : (p.map (Int.castRingHom ℂ)).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_map]
    change (p.coeff 0 : ℂ) ≠ 0
    exact_mod_cast h0
  have hlc : 0 ≤ Real.log ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ := by
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    exact nonneg_log_norm_intCast _ (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hconst : 0 ≤ Real.log ‖(p.map (Int.castRingHom ℂ)).coeff 0‖ := by
    rw [Polynomial.coeff_map]
    exact nonneg_log_norm_intCast _ h0
  have h := complex_log_eval_lower_bound_of_coeff μ t C ht ht1 hroot hpotential
    (p.map (Int.castRingHom ℂ)) hp' h0' hlc hconst
  simpa only [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective,
    ← integer_log_eval_eq_complex] using h
theorem ae_integer_aeval_ne_zero (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.NullSingletonClass μ] (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∀ᵐ (x : ℝ) ∂μ, Polynomial.aeval x p ≠ 0 := by
  have hp' : p.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have ha := (p.map (Int.castRingHom ℝ)).roots.toFinset.finite_toSet.countable.ae_notMem μ
  filter_upwards [ha] with x hx
  intro hz
  apply hx
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hp').mpr
  change (p.map (algebraMap ℤ ℝ)).eval x = 0
  rwa [Polynomial.eval_map_algebraMap]
theorem integer_log_eval_X_pow_mul (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ]
    (hroot : ∀ z : ℂ, MeasureTheory.Integrable
      (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) μ)
    (r : ℕ) (q : Polynomial ℤ) (hq : q ≠ 0) :
    MeasureTheory.integral μ
      (fun x : ℝ => Real.log |Polynomial.aeval x (Polynomial.X ^ r * q)|) =
    (r : ℝ) * MeasureTheory.integral μ (fun x : ℝ => Real.log ‖(x : ℂ)‖) +
      MeasureTheory.integral μ (fun x : ℝ => Real.log |Polynomial.aeval x q|) := by
  have hxlog : MeasureTheory.Integrable (fun x : ℝ => Real.log ‖(x : ℂ)‖) μ := by
    simpa only [zero_sub, norm_neg] using hroot 0
  have hqlog := integer_log_eval_integrable μ hroot q hq
  have heq : (fun x : ℝ => Real.log |Polynomial.aeval x (Polynomial.X ^ r * q)|) =ᵐ[μ]
      (fun x : ℝ => (r : ℝ) * Real.log ‖(x : ℂ)‖ + Real.log |Polynomial.aeval x q|) := by
    filter_upwards [μ.ae_ne (0 : ℝ), ae_integer_aeval_ne_zero μ q hq] with x hx hqx
    simp only [Polynomial.aeval_mul, map_pow, Polynomial.aeval_X, abs_mul, abs_pow]
    rw [Real.log_mul (pow_ne_zero r (abs_ne_zero.mpr hx)) (abs_ne_zero.mpr hqx),
      Real.log_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [MeasureTheory.integral_congr_ae heq,
    MeasureTheory.integral_add (hxlog.const_mul _) hqlog, MeasureTheory.integral_const_mul]
theorem potential_integer_polynomial_margin :
    ∀ (μ : MeasureTheory.Measure ℝ) (t C L : ℝ),
    MeasureTheory.IsProbabilityMeasure μ → MeasureTheory.NullSingletonClass μ →
    0 ≤ t → t ≤ 1 → 0 ≤ C → 0 ≤ L →
    (∀ z : ℂ, MeasureTheory.Integrable (fun x : ℝ => Real.log ‖z-(x : ℂ)‖) μ) →
    (∀ z : ℂ, z ≠ 0 → t*Real.log ‖z‖ + C ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log ‖z-(x : ℂ)‖)) →
    L ≤ MeasureTheory.integral μ (fun x : ℝ => Real.log ‖(x : ℂ)‖) →
    ∀ p : Polynomial ℤ, p ≠ 0 →
    MeasureTheory.Integrable (fun x : ℝ => Real.log |Polynomial.aeval x p|) μ ∧
    min C L * (p.natDegree : ℝ) ≤
      MeasureTheory.integral μ (fun x : ℝ => Real.log |Polynomial.aeval x p|) := by
  intro μ t C L hprob hatom ht ht1 _hC _hL hroot hpotential hLbound p hp
  have : MeasureTheory.IsProbabilityMeasure μ := hprob
  have : MeasureTheory.NullSingletonClass μ := hatom
  refine ⟨integer_log_eval_integrable μ hroot p hp, ?_⟩
  obtain ⟨r, q, hpq, hq, hq0, hd⟩ := exists_X_pow_mul_coeff_zero_ne p hp
  have hqbound := integer_log_eval_lower_bound_of_coeff μ t C ht ht1 hroot hpotential q hq hq0
  have hid : MeasureTheory.integral μ (fun x : ℝ => Real.log |Polynomial.aeval x p|) =
      (r : ℝ) * MeasureTheory.integral μ (fun x : ℝ => Real.log ‖(x : ℂ)‖) +
      MeasureTheory.integral μ (fun x : ℝ => Real.log |Polynomial.aeval x q|) := by
    rw [hpq]
    exact integer_log_eval_X_pow_mul μ hroot r q hq
  rw [hid, hd, Nat.cast_add, mul_add]
  calc
    min C L * (r : ℝ) + min C L * (q.natDegree : ℝ) ≤
        L * (r : ℝ) + C * (q.natDegree : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right (min_le_right C L) (Nat.cast_nonneg r))
        (mul_le_mul_of_nonneg_right (min_le_left C L) (Nat.cast_nonneg _))
    _ ≤ _ := add_le_add (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hLbound (Nat.cast_nonneg r)) hqbound
theorem weightedChebyshev_shifted_data (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (k j : ℕ) (hj : j < 8*k) :
    let Q := ∑ i ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) i : ℝ)*(r^2)^i) *
        scaledChebyshev (s*r) (s^2+r^2) (14*k-j-i)
    Q.Monic ∧ Q.natDegree = 14*k-j := by
  intro Q
  have hs : 0 < s := hr.trans hrs
  have hd : s*r ≠ 0 := (mul_pos hs hr).ne'
  have h := weightedChebyshev_data (s*r) (s^2+r^2) (r^2) (14*k-j) (6*k)
    hd (by omega)
  have heq : (∑ i ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) i : ℝ)*(r^2)^i) *
        scaledChebyshev (s*r) (s^2+r^2) (14*k-j-i)) =
      ∑ i ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) i : ℝ)*(r^2)^i) *
        scaledChebyshev (s*r) (s^2+r^2) ((14*k-j)-i) := rfl
  exact ⟨h.1, h.2.1⟩
theorem weightedChebyshev_shifted_eval_bound (s r : ℝ) (hr : 0 < r) (hrs : r < s)
    (k j : ℕ) (hj : j < 8*k) (x : ℝ)
    (hx : x ∈ Set.Icc ((s-r)^2) ((s+r)^2)) :
    let Q := ∑ i ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) i : ℝ)*(r^2)^i) *
        scaledChebyshev (s*r) (s^2+r^2) (14*k-j-i)
    |Q.eval x| ≤ 2*((s*r)⁻¹)^j*((s*r)^14/s^6)^k*x^(3*k) := by
  intro Q
  have hs : 0 < s := hr.trans hrs
  have hd : 0 < s*r := mul_pos hs hr
  let y := (x-(s^2+r^2))/(2*(s*r))
  have hylo : -1 ≤ y := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(s*r))).mpr
    nlinarith [hx.1]
  have hyhi : y ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(s*r))).mpr
    nlinarith [hx.2]
  let θ := Real.arccos y
  have hxθ : s^2+r^2+2*(s*r)*Real.cos θ = x := by
    rw [show Real.cos θ = y from Real.cos_arccos hylo hyhi]
    dsimp [y]
    field_simp
    ring
  let z := ((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)
  have hp := weightedChebyshev_eval_phase (s*r) (s^2+r^2) (r^2) θ hd.ne'
    (14*k-j) (6*k) (by omega)
  dsimp only at hp
  change Q.eval (s^2+r^2+2*(s*r)*Real.cos θ) =
    2*(s*r)^(14*k-j-6*k)*‖z‖^(6*k)*
      Real.cos ((14*k-j-6*k : ℕ)*θ+(6*k : ℕ)*z.arg) at hp
  rw [hxθ, show 14*k-j-6*k=8*k-j by omega] at hp
  have hamp : (s*r)^(8*k-j)*‖z‖^(6*k) =
      ((s*r)⁻¹)^j*((s*r)^14/s^6)^k*x^(3*k) := by
    have hpow : (s*r)^(8*k-j) = ((s*r)⁻¹)^j*(s*r)^(8*k) := by
      rw [pow_sub₀ (s*r) hd.ne' (by omega : j ≤ 8*k)]
      simp only [inv_pow, mul_comm]
    rw [hpow]
    have h := weightedChebyshev_amplitude s r θ hs.ne' k
    have hxθ' : s^2+r^2+2*s*r*Real.cos θ = x := by
      convert hxθ using 1
      ring
    rw [hxθ'] at h
    calc
      _ = ((s*r)⁻¹)^j*((s*r)^(8*k)*‖z‖^(6*k)) := by ring
      _ = _ := by rw [h]; ring
  rw [hp, abs_mul, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ 2*(s*r)^(8*k-j)), abs_of_nonneg (by positivity : 0 ≤ ‖z‖^(6*k))]
  have hc := abs_le.mpr ⟨Real.neg_one_le_cos
    ((8*k-j : ℕ)*θ+(6*k : ℕ)*z.arg), Real.cos_le_one _⟩
  calc
    _ ≤ 2*(s*r)^(8*k-j)*‖z‖^(6*k) := by
      simpa using mul_le_mul_of_nonneg_left hc
        (show 0 ≤ 2*(s*r)^(8*k-j)*‖z‖^(6*k) by positivity)
    _ = _ := by rw [mul_assoc, hamp]; ring
theorem exists_top_block_rounding_of_initial_integrality_up_to
    (n J b : ℕ) (hb : b ≤ n) (hJ : 1 ≤ J) (H : Polynomial ℝ)
    (hH : H.Monic) (hdeg : H.natDegree = n) (Q : ℕ → Polynomial ℝ)
    (hQ : ∀ j, J < j → j < b → (Q j).Monic ∧ (Q j).natDegree = n-j)
    (hinit : ∀ j, j ≤ J → ∃ z : ℤ, H.coeff (n-j) = (z : ℝ))
    (t : ℝ) (S : Set ℝ) (W : ℝ → ℝ)
    (hbound : ∀ j, J < j → j < b → ∀ x ∈ S, |(Q j).eval x| ≤ 2*t^j*W x) :
    ∀ m : ℕ, m < b → ∃ T : Polynomial ℝ,
      T.Monic ∧ T.natDegree = n ∧ T.coeff (n-1) = H.coeff (n-1) ∧
      (∀ j, j ≤ m → ∃ z : ℤ, T.coeff (n-j) = (z : ℝ)) ∧
      ∀ x ∈ S, |T.eval x-H.eval x| ≤
        (∑ j ∈ Finset.range (m+1), if J < j then t^j else 0)*W x := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨H, hH, hdeg, rfl, fun j hj => hinit j (by omega), ?_⟩
    intro x hx
    simp
  | succ m ih =>
    intro hmn
    by_cases hsmall : m+1 ≤ J
    · refine ⟨H, hH, hdeg, rfl, fun j hj => hinit j (hj.trans hsmall), ?_⟩
      intro x hx
      have hz : (∑ j ∈ Finset.range (m+1+1), if J < j then t^j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
      simp only [sub_self, abs_zero, hz, zero_mul, le_refl]
    · have hJm : J < m+1 := by omega
      obtain ⟨T, hT, hTd, hTtrace, hTint, hTerr⟩ := ih (by omega)
      obtain ⟨hQmon, hQd⟩ := hQ (m+1) hJm hmn
      let a : ℝ := (round (T.coeff (n-(m+1))) : ℤ)-T.coeff (n-(m+1))
      let P := T + Polynomial.C a * Q (m+1)
      have hPsmall : (Polynomial.C a * Q (m+1)).natDegree < n :=
        (Polynomial.natDegree_C_mul_le _ _).trans_lt (by rw [hQd]; omega)
      have hPlt : (Polynomial.C a * Q (m+1)).natDegree < T.natDegree := by
        rw [hTd]; exact hPsmall
      have hPd : P.natDegree = n := by
        exact (Polynomial.natDegree_add_eq_left_of_natDegree_lt hPlt).trans hTd
      have hP : P.Monic := hT.add_of_left (Polynomial.degree_lt_degree hPlt)
      have hQtrace : (Q (m+1)).coeff (n-1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQd]; omega)
      have hPtrace : P.coeff (n-1) = H.coeff (n-1) := by
        simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul, hQtrace,
          mul_zero, add_zero, hTtrace]
      refine ⟨P, hP, hPd, hPtrace, ?_, ?_⟩
      · intro j hj
        by_cases hjlast : j = m+1
        · subst j
          refine ⟨round (T.coeff (n-(m+1))), ?_⟩
          have htop : (Q (m+1)).coeff (n-(m+1)) = 1 := by
            simpa only [hQd] using hQmon.coeff_natDegree
          simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul, htop, mul_one]
          dsimp [a]
          ring
        · obtain ⟨z, hz⟩ := hTint j (by omega)
          refine ⟨z, ?_⟩
          have hQzero : (Q (m+1)).coeff (n-j) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQd]; omega)
          simpa only [P, Polynomial.coeff_add, Polynomial.coeff_C_mul, hQzero,
            mul_zero, add_zero] using hz
      · intro x hx
        have ha : |a| ≤ (1 / 2 : ℝ) := by
          simpa only [a, abs_sub_comm] using abs_sub_round (T.coeff (n-(m+1)))
        have hstep : |a*(Q (m+1)).eval x| ≤ t^(m+1)*W x := by
          rw [abs_mul]
          calc
            _ ≤ (1 / 2 : ℝ)*|(Q (m+1)).eval x| :=
              mul_le_mul_of_nonneg_right ha (abs_nonneg _)
            _ ≤ (1 / 2 : ℝ)*(2*t^(m+1)*W x) :=
              mul_le_mul_of_nonneg_left (hbound (m+1) hJm hmn x hx) (by norm_num)
            _ = _ := by ring
        have heval : P.eval x-H.eval x = (T.eval x-H.eval x)+a*(Q (m+1)).eval x := by
          simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
          ring
        rw [heval, Finset.sum_range_succ, ite_eq_left hJm, add_mul]
        exact (abs_add_le _ _).trans (add_le_add (hTerr x hx) hstep)
theorem exists_top_block_rounding_of_initial_integrality
    (n J : ℕ) (hJ : 1 ≤ J) (H : Polynomial ℝ)
    (hH : H.Monic) (hdeg : H.natDegree = n) (Q : ℕ → Polynomial ℝ)
    (hQ : ∀ j, J < j → j < n → (Q j).Monic ∧ (Q j).natDegree = n-j)
    (hinit : ∀ j, j ≤ J → ∃ z : ℤ, H.coeff (n-j) = (z : ℝ))
    (t : ℝ) (S : Set ℝ) (W : ℝ → ℝ)
    (hbound : ∀ j, J < j → j < n → ∀ x ∈ S, |(Q j).eval x| ≤ 2*t^j*W x) :
    ∀ m : ℕ, m < n → ∃ T : Polynomial ℝ,
      T.Monic ∧ T.natDegree = n ∧ T.coeff (n-1) = H.coeff (n-1) ∧
      (∀ j, j ≤ m → ∃ z : ℤ, T.coeff (n-j) = (z : ℝ)) ∧
      ∀ x ∈ S, |T.eval x-H.eval x| ≤
        (∑ j ∈ Finset.range (m+1), if J < j then t^j else 0)*W x :=
  exists_top_block_rounding_of_initial_integrality_up_to n J n le_rfl hJ H
    hH hdeg Q hQ hinit t S W hbound
noncomputable def matrixPolynomialDerivative {ι : Type*} {R : Type*} [Semiring R]
    (M : Matrix ι ι (Polynomial R)) : Matrix ι ι (Polynomial R) :=
  fun i j => (M i j).derivative
theorem matrixPolynomialDerivative_mul {ι : Type*} [Fintype ι]
    {R : Type*} [CommRing R] (M N : Matrix ι ι (Polynomial R)) :
    matrixPolynomialDerivative (M*N) =
      matrixPolynomialDerivative M*N + M*matrixPolynomialDerivative N := by
  ext i j
  simp only [matrixPolynomialDerivative, Matrix.mul_apply, Matrix.add_apply,
    Polynomial.derivative_sum, Polynomial.derivative_mul, Finset.sum_add_distrib]
theorem matrixPolynomialDerivative_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (M : Matrix ι ι (Polynomial R)) (n : ℕ) :
    matrixPolynomialDerivative (M^n) =
      ∑ i ∈ Finset.range n, M^i*matrixPolynomialDerivative M*M^(n-1-i) := by
  induction n with
  | zero =>
    funext i j
    by_cases h : i = j <;> simp [matrixPolynomialDerivative, h]
  | succ n ih =>
    rw [pow_succ, matrixPolynomialDerivative_mul, ih, Finset.sum_mul,
      Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
    apply congrArg (fun N : Matrix ι ι (Polynomial R) => N+M^n*matrixPolynomialDerivative M)
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [mul_assoc, ← pow_succ, show n-1-i+1=n-i by omega]
theorem matrix_trace_pow_derivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (M : Matrix ι ι (Polynomial R)) (n : ℕ) :
    (Matrix.trace (M^n)).derivative =
      (n : Polynomial R)*Matrix.trace (M^(n-1)*matrixPolynomialDerivative M) := by
  have ht (N : Matrix ι ι (Polynomial R)) :
      (Matrix.trace N).derivative = Matrix.trace (matrixPolynomialDerivative N) := by
    simp [Matrix.trace, matrixPolynomialDerivative]
  rw [ht, matrixPolynomialDerivative_pow]
  simp only [Matrix.trace_sum]
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
      Matrix.trace (M^i*matrixPolynomialDerivative M*M^(n-1-i)) =
        Matrix.trace (M^(n-1)*matrixPolynomialDerivative M) := by
    rw [Matrix.trace_mul_cycle, ← pow_add, show n-1-i+i=n-1 by
      have := Finset.mem_range.mp hi; omega]
  rw [Finset.sum_congr rfl hterm]
  simp
theorem integer_matrix_trace_power_coefficient_dvd (e k : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    (k : ℤ) ∣ (e : ℤ)*(Matrix.trace (M^k)).coeff e := by
  cases e with
  | zero => simp
  | succ e =>
    have h := congrArg (fun p : Polynomial ℤ => p.coeff e)
      (matrix_trace_pow_derivative M k)
    rw [Polynomial.coeff_derivative, Polynomial.coeff_natCast_mul] at h
    rw [Nat.cast_succ, mul_comm, h]
    exact dvd_mul_right _ _
noncomputable def polynomialCompanion {R : Type*} [Ring R] (b c : R) :
    Matrix (Fin 2) (Fin 2) (Polynomial R) :=
  !![Polynomial.X-Polynomial.C c, -Polynomial.C b; 1, 0]
theorem polynomialCompanion_sq {R : Type*} [CommRing R] (b c : R) :
    (polynomialCompanion b c)^2 =
      (Polynomial.X-Polynomial.C c) • polynomialCompanion b c -
        Polynomial.C b • (1 : Matrix (Fin 2) (Fin 2) (Polynomial R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [polynomialCompanion, pow_two, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
theorem trace_polynomialCompanion_pow (d c : ℝ) (hd : d ≠ 0) (n : ℕ) :
    Matrix.trace ((polynomialCompanion (d^2) c)^n) = scaledChebyshev d c n := by
  let M := polynomialCompanion (d^2) c
  change Matrix.trace (M^n) = _
  induction n using Nat.twoStepInduction with
  | zero => simp [scaledChebyshev_zero, Matrix.trace]
  | one => simp [M, polynomialCompanion, Matrix.trace, Fin.sum_univ_two, scaledChebyshev_one d c hd]
  | more n ih0 ih1 =>
    have hpow : M^(n+2) =
        (Polynomial.X-Polynomial.C c) • M^(n+1) - Polynomial.C (d^2) • M^n := by
      rw [show n+2=2+n by omega, pow_add, polynomialCompanion_sq]
      simp only [sub_mul, Matrix.smul_mul, one_mul]
      change (Polynomial.X-Polynomial.C c) • (M*M^n) - Polynomial.C (d^2) • M^n = _
      rw [← pow_succ']
    rw [hpow, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, ih0, ih1,
      smul_eq_mul, smul_eq_mul, scaledChebyshev_add_two d c hd]
theorem matrix_weighted_binomial_trace (M : Matrix (Fin 2) (Fin 2) (Polynomial ℝ))
    (a : ℝ) (n m : ℕ) (hm : m ≤ n) :
    Matrix.trace (M^(n-m)*(Polynomial.C a • 1+M)^m) =
      ∑ j ∈ Finset.range (m+1),
        Polynomial.C ((Nat.choose m j : ℝ)*a^j)*Matrix.trace (M^(n-j)) := by
  have hc : Commute (Polynomial.C a • (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℝ))) M := by
    show (Polynomial.C a • 1)*M = M*(Polynomial.C a • 1)
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  rw [hc.add_pow, Finset.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have heq : M^(n-m)*((Polynomial.C a • 1)^j*M^(m-j)*(Nat.choose m j)) =
      (Polynomial.C ((Nat.choose m j : ℝ)*a^j)) • M^(n-j) := by
    rw [smul_pow, one_pow, Matrix.smul_mul, one_mul]
    rw [show ((Nat.choose m j : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial ℝ)) =
      ((Nat.choose m j : ℕ) : Polynomial ℝ) • 1 by
        ext i k
        simp [Matrix.natCast_apply, Matrix.one_apply]]
    simp only [Matrix.mul_smul, mul_one]
    rw [← pow_add,
      show n-m+(m-j)=n-j by omega]
    simp [Polynomial.C_mul, mul_smul, Polynomial.C_pow, mul_comm]
  rw [heq, Matrix.trace_smul, smul_eq_mul]
noncomputable def polynomialWeightedMatrix {R : Type*} [Ring R] (b c a : R) :
    Matrix (Fin 2) (Fin 2) (Polynomial R) :=
  (polynomialCompanion b c)^8 * (Polynomial.C a • 1+polynomialCompanion b c)^6
theorem weightedChebyshev_matrix_trace (d c a : ℝ) (hd : d ≠ 0) (k : ℕ) :
    Matrix.trace ((polynomialWeightedMatrix (d^2) c a)^k) =
      ∑ j ∈ Finset.range (6*k+1),
        Polynomial.C ((Nat.choose (6*k) j : ℝ)*a^j)*scaledChebyshev d c (14*k-j) := by
  let M := polynomialCompanion (d^2) c
  have hc : Commute M (Polynomial.C a • 1+M) := by
    show M*(Polynomial.C a • 1+M) = (Polynomial.C a • 1+M)*M
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      mul_one, one_mul]
  have hpow : (polynomialWeightedMatrix (d^2) c a)^k =
      M^(14*k-6*k)*(Polynomial.C a • 1+M)^(6*k) := by
    rw [show 14*k-6*k=8*k by omega]
    exact (hc.pow_pow 8 6).mul_pow k |>.trans (by rw [← pow_mul, ← pow_mul])
  rw [hpow, matrix_weighted_binomial_trace M a (14*k) (6*k) (by omega)]
  simp only [M, trace_polynomialCompanion_pow d c hd]
theorem scaledChebyshev_scaling (D d c : ℝ) (hD : D ≠ 0) (hd : d ≠ 0)
    (n : ℕ) :
    scaledChebyshev (D*d) (D*c) n = Polynomial.C (D^n)*
      (scaledChebyshev d c n).comp (Polynomial.C D⁻¹*Polynomial.X) := by
  have hDd : D*d ≠ 0 := mul_ne_zero hD hd
  have hlin : Polynomial.C D *
      ((Polynomial.X-Polynomial.C c).comp (Polynomial.C D⁻¹*Polynomial.X)) =
      Polynomial.X-Polynomial.C (D*c) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, mul_sub,
      ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hD, Polynomial.C_1, one_mul]
  induction n using Nat.twoStepInduction with
  | zero => simp [scaledChebyshev_zero]
  | one =>
    rw [scaledChebyshev_one _ _ hDd, scaledChebyshev_one _ _ hd, pow_one]
    exact hlin.symm
  | more n ih0 ih1 =>
    rw [scaledChebyshev_add_two _ _ hDd, ih0, ih1,
      scaledChebyshev_add_two _ _ hd, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.mul_comp, Polynomial.C_comp]
    rw [show Polynomial.C (D^(n+1)) = Polynomial.C (D^n)*Polynomial.C D by
      rw [pow_succ, Polynomial.C_mul]]
    rw [show Polynomial.C (D^(n+2)) = Polynomial.C (D^n)*Polynomial.C D^2 by
      simp only [pow_add, Polynomial.C_mul, Polynomial.C_pow]]
    rw [show Polynomial.C ((D*d)^2) = Polynomial.C D^2*Polynomial.C (d^2) by
      simp only [mul_pow, Polynomial.C_mul, Polynomial.C_pow]]
    linear_combination (norm := ring_nf)
      -(Polynomial.C (D^n)*Polynomial.C D*
        (scaledChebyshev d c (n+1)).comp (Polynomial.C D⁻¹*Polynomial.X))*hlin
theorem weightedChebyshev_scaling (D d c a : ℝ) (hD : D ≠ 0) (hd : d ≠ 0)
    (n m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ Finset.range (m+1),
      Polynomial.C ((Nat.choose m j : ℝ)*(D*a)^j)*
        scaledChebyshev (D*d) (D*c) (n-j)) =
      Polynomial.C (D^n)*(∑ j ∈ Finset.range (m+1),
        Polynomial.C ((Nat.choose m j : ℝ)*a^j)*scaledChebyshev d c (n-j)).comp
          (Polynomial.C D⁻¹*Polynomial.X) := by
  simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Finset.mul_sum, scaledChebyshev_scaling D d c hD hd]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hm
  have hDn : D^n = D^j*D^(n-j) := by rw [← pow_add, Nat.add_sub_cancel' hjn]
  rw [hDn, mul_pow]
  simp only [Polynomial.C_mul]
  ring
theorem polynomialCompanion_map {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) (b c : R) :
    (polynomialCompanion b c).map (Polynomial.mapRingHom f) =
      polynomialCompanion (f b) (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [polynomialCompanion]
theorem polynomialWeightedMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b c a : R) :
    (polynomialWeightedMatrix b c a).map (Polynomial.mapRingHom f) =
      polynomialWeightedMatrix (f b) (f c) (f a) := by
  have hscalar : (Polynomial.C a • (1 : Matrix (Fin 2) (Fin 2) (Polynomial R))).map
      (Polynomial.mapRingHom f) =
        Polynomial.C (f a) • (1 : Matrix (Fin 2) (Fin 2) (Polynomial S)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map_apply, h]
  have hsum : (Polynomial.C a • (1 : Matrix (Fin 2) (Fin 2) (Polynomial R)) +
      polynomialCompanion b c).map (Polynomial.mapRingHom f) =
      Polynomial.C (f a) • (1 : Matrix (Fin 2) (Fin 2) (Polynomial S)) +
      polynomialCompanion (f b) (f c) := by
    rw [show (Polynomial.C a • (1 : Matrix (Fin 2) (Fin 2) (Polynomial R)) +
        polynomialCompanion b c).map (Polynomial.mapRingHom f) =
        (Polynomial.C a • (1 : Matrix (Fin 2) (Fin 2) (Polynomial R))).map
          (Polynomial.mapRingHom f) +
        (polynomialCompanion b c).map (Polynomial.mapRingHom f) from by
          funext i j; exact map_add (Polynomial.mapRingHom f) _ _]
    rw [hscalar, polynomialCompanion_map]
  simp only [polynomialWeightedMatrix, Matrix.map_mul, Matrix.map_pow,
    polynomialCompanion_map, hsum]
theorem integer_weighted_matrix_scaled_coeff (D : ℕ) (hD : 0 < D)
    (d c a : ℝ) (hd : d ≠ 0) (dz cz az : ℤ)
    (hdz : (D : ℝ)*d = (dz : ℝ)) (hcz : (D : ℝ)*c = (cz : ℝ))
    (haz : (D : ℝ)*a = (az : ℝ)) (k j : ℕ) (hj : j ≤ 14*k) :
    let H := ∑ i ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) i : ℝ)*a^i)*scaledChebyshev d c (14*k-i)
    ((Matrix.trace ((polynomialWeightedMatrix (dz^2) cz az)^k)).coeff (14*k-j) : ℝ) =
      (D : ℝ)^j*H.coeff (14*k-j) := by
  intro H
  have hD' : (D : ℝ) ≠ 0 := (Nat.cast_pos.mpr hD).ne'
  have hd' : (dz : ℝ) ≠ 0 := hdz ▸ mul_ne_zero hD' hd
  have hmap : (Matrix.trace ((polynomialWeightedMatrix (dz^2) cz az)^k)).map
      (Int.castRingHom ℝ) =
      ∑ i ∈ Finset.range (6*k+1),
        Polynomial.C ((Nat.choose (6*k) i : ℝ)*((D : ℝ)*a)^i)*
          scaledChebyshev ((D : ℝ)*d) ((D : ℝ)*c) (14*k-i) := by
    change (Polynomial.mapRingHom (Int.castRingHom ℝ))
      (Matrix.trace ((polynomialWeightedMatrix (dz^2) cz az)^k)) = _
    rw [AddMonoidHom.map_trace, Matrix.map_pow, polynomialWeightedMatrix_map]
    simp only [map_pow, Int.coe_castRingHom]
    rw [weightedChebyshev_matrix_trace (dz : ℝ) (cz : ℝ) (az : ℝ) hd' k,
      hdz, hcz, haz]
  rw [weightedChebyshev_scaling (D : ℝ) d c a hD' hd (14*k) (6*k) (by omega)] at hmap
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (14*k-j)) hmap
  simp only [Polynomial.coeff_map, Int.coe_castRingHom, Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff] at hc
  rw [hc]
  have hpow : (D : ℝ)^(14*k) = (D : ℝ)^j*(D : ℝ)^(14*k-j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hpow, inv_pow]
  field_simp
  rfl
theorem integer_matrix_trace_top_coefficient_dvd (k j : ℕ) (hj : j ≤ 14*k)
    (M : Matrix (Fin 2) (Fin 2) (Polynomial ℤ)) :
    (k : ℤ) ∣ (j : ℤ)*(Matrix.trace (M^k)).coeff (14*k-j) := by
  have he := integer_matrix_trace_power_coefficient_dvd (14*k-j) k M
  have hn : (k : ℤ) ∣ ((14*k : ℕ) : ℤ)*(Matrix.trace (M^k)).coeff (14*k-j) := by
    refine ⟨14*(Matrix.trace (M^k)).coeff (14*k-j), ?_⟩
    push_cast
    ring
  have h := dvd_sub hn he
  convert h using 1
  rw [Nat.cast_sub hj]
  ring
theorem weightedChebyshev_initial_integral_progression
    (D : ℕ) (hD : 0 < D) (d c a : ℝ) (hd : d ≠ 0) (dz cz az : ℤ)
    (hdz : (D : ℝ)*d = (dz : ℝ)) (hcz : (D : ℝ)*c = (cz : ℝ))
    (haz : (D : ℝ)*a = (az : ℝ)) (J : ℕ) :
    ∃ K : ℕ, 0 < K ∧ J < K ∧ ∀ l : ℕ, 0 < l → ∀ j : ℕ, j ≤ J →
      ∃ z : ℤ, (∑ i ∈ Finset.range (6*(K*l)+1),
        Polynomial.C ((Nat.choose (6*(K*l)) i : ℝ)*a^i)*
          scaledChebyshev d c (14*(K*l)-i)).coeff (14*(K*l)-j) = (z : ℝ) := by
  let B := J.factorial*D^J
  let K := (J+1)*B
  have hB : 0 < B := Nat.mul_pos (Nat.factorial_pos J) (pow_pos hD J)
  have hK : 0 < K := Nat.mul_pos (by omega) hB
  have hJK : J < K := by dsimp [K]; nlinarith
  refine ⟨K, hK, hJK, ?_⟩
  intro l hl j hj
  let k := K*l
  have hk : 0 < k := Nat.mul_pos hK hl
  have hjn : j ≤ 14*k := by dsimp [k]; nlinarith
  let H := ∑ i ∈ Finset.range (6*k+1),
    Polynomial.C ((Nat.choose (6*k) i : ℝ)*a^i)*scaledChebyshev d c (14*k-i)
  change ∃ z : ℤ, H.coeff (14*k-j) = (z : ℝ)
  by_cases hj0 : j = 0
  · subst j
    refine ⟨1, ?_⟩
    have hh := weightedChebyshev_data d c a (14*k) (6*k) hd (by omega)
    have hmon : H.Monic := hh.1
    have hdeg : H.natDegree = 14*k := hh.2.1
    simpa only [Nat.sub_zero, hdeg, Int.cast_one] using hmon.coeff_natDegree
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hdivB : j*D^j ∣ B :=
      Nat.mul_dvd_mul (Nat.dvd_factorial hjpos hj) (Nat.pow_dvd_pow D hj)
    have hdivk : j*D^j ∣ k := hdivB.trans (by
      dsimp [k, K]
      exact dvd_mul_of_dvd_left (dvd_mul_left B (J+1)) l)
    let N := (Matrix.trace ((polynomialWeightedMatrix (dz^2) cz az)^k)).coeff (14*k-j)
    have hdivN : (k : ℤ) ∣ (j : ℤ)*N :=
      integer_matrix_trace_top_coefficient_dvd k j hjn _
    have hDj : (D : ℤ)^j ∣ N := by
      apply (mul_dvd_mul_iff_left (show (j : ℤ) ≠ 0 by exact_mod_cast hj0)).mp
      exact (by exact_mod_cast hdivk : (j : ℤ)*(D : ℤ)^j ∣ (k : ℤ)).trans hdivN
    obtain ⟨z, hz⟩ := hDj
    refine ⟨z, ?_⟩
    have hscale := integer_weighted_matrix_scaled_coeff D hD d c a hd dz cz az
      hdz hcz haz k j hjn
    change (N : ℝ) = (D : ℝ)^j*H.coeff (14*k-j) at hscale
    have hz' : (N : ℝ) = (D : ℝ)^j*(z : ℝ) := by exact_mod_cast hz
    apply mul_left_cancel₀ (pow_ne_zero j (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)))
    exact hscale.symm.trans hz'
theorem geometric_tail_rounding_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (J m : ℕ) :
    (∑ j ∈ Finset.range (m+1), if J < j then t^j else 0) ≤ t^(J+1)/(1-t) := by
  classical
  rw [← Finset.sum_filter]
  have hset : (Finset.range (m+1)).filter (fun j => J < j) =
      Finset.Ico (J+1) (m+1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset]
  exact geom_sum_Ico_le_of_lt_one ht0 ht1
theorem exists_geometric_tail_rounding_budget (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ m : ℕ,
      (∑ j ∈ Finset.range (m+1), if J < j then t^j else 0) ≤ (1/2 : ℝ) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1-t)/2 by linarith) ht1
  refine ⟨N+1, by omega, fun m => ?_⟩
  apply (geometric_tail_rounding_bound t ht0 ht1 (N+1) m).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-t)).mpr
  have hpow : t^(N+1+1) ≤ t^N := by
    rw [show N+1+1 = N+2 by omega, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg ht0 _) (pow_le_one₀ ht0 ht1.le)
  linarith
theorem weighted_top_block_rounding :
    let u : ℝ := 294811 / 1000000
    let v : ℝ := 1049707 / 500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let c := s^2+r^2
    let A := d^14/s^6
    let R : ℕ → Polynomial ℝ := fun j =>
      Polynomial.C (d^j) * (Polynomial.Chebyshev.C ℝ (j : ℤ)).comp
        (Polynomial.C d⁻¹ * (Polynomial.X - Polynomial.C c))
    let H : ℕ → Polynomial ℝ := fun k => ∑ j ∈ Finset.range (6*k+1),
      Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j) * R (14*k-j)
    ∃ K : ℕ, 0 < K ∧ ∀ l : ℕ, 0 < l → let k := K*l
      ∀ m : ℕ, m < 8*k → ∃ T : Polynomial ℝ,
        T.Monic ∧ T.natDegree = 14*k ∧
        T.coeff (14*k-1) = (H k).coeff (14*k-1) ∧
        (∀ j : ℕ, j ≤ m → ∃ z : ℤ, T.coeff (14*k-j) = (z : ℝ)) ∧
        ∀ x : ℝ, x ∈ Set.Icc (u^2) (v^2) →
          |T.eval x-(H k).eval x| ≤ (1/2 : ℝ)*A^k*x^(3*k) := by
  intro u v s r d c A R H
  have hr : 0 < r := by norm_num [r, u, v]
  have hrs : r < s := by norm_num [r, s, u, v]
  have hs : 0 < s := hr.trans hrs
  have hd : 1 < d := by norm_num [d, s, r, u, v]
  have hd0 : 0 < d := lt_trans zero_lt_one hd
  have hdz : (4000000000000 : ℝ)*d = (4320625617675 : ℤ) := by
    norm_num [d, s, r, u, v]
  have hcz : (4000000000000 : ℝ)*c = (8988905338234 : ℤ) := by
    norm_num [c, s, r, u, v]
  have haz : (4000000000000 : ℝ)*r^2 = (3256591987609 : ℤ) := by
    norm_num [r, u, v]
  obtain ⟨J, hJ, hbudget⟩ := exists_geometric_tail_rounding_budget d⁻¹
    (inv_nonneg.mpr hd0.le) (inv_lt_one_of_one_lt₀ hd)
  obtain ⟨K, hK, _, hinit⟩ := weightedChebyshev_initial_integral_progression
    4000000000000 (by norm_num) d c (r^2) hd0.ne'
    4320625617675 8988905338234 3256591987609 hdz hcz haz J
  refine ⟨K, hK, ?_⟩
  intro l hl k m hm
  have hk : 0 < k := Nat.mul_pos hK hl
  have hdata := weightedChebyshev_data d c (r^2) (14*k) (6*k) hd0.ne' (by omega)
  have hmon : (H k).Monic := hdata.1
  have hdeg : (H k).natDegree = 14*k := hdata.2.1
  let Q : ℕ → Polynomial ℝ := fun j => ∑ i ∈ Finset.range (6*k+1),
    Polynomial.C ((Nat.choose (6*k) i : ℝ)*(r^2)^i)*
      scaledChebyshev d c (14*k-j-i)
  have hQ : ∀ j, J < j → j < 8*k → (Q j).Monic ∧ (Q j).natDegree = 14*k-j := by
    intro j _ hj
    exact weightedChebyshev_shifted_data s r hr hrs k j hj
  have hinit' : ∀ j, j ≤ J → ∃ z : ℤ, (H k).coeff (14*k-j) = (z : ℝ) := by
    intro j hj
    exact hinit l hl j hj
  have hleft : s-r = u := by dsimp [s, r]; ring
  have hright : s+r = v := by dsimp [s, r]; ring
  have hbound : ∀ j, J < j → j < 8*k → ∀ x ∈ Set.Icc (u^2) (v^2),
      |(Q j).eval x| ≤ 2*(d⁻¹)^j*(A^k*x^(3*k)) := by
    intro j _ hj x hx
    have hx' : x ∈ Set.Icc ((s-r)^2) ((s+r)^2) := by
      simpa only [hleft, hright] using hx
    simpa only [mul_assoc] using
      weightedChebyshev_shifted_eval_bound s r hr hrs k j hj x hx'
  obtain ⟨T, hT, hTd, hTtrace, hTint, hTerr⟩ :=
    exists_top_block_rounding_of_initial_integrality_up_to (14*k) J (8*k)
      (by omega) hJ (H k) hmon hdeg Q hQ hinit' d⁻¹
      (Set.Icc (u^2) (v^2)) (fun x => A^k*x^(3*k)) hbound m hm
  refine ⟨T, hT, hTd, hTtrace, hTint, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := (sq_nonneg u).trans hx.1
  have hW : 0 ≤ A^k*x^(3*k) := by dsimp [A]; positivity
  calc
    _ ≤ (∑ j ∈ Finset.range (m+1), if J < j then (d⁻¹)^j else 0)*
        (A^k*x^(3*k)) := hTerr x hx
    _ ≤ (1/2 : ℝ)*(A^k*x^(3*k)) := mul_le_mul_of_nonneg_right (hbudget m) hW
    _ = _ := by ring
theorem integer_polynomial_coefficient_matrix_isUnit (D : ℕ)
    (q : Fin D → Polynomial ℤ)
    (hq : LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)))
    (hdeg : ∀ i, (q i).natDegree < D) :
    IsUnit (show Matrix (Fin D) (Fin D) ℝ from fun i j => ((q i).coeff j : ℝ)) := by
  classical
  let M : Matrix (Fin D) (Fin D) ℚ := fun i j => ((q i).coeff j : ℚ)
  have hrows : LinearIndependent ℚ M.row := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    apply (Fintype.linearIndependent_iff.mp hq a ?_) i
    ext j
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
      Polynomial.coeff_map, Int.coe_castRingHom, smul_eq_mul, Polynomial.coeff_zero]
    by_cases hj : j < D
    · have h := congrFun ha (⟨j, hj⟩ : Fin D)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Matrix.row, M] using h
    · apply Finset.sum_eq_zero
      intro i _
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_le (by omega)),
        Int.cast_zero, mul_zero]
  have hM : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp hM |>.ne_zero
  let N : Matrix (Fin D) (Fin D) ℝ := fun i j => ((q i).coeff j : ℝ)
  apply (Matrix.isUnit_iff_isUnit_det N).mpr
  apply isUnit_iff_ne_zero.mpr
  have hmap : M.map (fun x : ℚ => (x : ℝ)) = N := by
    funext i j
    change (((q i).coeff j : ℚ) : ℝ) = ((q i).coeff j : ℝ)
    exact Rat.cast_intCast _
  rw [← hmap, ← Rat.cast_det]
  exact_mod_cast hdet
theorem exists_real_coordinates_of_integer_polynomials (D : ℕ)
    (q : Fin D → Polynomial ℤ)
    (hq : LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)))
    (hdeg : ∀ i, (q i).natDegree < D) (P : Polynomial ℝ)
    (hP : ∀ j : ℕ, D ≤ j → P.coeff j = 0) :
    ∃ a : Fin D → ℝ,
      P = ∑ i : Fin D, Polynomial.C (a i)*(q i).map (Int.castRingHom ℝ) := by
  classical
  let M : Matrix (Fin D) (Fin D) ℝ := fun i j => ((q i).coeff j : ℝ)
  have hM : IsUnit M := integer_polynomial_coefficient_matrix_isUnit D q hq hdeg
  obtain ⟨a, ha⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hM)
    (fun j : Fin D => P.coeff j)
  refine ⟨a, ?_⟩
  ext j
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_map, Int.coe_castRingHom]
  by_cases hj : j < D
  · exact (congrFun ha (⟨j, hj⟩ : Fin D)).symm
  · rw [hP j (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_le (by omega)),
      Int.cast_zero, mul_zero]
theorem exists_integer_polynomial_with_integral_top_block
    (n D : ℕ) (T : Polynomial ℝ) (hdeg : T.natDegree ≤ n)
    (htop : ∀ i : ℕ, D ≤ i → ∃ z : ℤ, T.coeff i = (z : ℝ)) :
    ∃ p : Polynomial ℤ, p.natDegree ≤ n ∧
      ∀ i : ℕ, D ≤ i → ((p.coeff i : ℤ) : ℝ) = T.coeff i := by
  classical
  let z : ℕ → ℤ := fun i => if h : D ≤ i then Classical.choose (htop i h) else 0
  let p : Polynomial ℤ := Polynomial.ofFn (n+1) (fun i => z i)
  have hpdeg : p.natDegree ≤ n := by
    have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ n+1)
      (fun i : Fin (n+1) => z i)
    exact Nat.le_of_lt_succ h
  refine ⟨p, hpdeg, ?_⟩
  intro i hi
  by_cases hin : i < n+1
  · rw [show p.coeff i = z i from Polynomial.ofFn_coeff_eq_val_of_lt _ hin]
    dsimp [z]
    rw [dite_eq_left hi]
    exact (Classical.choose_spec (htop i hi)).symm
  · rw [show p.coeff i = 0 from Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),
      Int.cast_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
theorem exists_integer_approximation_with_integral_top_block
    (n D : ℕ) (T : Polynomial ℝ) (hdeg : T.natDegree ≤ n)
    (htop : ∀ i : ℕ, D ≤ i → ∃ z : ℤ, T.coeff i = (z : ℝ))
    (q : Fin D → Polynomial ℤ)
    (hq : LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)))
    (hqdeg : ∀ i, (q i).natDegree < D) :
    ∃ p : Polynomial ℤ,
      (∀ i : ℕ, D ≤ i → ((p.coeff i : ℤ) : ℝ) = T.coeff i) ∧
      ∀ x : ℝ, |(p.map (Int.castRingHom ℝ)).eval x-T.eval x| ≤
        (1/2 : ℝ)*∑ i : Fin D, |Polynomial.aeval x (q i)| := by
  classical
  obtain ⟨r, _, hrtop⟩ := exists_integer_polynomial_with_integral_top_block n D T hdeg htop
  let P := T-r.map (Int.castRingHom ℝ)
  have hP : ∀ j : ℕ, D ≤ j → P.coeff j = 0 := by
    intro j hj
    simp only [P, Polynomial.coeff_sub, Polynomial.coeff_map, Int.coe_castRingHom,
      hrtop j hj, sub_self]
  obtain ⟨a, ha⟩ := exists_real_coordinates_of_integer_polynomials D q hq hqdeg P hP
  have hT : T = r.map (Int.castRingHom ℝ) +
      ∑ i : Fin D, Polynomial.C (a i)*(q i).map (Int.castRingHom ℝ) := by
    rw [← ha]
    dsimp [P]
    ring
  let p := r+∑ i : Fin D, Polynomial.C (round (a i))*q i
  refine ⟨p, ?_, ?_⟩
  · intro j hj
    have hz : (∑ i : Fin D, Polynomial.C (round (a i))*q i).coeff j = 0 := by
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
      apply Finset.sum_eq_zero
      intro i _
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hqdeg i).trans_le hj), mul_zero]
    simpa only [p, Polynomial.coeff_add, hz, add_zero] using hrtop j hj
  · intro x
    have heval : T.eval x-(p.map (Int.castRingHom ℝ)).eval x =
        ∑ i : Fin D, (a i-(round (a i) : ℤ))*
          ((q i).map (Int.castRingHom ℝ)).eval x := by
      rw [hT]
      simp only [p, Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, Int.coe_castRingHom]
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [abs_sub_comm, heval]
    simpa only [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_int_eq] using finite_rounding_error_bound Finset.univ a
      (fun i => ((q i).map (Int.castRingHom ℝ)).eval x)
theorem integral_top_block_short_basis_realization :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ (n D : ℕ), 0 < D → D < n → ∀ (T H : Polynomial ℝ),
      T.Monic → T.natDegree = n →
      (∀ i : ℕ, D ≤ i → ∃ z : ℤ, T.coeff i = (z : ℝ)) →
      ∀ q : Fin D → Polynomial ℤ,
      LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)) →
      (∀ i, (q i).natDegree < D) → ∀ x : Fin (n+1) → ℝ,
      StrictMono x → (∀ j, 0 < x j) →
      (∀ i : Fin n, H.eval (x i.castSucc)*H.eval (x i.succ) < 0) →
      (∀ j : Fin (n+1), |T.eval (x j)-H.eval (x j)| +
        (1/2 : ℝ)*(∑ i : Fin D, |Polynomial.aeval (x j) (q i)|) < |H.eval (x j)|) →
      ∃ p : Polynomial ℤ, p.Monic ∧ p.natDegree = n ∧
        ((p.coeff (n-1) : ℤ) : ℝ) = T.coeff (n-1) ∧ Squarefree p ∧
        ∀ z : ℂ, z ∈ p.aroots ℂ → 0 < z := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  classical
  intro n D hD hDn T H hT hTd htop q hq hqdeg x hx hxpos halt hbudget
  obtain ⟨p, hptop, hperr⟩ := exists_integer_approximation_with_integral_top_block
    n D T hTd.le htop q hq hqdeg
  have hple : p.natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have h : ((p.coeff i : ℤ) : ℝ) = 0 := by
      rw [hptop i (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact_mod_cast h
  have hpn : p.coeff n = 1 := by
    have h : ((p.coeff n : ℤ) : ℝ) = 1 := by
      rw [hptop n hDn.le]
      simpa only [hTd] using hT.coeff_natDegree
    exact_mod_cast h
  have hp : p.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hple hpn
  have hpd : p.natDegree = n := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hple
    (by rw [hpn]; exact one_ne_zero)
  have herr : ∀ j : Fin (n+1),
      |(p.map (Int.castRingHom ℝ)).eval (x j)-H.eval (x j)| < |H.eval (x j)| := by
    intro j
    calc
      _ ≤ |(p.map (Int.castRingHom ℝ)).eval (x j)-T.eval (x j)| +
          |T.eval (x j)-H.eval (x j)| := abs_sub_le _ _ _
      _ ≤ (1/2 : ℝ)*(∑ i : Fin D, |Polynomial.aeval (x j) (q i)|) +
          |T.eval (x j)-H.eval (x j)| := add_le_add (hperr (x j)) le_rfl
      _ < _ := by simpa only [add_comm] using hbudget j
  have hsign : ∀ j : Fin (n+1),
      0 < H.eval (x j)*(p.map (Int.castRingHom ℝ)).eval (x j) := by
    intro j
    exact same_sign_of_abs_sub_lt _ _ (herr j)
  have hpalt : ∀ i : Fin n,
      (p.map (Int.castRingHom ℝ)).eval (x i.castSucc)*
        (p.map (Int.castRingHom ℝ)).eval (x i.succ) < 0 := by
    intro i
    have hmul := mul_pos (hsign i.castSucc) (hsign i.succ)
    have hreorder :
        (H.eval (x i.castSucc)*(p.map (Int.castRingHom ℝ)).eval (x i.castSucc))*
          (H.eval (x i.succ)*(p.map (Int.castRingHom ℝ)).eval (x i.succ)) =
        (H.eval (x i.castSucc)*H.eval (x i.succ))*
          ((p.map (Int.castRingHom ℝ)).eval (x i.castSucc)*
            (p.map (Int.castRingHom ℝ)).eval (x i.succ)) := by ring
    rw [hreorder] at hmul
    exact neg_of_mul_pos_right hmul (halt i).le
  obtain ⟨hsq, hpos⟩ := squarefree_positive_of_alternating_eval n p x hp hpd hx hxpos hpalt
  exact ⟨p, hp, hpd, hptop (n-1) (by omega), hsq, hpos⟩
theorem nearby_weighted_potential_margins :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    ∀ t : ℝ, 3/14 ≤ t → t ≤ 3/14+1/10000000 →
      1/10000000 < Real.log d-2*t*Real.log s ∧
      1/10000000 < 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s) := by
  intro u v s r d t ht0 ht1
  let A := d^14/s^6
  let B := s^8*(u*v)^3
  have hs : 0 < s := by norm_num [s, u, v]
  have hd : 0 < d := by norm_num [d, s, r, u, v]
  have huv : 0 < u*v := by norm_num [u, v]
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hArat : (56:ℝ)/10000000 < 1-A⁻¹ := by norm_num [A, d, s, r, u, v]
  have hBrat : (105:ℝ)/10000000 < 1-B⁻¹ := by norm_num [B, s, u, v]
  have hC0 : (4:ℝ)/10000000 < Real.log A/14 := by
    have h := Real.one_sub_inv_le_log_of_pos hA
    linarith
  have hL0 : (15:ℝ)/10000000 < Real.log B/7 := by
    have h := Real.one_sub_inv_le_log_of_pos hB
    linarith
  have hslog : Real.log s ≤ 1/5 := by
    have h := Real.log_le_sub_one_of_pos hs
    have hr : s-1 ≤ (1:ℝ)/5 := by norm_num [s, u, v]
    exact h.trans hr
  have huvlog : -1 ≤ Real.log (u*v) := by
    have h := Real.one_sub_inv_le_log_of_pos huv
    have hr : (-1:ℝ) ≤ 1-(u*v)⁻¹ := by norm_num [u, v]
    exact hr.trans h
  have hCeq : Real.log A/14 = Real.log d-2*(3/14)*Real.log s := by
    dsimp [A]
    rw [Real.log_div (pow_ne_zero 14 hd.ne') (pow_ne_zero 6 hs.ne'),
      Real.log_pow, Real.log_pow]
    ring
  have hLeq : Real.log B/7 =
      2*Real.log s+2*(3/14)*(Real.log (u*v)-2*Real.log s) := by
    dsimp [B]
    rw [Real.log_mul (pow_ne_zero 8 hs.ne') (pow_ne_zero 3 huv.ne'),
      Real.log_pow, Real.log_pow]
    ring
  have ht : 0 ≤ t-3/14 := by linarith
  have hct := mul_nonneg ht (sub_nonneg.mpr hslog)
  have hlt := mul_nonneg ht (show 0 ≤ Real.log (u*v)-2*Real.log s+7/5 by linarith)
  constructor <;> nlinarith
theorem poisson_log_distance_exterior (w : ℂ) (h : ℝ)
    (hw : 1 < ‖w‖) (hh : |h| < 1) :
    Real.circleAverage (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) 0 1 =
      Real.log ‖w+(h : ℂ)‖ := by
  have hf : InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => Real.log ‖w-z‖) (Metric.closedBall 0 1) := by
    intro z hz
    apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
    intro heq
    have heq' : w = z := sub_eq_zero.mp heq
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    exact (not_lt_of_ge hz') (heq' ▸ hw)
  have hh' : -(h : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simpa using hh
  have heq := hf.circleAverage_poissonKernel_smul hh'
  change Real.circleAverage (fun z : ℂ =>
    poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) 0 1 = _ at heq
  simpa only [sub_neg_eq_add] using heq
theorem poisson_log_distance_boundary (w : ℂ) (h : ℝ)
    (hw : ‖w‖ = 1) (hh : |h| < 1) :
    Real.circleAverage (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) 0 1 =
      Real.log ‖w+(h : ℂ)‖ := by
  have hh' : -(h : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simpa using hh
  have hw' : w ∈ Metric.sphere (0 : ℂ) 1 := by simpa using hw
  have heq := circleAverage_re_herglotzRieszKernel_mul_log hw' hh'
  rw [← poissonKernel_eq_re_herglotzRieszKernel] at heq
  change Real.circleAverage (fun z : ℂ =>
    poissonKernel 0 (-(h : ℂ)) z * Real.log ‖z-w‖) 0 1 = _ at heq
  simpa only [norm_sub_rev, sub_neg_eq_add] using heq
theorem poisson_log_distance_closed_exterior (w : ℂ) (h : ℝ)
    (hw : 1 ≤ ‖w‖) (hh : |h| < 1) :
    Real.circleAverage (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) 0 1 =
      Real.log ‖w+(h : ℂ)‖ := by
  rcases hw.eq_or_lt with heq | hlt
  · exact poisson_log_distance_boundary w h heq.symm hh
  · exact poisson_log_distance_exterior w h hlt hh
theorem poisson_weight_log_circleIntegrable (w : ℂ) (h : ℝ) (hh : |h| < 1) :
    CircleIntegrable (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) 0 1 := by
  have hn : -(h : ℂ) ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa using ne_of_lt hh
  have hK : ContinuousOn (poissonKernel 0 (-(h : ℂ)))
      (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hn)
  have hlog : CircleIntegrable (fun z : ℂ => Real.log ‖w-z‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop)
  exact hlog.continuousOn_mul hK
theorem poissonKernel_circleAverage (h : ℝ) (hh : |h| < 1) :
    Real.circleAverage (poissonKernel 0 (-(h : ℂ))) 0 1 = 1 := by
  have hh' : -(h : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simpa using hh
  have heq := (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)
    (s := Metric.closedBall (0 : ℂ) 1)).circleAverage_poissonKernel_smul hh'
  change Real.circleAverage (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z * 1) 0 1 = 1 at heq
  simpa only [mul_one] using heq
theorem fixed_tilt_strict_margins :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let t : ℝ := 3000000/13999999
    1/10000000 < Real.log d-2*t*Real.log s ∧
      1/10000000 < 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s) := by
  exact nearby_weighted_potential_margins (3000000/13999999) (by norm_num) (by norm_num)
theorem intervalIntegrable_log_cos (z : ℂ) (c d : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖z-((c+2*d*Real.cos θ : ℝ) : ℂ)‖)
      MeasureTheory.volume 0 (2*Real.pi) := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro θ hθ
  have hcos : AnalyticAt ℝ (fun θ : ℝ => c+2*d*Real.cos θ) θ := by fun_prop
  exact (analyticAt_const.sub ((Complex.ofRealCLM.analyticAt _).comp hcos)).meromorphicAt
theorem poissonKernel_continuousOn_unit (h : ℝ) (hh : |h| < 1) :
    ContinuousOn (poissonKernel 0 (-(h : ℂ))) (Metric.sphere (0 : ℂ) 1) := by
  have hn : -(h : ℂ) ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa using ne_of_lt hh
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simpa using Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hn)
theorem poissonKernel_pos_unit (h : ℝ) (hh : |h| < 1)
    (z : ℂ) (hz : ‖z‖ = 1) : 0 < poissonKernel 0 (-(h : ℂ)) z := by
  have hne : z+(h : ℂ) ≠ 0 := by
    intro heq
    have heq' : z = -(h : ℂ) := eq_neg_of_add_eq_zero_left heq
    have : ‖z‖ = |h| := by rw [heq']; simp
    linarith
  have hh0 := (abs_lt.mp hh).1
  have hh1 := (abs_lt.mp hh).2
  have hnum : 0 < 1-h^2 := by nlinarith
  simp only [poissonKernel_def, sub_zero, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, hz, one_pow, sq_abs, sub_neg_eq_add]
  exact div_pos hnum (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))
noncomputable def poissonAngleWeight (h t θ : ℝ) : ℝ :=
  (1-t)+t*poissonKernel 0 (-(h : ℂ)) (circleMap 0 1 θ)
theorem continuous_poissonAngleWeight (h t : ℝ) (hh : |h| < 1) :
    Continuous (poissonAngleWeight h t) := by
  have hP : Continuous (fun θ : ℝ =>
      poissonKernel 0 (-(h : ℂ)) (circleMap 0 1 θ)) :=
    (poissonKernel_continuousOn_unit h hh).comp_continuous
      (continuous_circleMap 0 1) (by intro θ; simp)
  exact continuous_const.add (continuous_const.mul hP)
theorem poissonAngleWeight_nonneg (h t : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (θ : ℝ) : 0 ≤ poissonAngleWeight h t θ := by
  exact add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0
    (poissonKernel_pos_unit h hh _ (by simp)).le)
theorem poissonAngleWeight_integral (h t : ℝ) (hh : |h| < 1) :
    (2*Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2*Real.pi, poissonAngleWeight h t θ = 1 := by
  have hP : CircleIntegrable (poissonKernel 0 (-(h : ℂ))) 0 1 :=
    (by simpa using poissonKernel_continuousOn_unit h hh :
      ContinuousOn (poissonKernel 0 (-(h : ℂ))) (Metric.sphere (0 : ℂ) |(1 : ℝ)|)).circleIntegrable'
  have hAvg := Real.circleAverage_fun_add (circleIntegrable_const (1-t) 0 1)
    (hP.const_smul (a := t))
  change Real.circleAverage (fun z : ℂ =>
    (1-t)+t*poissonKernel 0 (-(h : ℂ)) z) 0 1 = _ at hAvg
  change Real.circleAverage (fun z : ℂ => (1-t)+t*poissonKernel 0 (-(h : ℂ)) z) 0 1 = 1
  simpa only [Real.circleAverage_const, Real.circleAverage_smul, smul_eq_mul,
    poissonKernel_circleAverage h hh, mul_one, sub_add_cancel] using hAvg
noncomputable def poissonAngleDensity (h t θ : ℝ) : ℝ :=
  (2*Real.pi)⁻¹ * poissonAngleWeight h t θ
noncomputable def poissonAngleMeasure (h t : ℝ) : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioc 0 (2*Real.pi))).withDensity
    (fun θ => ENNReal.ofReal (poissonAngleDensity h t θ))
theorem continuous_poissonAngleDensity (h t : ℝ) (hh : |h| < 1) :
    Continuous (poissonAngleDensity h t) :=
  continuous_const.mul (continuous_poissonAngleWeight h t hh)
theorem poissonAngleDensity_nonneg (h t : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (θ : ℝ) : 0 ≤ poissonAngleDensity h t θ :=
  mul_nonneg (by positivity) (poissonAngleWeight_nonneg h t hh ht0 ht1 θ)
theorem poissonAngleDensity_integral (h t : ℝ) (hh : |h| < 1) :
    ∫ θ in Set.Ioc 0 (2*Real.pi), poissonAngleDensity h t θ = 1 := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]
  change (∫ θ in (0 : ℝ)..2*Real.pi, (2*Real.pi)⁻¹*poissonAngleWeight h t θ) = 1
  rw [intervalIntegral.integral_const_mul]
  exact poissonAngleWeight_integral h t hh
theorem poissonAngleMeasure_probability (h t : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (poissonAngleMeasure h t) := by
  constructor
  rw [poissonAngleMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [MeasureTheory.Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [poissonAngleDensity_integral h t hh]
    simp
  · exact (continuous_poissonAngleDensity h t hh).continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
  · exact Filter.Eventually.of_forall (poissonAngleDensity_nonneg h t hh ht0 ht1)
noncomputable def poissonCosMeasure (h t c d : ℝ) : MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map (fun θ : ℝ => c+2*d*Real.cos θ) (poissonAngleMeasure h t)
theorem poissonCosMeasure_probability (h t c d : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MeasureTheory.IsProbabilityMeasure (poissonCosMeasure h t c d) := by
  let := poissonAngleMeasure_probability h t hh ht0 ht1
  unfold poissonCosMeasure
  infer_instance
theorem poissonCosMeasure_support (h t c d : ℝ) (hd : 0 ≤ d) :
    poissonCosMeasure h t c d (Set.Icc (c-2*d) (c+2*d))ᶜ = 0 := by
  rw [poissonCosMeasure, MeasureTheory.Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  have he : (fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' (Set.Icc (c-2*d) (c+2*d))ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro θ hθ
    have hlow := Real.neg_one_le_cos θ
    have hupp := Real.cos_le_one θ
    apply hθ
    constructor <;> nlinarith
  rw [he]
  exact MeasureTheory.measure_empty
theorem poissonCosMeasure_log_integrable (h t c d : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : ℂ) :
    MeasureTheory.Integrable (fun x : ℝ => Real.log ‖z-(x : ℂ)‖)
      (poissonCosMeasure h t c d) := by
  have hm : Measurable (fun x : ℝ => Real.log ‖z-(x : ℂ)‖) := by fun_prop
  rw [poissonCosMeasure, MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
    (by fun_prop)]
  rw [poissonAngleMeasure, MeasureTheory.integrable_withDensity_iff
    (by exact ENNReal.measurable_ofReal.comp (continuous_poissonAngleDensity h t hh).measurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal
    (poissonAngleDensity_nonneg h t hh ht0 ht1 _)]
  have hi := (intervalIntegrable_log_cos z c d).mul_continuousOn
    (continuous_poissonAngleDensity h t hh).continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp hi
theorem cosine_fiber_countable (c d y : ℝ) (hd : d ≠ 0) :
    Set.Countable {θ : ℝ | c+2*d*Real.cos θ = y} := by
  by_cases he : Set.Nonempty {θ : ℝ | c+2*d*Real.cos θ = y}
  · obtain ⟨θ₀, hθ₀⟩ := he
    apply ((Set.countable_range (fun k : ℤ => θ₀-2*(k : ℝ)*Real.pi)).union
      (Set.countable_range (fun k : ℤ => 2*(k : ℝ)*Real.pi-θ₀))).mono
    intro θ hθ
    have hcos : Real.cos θ = Real.cos θ₀ := by
      dsimp at hθ hθ₀
      apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hd))
      linarith
    obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hcos
    · exact Or.inl ⟨k, by linarith⟩
    · exact Or.inr ⟨k, by linarith⟩
  · exact Set.countable_empty.mono (Set.not_nonempty_iff_eq_empty.mp he ▸ Set.Subset.rfl)
theorem poissonCosMeasure_atomless (h t c d : ℝ) (hd : d ≠ 0) :
    MeasureTheory.NullSingletonClass (poissonCosMeasure h t c d) := by
  constructor
  intro y
  rw [poissonCosMeasure, MeasureTheory.Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hz : MeasureTheory.volume {θ : ℝ | c+2*d*Real.cos θ = y} = 0 :=
    (cosine_fiber_countable c d y hd).measure_zero _
  apply MeasureTheory.withDensity_absolutelyContinuous _ _
  exact MeasureTheory.Measure.absolutelyContinuous_restrict hz
theorem poissonCosMeasure_integral (h t c d : ℝ) (hh : |h| < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (f : ℝ → ℝ) (hf : Measurable f) :
    MeasureTheory.integral (poissonCosMeasure h t c d) f =
      (2*Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2*Real.pi,
        poissonAngleWeight h t θ * f (c+2*d*Real.cos θ) := by
  rw [poissonCosMeasure, MeasureTheory.integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [poissonAngleMeasure, integral_withDensity_eq_integral_toReal_smul
    (f := fun θ => ENNReal.ofReal (poissonAngleDensity h t θ))
    (by exact ENNReal.measurable_ofReal.comp (continuous_poissonAngleDensity h t hh).measurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (poissonAngleDensity_nonneg h t hh ht0 ht1 _)]
  simp only [smul_eq_mul, poissonAngleDensity, mul_assoc]
  rw [MeasureTheory.integral_const_mul,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
theorem poissonKernel_inv_unit (h : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    poissonKernel 0 (-(h : ℂ)) z⁻¹ = poissonKernel 0 (-(h : ℂ)) z := by
  have hn : ‖z⁻¹+(h : ℂ)‖ = ‖z+(h : ℂ)‖ := by
    rw [Complex.inv_eq_conj hz]
    calc
      _ = ‖(starRingEnd ℂ) (z+(h : ℂ))‖ := by congr 1; simp
      _ = _ := Complex.norm_conj _
  simp only [poissonKernel_def, sub_zero, norm_inv, hz, inv_one, sub_neg_eq_add, hn]
theorem poisson_log_distance_inv (w : ℂ) (h : ℝ) (hw : 1 ≤ ‖w‖) (hh : |h| < 1) :
    Real.circleAverage (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z⁻¹‖) 0 1 =
      Real.log ‖w+(h : ℂ)‖ := by
  calc
    _ = Real.circleAverage ((fun z : ℂ =>
        poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖) ∘ Inv.inv) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz' : ‖z‖ = 1 := by simpa using hz
      dsimp only [Function.comp_apply]
      rw [poissonKernel_inv_unit h z hz']
    _ = _ := (Real.circleAverage_zero_one_congr_inv (f := fun z : ℂ =>
        poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z‖)).trans
      (poisson_log_distance_closed_exterior w h hw hh)
theorem joukowski_difference_factor (d : ℝ) (w z : ℂ) (hw : w ≠ 0) (hz : z ≠ 0) :
    (d : ℂ)*(w+w⁻¹-z-z⁻¹) = (d : ℂ)/w*(w-z)*(w-z⁻¹) := by
  field_simp; ring
theorem log_joukowski_difference (d : ℝ) (w z : ℂ) (hd : d ≠ 0)
    (hw : w ≠ 0) (hz : z ≠ 0) (hwz : w-z ≠ 0) (hwzi : w-z⁻¹ ≠ 0) :
    Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖ =
      Real.log |d|-Real.log ‖w‖+Real.log ‖w-z‖+Real.log ‖w-z⁻¹‖ := by
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hdiv := div_ne_zero hd' hw
  rw [joukowski_difference_factor d w z hw hz, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (mul_ne_zero hdiv hwz)) (norm_ne_zero_iff.mpr hwzi),
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hdiv) (norm_ne_zero_iff.mpr hwz),
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hd') (norm_ne_zero_iff.mpr hw),
    Complex.norm_real, Real.norm_eq_abs]
theorem poisson_joukowski_log_average (d h : ℝ) (w : ℂ) (hd : d ≠ 0)
    (hh : |h| < 1) (hw : 1 ≤ ‖w‖) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z *
      Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖) 0 1 =
      Real.log |d|+2*Real.log ‖w+(h : ℂ)‖-Real.log ‖w‖ := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
  have hP : CircleIntegrable (poissonKernel 0 (-(h : ℂ))) 0 1 :=
    (by simpa using poissonKernel_continuousOn_unit h hh :
      ContinuousOn (poissonKernel 0 (-(h : ℂ))) (Metric.sphere (0 : ℂ) |(1 : ℝ)|)).circleIntegrable'
  have hK : ContinuousOn (poissonKernel 0 (-(h : ℂ)))
      (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa using poissonKernel_continuousOn_unit h hh
  let l := Real.log |d|-Real.log ‖w‖
  have hc : CircleIntegrable (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*l) 0 1 := by
    have hc' : CircleIntegrable (fun z : ℂ => l*poissonKernel 0 (-(h : ℂ)) z) 0 1 :=
      hP.const_smul (a := l)
    simpa only [mul_comm] using hc'
  have h1 := poisson_weight_log_circleIntegrable w h hh
  have h2 : CircleIntegrable (fun z : ℂ =>
      poissonKernel 0 (-(h : ℂ)) z * Real.log ‖w-z⁻¹‖) 0 1 :=
    (MeromorphicOn.circleIntegrable_log_norm (f := fun z : ℂ => w-z⁻¹)
      (fun _ _ => by fun_prop)).continuousOn_mul hK
  have he : (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z *
        Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖) =ᶠ[Filter.codiscreteWithin
        (Metric.sphere (0 : ℂ) |(1 : ℝ)|)]
      (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*l+
        poissonKernel 0 (-(h : ℂ)) z*Real.log ‖w-z‖+
        poissonKernel 0 (-(h : ℂ)) z*Real.log ‖w-z⁻¹‖) := by
    filter_upwards [Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |(1 : ℝ)|),
      compl_singleton_mem_codiscreteWithin w,
      compl_singleton_mem_codiscreteWithin w⁻¹] with z hz hzw hzi
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz1
    have hwz : w-z ≠ 0 := by simpa [sub_eq_zero, eq_comm] using hzw
    have hwzi : w-z⁻¹ ≠ 0 := by
      intro h
      have heq := sub_eq_zero.mp h
      apply hzi
      change z = w⁻¹
      rw [heq, inv_inv]
    rw [log_joukowski_difference d w z hd hw0 hz0 hwz hwzi]
    dsimp [l]
    ring
  have hca : Real.circleAverage (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*l) 0 1 = l := by
    calc
      _ = Real.circleAverage (l • poissonKernel 0 (-(h : ℂ))) 0 1 := by
        congr 1
        ext z
        simp [mul_comm]
      _ = _ := by rw [Real.circleAverage_smul, poissonKernel_circleAverage h hh]; simp
  rw [Real.circleAverage_congr_codiscreteWithin he (by norm_num)]
  rw [Real.circleAverage_fun_add
    (f₁ := fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*l+
      poissonKernel 0 (-(h : ℂ)) z*Real.log ‖w-z‖)
    (f₂ := fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*Real.log ‖w-z⁻¹‖)
    (hc.add h1) h2,
    Real.circleAverage_fun_add hc h1, hca,
    poisson_log_distance_closed_exterior w h hw hh, poisson_log_distance_inv w h hw hh]
  dsimp [l]
  ring
theorem joukowski_log_average (d : ℝ) (w : ℂ) (hd : d ≠ 0)
    (hw : 1 ≤ ‖w‖) :
    Real.circleAverage (fun z : ℂ =>
      Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖) 0 1 =
      Real.log |d|+Real.log ‖w‖ := by
  have h := poisson_joukowski_log_average d 0 w hd (by norm_num) hw
  have he : Real.circleAverage (fun z : ℂ => poissonKernel 0 (-(0 : ℂ)) z *
      Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖) 0 1 =
      Real.circleAverage (fun z : ℂ =>
      Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz' : ‖z‖ = 1 := by simpa using hz
    simp [poissonKernel_def, hz']
  simp only [Complex.ofReal_zero, add_zero] at h
  rw [he] at h
  linarith
theorem circleMap_add_inv (θ : ℝ) :
    circleMap 0 1 θ+(circleMap 0 1 θ)⁻¹ = ((2*Real.cos θ : ℝ) : ℂ) := by
  simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
  rw [← circle_exp_conj θ]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_re]
    ring
  · simp
theorem poissonCosMeasure_joukowski_potential (h t c d : ℝ) (w : ℂ)
    (hd : d ≠ 0) (hh : |h| < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : 1 ≤ ‖w‖) :
    (∫ x : ℝ, Real.log ‖(c : ℂ)+(d : ℂ)*(w+w⁻¹)-(x : ℂ)‖
      ∂poissonCosMeasure h t c d) =
      Real.log |d|+(1-2*t)*Real.log ‖w‖+2*t*Real.log ‖w+(h : ℂ)‖ := by
  let f : ℂ → ℝ := fun z => Real.log ‖(d : ℂ)*(w+w⁻¹-z-z⁻¹)‖
  have hf : CircleIntegrable f 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop)
  have hP : ContinuousOn (poissonKernel 0 (-(h : ℂ)))
      (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa using poissonKernel_continuousOn_unit h hh
  have hPf : CircleIntegrable (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*f z) 0 1 :=
    hf.continuousOn_mul hP
  have he : (∫ x : ℝ, Real.log ‖(c : ℂ)+(d : ℂ)*(w+w⁻¹)-(x : ℂ)‖
      ∂poissonCosMeasure h t c d) =
      Real.circleAverage (fun z : ℂ => (1-t)*f z+
        t*(poissonKernel 0 (-(h : ℂ)) z*f z)) 0 1 := by
    rw [poissonCosMeasure_integral h t c d hh ht0 ht1 _ (by fun_prop)]
    rw [Real.circleAverage_def]
    simp only [smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    have heq : (c : ℂ)+(d : ℂ)*(w+w⁻¹)-((c+2*d*Real.cos θ : ℝ) : ℂ) =
        (d : ℂ)*(w+w⁻¹-circleMap 0 1 θ-(circleMap 0 1 θ)⁻¹) := by
      rw [sub_sub, circleMap_add_inv]
      push_cast
      ring
    dsimp only
    rw [heq]
    dsimp [poissonAngleWeight, f]
    ring
  rw [he, Real.circleAverage_fun_add
    (f₁ := fun z : ℂ => (1-t)*f z)
    (f₂ := fun z : ℂ => t*(poissonKernel 0 (-(h : ℂ)) z*f z))
    (hf.const_smul (a := 1-t)) (hPf.const_smul (a := t))]
  change Real.circleAverage ((1-t) • f) 0 1+
    Real.circleAverage (t • (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*f z)) 0 1 = _
  rw [Real.circleAverage_smul, Real.circleAverage_smul]
  change (1-t)*Real.circleAverage f 0 1+
    t*Real.circleAverage (fun z : ℂ => poissonKernel 0 (-(h : ℂ)) z*f z) 0 1 = _
  rw [joukowski_log_average d w hd hw, poisson_joukowski_log_average d h w hd hh hw]
  ring
theorem exists_joukowski_closed_exterior (c d : ℝ) (hd : d ≠ 0) (z : ℂ) :
    ∃ w : ℂ, 1 ≤ ‖w‖ ∧ z = (c : ℂ)+(d : ℂ)*(w+w⁻¹) := by
  let a : ℂ := (z-(c : ℂ))/(d : ℂ)
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (a^2-4) (by norm_num : 0 < (2 : ℕ))
  let w : ℂ := (a+q)/2
  have hpoly : w^2-a*w+1 = 0 := by dsimp [w]; linear_combination hq / 4
  have hw : w ≠ 0 := by intro hw; simp [hw] at hpoly
  have heq : w+w⁻¹ = a := by
    apply (mul_right_inj' hw).mp
    calc
      w*(w+w⁻¹) = w^2+1 := by field_simp
      _ = w*a := by linear_combination hpoly
  have hz : z = (c : ℂ)+(d : ℂ)*(w+w⁻¹) := by
    rw [heq]
    dsimp [a]
    field_simp [Complex.ofReal_ne_zero.mpr hd]; ring
  by_cases hn : 1 ≤ ‖w‖
  · exact ⟨w, hn, hz⟩
  · refine ⟨w⁻¹, ?_, ?_⟩
    · rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.mpr hw)).mpr (le_of_lt (lt_of_not_ge hn))
    · simpa only [inv_inv, add_comm] using hz
theorem tilted_joukowski_factor (s r : ℝ) (w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) :
    ((s^2+r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*(w+w⁻¹) =
      ((s^2 : ℝ) : ℂ)/w*(w+((r/s : ℝ) : ℂ))*(1+((r/s : ℝ) : ℂ)*w) := by
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hs]; ring
theorem norm_tilted_joukowski_pair (h : ℝ) (w : ℂ) (hh : |h| ≤ 1)
    (hw : 1 ≤ ‖w‖) : ‖1+(h : ℂ)*w‖ ≤ ‖w+(h : ℂ)‖ := by
  have he : ‖w+(h : ℂ)‖^2-‖1+(h : ℂ)*w‖^2 =
      (1-h^2)*(‖w‖^2-1) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  have hh' : 0 ≤ 1-h^2 := by
    rcases abs_le.mp hh with ⟨hl, hu⟩
    nlinarith
  have hw' : 0 ≤ ‖w‖^2-1 := by nlinarith
  have := mul_nonneg hh' hw'
  nlinarith [norm_nonneg (w+(h : ℂ)), norm_nonneg (1+(h : ℂ)*w)]
theorem exterior_add_real_ne_zero (h : ℝ) (w : ℂ) (hh : |h| < 1)
    (hw : 1 ≤ ‖w‖) : w+(h : ℂ) ≠ 0 := by
  intro heq
  have heq' : w = -(h : ℂ) := eq_neg_of_add_eq_zero_left heq
  rw [heq', norm_neg, Complex.norm_real, Real.norm_eq_abs] at hw
  linarith
theorem tilted_joukowski_log (s r : ℝ) (w : ℂ) (hs : 0 < s)
    (hw : w ≠ 0) (hA : w+((r/s : ℝ) : ℂ) ≠ 0)
    (hB : 1+((r/s : ℝ) : ℂ)*w ≠ 0) :
    Real.log ‖((s^2+r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*(w+w⁻¹)‖ =
      2*Real.log s-Real.log ‖w‖+Real.log ‖w+((r/s : ℝ) : ℂ)‖+
        Real.log ‖1+((r/s : ℝ) : ℂ)*w‖ := by
  have hs' : ((s^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hs.ne')
  rw [tilted_joukowski_factor s r w hs.ne' hw, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr (mul_ne_zero (div_ne_zero hs' hw) hA))
      (norm_ne_zero_iff.mpr hB),
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (div_ne_zero hs' hw))
      (norm_ne_zero_iff.mpr hA),
    norm_div, Real.log_div (norm_ne_zero_iff.mpr hs') (norm_ne_zero_iff.mpr hw),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hs), Real.log_pow]
  ring
theorem poissonCosMeasure_tilted_potential_lower_bound (s r t : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (z : ℂ) (hz : z ≠ 0) :
    t*Real.log ‖z‖+(Real.log (s*r)-2*t*Real.log s) ≤
      ∫ x : ℝ, Real.log ‖z-(x : ℂ)‖ ∂poissonCosMeasure (r/s) t (s^2+r^2) (s*r) := by
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  obtain ⟨w, hw, hzw⟩ := exists_joukowski_closed_exterior (s^2+r^2) (s*r) (mul_pos hs hr).ne' z
  have hw0 : w ≠ 0 := by intro heq; simp [heq] at hw; norm_num at hw
  have hA := exterior_add_real_ne_zero (r/s) w hh hw
  have hB : 1+((r/s : ℝ) : ℂ)*w ≠ 0 := by
    intro heq
    apply hz
    rw [hzw, tilted_joukowski_factor s r w hs.ne' hw0, heq, mul_zero]
  have hlog := tilted_joukowski_log s r w hs hw0 hA hB
  rw [← hzw] at hlog
  have hlw : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hw
  have hcomp : Real.log ‖1+((r/s : ℝ) : ℂ)*w‖ ≤ Real.log ‖w+((r/s : ℝ) : ℂ)‖ :=
    Real.log_le_log (norm_pos_iff.mpr hB) (norm_tilted_joukowski_pair (r/s) w hh.le hw)
  rw [hzw, poissonCosMeasure_joukowski_potential (r/s) t (s^2+r^2) (s*r) w
    (mul_pos hs hr).ne' hh ht0 ht1 hw, abs_of_pos (mul_pos hs hr)]
  rw [hzw] at hlog
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hlw, mul_nonneg ht0 (sub_nonneg.mpr hcomp)]
theorem norm_tilted_joukowski_pair_eq (h : ℝ) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖1+(h : ℂ)*w‖ = ‖w+(h : ℂ)‖ := by
  have he : ‖w+(h : ℂ)‖^2-‖1+(h : ℂ)*w‖^2 =
      (1-h^2)*(‖w‖^2-1) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  rw [hw] at he
  nlinarith [norm_nonneg (w+(h : ℂ)), norm_nonneg (1+(h : ℂ)*w)]
theorem exists_joukowski_unit_real (c d x : ℝ) (hd : 0 < d)
    (hx : x ∈ Set.Icc (c-2*d) (c+2*d)) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ (x : ℂ) = (c : ℂ)+(d : ℂ)*(w+w⁻¹) := by
  let θ := Real.arccos ((x-c)/(2*d))
  have hlo : -1 ≤ (x-c)/(2*d) := (le_div_iff₀ (by positivity)).mpr (by linarith [hx.1])
  have hhi : (x-c)/(2*d) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [hx.2])
  have hcos : Real.cos θ = (x-c)/(2*d) := Real.cos_arccos hlo hhi
  refine ⟨circleMap 0 1 θ, by simp, ?_⟩
  rw [circleMap_add_inv, hcos]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hd.ne']; ring
theorem poissonCosMeasure_tilted_potential_on_interval (s r t x : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : x ∈ Set.Icc ((s-r)^2) ((s+r)^2)) :
    (∫ y : ℝ, Real.log ‖(x : ℂ)-(y : ℂ)‖
      ∂poissonCosMeasure (r/s) t (s^2+r^2) (s*r)) =
      Real.log (s*r)-2*t*Real.log s+t*Real.log x := by
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  have hx0 : 0 < x := lt_of_lt_of_le (sq_pos_of_pos (sub_pos.mpr hrs)) hx.1
  have hx' : x ∈ Set.Icc (s^2+r^2-2*(s*r)) (s^2+r^2+2*(s*r)) := by
    constructor <;> nlinarith [hx.1, hx.2]
  obtain ⟨w, hw, hzw⟩ := exists_joukowski_unit_real (s^2+r^2) (s*r) x (mul_pos hs hr) hx'
  have hw0 : w ≠ 0 := by intro heq; simp [heq] at hw
  have hA := exterior_add_real_ne_zero (r/s) w hh hw.ge
  have hB : 1+((r/s : ℝ) : ℂ)*w ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_tilted_joukowski_pair_eq (r/s) w hw]
    exact norm_ne_zero_iff.mpr hA
  have hlog := tilted_joukowski_log s r w hs hw0 hA hB
  rw [← hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hw,
    Real.log_one, norm_tilted_joukowski_pair_eq (r/s) w hw] at hlog
  rw [hzw, poissonCosMeasure_joukowski_potential (r/s) t (s^2+r^2) (s*r) w
    (mul_pos hs hr).ne' hh ht0 ht1 hw.ge,
    abs_of_pos (mul_pos hs hr), hw, Real.log_one]
  nlinarith
theorem poissonCosMeasure_tilted_zero_moment (s r t : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂poissonCosMeasure (r/s) t (s^2+r^2) (s*r)) =
      2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s) := by
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  let w : ℂ := ((-(s/r) : ℝ) : ℂ)
  have hw : ‖w‖ = s/r := by dsimp [w]; rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (neg_neg_of_pos (div_pos hs hr)), neg_neg]
  have hw' : 1 ≤ ‖w‖ := by rw [hw]; exact (one_le_div hr).mpr hrs.le
  have hzw : (0 : ℂ) = ((s^2+r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*(w+w⁻¹) := by
    dsimp [w]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne', Complex.ofReal_ne_zero.mpr hr.ne']; ring
  have hsr : 0 < s^2-r^2 := by nlinarith
  have hwa : ‖w+((r/s : ℝ) : ℂ)‖ = (s^2-r^2)/(s*r) := by
    have he : w+((r/s : ℝ) : ℂ) = ((-((s^2-r^2)/(s*r)) : ℝ) : ℂ) := by
      dsimp [w]
      push_cast
      field_simp; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos
      (div_pos hsr (mul_pos hs hr))), neg_neg]
  have he := poissonCosMeasure_joukowski_potential (r/s) t (s^2+r^2) (s*r) w
    (mul_pos hs hr).ne' hh ht0 ht1 hw'
  rw [← hzw] at he
  simp only [zero_sub, norm_neg] at he
  rw [he, abs_of_pos (mul_pos hs hr), hw, hwa,
    Real.log_div hs.ne' hr.ne', Real.log_div hsr.ne' (mul_pos hs hr).ne',
    Real.log_mul hs.ne' hr.ne']
  ring
theorem joukowski_exterior_continuous (c d : ℝ) :
    Continuous (fun w : {w : ℂ // 1 ≤ ‖w‖} => (c : ℂ)+(d : ℂ)*(w.val+w.val⁻¹)) := by
  have hw : ∀ w : {w : ℂ // 1 ≤ ‖w‖}, w.val ≠ 0 := by
    intro w heq
    have := w.property
    simp [heq] at this
    norm_num at this
  exact continuous_const.add (continuous_const.mul
    (continuous_subtype_val.add (continuous_subtype_val.inv₀ hw)))
theorem joukowski_exterior_norm_bound (c d : ℝ) (w : ℂ) (hw : 1 ≤ ‖w‖) :
    |d| * ‖w‖ ≤ ‖(c : ℂ)+(d : ℂ)*(w+w⁻¹)‖+|c|+|d| := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hw
  have hwi : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact (inv_le_one₀ hw0).mpr hw
  have he : (d : ℂ)*w = ((c : ℂ)+(d : ℂ)*(w+w⁻¹))-(c : ℂ)-(d : ℂ)*w⁻¹ := by ring
  calc
    |d| * ‖w‖ = ‖(d : ℂ)*w‖ := by simp
    _ ≤ ‖(c : ℂ)+(d : ℂ)*(w+w⁻¹)‖+|c|+|d| * ‖w⁻¹‖ := by
      rw [he]
      have hn := norm_sub_le ((c : ℂ)+(d : ℂ)*(w+w⁻¹)-(c : ℂ)) ((d : ℂ)*w⁻¹)
      have hn' := norm_sub_le ((c : ℂ)+(d : ℂ)*(w+w⁻¹)) (c : ℂ)
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hn hn'
      linarith
    _ ≤ _ := by nlinarith [abs_nonneg d]
theorem joukowski_exterior_isQuotientMap (c d : ℝ) (hd : d ≠ 0) :
    Topology.IsQuotientMap
      (fun w : {w : ℂ // 1 ≤ ‖w‖} => (c : ℂ)+(d : ℂ)*(w.val+w.val⁻¹)) := by
  let J : {w : ℂ // 1 ≤ ‖w‖} → ℂ := fun w => (c : ℂ)+(d : ℂ)*(w.val+w.val⁻¹)
  have hJ : Continuous J := joukowski_exterior_continuous c d
  let : ProperSpace {w : ℂ // 1 ≤ ‖w‖} :=
    ProperSpace.of_isClosed (isClosed_le continuous_const continuous_norm)
  have hp : IsProperMap J := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hJ, fun K hK => ?_⟩
    apply Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage hJ)
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
    let R := (B+|c|+|d|)/|d|
    apply (Metric.isBounded_iff_subset_closedBall (⟨(1 : ℂ), by simp⟩ : {w : ℂ // 1 ≤ ‖w‖})).mpr
    refine ⟨R+1, ?_⟩
    intro w hw
    have hJw : ‖J w‖ ≤ B := by simpa using hB hw
    have hnorm : ‖w.val‖ ≤ R := (le_div_iff₀ (abs_pos.mpr hd)).mpr (by
      have hn := joukowski_exterior_norm_bound c d w.val w.property
      dsimp [J] at hJw
      nlinarith)
    change dist w.val (1 : ℂ) ≤ R+1
    rw [dist_eq_norm]
    have hn := norm_sub_le w.val (1 : ℂ)
    simp only [norm_one] at hn
    linarith
  apply hp.isClosedMap.isQuotientMap hJ
  intro z
  obtain ⟨w, hw, hzw⟩ := exists_joukowski_closed_exterior c d hd z
  exact ⟨⟨w, hw⟩, hzw.symm⟩
theorem poissonCosMeasure_potential_continuous (h t c d : ℝ) (hd : d ≠ 0)
    (hh : |h| < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Continuous (fun z : ℂ => ∫ x : ℝ, Real.log ‖z-(x : ℂ)‖ ∂poissonCosMeasure h t c d) := by
  apply (joukowski_exterior_isQuotientMap c d hd).continuous_iff.mpr
  have he : (fun w : {w : ℂ // 1 ≤ ‖w‖} =>
      (∫ x : ℝ, Real.log ‖(c : ℂ)+(d : ℂ)*(w.val+w.val⁻¹)-(x : ℂ)‖
        ∂poissonCosMeasure h t c d)) =
      (fun w : {w : ℂ // 1 ≤ ‖w‖} =>
        Real.log |d|+(1-2*t)*Real.log ‖w.val‖+2*t*Real.log ‖w.val+(h : ℂ)‖) := by
    funext w
    exact poissonCosMeasure_joukowski_potential h t c d w.val hd hh ht0 ht1 w.property
  change Continuous (fun w : {w : ℂ // 1 ≤ ‖w‖} =>
      (∫ x : ℝ, Real.log ‖(c : ℂ)+(d : ℂ)*(w.val+w.val⁻¹)-(x : ℂ)‖
        ∂poissonCosMeasure h t c d))
  rw [he]
  have hlogw : Continuous (fun w : {w : ℂ // 1 ≤ ‖w‖} => Real.log ‖w.val‖) :=
    (continuous_norm.comp continuous_subtype_val).log (fun w => ne_of_gt
      (lt_of_lt_of_le (by norm_num) w.property))
  have hlogA : Continuous (fun w : {w : ℂ // 1 ≤ ‖w‖} => Real.log ‖w.val+(h : ℂ)‖) :=
    ((continuous_subtype_val.add continuous_const).norm).log
      (fun w => norm_ne_zero_iff.mpr (exterior_add_real_ne_zero h w.val hh w.property))
  exact (continuous_const.add (continuous_const.mul hlogw)).add (continuous_const.mul hlogA)
theorem log_kernel_integrable_prod_of_compact_potential
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] (a b : ℝ)
    (hsupport : μ (Set.Icc a b)ᶜ = 0)
    (hlog : ∀ z : ℂ, MeasureTheory.Integrable (fun x : ℝ => Real.log ‖z-(x : ℂ)‖) μ)
    (hpotential : Continuous (fun z : ℂ => ∫ x : ℝ, Real.log ‖z-(x : ℂ)‖ ∂μ)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Real.log ‖(p.1 : ℂ)-(p.2 : ℂ)‖) (μ.prod μ) := by
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc a b := by
    exact MeasureTheory.ae_iff.mpr hsupport
  have hrestrict : μ.restrict (Set.Icc a b) = μ :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae
  let B := |a|+|b|
  let M := Real.log (1+2*B)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hM : 0 ≤ M := Real.log_nonneg (by linarith)
  have hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      Real.log ‖(x : ℂ)-(y : ℂ)‖ ≤ M := by
    intro x hx y hy
    have hx' : |x| ≤ B := abs_le.mpr ⟨by dsimp [B]; linarith [neg_abs_le a, abs_nonneg b, hx.1],
      by dsimp [B]; linarith [le_abs_self b, abs_nonneg a, hx.2]⟩
    have hy' : |y| ≤ B := abs_le.mpr ⟨by dsimp [B]; linarith [neg_abs_le a, abs_nonneg b, hy.1],
      by dsimp [B]; linarith [le_abs_self b, abs_nonneg a, hy.2]⟩
    have hn : ‖(x : ℂ)-(y : ℂ)‖ ≤ 1+2*B := by
      have hn' := norm_sub_le (x : ℂ) (y : ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs] at hn'
      linarith
    by_cases hz : ‖(x : ℂ)-(y : ℂ)‖ = 0
    · rw [hz, Real.log_zero]
      exact hM
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) hn
  have hpot : MeasureTheory.Integrable
      (fun x : ℝ => ∫ y : ℝ, Real.log ‖(x : ℂ)-(y : ℂ)‖ ∂μ) μ := by
    have hc := (hpotential.comp Complex.continuous_ofReal).continuousOn.integrableOn_compact
      (μ := μ) (K := Set.Icc a b) isCompact_Icc
    rwa [MeasureTheory.IntegrableOn, hrestrict] at hc
  have hmeas : Measurable (fun p : ℝ × ℝ => Real.log ‖(p.1 : ℂ)-(p.2 : ℂ)‖) := by fun_prop
  apply (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => hlog (x : ℂ)), ?_⟩
  apply ((MeasureTheory.integrable_const (2*M)).sub hpot).mono'
    hmeas.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [hae] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))]
  calc
    (∫ y : ℝ, ‖Real.log ‖(x : ℂ)-(y : ℂ)‖‖ ∂μ) ≤
        ∫ y : ℝ, (2*M-Real.log ‖(x : ℂ)-(y : ℂ)‖) ∂μ := by
      apply MeasureTheory.integral_mono_ae (hlog (x : ℂ)).norm
        ((MeasureTheory.integrable_const (2*M)).sub (hlog (x : ℂ)))
      filter_upwards [hae] with y hy
      rw [Real.norm_eq_abs]
      dsimp only [Pi.sub_apply]
      exact abs_le.mpr ⟨by linarith, by linarith [hbound x hx y hy]⟩
    _ = 2*M-∫ y : ℝ, Real.log ‖(x : ℂ)-(y : ℂ)‖ ∂μ := by
      rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const (2*M)) (hlog (x : ℂ))]
      simp
theorem poissonCosMeasure_tilted_energy (s r t : ℝ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Real.log ‖(p.1 : ℂ)-(p.2 : ℂ)‖)
      ((poissonCosMeasure (r/s) t (s^2+r^2) (s*r)).prod
        (poissonCosMeasure (r/s) t (s^2+r^2) (s*r))) ∧
    (∫ p : ℝ × ℝ, Real.log ‖(p.1 : ℂ)-(p.2 : ℂ)‖
      ∂((poissonCosMeasure (r/s) t (s^2+r^2) (s*r)).prod
        (poissonCosMeasure (r/s) t (s^2+r^2) (s*r)))) =
      Real.log (s*r)-2*t*Real.log s+
        t*(2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s)) := by
  let μ := poissonCosMeasure (r/s) t (s^2+r^2) (s*r)
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  let := poissonCosMeasure_probability (r/s) t (s^2+r^2) (s*r) hh ht0 ht1
  have hsupport : μ (Set.Icc ((s-r)^2) ((s+r)^2))ᶜ = 0 := by
    have he1 : (s-r)^2 = s^2+r^2-2*(s*r) := by ring
    have he2 : (s+r)^2 = s^2+r^2+2*(s*r) := by ring
    rw [he1, he2]
    exact poissonCosMeasure_support (r/s) t (s^2+r^2) (s*r) (mul_pos hs hr).le
  have hlog := poissonCosMeasure_log_integrable (r/s) t (s^2+r^2) (s*r) hh ht0 ht1
  have hcont := poissonCosMeasure_potential_continuous (r/s) t (s^2+r^2) (s*r)
    (mul_pos hs hr).ne' hh ht0 ht1
  have hi := log_kernel_integrable_prod_of_compact_potential μ ((s-r)^2) ((s+r)^2)
    hsupport hlog hcont
  refine ⟨hi, ?_⟩
  rw [MeasureTheory.integral_prod _ hi]
  have hae : ∀ᵐ x ∂μ, x ∈ Set.Icc ((s-r)^2) ((s+r)^2) := MeasureTheory.ae_iff.mpr hsupport
  have he : (fun x : ℝ => ∫ y : ℝ, Real.log ‖(x : ℂ)-(y : ℂ)‖ ∂μ) =ᵐ[μ]
      (fun x : ℝ => Real.log (s*r)-2*t*Real.log s+t*Real.log x) := by
    filter_upwards [hae] with x hx
    exact poissonCosMeasure_tilted_potential_on_interval s r t x hs hr hrs ht0 ht1 hx
  rw [MeasureTheory.integral_congr_ae he]
  have hlogx : MeasureTheory.Integrable Real.log μ := by
    have hi0 := hlog 0
    simpa only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, Real.log_abs] using hi0
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _)
      (hlogx.const_mul t), MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
  have hz := poissonCosMeasure_tilted_zero_moment s r t hs hr hrs ht0 ht1
  simp only [Complex.norm_real, Real.norm_eq_abs, Real.log_abs] at hz
  rw [hz]
theorem cosine_inverse_sqrt_bound (a b : ℝ) (ha : a ∈ Set.Icc 0 Real.pi)
    (hb : b ∈ Set.Icc 0 Real.pi) :
    |a-b| ≤ Real.pi*Real.sqrt (|Real.cos a-Real.cos b|/2) := by
  wlog hab : a ≤ b
  · simpa only [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
  let δ := (b-a)/2
  let σ := (a+b)/2
  have hd0 : 0 ≤ δ := by dsimp [δ]; linarith
  have hd1 : δ ≤ Real.pi/2 := by dsimp [δ]; linarith [ha.1, hb.2]
  have hdσ : δ ≤ σ := by dsimp [δ, σ]; linarith [ha.1]
  have hdπ : δ ≤ Real.pi-σ := by dsimp [δ, σ]; linarith [hb.2]
  have hsin : Real.sin δ ≤ Real.sin σ := by
    by_cases hσ : σ ≤ Real.pi/2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hσ hdσ
    · rw [← Real.sin_pi_sub σ]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith) hdπ
  have hsind := Real.mul_le_sin hd0 hd1
  have hsd : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [Real.pi_pos])
  have hcos : Real.cos a-Real.cos b = 2*Real.sin σ*Real.sin δ := by
    have he := Real.cos_sub_cos a b
    rw [show (a-b)/2 = -δ by dsimp [δ]; ring, Real.sin_neg] at he
    dsimp [σ]
    nlinarith [he]
  have hcos0 : 0 ≤ Real.cos a-Real.cos b := by rw [hcos]; exact mul_nonneg (mul_nonneg (by norm_num) (hsd.trans hsin)) hsd
  have hsqrt := Real.sq_sqrt (show 0 ≤ |Real.cos a-Real.cos b|/2 by positivity)
  have hsqrt0 := Real.sqrt_nonneg (|Real.cos a-Real.cos b|/2)
  rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg hcos0] at *
  have hlow : (2/Real.pi*δ)^2 ≤ (Real.cos a-Real.cos b)/2 := by
    have hq0 : 0 ≤ 2/Real.pi*δ := by positivity
    have hsq : (2/Real.pi*δ)^2 ≤ (Real.sin δ)^2 :=
      pow_le_pow_left₀ hq0 hsind 2
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin) hsd]
  have hpi : 0 < Real.pi := Real.pi_pos
  have heδ : Real.pi*(2/Real.pi*δ) = b-a := by dsimp [δ]; field_simp
  have hcmp : 2/Real.pi*δ ≤ Real.sqrt ((Real.cos a-Real.cos b)/2) := by nlinarith
  have := mul_le_mul_of_nonneg_left hcmp hpi.le
  nlinarith
theorem cosine_ball_preimage_diameter (c d x ρ a b : ℝ) (hd : 0 < d)
    (hρ : 0 ≤ ρ) (ha : a ∈ Set.Icc 0 Real.pi) (hb : b ∈ Set.Icc 0 Real.pi)
    (hax : c+2*d*Real.cos a ∈ Metric.ball x ρ)
    (hbx : c+2*d*Real.cos b ∈ Metric.ball x ρ) :
    dist a b ≤ Real.pi*Real.sqrt (ρ/d) := by
  have hdist : |Real.cos a-Real.cos b|/2 ≤ ρ/d := by
    have htriangle := dist_triangle (c+2*d*Real.cos a) x (c+2*d*Real.cos b)
    have hax' : dist (c+2*d*Real.cos a) x < ρ := hax
    have hbx' : dist x (c+2*d*Real.cos b) < ρ := by rw [dist_comm]; exact hbx
    have he : dist (c+2*d*Real.cos a) (c+2*d*Real.cos b) =
        2*d*|Real.cos a-Real.cos b| := by
      rw [Real.dist_eq, show c+2*d*Real.cos a-(c+2*d*Real.cos b) =
        (2*d)*(Real.cos a-Real.cos b) by ring, abs_mul, abs_of_pos (by positivity : 0 < 2*d)]
    rw [he] at htriangle
    apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg (Real.cos a-Real.cos b)]
  calc
    dist a b = |a-b| := Real.dist_eq a b
    _ ≤ Real.pi*Real.sqrt (|Real.cos a-Real.cos b|/2) := cosine_inverse_sqrt_bound a b ha hb
    _ ≤ Real.pi*Real.sqrt (ρ/d) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist) Real.pi_pos.le
theorem cosine_ball_preimage_volume (c d x ρ : ℝ) (hd : 0 < d) (hρ : 0 ≤ ρ) :
    MeasureTheory.volume ((fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' Metric.ball x ρ ∩
      Set.Ioc 0 (2*Real.pi)) ≤ ENNReal.ofReal (2*Real.pi*Real.sqrt (ρ/d)) := by
  let S₁ := (fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' Metric.ball x ρ ∩ Set.Icc 0 Real.pi
  let S₂ := (fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' Metric.ball x ρ ∩ Set.Icc Real.pi (2*Real.pi)
  have hS₁ : MeasureTheory.volume S₁ ≤ ENNReal.ofReal (Real.pi*Real.sqrt (ρ/d)) := by
    apply (Real.volume_le_diam S₁).trans
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    exact cosine_ball_preimage_diameter c d x ρ a b hd hρ ha.2 hb.2 ha.1 hb.1
  have hS₂ : MeasureTheory.volume S₂ ≤ ENNReal.ofReal (Real.pi*Real.sqrt (ρ/d)) := by
    apply (Real.volume_le_diam S₂).trans
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    have ha' : 2*Real.pi-a ∈ Set.Icc 0 Real.pi := ⟨by linarith [ha.2.2], by linarith [ha.2.1]⟩
    have hb' : 2*Real.pi-b ∈ Set.Icc 0 Real.pi := ⟨by linarith [hb.2.2], by linarith [hb.2.1]⟩
    have hax : c+2*d*Real.cos (2*Real.pi-a) ∈ Metric.ball x ρ := by
      rw [Real.cos_two_pi_sub]
      exact ha.1
    have hbx : c+2*d*Real.cos (2*Real.pi-b) ∈ Metric.ball x ρ := by
      rw [Real.cos_two_pi_sub]
      exact hb.1
    have ht := cosine_ball_preimage_diameter c d x ρ (2*Real.pi-a) (2*Real.pi-b)
      hd hρ ha' hb' hax hbx
    simpa only [Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm] using ht
  calc
    _ ≤ MeasureTheory.volume (S₁ ∪ S₂) := by
      apply MeasureTheory.measure_mono
      intro θ hθ
      by_cases hθπ : θ ≤ Real.pi
      · exact Or.inl ⟨hθ.1, hθ.2.1.le, hθπ⟩
      · exact Or.inr ⟨hθ.1, (lt_of_not_ge hθπ).le, hθ.2.2⟩
    _ ≤ MeasureTheory.volume S₁+MeasureTheory.volume S₂ := MeasureTheory.measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.pi*Real.sqrt (ρ/d))+ENNReal.ofReal (Real.pi*Real.sqrt (ρ/d)) :=
      add_le_add hS₁ hS₂
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
theorem poissonCosMeasure_sqrt_ball_bound (h t c d : ℝ) (hh : |h| < 1) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x ρ : ℝ), 0 < ρ →
      poissonCosMeasure h t c d (Metric.ball x ρ) ≤ ENNReal.ofReal (K*Real.sqrt ρ) := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.bddAbove_image (continuous_poissonAngleDensity h t hh).continuousOn
  let M := |M₀|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hdens : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc 0 (2*Real.pi))),
      ENNReal.ofReal (poissonAngleDensity h t θ) ≤ ENNReal.ofReal M := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hm := hM₀ (Set.mem_image_of_mem (poissonAngleDensity h t) (Set.Ioc_subset_Icc_self hθ))
    dsimp [M]
    linarith [le_abs_self M₀]
  have hmeasure : poissonAngleMeasure h t ≤ ENNReal.ofReal M •
      (MeasureTheory.volume.restrict (Set.Ioc 0 (2*Real.pi))) := by
    have hm := MeasureTheory.withDensity_mono hdens
    rwa [MeasureTheory.withDensity_const] at hm
  refine ⟨M*(2*Real.pi)*Real.sqrt (d⁻¹), by positivity, ?_⟩
  intro x ρ hρ
  rw [poissonCosMeasure, MeasureTheory.Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet]
  calc
    _ ≤ (ENNReal.ofReal M • (MeasureTheory.volume.restrict (Set.Ioc 0 (2*Real.pi))))
        ((fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' Metric.ball x ρ) :=
      hmeasure _
    _ = ENNReal.ofReal M * MeasureTheory.volume
        ((fun θ : ℝ => c+2*d*Real.cos θ) ⁻¹' Metric.ball x ρ ∩ Set.Ioc 0 (2*Real.pi)) := by
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.restrict_apply
        (Metric.isOpen_ball.measurableSet.preimage (by fun_prop))]
      rfl
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (2*Real.pi*Real.sqrt (ρ/d)) :=
      mul_le_mul_right (cosine_ball_preimage_volume c d x ρ hd hρ.le) _
    _ = ENNReal.ofReal (M*(2*Real.pi)*Real.sqrt (d⁻¹)*Real.sqrt ρ) := by
      rw [← ENNReal.ofReal_mul hM.le]
      congr 1
      rw [div_eq_mul_inv, Real.sqrt_mul hρ.le]
      ring
theorem fixed_tilt_measure_certificate :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let t : ℝ := 3000000/13999999
    let C := Real.log d-2*t*Real.log s
    let L := 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s)
    1/10000000 < C ∧ 1/10000000 < L ∧
    ∃ μ : MeasureTheory.Measure ℝ,
      MeasureTheory.IsProbabilityMeasure μ ∧ MeasureTheory.NullSingletonClass μ ∧
      μ (Set.Icc (u^2) (v^2))ᶜ = 0 ∧
      (∀ z : ℂ, MeasureTheory.Integrable (fun x : ℝ => Real.log ‖z-(x : ℂ)‖) μ) ∧
      Continuous (fun z : ℂ => ∫ x : ℝ, Real.log ‖z-(x : ℂ)‖ ∂μ) ∧
      MeasureTheory.Integrable (fun xy : ℝ × ℝ => Real.log |xy.1-xy.2|) (μ.prod μ) ∧
      (∀ z : ℂ, z ≠ 0 → t*Real.log ‖z‖+C ≤ ∫ x : ℝ, Real.log ‖z-(x : ℂ)‖ ∂μ) ∧
      (∀ x : ℝ, x ∈ Set.Icc (u^2) (v^2) →
        (∫ y : ℝ, Real.log ‖(x : ℂ)-(y : ℂ)‖ ∂μ) = C+t*Real.log x) ∧
      (∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂μ) = L ∧
      (∫ x : ℝ, ∫ y : ℝ, Real.log |x-y| ∂μ ∂μ) = C+t*L ∧
      ∃ K : ℝ, 0 < K ∧ ∀ (x ρ : ℝ), 0 < ρ →
        μ (Metric.ball x ρ) ≤ ENNReal.ofReal (K*Real.sqrt ρ) := by
  let u : ℝ := 294811/1000000
  let v : ℝ := 1049707/500000
  let s := (u+v)/2
  let r := (v-u)/2
  let d := s*r
  let t : ℝ := 3000000/13999999
  let C := Real.log d-2*t*Real.log s
  let L := 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s)
  have hs : 0 < s := by norm_num [s, u, v]
  have hr : 0 < r := by norm_num [r, u, v]
  have hrs : r < s := by norm_num [r, s, u, v]
  have ht0 : 0 ≤ t := by norm_num [t]
  have ht1 : t ≤ 1 := by norm_num [t]
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  have hd : 0 < d := mul_pos hs hr
  have heuv : s^2-r^2 = u*v := by dsimp [s, r]; ring
  have hlow : (s-r)^2 = u^2 := by dsimp [s, r]; ring
  have hupp : (s+r)^2 = v^2 := by dsimp [s, r]; ring
  let μ := poissonCosMeasure (r/s) t (s^2+r^2) d
  have hprob : MeasureTheory.IsProbabilityMeasure μ :=
    poissonCosMeasure_probability (r/s) t (s^2+r^2) d hh ht0 ht1
  have hatom : MeasureTheory.NullSingletonClass μ :=
    poissonCosMeasure_atomless (r/s) t (s^2+r^2) d hd.ne'
  have hsupport : μ (Set.Icc (u^2) (v^2))ᶜ = 0 := by
    rw [← hlow, ← hupp,
      show (s-r)^2 = s^2+r^2-2*d by dsimp [d]; ring,
      show (s+r)^2 = s^2+r^2+2*d by dsimp [d]; ring]
    exact poissonCosMeasure_support (r/s) t (s^2+r^2) d hd.le
  have hroot := poissonCosMeasure_log_integrable (r/s) t (s^2+r^2) d hh ht0 ht1
  have hcont := poissonCosMeasure_potential_continuous (r/s) t (s^2+r^2) d hd.ne' hh ht0 ht1
  have henergy := poissonCosMeasure_tilted_energy s r t hs hr hrs ht0 ht1
  have henergy_integrable : MeasureTheory.Integrable
      (fun xy : ℝ × ℝ => Real.log |xy.1-xy.2|) (μ.prod μ) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using henergy.1
  have hmargin : 1/10000000 < C ∧ 1/10000000 < L := fixed_tilt_strict_margins
  refine ⟨hmargin.1, hmargin.2, μ, hprob, hatom, hsupport, hroot, hcont,
    henergy_integrable, ?_, ?_, ?_, ?_, poissonCosMeasure_sqrt_ball_bound (r/s) t (s^2+r^2) d hh hd⟩
  · exact poissonCosMeasure_tilted_potential_lower_bound s r t hs hr hrs ht0 ht1
  · intro x hx
    apply poissonCosMeasure_tilted_potential_on_interval s r t x hs hr hrs ht0 ht1
    rwa [hlow, hupp]
  · have hz := poissonCosMeasure_tilted_zero_moment s r t hs hr hrs ht0 ht1
    rwa [heuv] at hz
  · have he := henergy.2
    let : MeasureTheory.IsProbabilityMeasure μ := hprob
    rw [← MeasureTheory.integral_prod _ henergy_integrable]
    simpa only [heuv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using he
theorem fixed_tilt_integer_polynomial_margin :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let t : ℝ := 3000000/13999999
    let μ := poissonCosMeasure (r/s) t (s^2+r^2) (s*r)
    ∀ p : Polynomial ℤ, p ≠ 0 →
      MeasureTheory.Integrable (fun x : ℝ => Real.log |Polynomial.aeval x p|) μ ∧
      (1/10000000 : ℝ)*(p.natDegree : ℝ) ≤
        ∫ x : ℝ, Real.log |Polynomial.aeval x p| ∂μ := by
  let u : ℝ := 294811/1000000
  let v : ℝ := 1049707/500000
  let s := (u+v)/2
  let r := (v-u)/2
  let t : ℝ := 3000000/13999999
  let μ := poissonCosMeasure (r/s) t (s^2+r^2) (s*r)
  let C := Real.log (s*r)-2*t*Real.log s
  let L := 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s)
  have hs : 0 < s := by norm_num [s, u, v]
  have hr : 0 < r := by norm_num [r, u, v]
  have hrs : r < s := by norm_num [r, s, u, v]
  have ht0 : 0 ≤ t := by norm_num [t]
  have ht1 : t ≤ 1 := by norm_num [t]
  have hh : |r/s| < 1 := by rw [abs_of_pos (div_pos hr hs)]; exact (div_lt_one hs).mpr hrs
  have hmargin : 1/10000000 < C ∧ 1/10000000 < L := fixed_tilt_strict_margins
  have hC : 0 ≤ C := by linarith [hmargin.1]
  have hL : 0 ≤ L := by linarith [hmargin.2]
  have hz : L ≤ ∫ x : ℝ, Real.log ‖(x : ℂ)‖ ∂μ := by
    have he := poissonCosMeasure_tilted_zero_moment s r t hs hr hrs ht0 ht1
    have heuv : s^2-r^2 = u*v := by dsimp [s, r]; ring
    rw [heuv] at he
    exact he.ge
  have hp := potential_integer_polynomial_margin μ t C L
    (poissonCosMeasure_probability (r/s) t (s^2+r^2) (s*r) hh ht0 ht1)
    (poissonCosMeasure_atomless (r/s) t (s^2+r^2) (s*r) (mul_pos hs hr).ne')
    ht0 ht1 hC hL
    (poissonCosMeasure_log_integrable (r/s) t (s^2+r^2) (s*r) hh ht0 ht1)
    (poissonCosMeasure_tilted_potential_lower_bound s r t hs hr hrs ht0 ht1) hz
  change ∀ p : Polynomial ℤ, p ≠ 0 →
    MeasureTheory.Integrable (fun x : ℝ => Real.log |Polynomial.aeval x p|) μ ∧
    (1/10000000 : ℝ)*(p.natDegree : ℝ) ≤ ∫ x : ℝ, Real.log |Polynomial.aeval x p| ∂μ
  intro p hp0
  obtain ⟨hi, hb⟩ := hp p hp0
  exact ⟨hi, (mul_le_mul_of_nonneg_right (le_min hmargin.1.le hmargin.2.le)
    (Nat.cast_nonneg p.natDegree)).trans hb⟩
theorem exists_descending_permuted_pivot_rounding
    (D : ℕ) (P : Fin D → Polynomial ℝ) (e : Fin D ≃ Fin D)
    (hdeg : ∀ i, (P i).natDegree < D)
    (hpivot : ∀ i, (P i).coeff (e i).val = 1)
    (htri : ∀ i j, i.val < j.val → (P i).coeff (e j).val = 0)
    (m : ℕ) (hm : m ≤ D) (T : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ,
      (∀ j : Fin D, m ≤ j.val → Q.coeff (e j).val = T.coeff (e j).val) ∧
      (∀ j : Fin D, j.val < m → ∃ z : ℤ, Q.coeff (e j).val = (z : ℝ)) ∧
      (∀ k : ℕ, D ≤ k → Q.coeff k = T.coeff k) ∧
      ∀ x : ℝ, |Q.eval x-T.eval x| ≤ (1/2 : ℝ)*
        ∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < m), |(P j).eval x| := by
  classical
  induction m generalizing T with
  | zero =>
    refine ⟨T, fun _ _ => rfl, ?_, fun _ _ => rfl, ?_⟩
    · intro j hj
      omega
    · intro x
      simp
  | succ m ih =>
    let j : Fin D := ⟨m, by omega⟩
    let a : ℝ := (round (T.coeff (e j).val) : ℤ)-T.coeff (e j).val
    let S : Polynomial ℝ := T+Polynomial.C a*P j
    obtain ⟨Q, hQsame, hQint, hQhigh, hQerr⟩ := ih (by omega) S
    have hSm : S.coeff (e j).val = (round (T.coeff (e j).val) : ℤ) := by
      simp only [S, Polynomial.coeff_add, Polynomial.coeff_C_mul, hpivot, mul_one]
      dsimp [a]
      ring
    have ha : |a| ≤ (1/2 : ℝ) := by
      simpa only [a, abs_sub_comm] using abs_sub_round (T.coeff (e j).val)
    refine ⟨Q, ?_, ?_, ?_, ?_⟩
    · intro l hl
      rw [hQsame l (by omega)]
      simp only [S, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        htri j l (by dsimp [j]; omega), mul_zero, add_zero]
    · intro l hl
      by_cases hlm : l.val < m
      · exact hQint l hlm
      · have hlj : l = j := Fin.ext (by dsimp [j]; omega)
        subst l
        exact ⟨round (T.coeff (e j).val), (hQsame j (by simp [j])).trans hSm⟩
    · intro k hk
      rw [hQhigh k hk]
      simp only [S, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_le hk),
        mul_zero, add_zero]
    · intro x
      have hfilter : Finset.univ.filter (fun l : Fin D => l.val < m+1) =
          insert j (Finset.univ.filter (fun l : Fin D => l.val < m)) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hl
          by_cases hlm : l.val < m
          · exact Or.inr hlm
          · exact Or.inl (Fin.ext (by dsimp [j]; omega))
        · rintro (rfl | hl)
          · simp [j]
          · omega
      have hjnot : j ∉ Finset.univ.filter (fun l : Fin D => l.val < m) := by
        simp [j]
      have hSerr : |S.eval x-T.eval x| ≤ (1/2 : ℝ)*|(P j).eval x| := by
        simp only [S, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          add_sub_cancel_left, abs_mul]
        exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      calc
        _ = |(Q.eval x-S.eval x)+(S.eval x-T.eval x)| := by congr 1; ring
        _ ≤ |Q.eval x-S.eval x|+|S.eval x-T.eval x| := abs_add_le _ _
        _ ≤ (1/2 : ℝ)*(∑ l ∈ Finset.univ.filter (fun l : Fin D => l.val < m),
            |(P l).eval x|)+(1/2 : ℝ)*|(P j).eval x| := add_le_add (hQerr x) hSerr
        _ = _ := by rw [hfilter, Finset.sum_insert hjnot]; ring
theorem exists_integer_polynomial_of_integral_coefficients
    (D : ℕ) (hD : 0 < D) (P : Polynomial ℝ)
    (hhigh : ∀ k : ℕ, D ≤ k → P.coeff k = 0)
    (hlow : ∀ k : Fin D, ∃ z : ℤ, P.coeff k.val = (z : ℝ)) :
    ∃ q : Polynomial ℤ, q.natDegree < D ∧ q.map (Int.castRingHom ℝ) = P := by
  classical
  choose z hz using hlow
  refine ⟨Polynomial.ofFn D z, Polynomial.ofFn_natDegree_lt hD z, ?_⟩
  ext k
  simp only [Polynomial.coeff_map, Int.coe_castRingHom]
  by_cases hk : k < D
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt z hk]
    exact (hz ⟨k, hk⟩).symm
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge z (by omega), Int.cast_zero,
      hhigh k (by omega)]
theorem linearIndependent_polynomials_of_permuted_unit_pivots
    (D : ℕ) (P : Fin D → Polynomial ℚ) (e : Fin D ≃ Fin D)
    (hpivot : ∀ i, (P i).coeff (e i).val = 1)
    (htri : ∀ i j, i.val < j.val → (P i).coeff (e j).val = 0) :
    LinearIndependent ℚ P := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hall : ∀ k : ℕ, ∀ j : Fin D, D-k ≤ j.val → a j = 0 := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have := j.isLt
      omega
    | succ k ih =>
      intro j hj
      by_cases hjold : D-k ≤ j.val
      · exact ih j hjold
      · have hcoeff : ∑ l : Fin D, a l*(P l).coeff (e j).val = 0 := by
          have h := congrArg (fun Q : Polynomial ℚ => Q.coeff (e j).val) ha
          simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
            smul_eq_mul, Polynomial.coeff_zero] using h
        have hsum : ∑ l : Fin D, a l*(P l).coeff (e j).val = a j := by
          rw [Finset.sum_eq_single j]
          · rw [hpivot, mul_one]
          · intro l _ hlj
            by_cases hlt : l.val < j.val
            · rw [htri l j hlt, mul_zero]
            · have hgt : j.val < l.val := by
                have hne : l.val ≠ j.val := fun h => hlj (Fin.ext h)
                omega
              rw [ih l (by omega), zero_mul]
          · simp
        exact hsum.symm.trans hcoeff
  exact hall D i (by omega)
theorem permuted_unit_pivot_integer_rounding_triangular
    (D : ℕ) (hD : 0 < D) (P : Fin D → Polynomial ℝ) (e : Fin D ≃ Fin D)
    (hdeg : ∀ i, (P i).natDegree < D)
    (hpivot : ∀ i, (P i).coeff (e i).val = 1)
    (htri : ∀ i j, i.val < j.val → (P i).coeff (e j).val = 0) :
    ∃ q : Fin D → Polynomial ℤ,
      (∀ i, (q i).natDegree < D) ∧
      (∀ i, (q i).coeff (e i).val = 1) ∧
      (∀ i j, i.val < j.val → (q i).coeff (e j).val = 0) ∧
      ∀ (i : Fin D) (x : ℝ),
        |Polynomial.aeval x (q i)-(P i).eval x| ≤ (1/2 : ℝ)*
          ∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val), |(P j).eval x| := by
  classical
  have hex : ∀ i : Fin D, ∃ q : Polynomial ℤ,
      q.natDegree < D ∧ q.coeff (e i).val = 1 ∧
      (∀ j : Fin D, i.val < j.val → q.coeff (e j).val = 0) ∧
      ∀ x : ℝ, |Polynomial.aeval x q-(P i).eval x| ≤ (1/2 : ℝ)*
        ∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val), |(P j).eval x| := by
    intro i
    obtain ⟨Q, hsame, hint, hhigh, herr⟩ := exists_descending_permuted_pivot_rounding
      D P e hdeg hpivot htri i.val i.isLt.le (P i)
    have hQhigh : ∀ k : ℕ, D ≤ k → Q.coeff k = 0 := by
      intro k hk
      rw [hhigh k hk, Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_le hk)]
    have hQint : ∀ j : Fin D, ∃ z : ℤ, Q.coeff (e j).val = (z : ℝ) := by
      intro j
      by_cases hji : j.val < i.val
      · exact hint j hji
      · rw [hsame j (by omega)]
        by_cases hjeq : j = i
        · subst j
          exact ⟨1, by simpa using hpivot i⟩
        · refine ⟨0, ?_⟩
          have hlt : i.val < j.val := by
            have hne : j.val ≠ i.val := fun h => hjeq (Fin.ext h)
            omega
          simpa using htri i j hlt
    obtain ⟨q, hqdeg, hmap⟩ := exists_integer_polynomial_of_integral_coefficients
      D hD Q hQhigh (fun k => by simpa using hQint (e.symm k))
    have hcoeff : ∀ k : ℕ, ((q.coeff k : ℤ) : ℝ) = Q.coeff k := by
      intro k
      have h := congrArg (fun R : Polynomial ℝ => R.coeff k) hmap
      simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using h
    refine ⟨q, hqdeg, ?_, ?_, ?_⟩
    · have h : ((q.coeff (e i).val : ℤ) : ℝ) = 1 :=
        (hcoeff _).trans ((hsame i le_rfl).trans (hpivot i))
      exact_mod_cast h
    · intro j hij
      have h : ((q.coeff (e j).val : ℤ) : ℝ) = 0 :=
        (hcoeff _).trans ((hsame j hij.le).trans (htri i j hij))
      exact_mod_cast h
    · intro x
      have heval : Polynomial.aeval x q = Q.eval x := by
        rw [← hmap]
        simp only [Polynomial.aeval_def, Polynomial.eval_map, algebraMap_int_eq]
      rw [heval]
      exact herr x
  choose q hqdeg hqpivot hqtri hqerr using hex
  exact ⟨q, hqdeg, hqpivot, hqtri, hqerr⟩
theorem permuted_unit_pivot_integer_rounding :
    ∀ (D : ℕ), 0 < D → ∀ (P : Fin D → Polynomial ℝ) (e : Fin D ≃ Fin D),
      (∀ i, (P i).natDegree < D) →
      (∀ i, (P i).coeff (e i).val = 1) →
      (∀ i j, i.val < j.val → (P i).coeff (e j).val = 0) →
      ∃ q : Fin D → Polynomial ℤ,
        LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)) ∧
        (∀ i, (q i).natDegree < D) ∧
        ∀ (i : Fin D) (x : ℝ), |Polynomial.aeval x (q i)| ≤ |(P i).eval x| +
          (1/2 : ℝ)*∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val),
            |(P j).eval x| := by
  intro D hD P e hdeg hpivot htri
  obtain ⟨q, hqdeg, hqpivot, hqtri, hqerr⟩ :=
    permuted_unit_pivot_integer_rounding_triangular D hD P e hdeg hpivot htri
  refine ⟨q, ?_, hqdeg, ?_⟩
  · apply linearIndependent_polynomials_of_permuted_unit_pivots D
      (fun i => (q i).map (Int.castRingHom ℚ)) e
    · intro i
      simp only [Polynomial.coeff_map, Int.coe_castRingHom, hqpivot, Int.cast_one]
    · intro i j hij
      simp only [Polynomial.coeff_map, Int.coe_castRingHom, hqtri i j hij, Int.cast_zero]
  · intro i x
    calc
      _ = |(Polynomial.aeval x (q i)-(P i).eval x)+(P i).eval x| := by
        rw [sub_add_cancel]
      _ ≤ |Polynomial.aeval x (q i)-(P i).eval x|+|(P i).eval x| := abs_add_le _ _
      _ ≤ _ := by linarith [hqerr i x]
theorem weightedChebyshev_general_pivots :
    ∀ (s r : ℝ) (n M : ℕ), 0 < r → r < s → 0 < M → 2*M < n →
    let H : Polynomial ℝ := ∑ j ∈ Finset.range (2*M+1),
      Polynomial.C ((Nat.choose (2*M) j : ℝ)*(r^2)^j) *
        scaledChebyshev (s*r) (s^2+r^2) (n-j)
    H.Monic ∧ H.natDegree = n ∧
      H.coeff 0 = (-(s^2))^(n-2*M)*(r^2-s^2)^(2*M) ∧
      ∀ x : ℝ, x ∈ Set.Icc ((s-r)^2) ((s+r)^2) →
        |H.eval x| ≤ 2*((s*r)^n/s^(2*M))*x^M := by
  set_option maxHeartbeats 800000 in
    intro s r n M hr hrs hM hmn H
    have hs : 0 < s := hr.trans hrs
    have hd : s*r ≠ 0 := (mul_pos hs hr).ne'
    have h2M : 2*M < n := hmn
    have hMle : 2*M ≤ n := h2M.le
    have hdata := weightedChebyshev_data (s*r) (s^2+r^2) (r^2) n (2*M) hd h2M
    refine ⟨hdata.1, hdata.2.1, ?_, ?_⟩
    · have hw : (-s/r : ℝ) ≠ 0 := by
        exact div_ne_zero (neg_ne_zero.mpr hs.ne') hr.ne'
      have hwl : ((-s/r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
      have he := weightedChebyshev_eval_laurent (s*r) (s^2+r^2) (r^2)
        hd n (2*M) hMle ((-s/r : ℝ) : ℂ) hwl
      change (H.map (algebraMap ℝ ℂ)).eval
        (((s^2+r^2 : ℝ) : ℂ) +
          ((s*r : ℝ) : ℂ) * (((-s/r : ℝ) : ℂ) + (((-s/r : ℝ) : ℂ))⁻¹)) = _ at he
      have harg :
          ((s^2+r^2 : ℝ) : ℂ) + ((s*r : ℝ) : ℂ) *
              (((-s/r : ℝ) : ℂ) + (((-s/r : ℝ) : ℂ))⁻¹) = 0 := by
        push_cast
        field_simp [ne_of_gt hs, ne_of_gt hr]
        ring
      rw [harg] at he
      have hev :
          ((H.map (algebraMap ℝ ℂ)).eval (0 : ℂ)) = ((H.eval 0 : ℝ) : ℂ) := by
        simpa using
          (Polynomial.eval_map_apply (algebraMap ℝ ℂ) (0 : ℝ) (p := H))
      rw [hev] at he
      have hfirst :
          (((s*r : ℝ) : ℂ) * (((-s/r : ℝ) : ℂ))) ^ (n-2*M) =
            ((-(s^2) : ℝ) : ℂ) ^ (n-2*M) := by
        congr 1
        push_cast
        field_simp [ne_of_gt hs, ne_of_gt hr]
      have hsecond :
          ((r^2 : ℝ) : ℂ) + ((s*r : ℝ) : ℂ) *
              (((-s/r : ℝ) : ℂ))⁻¹ = 0 := by
        push_cast
        field_simp [ne_of_gt hs, ne_of_gt hr]
        ring
      have hthird :
          ((r^2 : ℝ) : ℂ) + ((s*r : ℝ) : ℂ) *
              (((-s/r : ℝ) : ℂ)) = ((r^2-s^2 : ℝ) : ℂ) := by
        push_cast
        field_simp [ne_of_gt hs, ne_of_gt hr]
        ring
      rw [hfirst, hsecond, hthird] at he
      simp only [Complex.ofReal_pow, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_sub, zero_pow (by omega : 2*M ≠ 0),
        mul_zero, add_zero] at he
      have he' : H.eval 0 =
          (-s^2)^(n-2*M) * (r^2-s^2)^(2*M) := by
        exact_mod_cast he
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact he'
    · intro x hx
      let θ : ℝ := Real.arccos ((x - (s^2+r^2))/(2*(s*r)))
      have hdpos : 0 < s*r := mul_pos hs hr
      have hlo : (s-r)^2 = s^2+r^2-2*(s*r) := by ring
      have hupp : (s+r)^2 = s^2+r^2+2*(s*r) := by ring
      have hargmem :
          -1 ≤ (x - (s^2+r^2))/(2*(s*r)) ∧
            (x - (s^2+r^2))/(2*(s*r)) ≤ 1 := by
        have hden : (0:ℝ) < 2*(s*r) := by positivity
        constructor
        · apply (le_div_iff₀ hden).2
          linarith [hx.1, hlo]
        · apply (div_le_iff₀ hden).2
          linarith [hx.2, hupp]
      have hθmem : θ ∈ Set.Icc 0 Real.pi := by
        exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
      have hcos : Real.cos θ =
          (x - (s^2+r^2))/(2*(s*r)) := by
        dsimp [θ]
        exact Real.cos_arccos hargmem.1 hargmem.2
      have hxrepr : s^2+r^2+2*(s*r)*Real.cos θ = x := by
        rw [hcos]
        field_simp
        ring
      have hp := weightedChebyshev_eval_phase (s*r) (s^2+r^2) (r^2) θ
        hd n (2*M) hMle
      change H.eval (s^2+r^2+2*(s*r)*Real.cos θ) = _ at hp
      rw [hxrepr] at hp
      have hnormsq :
          ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
            ((θ : ℂ)*Complex.I)‖^2 = r^2*x := by
        calc
          _ = r^2*(s^2+r^2+2*(s*r)*Real.cos θ) := by
            rw [weighted_circle_norm_sq]
            ring
          _ = r^2*x := by rw [hxrepr]
      have hcosle : |Real.cos ((n-2*M : ℕ)*θ +
          ((2*M : ℕ) : ℝ) * (((r^2 : ℝ) : ℂ) + ((s*r : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ)*Complex.I)).arg)| ≤ 1 := by
        exact Real.abs_cos_le_one _
      have hnormnonneg :
          0 ≤ ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
            ((θ : ℂ)*Complex.I)‖ := norm_nonneg _
      have hbound0 : |H.eval x| ≤
          2 * (s*r)^(n-2*M) *
            ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
              ((θ : ℂ)*Complex.I)‖^(2*M) := by
        calc
          _ = |2 * (s*r)^(n-2*M) *
              ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
                ((θ : ℂ)*Complex.I)‖^(2*M) *
              Real.cos ((n-2*M : ℕ)*θ + ((2*M : ℕ) : ℝ) *
                (((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
                  ((θ : ℂ)*Complex.I)).arg)| := congrArg abs hp
          _ = |2 * (s*r)^(n-2*M) *
              ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
                ((θ : ℂ)*Complex.I)‖^(2*M)| *
              |Real.cos ((n-2*M : ℕ)*θ + ((2*M : ℕ) : ℝ) *
                (((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
                  ((θ : ℂ)*Complex.I)).arg)| := by rw [abs_mul]
          _ ≤ |2 * (s*r)^(n-2*M) *
              ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
                ((θ : ℂ)*Complex.I)‖^(2*M)| := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hcosle (abs_nonneg _)
          _ = _ := abs_of_nonneg (by positivity)
      have hnormpow :
          ‖((r^2 : ℝ) : ℂ)+((s*r : ℝ) : ℂ)*Complex.exp
            ((θ : ℂ)*Complex.I)‖^(2*M) = (r^2*x)^M := by
        rw [pow_mul, hnormsq]
      rw [hnormpow] at hbound0
      have hscale :
          (s*r)^(n-2*M) * (r^2*x)^M =
            ((s*r)^n/s^(2*M))*x^M := by
        have hpow : (s*r)^n = (s*r)^(n-2*M) * (s*r)^(2*M) := by
          rw [← pow_add, Nat.sub_add_cancel hMle]
        rw [hpow]
        field_simp [ne_of_gt hs]
        simp only [mul_pow, pow_mul]
        ring
      calc
        _ ≤ 2 * ((s*r)^(n-2*M) * (r^2*x)^M) := by
          simpa only [mul_assoc] using hbound0
        _ = _ := by rw [hscale]; ring
theorem tilted_ceiling_path (t : ℝ) (ht : 0 < t) (ht4 : t < 1/4) :
    let M : ℕ → ℕ := fun i => Nat.ceil (t*(i : ℝ))
    M 0 = 0 ∧ M 1 = 1 ∧ M 2 = 1 ∧
    Monotone M ∧ (∀ i, M i ≤ i) ∧
    (∀ i, M (i+1) ≤ M i+1) ∧
    (∀ i, 3 ≤ i → 0 < M i ∧ 2*M i < i) ∧
    (∀ i, 0 ≤ (M i : ℝ)-t*i ∧ (M i : ℝ)-t*i < 1) := by
  intro M
  have ht1 : t ≤ 1 := by linarith
  have hnonneg (i : ℕ) : 0 ≤ t*(i : ℝ) := mul_nonneg ht.le (Nat.cast_nonneg _)
  have hm : Monotone M := fun i j hij => Nat.ceil_mono (by
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) ht.le)
  have h01 : M 0 = 0 := by simp [M]
  have h11 : M 1 = 1 := by
    apply le_antisymm
    · exact Nat.ceil_le.mpr (by simp; exact ht1)
    · exact Nat.one_le_ceil_iff.mpr (by simpa using ht)
  have h21 : M 2 = 1 := by
    apply le_antisymm
    · apply Nat.ceil_le.mpr
      norm_num
      linarith
    · exact Nat.one_le_ceil_iff.mpr (by norm_num; linarith)
  refine ⟨h01, h11, h21, hm, ?_, ?_, ?_, ?_⟩
  · intro i
    change Nat.ceil (t*(i : ℝ)) ≤ i
    apply Nat.ceil_le.mpr
    nlinarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
  · intro i
    calc
      M (i+1) ≤ Nat.ceil (t*(i : ℝ)+1) := Nat.ceil_mono (by push_cast; linarith)
      _ = M i+1 := Nat.ceil_add_one (hnonneg i)
  · intro i hi
    have hpos : 0 < M i := Nat.one_le_ceil_iff.mpr (by
      have : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
      exact mul_pos ht this)
    refine ⟨hpos, ?_⟩
    by_cases hi3 : i = 3
    · subst i
      have : M 3 ≤ 1 := Nat.ceil_le.mpr (by norm_num; linarith)
      omega
    · have hi4 : (4 : ℝ) ≤ i := by exact_mod_cast (show 4 ≤ i by omega)
      have hc := Nat.ceil_lt_add_one (hnonneg i)
      have htprod : t*(i : ℝ) < (i : ℝ)/4 := by
        nlinarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
      have : (2 : ℝ)*(M i : ℝ) < i := by
        change (M i : ℝ) < _ at hc
        linarith
      exact_mod_cast this
  · intro i
    exact ⟨sub_nonneg.mpr (Nat.le_ceil _), by
      have := Nat.ceil_lt_add_one (hnonneg i)
      change (M i : ℝ) < _ at this
      linarith⟩
theorem rounding_of_unit_pivot_map
    (D : ℕ) (hD : 0 < D) (P : Fin D → Polynomial ℝ) (e : Fin D → Fin D)
    (hdeg : ∀ i, (P i).natDegree < D)
    (hpiv : ∀ i, (P i).coeff (e i).val = 1)
    (htri : ∀ i j, i.val < j.val → (P i).coeff (e j).val = 0) :
    ∃ q : Fin D → Polynomial ℤ,
      LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)) ∧
      (∀ i, (q i).natDegree < D) ∧
      ∀ (i : Fin D) (x : ℝ), |Polynomial.aeval x (q i)| ≤ |(P i).eval x| +
        (1/2 : ℝ)*∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val),
          |(P j).eval x| := by
  classical
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := htri i j hlt
      rw [← hij, hpiv] at this
      norm_num at this
    · have := htri j i hgt
      rw [hij, hpiv] at this
      norm_num at this
  exact permuted_unit_pivot_integer_rounding D hD P
    (Equiv.ofBijective e ((Finite.injective_iff_bijective).mp he)) hdeg hpiv htri
theorem nested_interval_unit_pivots
    (D : ℕ) (hD : 0 < D) (M : ℕ → ℕ)
    (hM0 : M 0 = 0) (hM : Monotone M) (hMi : ∀ i, M i ≤ i)
    (hstep : ∀ i, M (i+1) ≤ M i+1)
    (F : ℕ → Polynomial ℝ)
    (hdeg : ∀ i, i < D → (F i).natDegree ≤ i)
    (hzero : (F 0).coeff 0 = 1)
    (hleft : ∀ i, 0 < i → i < D → M (i-1) < M i → (F i).coeff 0 = 1)
    (hright : ∀ i, 0 < i → i < D → M (i-1) = M i → (F i).coeff i = 1) :
    let h := M (D-1)
    let P : Fin D → Polynomial ℝ := fun i => Polynomial.X^(h-M i.val)*F i.val
    ∃ e : Fin D → Fin D,
      (∀ i, (P i).natDegree < D) ∧
      (∀ i, (P i).coeff (e i).val = 1) ∧
      (∀ i j, i.val < j.val → (P i).coeff (e j).val = 0) := by
  classical
  intro h P
  have hN : Monotone (fun i => i-M i) := by
    apply monotone_nat_of_le_succ
    intro i
    have := hstep i
    have := hMi i
    omega
  have hMh (i : Fin D) : M i.val ≤ h := hM (by omega)
  have hup (i : Fin D) : h+(i.val-M i.val) < D := by
    have hn := hN (show i.val ≤ D-1 by omega)
    dsimp only at hn
    have := hMi i.val
    have := hMi (D-1)
    dsimp [h]
    omega
  let e : Fin D → Fin D := fun i =>
    if hi : i.val = 0 then ⟨h, by have := hMi (D-1); dsimp [h]; omega⟩
    else if hl : M (i.val-1) < M i.val then ⟨h-M i.val, by have := hup i; omega⟩
    else ⟨h+(i.val-M i.val), hup i⟩
  have epiv (i : Fin D) : (P i).coeff (e i).val = 1 := by
    dsimp [e]
    split_ifs with hi hl
    · have hMi0 : M i.val = 0 := by rw [hi, hM0]
      dsimp [P]
      rw [hMi0, Nat.sub_zero]
      simpa [hi] using (Polynomial.coeff_X_pow_mul (F i.val) h 0).trans (by simpa [hi] using hzero)
    · dsimp [P]
      simpa only [Nat.zero_add] using
        (Polynomial.coeff_X_pow_mul (F i.val) (h-M i.val) 0).trans
          (hleft i.val (by omega) i.isLt hl)
    · have hmEq : M (i.val-1) = M i.val := le_antisymm
        (hM (Nat.sub_le _ _)) (by omega)
      have heq : h+(i.val-M i.val) = i.val+(h-M i.val) := by
        have := hMh i
        have := hMi i.val
        omega
      dsimp [P]
      rw [heq, Polynomial.coeff_X_pow_mul]
      exact hright i.val (by omega) i.isLt hmEq
  have pdeg (i : Fin D) : (P i).natDegree < D := by
    have hne : F i.val ≠ 0 := by
      intro heq
      have := epiv i
      simp [P, heq] at this
    dsimp [P]
    rw [Polynomial.natDegree_X_pow_mul _ hne]
    have := hdeg i.val i.isLt
    have := hMh i
    have := hMi i.val
    have := hup i
    omega
  refine ⟨e, pdeg, epiv, ?_⟩
  intro i j hij
  have hj0 : j.val ≠ 0 := by omega
  dsimp [e]
  split_ifs with hz hl
  · exact (hj0 hz).elim
  · have hmij : M i.val ≤ M (j.val-1) := hM (by omega)
    have hlt : h-M j.val < h-M i.val := by have := hMh j; omega
    dsimp [P]
    rw [Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]
  · have hmEq : M (j.val-1) = M j.val := le_antisymm
        (hM (Nat.sub_le _ _)) (by omega)
    have hNij := hN (show i.val ≤ j.val-1 by omega)
    dsimp only at hNij
    have hjMi := hMi (j.val-1)
    have hMi0 := hMi i.val
    have hMih := hMh i
    have hMjh := hMh j
    have hlt : (F i.val).natDegree+(h-M i.val) < h+(j.val-M j.val) := by
      have := hdeg i.val i.isLt
      omega
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    dsimp [P]
    apply lt_of_le_of_lt Polynomial.natDegree_mul_le
    rw [Polynomial.natDegree_X_pow]
    omega
theorem weighted_pivot_normalization_bound
    (s r t : ℝ) (n M : ℕ) (hs : 1 ≤ s) (hr : 0 < r) (hrs : r < s)
    (hMN : 2*M ≤ n)
    (hδ0 : 0 ≤ (M : ℝ)-t*n) (hδ1 : (M : ℝ)-t*n ≤ 1)
    (hL : 0 ≤ 2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s)) :
    let C := Real.log (s*r)-2*t*Real.log s
    let A := (s*r)^n/s^(2*M)
    let Z := (s^2)^(n-2*M)*(s^2-r^2)^(2*M)
    A ≤ Real.exp ((n : ℝ)*C) ∧
      A/Z ≤ Real.exp ((n : ℝ)*C)*Real.exp (2*|Real.log s-Real.log (s^2-r^2)|) := by
  intro C A Z
  have hs0 : 0 < s := by linarith
  have hk : 0 < s^2-r^2 := by nlinarith
  have hd : 0 < s*r := mul_pos hs0 hr
  have hA : 0 < A := by dsimp [A]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hlogA : Real.log A = (n : ℝ)*C-2*((M : ℝ)-t*n)*Real.log s := by
    dsimp [A, C]
    rw [Real.log_div (pow_pos hd _).ne' (pow_pos hs0 _).ne',
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogZ : Real.log Z =
      (n : ℝ)*(2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s)) +
        2*((M : ℝ)-t*n)*(Real.log (s^2-r^2)-2*Real.log s) := by
    dsimp [Z]
    rw [Real.log_mul (pow_pos (sq_pos_of_pos hs0) _).ne'
      (pow_pos hk _).ne', Real.log_pow, Real.log_pow, Real.log_pow]
    rw [Nat.cast_sub hMN]
    push_cast
    ring
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs
  constructor
  · rw [← Real.exp_log hA]
    apply Real.exp_le_exp.mpr
    rw [hlogA]
    nlinarith
  · rw [← Real.exp_log (div_pos hA hZ), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hA.ne' hZ.ne', hlogA, hlogZ]
    have hnl : 0 ≤ (n : ℝ)*(2*Real.log s+
        2*t*(Real.log (s^2-r^2)-2*Real.log s)) :=
      mul_nonneg (Nat.cast_nonneg n) hL
    have hdelta : ((M : ℝ)-t*n)*(Real.log s-Real.log (s^2-r^2)) ≤
        |Real.log s-Real.log (s^2-r^2)| := by
      calc
        _ ≤ ((M : ℝ)-t*n)*|Real.log s-Real.log (s^2-r^2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hδ0
        _ ≤ |Real.log s-Real.log (s^2-r^2)| :=
          (mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)).trans_eq (one_mul _)
    nlinarith
theorem tilted_laurent_numerators
    (s r t : ℝ) (hr : 0 < r) (hrs : r < s) (hs : 1 ≤ s)
    (ht : 0 < t) (ht4 : t < 1/4)
    (hC : 0 ≤ Real.log (s*r)-2*t*Real.log s)
    (hL : 0 ≤ 2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s)) :
    let M : ℕ → ℕ := fun i => Nat.ceil (t*(i : ℝ))
    let C := Real.log (s*r)-2*t*Real.log s
    ∃ B : ℝ, 0 < B ∧ ∃ F : ℕ → Polynomial ℝ,
      (∀ i, (F i).natDegree ≤ i) ∧ (F 0).coeff 0 = 1 ∧
      (∀ i, 0 < i → M (i-1) < M i → (F i).coeff 0 = 1) ∧
      (∀ i, 0 < i → M (i-1) = M i → (F i).coeff i = 1) ∧
      ∀ i x, x ∈ Set.Icc ((s-r)^2) ((s+r)^2) →
        |(F i).eval x| ≤ B*Real.exp ((i : ℝ)*C)*x^(M i) := by
  set_option maxHeartbeats 800000 in
    classical
    intro M C
    obtain ⟨hM0, hM1, hM2, hMmono, hMle, hMstep, hMlarge, hδ⟩ :=
      tilted_ceiling_path t ht ht4
    change M 0 = 0 at hM0
    change M 1 = 1 at hM1
    change M 2 = 1 at hM2
    change ∀ i, 3 ≤ i → 0 < M i ∧ 2*M i < i at hMlarge
    change ∀ i, 0 ≤ (M i : ℝ)-t*i ∧ (M i : ℝ)-t*i < 1 at hδ
    let H : ℕ → Polynomial ℝ := fun i => ∑ j ∈ Finset.range (2*M i+1),
      Polynomial.C ((Nat.choose (2*M i) j : ℝ)*(r^2)^j) *
        scaledChebyshev (s*r) (s^2+r^2) (i-j)
    have hH (i : ℕ) (hi : 3 ≤ i) :
        (H i).Monic ∧ (H i).natDegree = i ∧
        (H i).coeff 0 = (-(s^2))^(i-2*M i)*(r^2-s^2)^(2*M i) ∧
        ∀ x, x ∈ Set.Icc ((s-r)^2) ((s+r)^2) →
          |(H i).eval x| ≤ 2*((s*r)^i/s^(2*M i))*x^(M i) :=
      weightedChebyshev_general_pivots s r i (M i) hr hrs
        (hMlarge i hi).1 (hMlarge i hi).2
    have hs0 : 0 < s := by linarith
    have hk : 0 < s^2-r^2 := by nlinarith
    have ha : 0 < (s-r)^2 := sq_pos_of_pos (sub_pos.mpr hrs)
    have hb : 0 ≤ (s+r)^2 := sq_nonneg _
    let E := Real.exp (2*|Real.log s-Real.log (s^2-r^2)|)
    let B : ℝ := 3+((s-r)^2)⁻¹+(s+r)^2+2*E
    have hE : 0 < E := Real.exp_pos _
    have hB : 0 < B := by dsimp [B]; positivity
    have hB1 : 1 ≤ B := by dsimp [B]; linarith [inv_pos.mpr ha]
    have hBa : ((s-r)^2)⁻¹ ≤ B := by dsimp [B]; linarith [inv_pos.mpr ha]
    have hBb : (s+r)^2 ≤ B := by dsimp [B]; linarith [inv_pos.mpr ha]
    have hB2 : 2 ≤ B := by dsimp [B]; linarith [inv_pos.mpr ha]
    have hBE : 2*E ≤ B := by dsimp [B]; linarith [inv_pos.mpr ha]
    have hH0 (i : ℕ) (hi : 3 ≤ i) : (H i).coeff 0 ≠ 0 := by
      rw [(hH i hi).2.2.1]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (pow_pos hs0 2).ne'))
        (pow_ne_zero _ (by nlinarith))
    have hHabs (i : ℕ) (hi : 3 ≤ i) : |(H i).coeff 0| =
        (s^2)^(i-2*M i)*(s^2-r^2)^(2*M i) := by
      rw [(hH i hi).2.2.1, abs_mul, abs_pow, abs_pow, abs_neg,
        abs_of_pos (pow_pos hs0 2), abs_of_neg (by nlinarith : r^2-s^2 < 0)]
      congr 2
      ring
    let F : ℕ → Polynomial ℝ := fun i =>
      if i ≤ 1 then 1 else if i = 2 then Polynomial.X^2
      else if M (i-1) < M i then Polynomial.C ((H i).coeff 0)⁻¹ * H i else H i
    refine ⟨B, hB, F, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      dsimp [F]
      split_ifs with hi hi2 hl
      · simp
      · subst i; simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [(hH i (by omega)).2.1])
      · exact (hH i (by omega)).2.1.le
    · simp [F]
    · intro i hi hl
      by_cases hi1 : i ≤ 1
      · simp [F, hi1]
      by_cases hi2 : i = 2
      · subst i
        simp only [Nat.reduceSub, hM1, hM2, lt_self_iff_false] at hl
      · simp only [F, ite_eq_right hi1, ite_eq_right hi2, ite_eq_left hl, Polynomial.coeff_C_mul]
        exact inv_mul_cancel₀ (hH0 i (by omega))
    · intro i hi hmEq
      have hi1 : ¬i ≤ 1 := by
        intro hi1
        have : i = 1 := by omega
        subst i
        simp [hM0, hM1] at hmEq
      by_cases hi2 : i = 2
      · simp [F, hi2]
      · have hl : ¬M (i-1) < M i := by omega
        simp only [F, ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hl]
        simpa only [(hH i (by omega)).2.1] using
          (hH i (by omega)).1.coeff_natDegree
    · intro i x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      have hexp : 1 ≤ Real.exp ((i : ℝ)*C) := Real.one_le_exp_iff.mpr
        (mul_nonneg (Nat.cast_nonneg i) hC)
      have hBX : 0 ≤ B*Real.exp ((i : ℝ)*C) := by positivity
      by_cases hi1 : i ≤ 1
      · have hiCases : i = 0 ∨ i = 1 := by omega
        rcases hiCases with rfl | rfl
        · simpa [F, hM0] using hB1
        · have hxa : 1 ≤ B*x := by
            have := mul_le_mul_of_nonneg_left hx.1 (le_trans (by positivity) hBa)
            have : 1 ≤ B*((s-r)^2) := by
              have := mul_le_mul_of_nonneg_right hBa ha.le
              simpa [ha.ne'] using this
            nlinarith
          have : 1 ≤ B*Real.exp C*x := by
            calc
              1 ≤ B*x := hxa
              _ ≤ B*Real.exp C*x := by
                have he : 1 ≤ Real.exp C := by simpa using hexp
                nlinarith [mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hB.le hx0.le)]
          simpa [F, hM1] using this
      by_cases hi2 : i = 2
      · subst i
        have hxb : x ≤ B := hx.2.trans hBb
        have hble : B ≤ B*Real.exp ((2 : ℝ)*C) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (show 1 ≤ Real.exp ((2 : ℝ)*C) by simpa using hexp) hB.le
        have : x^2 ≤ B*Real.exp ((2 : ℝ)*C)*x := by nlinarith
        simpa [F, hM2, abs_of_pos hx0, abs_of_nonneg (sq_nonneg x)] using this
      have hi : 3 ≤ i := by omega
      have hnorm := weighted_pivot_normalization_bound s r t i (M i) hs hr hrs
        (hMlarge i hi).2.le (hδ i).1 (hδ i).2.le hL
      change (s*r)^i/s^(2*M i) ≤ Real.exp ((i : ℝ)*C) ∧
        ((s*r)^i/s^(2*M i))/((s^2)^(i-2*M i)*(s^2-r^2)^(2*M i)) ≤
          Real.exp ((i : ℝ)*C)*E at hnorm
      have heval := (hH i hi).2.2.2 x hx
      dsimp [F]
      rw [ite_eq_right hi1, ite_eq_right hi2]
      split_ifs with hl
      · simp only [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_inv]
        calc
          _ ≤ |(H i).coeff 0|⁻¹ * (2*((s*r)^i/s^(2*M i))*x^(M i)) :=
            mul_le_mul_of_nonneg_left heval (inv_nonneg.mpr (abs_nonneg _))
          _ = 2*(((s*r)^i/s^(2*M i))/
              ((s^2)^(i-2*M i)*(s^2-r^2)^(2*M i)))*x^(M i) := by
            rw [hHabs i hi]; ring
          _ ≤ 2*(Real.exp ((i : ℝ)*C)*E)*x^(M i) := by
            gcongr
            exact hnorm.2
          _ ≤ B*Real.exp ((i : ℝ)*C)*x^(M i) := by
            calc
              _ = (2*E)*Real.exp ((i : ℝ)*C)*x^(M i) := by ring
              _ ≤ _ := by gcongr
      · calc
          _ ≤ 2*((s*r)^i/s^(2*M i))*x^(M i) := heval
          _ ≤ 2*Real.exp ((i : ℝ)*C)*x^(M i) := by gcongr; exact hnorm.1
          _ ≤ B*Real.exp ((i : ℝ)*C)*x^(M i) := by gcongr
theorem ceiling_shift_exp_bound
    (a b t C x : ℝ) (D : ℕ) (hD : 0 < D)
    (ha : 0 < a) (hx : x ∈ Set.Icc a b) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp ((D : ℝ)*C)*x^(Nat.ceil (t*((D-1 : ℕ) : ℝ))) ≤
      Real.exp (|Real.log a|+|Real.log b|)*
        Real.exp ((D : ℝ)*(C+t*Real.log x)) := by
  have hx0 : 0 < x := ha.trans_le hx.1
  let h := Nat.ceil (t*((D-1 : ℕ) : ℝ))
  have hcast : ((D-1 : ℕ) : ℝ) = (D : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ D)]
    norm_num
  have hnonneg : 0 ≤ t*((D-1 : ℕ) : ℝ) := mul_nonneg ht (Nat.cast_nonneg _)
  have hlo := Nat.le_ceil (t*((D-1 : ℕ) : ℝ))
  have hhi := Nat.ceil_lt_add_one hnonneg
  change t*((D-1 : ℕ) : ℝ) ≤ (h : ℝ) at hlo
  change (h : ℝ) < t*((D-1 : ℕ) : ℝ)+1 at hhi
  rw [hcast] at hlo hhi
  have hδ : |(h : ℝ)-t*D| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hlog : |Real.log x| ≤ |Real.log a|+|Real.log b| := by
    have hl := Real.log_le_log ha hx.1
    have hu := Real.log_le_log hx0 hx.2
    have hal := neg_abs_le (Real.log a)
    have hbu := le_abs_self (Real.log b)
    have haa := abs_nonneg (Real.log a)
    have hba := abs_nonneg (Real.log b)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmul : ((h : ℝ)-t*D)*Real.log x ≤ |Real.log a|+|Real.log b| := by
    calc
      _ ≤ |((h : ℝ)-t*D)*Real.log x| := le_abs_self _
      _ = |(h : ℝ)-t*D| * |Real.log x| := abs_mul _ _
      _ ≤ 1*(|Real.log a|+|Real.log b|) :=
        mul_le_mul hδ hlog (abs_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hxpow : x^h = Real.exp ((h : ℝ)*Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx0]
  change Real.exp ((D : ℝ)*C)*x^h ≤ _
  rw [hxpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith
theorem tilted_short_integer_polynomials
    (s r t : ℝ) (hr : 0 < r) (hrs : r < s) (hs : 1 ≤ s)
    (ht : 0 < t) (ht4 : t < 1/4)
    (hC : 0 ≤ Real.log (s*r)-2*t*Real.log s)
    (hL : 0 ≤ 2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s)) :
    let C := Real.log (s*r)-2*t*Real.log s
    ∃ B : ℝ, 0 < B ∧ ∀ D : ℕ, 3 ≤ D →
      ∃ q : Fin D → Polynomial ℤ,
        LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)) ∧
        (∀ i, (q i).natDegree < D) ∧
        ∀ (i : Fin D) (x : ℝ), x ∈ Set.Icc ((s-r)^2) ((s+r)^2) →
          |Polynomial.aeval x (q i)| ≤
            B*((D : ℝ)+1)*Real.exp ((D : ℝ)*(C+t*Real.log x)) := by
  classical
  intro C
  let M : ℕ → ℕ := fun i => Nat.ceil (t*(i : ℝ))
  obtain ⟨hM0, hM1, hM2, hMmono, hMle, hMstep, hMlarge, hδ⟩ :=
    tilted_ceiling_path t ht ht4
  obtain ⟨B0, hB0, F, hFdeg, hFzero, hFleft, hFright, hFeval⟩ :=
    tilted_laurent_numerators s r t hr hrs hs ht ht4 hC hL
  change ∀ i x, x ∈ Set.Icc ((s-r)^2) ((s+r)^2) →
    |(F i).eval x| ≤ B0*Real.exp ((i : ℝ)*C)*x^(M i) at hFeval
  let J := |Real.log ((s-r)^2)|+|Real.log ((s+r)^2)|
  refine ⟨B0*Real.exp J, by positivity, ?_⟩
  intro D hD3
  have hD : 0 < D := by omega
  let h := M (D-1)
  let P : Fin D → Polynomial ℝ := fun i => Polynomial.X^(h-M i.val)*F i.val
  obtain ⟨e, hPdeg, hPpiv, hPtri⟩ := nested_interval_unit_pivots D hD M
    hM0 hMmono hMle hMstep F (fun i hi => hFdeg i) hFzero
    (fun i hi _ hl => hFleft i hi hl) (fun i hi _ he => hFright i hi he)
  change ∀ i, (P i).natDegree < D at hPdeg
  change ∀ i, (P i).coeff (e i).val = 1 at hPpiv
  change ∀ i j, i.val < j.val → (P i).coeff (e j).val = 0 at hPtri
  obtain ⟨q, hqind, hqdeg, hqbound⟩ :=
    rounding_of_unit_pivot_map D hD P e hPdeg hPpiv hPtri
  refine ⟨q, hqind, hqdeg, ?_⟩
  intro i x hx
  have ha : 0 < (s-r)^2 := sq_pos_of_pos (sub_pos.mpr hrs)
  have hx0 : 0 < x := ha.trans_le hx.1
  let K := B0*Real.exp ((D : ℝ)*C)*x^h
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hPbound (j : Fin D) : |(P j).eval x| ≤ K := by
    have hmj : M j.val ≤ h := hMmono (by omega)
    have hpow : x^(h-M j.val)*x^(M j.val) = x^h := by
      rw [← pow_add, Nat.sub_add_cancel hmj]
    have he : Real.exp ((j.val : ℝ)*C) ≤ Real.exp ((D : ℝ)*C) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_of_lt j.isLt)) hC
    calc
      _ = x^(h-M j.val)*|(F j.val).eval x| := by
        simp only [P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, abs_mul,
          abs_of_nonneg (pow_nonneg hx0.le _)]
      _ ≤ x^(h-M j.val)*(B0*Real.exp ((j.val : ℝ)*C)*x^(M j.val)) :=
        mul_le_mul_of_nonneg_left (hFeval j.val x hx) (pow_nonneg hx0.le _)
      _ = B0*Real.exp ((j.val : ℝ)*C)*x^h := by rw [← hpow]; ring
      _ ≤ K := by dsimp [K]; gcongr
  have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val),
      |(P j).eval x|) ≤ (D : ℝ)*K := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin D => j.val < i.val), K :=
        Finset.sum_le_sum (fun j _ => hPbound j)
      _ = ((Finset.univ.filter (fun j : Fin D => j.val < i.val)).card : ℝ)*K := by simp
      _ ≤ (D : ℝ)*K := by
        apply mul_le_mul_of_nonneg_right _ hK
        exact_mod_cast (Finset.card_filter_le (Finset.univ : Finset (Fin D))
          (fun j => j.val < i.val)).trans_eq (Finset.card_univ.trans (Fintype.card_fin D))
  have hqK : |Polynomial.aeval x (q i)| ≤ ((D : ℝ)+1)*K := by
    have hqb := hqbound i x
    have hPi := hPbound i
    have hDK : 0 ≤ (D : ℝ)*K := mul_nonneg (Nat.cast_nonneg D) hK
    nlinarith
  have hshift := ceiling_shift_exp_bound ((s-r)^2) ((s+r)^2) t C x D hD ha hx ht.le
    (by linarith)
  change Real.exp ((D : ℝ)*C)*x^h ≤
    Real.exp J*Real.exp ((D : ℝ)*(C+t*Real.log x)) at hshift
  calc
    _ ≤ ((D : ℝ)+1)*K := hqK
    _ = (B0*((D : ℝ)+1))*(Real.exp ((D : ℝ)*C)*x^h) := by dsimp [K]; ring
    _ ≤ (B0*((D : ℝ)+1))*(Real.exp J*Real.exp ((D : ℝ)*(C+t*Real.log x))) := by
      exact mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = _ := by ring
theorem fixed_tilt_short_integer_polynomials :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let t : ℝ := 3000000/13999999
    let C := Real.log d-2*t*Real.log s
    ∃ B : ℝ, 0 < B ∧ ∀ D : ℕ, 3 ≤ D →
      ∃ q : Fin D → Polynomial ℤ,
        LinearIndependent ℚ (fun i => (q i).map (Int.castRingHom ℚ)) ∧
        (∀ i, (q i).natDegree < D) ∧
        ∀ (i : Fin D) (x : ℝ), x ∈ Set.Icc (u^2) (v^2) →
          |Polynomial.aeval x (q i)| ≤
            B*((D : ℝ)+1)*Real.exp ((D : ℝ)*(C+t*Real.log x)) := by
  intro u v s r d t C
  have hr : 0 < r := by norm_num [r, v, u]
  have hrs : r < s := by norm_num [r, s, v, u]
  have hs : 1 ≤ s := by norm_num [s, v, u]
  have ht : 0 < t := by norm_num [t]
  have ht4 : t < 1/4 := by norm_num [t]
  have hsu : s-r = u := by dsimp [s, r]; ring
  have hsv : s+r = v := by dsimp [s, r]; ring
  have hprod : s^2-r^2 = u*v := by dsimp [s, r]; ring
  have hmarg := fixed_tilt_strict_margins
  change (1/10000000 : ℝ) < C ∧
    (1/10000000 : ℝ) < 2*Real.log s+2*t*(Real.log (u*v)-2*Real.log s) at hmarg
  have hC : 0 ≤ Real.log (s*r)-2*t*Real.log s := by
    change 0 ≤ C
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1/10000000) hmarg.1.le
  have hL : 0 ≤ 2*Real.log s+2*t*(Real.log (s^2-r^2)-2*Real.log s) := by
    rw [hprod]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1/10000000) hmarg.2.le
  simpa only [hsu, hsv] using tilted_short_integer_polynomials s r t hr hrs hs ht ht4 hC hL
theorem fixed_tilt_weight_normalization :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    let t : ℝ := 3000000/13999999
    let C := Real.log d-2*t*Real.log s
    ∀ (L : ℕ) (x : ℝ), 0 < x →
      let k : ℕ := 1000000*L
      let D : ℕ := 13999999*L
      (d^14/s^6)^k*x^(3*k) =
        d^L*Real.exp ((D : ℝ)*(C+t*Real.log x)) := by
  intro u v s r d t C L x hx k D
  have hs : 0 < s := by norm_num [s, u, v]
  have hd : 0 < d := by norm_num [d, s, r, u, v]
  have hA : 0 < d^14/s^6 := div_pos (pow_pos hd _) (pow_pos hs _)
  have hweight : 0 < (d^14/s^6)^k*x^(3*k) :=
    mul_pos (pow_pos hA _) (pow_pos hx _)
  have hlog : Real.log ((d^14/s^6)^k*x^(3*k)) =
      (L : ℝ)*Real.log d + (D : ℝ)*(C+t*Real.log x) := by
    rw [Real.log_mul (pow_ne_zero k hA.ne') (pow_ne_zero (3*k) hx.ne'),
      Real.log_pow, Real.log_pow,
      Real.log_div (pow_ne_zero 14 hd.ne') (pow_ne_zero 6 hs.ne'),
      Real.log_pow, Real.log_pow]
    dsimp [k, D, C, t]
    push_cast
    ring
  calc
    _ = Real.exp (Real.log ((d^14/s^6)^k*x^(3*k))) :=
      (Real.exp_log hweight).symm
    _ = Real.exp ((L : ℝ)*Real.log d + (D : ℝ)*(C+t*Real.log x)) :=
      congrArg Real.exp hlog
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hd]
theorem fixed_tilt_eventual_rounding_budget :
    let u : ℝ := 294811/1000000
    let v : ℝ := 1049707/500000
    let s := (u+v)/2
    let r := (v-u)/2
    let d := s*r
    ∀ B : ℝ, 0 < B → ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
      let D : ℕ := 13999999*L
      (D : ℝ)/2*B*((D : ℝ)+1) < d^L := by
  intro u v s r d B hB
  have hd : 1 < d := by norm_num [d, s, r, u, v]
  have hlim2 := tendsto_pow_const_div_const_pow_of_one_lt 2 hd
  have hlim1 : Filter.Tendsto (fun L : ℕ => (L : ℝ)/d^L)
      Filter.atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hd
  let a : ℝ := 13999999
  have hlim : Filter.Tendsto
      (fun L : ℕ => (a/2*B*a)*((L : ℝ)^2/d^L) + (a/2*B)*((L : ℝ)/d^L))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hlim2.const_mul (a/2*B*a)).add (hlim1.const_mul (a/2*B))
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨L0, fun L hL => ?_⟩
  dsimp only
  have hineq := hL0 L hL
  have hden : 0 < d^L := pow_pos (lt_trans zero_lt_one hd) L
  have hbudget :
      (((13999999*L : ℕ) : ℝ)/2*B*(((13999999*L : ℕ) : ℝ)+1))/d^L =
        (a/2*B*a)*((L : ℝ)^2/d^L) + (a/2*B)*((L : ℝ)/d^L) := by
    push_cast
    dsimp [a]
    ring
  exact (div_lt_one hden).mp (by rw [hbudget]; exact hineq)
theorem explicit_unbounded_positive_polynomials :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∀ N : ℕ, ∃ p : Polynomial ℤ,
      p.Monic ∧ Squarefree p ∧ N < p.natDegree ∧
      (∀ z : ℂ, z ∈ p.aroots ℂ → 0 < z) ∧
      -((p.coeff (p.natDegree-1) : ℤ) : ℝ) <
        (1.898306 : ℝ)*(p.natDegree : ℝ) := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  classical
  intro N
  let u : ℝ := 294811/1000000
  let v : ℝ := 1049707/500000
  let s := (u+v)/2
  let r := (v-u)/2
  let d := s*r
  let c := s^2+r^2
  let A := d^14/s^6
  let t : ℝ := 3000000/13999999
  let C := Real.log d-2*t*Real.log s
  let R : ℕ → Polynomial ℝ := fun j =>
    Polynomial.C (d^j) * (Polynomial.Chebyshev.C ℝ (j : ℤ)).comp
      (Polynomial.C d⁻¹ * (Polynomial.X-Polynomial.C c))
  let H : ℕ → Polynomial ℝ := fun k => ∑ j ∈ Finset.range (6*k+1),
    Polynomial.C ((Nat.choose (6*k) j : ℝ)*(r^2)^j)*R (14*k-j)
  have hu : 0 < u := by norm_num [u]
  have huv : u < v := by norm_num [u, v]
  have hs : 0 < s := by norm_num [s, u, v]
  have hd : 0 < d := by norm_num [d, s, r, u, v]
  have hA : 0 < A := div_pos (pow_pos hd _) (pow_pos hs _)
  have htop : ∃ K : ℕ, 0 < K ∧ ∀ l : ℕ, 0 < l → let k := K*l
      ∀ m : ℕ, m < 8*k → ∃ T : Polynomial ℝ,
        T.Monic ∧ T.natDegree = 14*k ∧
        T.coeff (14*k-1) = (H k).coeff (14*k-1) ∧
        (∀ j : ℕ, j ≤ m → ∃ z : ℤ, T.coeff (14*k-j) = (z : ℝ)) ∧
        ∀ y : ℝ, y ∈ Set.Icc (u^2) (v^2) →
          |T.eval y-(H k).eval y| ≤ (1/2 : ℝ)*A^k*y^(3*k) :=
    weighted_top_block_rounding
  obtain ⟨K, hK, htop⟩ := htop
  obtain ⟨B, hB, hshort⟩ := fixed_tilt_short_integer_polynomials
  obtain ⟨L0, hbudget⟩ := fixed_tilt_eventual_rounding_budget B hB
  let l : ℕ := L0+N+1
  let L : ℕ := K*l
  let k : ℕ := 1000000*L
  let n : ℕ := 14*k
  let D : ℕ := 13999999*L
  have hl : 0 < l := by dsimp [l]; omega
  have hL : 0 < L := Nat.mul_pos hK hl
  have hlL : l ≤ L := by
    dsimp [L]
    nlinarith [show 1 ≤ K by omega]
  have hL0 : L0 ≤ L := by dsimp [l] at hlL; omega
  have hk : 0 < k := Nat.mul_pos (by norm_num) hL
  have hn : 0 < n := Nat.mul_pos (by norm_num) hk
  have hN : N < n := by dsimp [l] at hlL; dsimp [n, k]; omega
  have hD3 : 3 ≤ D := by dsimp [D]; omega
  have hD : 0 < D := by omega
  have hDn : D < n := by dsimp [D, n, k]; omega
  have hnD : n = D+L := by dsimp [n, D, k]; omega
  have hkprog : K*(1000000*l) = k := by dsimp [k, L]; ring
  have hTdata := htop (1000000*l) (by omega)
  dsimp only at hTdata
  rw [hkprog] at hTdata
  obtain ⟨T, hT, hTd, hTtrace, hTint, hTerr⟩ := hTdata L (by dsimp [k]; omega)
  have hTintop : ∀ i : ℕ, D ≤ i → ∃ z : ℤ, T.coeff i = (z : ℝ) := by
    intro i hi
    by_cases hin : i ≤ n
    · obtain ⟨z, hz⟩ := hTint (n-i) (by omega)
      refine ⟨z, ?_⟩
      have heq : 14*k-(n-i) = i := by change n-(n-i) = i; omega
      rwa [heq] at hz
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      norm_num
  have htarget := explicit_weighted_chebyshev_target u v k hu huv hk
  change (H k).Monic ∧ (H k).natDegree = n ∧
    (H k).coeff (n-1) = -(14*k : ℝ)*c+(6*k : ℝ)*r^2 ∧
    ∃ x : Fin (n+1) → ℝ, StrictMono x ∧ x 0 = u^2 ∧
      x (Fin.last n) = v^2 ∧ ∀ j,
        (H k).eval (x j) = (-1 : ℝ)^j.val*2*A^k*(x j)^(3*k) at htarget
  obtain ⟨_, _, hHtrace, x, hx, hx0, hxlast, hxeval⟩ := htarget
  have hxmem : ∀ j : Fin (n+1), x j ∈ Set.Icc (u^2) (v^2) := by
    intro j
    constructor
    · rw [← hx0]
      apply hx.monotone
      change 0 ≤ j.val
      exact Nat.zero_le _
    · rw [← hxlast]
      apply hx.monotone
      change j.val ≤ n
      exact Nat.le_of_lt_succ j.isLt
  have hxpos : ∀ j : Fin (n+1), 0 < x j := by
    intro j
    exact (sq_pos_of_pos hu).trans_le (hxmem j).1
  let W : ℝ → ℝ := fun y => A^k*y^(3*k)
  let E : ℝ → ℝ := fun y => Real.exp ((D : ℝ)*(C+t*Real.log y))
  have hW : ∀ y : ℝ, 0 < y → 0 < W y := by
    intro y hy
    exact mul_pos (pow_pos hA _) (pow_pos hy _)
  have heval : ∀ j : Fin (n+1),
      (H k).eval (x j) = (-1 : ℝ)^j.val*2*W (x j) := by
    intro j
    simpa only [W, mul_assoc] using hxeval j
  have habs : ∀ j : Fin (n+1), |(H k).eval (x j)| = 2*W (x j) := by
    intro j
    rw [heval]
    simp [abs_mul, abs_of_pos (hW _ (hxpos j))]
  have halt : ∀ i : Fin n,
      (H k).eval (x i.castSucc)*(H k).eval (x i.succ) < 0 := by
    intro i
    have hsign : (-1 : ℝ)^i.val*(-1 : ℝ)^i.val = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = -4*W (x i.castSucc)*W (x i.succ) := by
        rw [heval, heval]
        simp only [Fin.val_castSucc, Fin.val_succ, pow_succ]
        calc
          _ = -4*((-1 : ℝ)^i.val*(-1 : ℝ)^i.val)*
              W (x i.castSucc)*W (x i.succ) := by ring
          _ = _ := by rw [hsign]; ring
      _ < 0 := by
        have := mul_pos (hW _ (hxpos i.castSucc)) (hW _ (hxpos i.succ))
        nlinarith
  have hnorm : ∀ y : ℝ, 0 < y → W y = d^L*E y := by
    intro y hy
    exact fixed_tilt_weight_normalization L y hy
  have hbud : (D : ℝ)/2*B*((D : ℝ)+1) < d^L := hbudget L hL0
  obtain ⟨q, hq, hqdeg, hqbound⟩ := hshort D hD3
  have hround : ∀ j : Fin (n+1), |T.eval (x j)-(H k).eval (x j)| +
      (1/2 : ℝ)*(∑ i : Fin D, |Polynomial.aeval (x j) (q i)|) <
        |(H k).eval (x j)| := by
    intro j
    have hsum : ∑ i : Fin D, |Polynomial.aeval (x j) (q i)| ≤
        (D : ℝ)*(B*((D : ℝ)+1)*E (x j)) := by
      calc
        _ ≤ ∑ _i : Fin D, B*((D : ℝ)+1)*E (x j) := by
          apply Finset.sum_le_sum
          intro i _
          exact hqbound i (x j) (hxmem j)
        _ = _ := by simp
    have hsmall : (1/2 : ℝ)*(∑ i : Fin D, |Polynomial.aeval (x j) (q i)|) <
        W (x j) := by
      calc
        _ ≤ (1/2 : ℝ)*((D : ℝ)*(B*((D : ℝ)+1)*E (x j))) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = ((D : ℝ)/2*B*((D : ℝ)+1))*E (x j) := by ring
        _ < d^L*E (x j) := mul_lt_mul_of_pos_right hbud (Real.exp_pos _)
        _ = W (x j) := (hnorm _ (hxpos j)).symm
    have htoperr : |T.eval (x j)-(H k).eval (x j)| ≤ (1/2 : ℝ)*W (x j) := by
      simpa only [W, mul_assoc] using hTerr (x j) (hxmem j)
    rw [habs]
    linarith [hW _ (hxpos j)]
  obtain ⟨p, hp, hpd, hptrace, hpsq, hppos⟩ :=
    integral_top_block_short_basis_realization n D hD hDn T (H k)
      hT hTd hTintop q hq hqdeg x hx hxpos halt hround
  have htrace : -((p.coeff (n-1) : ℤ) : ℝ) =
      (53152561404811/28000000000000 : ℝ)*(n : ℝ) := by
    rw [hptrace, hTtrace, hHtrace]
    dsimp [n, c, s, r, u, v]
    push_cast
    ring
  refine ⟨p, hp, hpsq, ?_, hppos, ?_⟩
  · rwa [hpd]
  · rw [hpd, htrace]
    exact mul_lt_mul_of_pos_right (by norm_num) (Nat.cast_pos.mpr hn)
theorem exists_small_trace_infinite_family :
    letI : PartialOrder ℂ := Complex.partialOrder
    ∃ (c : ℝ), 0 ≤ c ∧ c < (1.89831 : ℝ) ∧
      Set.Infinite { α : ℂ | IsIntegral ℤ α ∧
        AlgebraicIntegers.IsTotallyPositive α ∧
        AlgebraicIntegers.trace α < (c : ℂ) * AlgebraicIntegers.degree α } := by
  let _ : PartialOrder ℂ := Complex.partialOrder
  exact exists_small_trace_infinite_family_of_squarefree_polynomials
    (1.898306 : ℝ) (by norm_num) (by norm_num)
    explicit_unbounded_positive_polynomials
end Submission.Helpers
