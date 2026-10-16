import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import ChallengeDeps
namespace Submission.Helpers

theorem coefficient_continuous (n d : ℕ) (m : Fin n →₀ ℕ) :
    Continuous (fun f : LorentzianPolynomials.H n d => f.1.coeff m) := by
  let : TopologicalSpace (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) :=
    moduleTopology ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d)
  change Continuous
    (fun f : MvPolynomial.homogeneousSubmodule (Fin n) ℝ d => f.1.coeff m)
  exact IsModuleTopology.continuous_of_linearMap
    ((MvPolynomial.lcoeff ℝ m).comp
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d).subtype)
lemma positive_mixing_variable_pderiv (n : ℕ) (t : ℝ) (i j : Fin n) :
    MvPolynomial.pderiv i (MvPolynomial.X j + MvPolynomial.C t *
      ∑ k : Fin n, (MvPolynomial.X k : MvPolynomial (Fin n) ℝ)) =
      MvPolynomial.C ((if j = i then 1 else 0) + t) := by
  classical
  have hs : MvPolynomial.pderiv i
      (∑ k : Fin n, (MvPolynomial.X k : MvPolynomial (Fin n) ℝ)) = 1 := by
    rw [map_sum]
    simp [MvPolynomial.pderiv_X, Pi.single_apply]
  rw [map_add, MvPolynomial.pderiv_C_mul, hs, mul_one]
  by_cases h : j = i <;> simp [h]
lemma positive_mixing_pderiv_chain (n : ℕ) (t : ℝ) (k : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv k (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) p) =
      ∑ i : Fin n, ((if i = k then 1 else 0) + t) •
        MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
          ∑ j : Fin n, MvPolynomial.X j) (MvPolynomial.pderiv i p) := by
  classical
  let E := MvPolynomial.aeval (R := ℝ)
    (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
      ∑ j : Fin n, MvPolynomial.X j)
  change MvPolynomial.pderiv k (E p) = ∑ i : Fin n,
    ((if i = k then 1 else 0) + t) • E (MvPolynomial.pderiv i p)
  induction p using MvPolynomial.induction_on with
  | C c => simp [E, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, MvPolynomial.pderiv_mul, hp]
    have hvar : MvPolynomial.pderiv k (E (MvPolynomial.X j)) =
        MvPolynomial.C ((if j = k then 1 else 0) + t) := by
      simpa only [E, MvPolynomial.aeval_X] using positive_mixing_variable_pderiv n t k j
    rw [hvar]
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, smul_add,
      Finset.sum_add_distrib, ← smul_mul_assoc, ← Finset.sum_mul]
    congr 1
    simp [MvPolynomial.pderiv_X, Pi.single_apply, E, Algebra.smul_def, mul_comm]
lemma positive_mixing_preserves_stability (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (p : MvPolynomial (Fin n) ℝ) (hp : LorentzianPolynomials.IsStable p) :
    LorentzianPolynomials.IsStable (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) p) := by
  classical
  rcases hp with hp | hp
  · left
    simp [hp]
  right
  intro z
  let y : Fin n → UpperHalfPlane := fun i =>
    ⟨(z i : ℂ) + (t : ℂ) * ∑ j : Fin n, (z j : ℂ), by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.im_sum]
      exact add_pos_of_pos_of_nonneg (z i).im_pos
        (mul_nonneg ht (Finset.sum_nonneg (fun j _ => (z j).im_pos.le)))⟩
  have heq : MvPolynomial.aeval (((↑) : UpperHalfPlane → ℂ) ∘ z)
      (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) p) =
      MvPolynomial.aeval (((↑) : UpperHalfPlane → ℂ) ∘ y) p := by
    rw [MvPolynomial.comp_aeval_apply]
    apply congrArg (fun u : Fin n → ℂ => MvPolynomial.aeval u p)
    funext i
    simp [y]
  rw [heq]
  exact hp y
lemma positive_mixing_preservation_induction (n : ℕ) (t : ℝ) (ht : 0 < t)
    (hzero : ∀ d : ℕ,
      (⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ d⟩ : LorentzianPolynomials.H n d) ∈
        LorentzianPolynomials.L n d)
    (hsupport : ∀ (d : ℕ) (f : LorentzianPolynomials.H n d),
      f ∈ LorentzianPolynomials.P n d →
        LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)))
    (hpositive : ∀ (d : ℕ) (f : LorentzianPolynomials.H n d), f.1 ≠ 0 →
      (∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) → ∀ g : LorentzianPolynomials.H n d,
      g.1 = MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) f.1 → g ∈ LorentzianPolynomials.P n d)
    (hdirectional : ∀ (d : ℕ) (f : LorentzianPolynomials.H n (d + 1)),
      f ∈ LorentzianPolynomials.L n (d + 1) → ∀ a : Fin n → ℝ,
      (∀ i : Fin n, 0 < a i) → ∃ q : LorentzianPolynomials.H n d,
      q.1 = ∑ i : Fin n, a i • MvPolynomial.pderiv i f.1 ∧
        q ∈ LorentzianPolynomials.L n d) :
    ∀ (d : ℕ) (f : LorentzianPolynomials.H n d), f ∈ LorentzianPolynomials.L n d →
      ∀ g : LorentzianPolynomials.H n d,
      g.1 = MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) f.1 → g ∈ LorentzianPolynomials.L n d := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hf g hg
    by_cases hz : f.1 = 0
    · have heq : g = ⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ d⟩ := by
        apply Subtype.ext
        simpa only [hz, map_zero] using hg
      rw [heq]
      exact hzero d
    have hfc : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
      match d with
      | 0 => exact hf.2
      | 1 => exact hf.2
      | 2 => exact hf.2
      | d + 3 => exact hf.1.2
    have hp : g ∈ LorentzianPolynomials.P n d := hpositive d f hz hfc g hg
    have hc : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m := by
      intro m
      by_cases hm : Finsupp.weight 1 m = d
      · exact (hp m hm).le
      · rw [MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero g.2 m hm]
    match d with
    | 0 =>
      refine ⟨?_, hc⟩
      rw [hg]
      exact positive_mixing_preserves_stability n t ht.le f.1 hf.1
    | 1 =>
      refine ⟨?_, hc⟩
      rw [hg]
      exact positive_mixing_preserves_stability n t ht.le f.1 hf.1
    | 2 =>
      refine ⟨?_, hc⟩
      rw [hg]
      exact positive_mixing_preserves_stability n t ht.le f.1 hf.1
    | d + 3 =>
      refine ⟨⟨hsupport (d + 3) g hp, hc⟩, ?_⟩
      intro k
      let a : Fin n → ℝ := fun i => (if i = k then 1 else 0) + t
      have ha : ∀ i : Fin n, 0 < a i := by
        intro i
        dsimp [a]
        split_ifs <;> linarith
      obtain ⟨q, hq, hqL⟩ := hdirectional (d + 2) f hf a ha
      let φ : Fin n → MvPolynomial (Fin n) ℝ :=
        fun i => MvPolynomial.X i + MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j
      have hhom : (MvPolynomial.aeval φ q.1).IsHomogeneous (d + 2) := by
        simpa only [one_mul] using q.2.aeval φ (fun i =>
          (MvPolynomial.isHomogeneous_X _ i).add
            ((MvPolynomial.IsHomogeneous.sum Finset.univ
              (fun j : Fin n => MvPolynomial.X j) 1
              (fun j _ => MvPolynomial.isHomogeneous_X _ j)).C_mul t))
      let r : LorentzianPolynomials.H n (d + 2) := ⟨MvPolynomial.aeval φ q.1, hhom⟩
      have hrL : r ∈ LorentzianPolynomials.L n (d + 2) :=
        ih (d + 2) (by omega) q hqL r rfl
      have heq : (⟨g.1.pderiv k, g.2.pderiv⟩ :
          LorentzianPolynomials.H n (d + 2)) = r := by
        apply Subtype.ext
        change g.1.pderiv k = MvPolynomial.aeval φ q.1
        rw [hg, positive_mixing_pderiv_chain, hq, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact ((MvPolynomial.aeval φ).toLinearMap.map_smul (a i) (f.1.pderiv i)).symm
      rwa [heq]
theorem nonnegative_coefficients_isClosed (n d : ℕ) :
    IsClosed {f : LorentzianPolynomials.H n d |
      ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
  have hset : {f : LorentzianPolynomials.H n d |
      ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} =
      ⋂ m : Fin n →₀ ℕ, {f : LorentzianPolynomials.H n d | 0 ≤ f.1.coeff m} := by
    ext f
    simp
  rw [hset]
  exact isClosed_iInter fun m =>
    isClosed_le continuous_const (coefficient_continuous n d m)
theorem positive_coefficients_nonnegative (n d : ℕ)
    {f : LorentzianPolynomials.H n d} (hf : f ∈ LorentzianPolynomials.P n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
  intro m
  by_cases hm : Finsupp.weight 1 m = d
  · exact (hf m hm).le
  · rw [MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero f.2 m hm]
theorem strict_subset_positive (n d : ℕ) :
    LorentzianPolynomials.Ŀ n d ⊆ LorentzianPolynomials.P n d := by
  match d with
  | 0 => exact fun _ hf => hf
  | 1 => exact fun _ hf => hf
  | 2 => exact fun _ hf => hf.1
  | d + 3 => exact fun _ hf => hf.1
theorem closure_strict_coefficients_nonnegative (n d : ℕ) :
    closure (LorentzianPolynomials.Ŀ n d) ⊆
      {f : LorentzianPolynomials.H n d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
  exact closure_minimal
    (fun f hf => positive_coefficients_nonnegative n d (strict_subset_positive n d hf))
    (nonnegative_coefficients_isClosed n d)
theorem partial_derivative_continuous (n d : ℕ) (i : Fin n) :
    Continuous (X := LorentzianPolynomials.H n (d + 3))
      (Y := LorentzianPolynomials.H n (d + 2)) (fun f =>
      (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n (d + 2))) := by
  letI : TopologicalSpace (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 3)) :=
    moduleTopology ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 3))
  letI : TopologicalSpace (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 2)) :=
    moduleTopology ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 2))
  letI : ContinuousAdd (MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 2)) :=
    IsModuleTopology.toContinuousAdd ℝ _
  change Continuous (fun f : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 3) =>
    (⟨f.1.pderiv i, f.2.pderiv⟩ : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 2)))
  let D : MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 3) →ₗ[ℝ]
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ (d + 2) :=
    { toFun := fun f => ⟨f.1.pderiv i, f.2.pderiv⟩
      map_add' := fun f g => Subtype.ext ((MvPolynomial.pderiv i).map_add f.1 g.1)
      map_smul' := fun c f => Subtype.ext ((MvPolynomial.pderiv i).map_smul c f.1) }
  exact IsModuleTopology.continuous_of_linearMap D
theorem partial_derivative_mem_closure (n d : ℕ)
    {f : LorentzianPolynomials.H n (d + 3)}
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n (d + 3))) (i : Fin n) :
    (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n (d + 2)) ∈
      closure (LorentzianPolynomials.Ŀ n (d + 2)) := by
  exact map_mem_closure (partial_derivative_continuous n d i) hf
    (fun g hg => hg.2 i)
theorem homogeneous_degree_zero_stable (n : ℕ) (f : LorentzianPolynomials.H n 0) :
    LorentzianPolynomials.IsStable f.1 := by
  have heq : f.1 = MvPolynomial.C (f.1.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).mpr f.2)
  rw [heq]
  by_cases hc : f.1.coeff 0 = 0
  · left
    simp [hc]
  · right
    intro z
    simpa using Complex.ofReal_ne_zero.mpr hc
theorem homogeneous_degree_one_eq_sum (n : ℕ) (f : LorentzianPolynomials.H n 1) :
    f.1 = ∑ i : Fin n, MvPolynomial.X i * MvPolynomial.C (f.1.coeff (Finsupp.single i 1)) := by
  have hc : ∀ i : Fin n, f.1.pderiv i = MvPolynomial.C (f.1.coeff (Finsupp.single i 1)) := by
    intro i
    have hh : (f.1.pderiv i).IsHomogeneous 0 := f.2.pderiv
    have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).mpr hh)
    simpa [MvPolynomial.coeff_pderiv] using heq
  simpa only [hc, one_smul] using f.2.sum_X_mul_pderiv.symm
theorem homogeneous_degree_one_stable (n : ℕ) (f : LorentzianPolynomials.H n 1)
    (hcoeff : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) :
    LorentzianPolynomials.IsStable f.1 := by
  classical
  by_cases hf : f.1 = 0
  · exact Or.inl hf
  right
  intro z
  have hpos : ∃ i : Fin n, 0 < f.1.coeff (Finsupp.single i 1) := by
    by_contra h
    have hc : ∀ i : Fin n, f.1.coeff (Finsupp.single i 1) = 0 := by
      intro i
      exact le_antisymm (not_lt.mp (fun hi => h ⟨i, hi⟩)) (hcoeff _)
    apply hf
    rw [homogeneous_degree_one_eq_sum n f]
    simp [hc]
  have heval : MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 =
      ∑ i : Fin n, (z i : ℂ) * (f.1.coeff (Finsupp.single i 1) : ℂ) := by
    conv_lhs => rw [homogeneous_degree_one_eq_sum n f]
    simp
  have him : 0 < (MvPolynomial.aeval (fun i => (z i : ℂ)) f.1).im := by
    rw [heval]
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_im, mul_zero,
      Complex.ofReal_re, zero_add]
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (z i).im_pos.le (hcoeff _)
    · obtain ⟨i, hi⟩ := hpos
      exact ⟨i, Finset.mem_univ _, mul_pos (z i).im_pos hi⟩
  intro heq
  change MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = 0 at heq
  rw [heq] at him
  exact (lt_irrefl 0) him
theorem closure_strict_subset_lorentzian_degree_zero (n : ℕ) :
    closure (LorentzianPolynomials.Ŀ n 0) ⊆ LorentzianPolynomials.L n 0 := by
  intro f hf
  exact ⟨homogeneous_degree_zero_stable n f,
    closure_strict_coefficients_nonnegative n 0 hf⟩
theorem closure_strict_subset_lorentzian_degree_one (n : ℕ) :
    closure (LorentzianPolynomials.Ŀ n 1) ⊆ LorentzianPolynomials.L n 1 := by
  intro f hf
  have hc := closure_strict_coefficients_nonnegative n 1 hf
  exact ⟨homogeneous_degree_one_stable n f hc, hc⟩
theorem closure_strict_subset_lorentzian_low_degree (n d : ℕ) (hd : d ≤ 1) :
    closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  match d with
  | 0 => exact closure_strict_subset_lorentzian_degree_zero n
  | 1 => exact closure_strict_subset_lorentzian_degree_one n
  | d + 2 => omega
theorem closure_strict_subset_of_bridges
    (hquadratic : ∀ n : ℕ, 0 < n →
      ∀ f : LorentzianPolynomials.H n 2,
        f ∈ closure (LorentzianPolynomials.Ŀ n 2) →
          LorentzianPolynomials.IsStable f.1)
    (hsupport : ∀ n d : ℕ, 0 < n →
      ∀ f : LorentzianPolynomials.H n (d + 3),
        f ∈ closure (LorentzianPolynomials.Ŀ n (d + 3)) →
          LorentzianPolynomials.IsMConvex
            (f.1.support : Set (Fin n →₀ ℕ))) :
    ∀ n d : ℕ, 0 < n →
      closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  intro n d hn
  induction d using Nat.strong_induction_on with
  | h d ih =>
    match d with
    | 0 => exact closure_strict_subset_lorentzian_degree_zero n
    | 1 => exact closure_strict_subset_lorentzian_degree_one n
    | 2 =>
      intro f hf
      exact ⟨hquadratic n hn f hf,
        closure_strict_coefficients_nonnegative n 2 hf⟩
    | d + 3 =>
      intro f hf
      refine ⟨⟨hsupport n d hn f hf,
        closure_strict_coefficients_nonnegative n (d + 3) hf⟩, ?_⟩
      intro i
      exact ih (d + 2) (by omega) (partial_derivative_mem_closure n d hf i)
theorem one_variable_exponent (d : ℕ) (m : Fin 1 →₀ ℕ)
    (hm : Finsupp.weight 1 m = d) : m = Finsupp.single 0 d := by
  have hm0 : m 0 = d := by
    simpa [Finsupp.weight_eq_sum] using hm
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simpa using hm0
theorem one_variable_homogeneous_eq_monomial (d : ℕ)
    (f : LorentzianPolynomials.H 1 d) :
    f.1 = MvPolynomial.monomial (Finsupp.single 0 d)
      (f.1.coeff (Finsupp.single 0 d)) := by
  classical
  ext m
  by_cases hm : m = Finsupp.single 0 d
  · subst m
    simp
  · have hdeg : Finsupp.weight 1 m ≠ d := fun h => hm (one_variable_exponent d m h)
    rw [MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero f.2 m hdeg]
    simp [MvPolynomial.coeff_monomial, Ne.symm hm]
theorem one_variable_homogeneous_stable (d : ℕ)
    (f : LorentzianPolynomials.H 1 d) : LorentzianPolynomials.IsStable f.1 := by
  by_cases hc : f.1.coeff (Finsupp.single 0 d) = 0
  · left
    rw [one_variable_homogeneous_eq_monomial d f, hc]
    simp
  · right
    intro z
    conv_lhs => rw [one_variable_homogeneous_eq_monomial d f]
    rw [← MvPolynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Function.comp_apply]
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr hc)
    apply pow_ne_zero
    intro hz
    have hi := (z 0).coe_im_pos
    rw [hz] at hi
    exact (lt_irrefl 0) hi
theorem one_variable_homogeneous_support_mconvex (d : ℕ)
    (f : LorentzianPolynomials.H 1 d) :
    LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin 1 →₀ ℕ)) := by
  intro α hα β hβ i hi
  have hα' : α = Finsupp.single 0 d :=
    one_variable_exponent d α (f.2 (MvPolynomial.mem_support_iff.mp hα))
  have hβ' : β = Finsupp.single 0 d :=
    one_variable_exponent d β (f.2 (MvPolynomial.mem_support_iff.mp hβ))
  rw [hα', hβ'] at hi
  exact False.elim ((lt_irrefl _) hi)
theorem one_variable_nonnegative_mem_lorentzian (d : ℕ)
    (f : LorentzianPolynomials.H 1 d)
    (hf : ∀ m : Fin 1 →₀ ℕ, 0 ≤ f.1.coeff m) : f ∈ LorentzianPolynomials.L 1 d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    match d with
    | 0 => exact ⟨one_variable_homogeneous_stable 0 f, hf⟩
    | 1 => exact ⟨one_variable_homogeneous_stable 1 f, hf⟩
    | 2 => exact ⟨one_variable_homogeneous_stable 2 f, hf⟩
    | d + 3 =>
      refine ⟨⟨one_variable_homogeneous_support_mconvex (d + 3) f, hf⟩, ?_⟩
      intro i
      apply ih (d + 2) (by omega)
      intro m
      rw [MvPolynomial.coeff_pderiv]
      exact mul_nonneg (hf _) (by positivity)
theorem closure_strict_subset_lorentzian_one_variable (d : ℕ) :
    closure (LorentzianPolynomials.Ŀ 1 d) ⊆ LorentzianPolynomials.L 1 d := by
  intro f hf
  exact one_variable_nonnegative_mem_lorentzian d f
    (closure_strict_coefficients_nonnegative 1 d hf)
theorem coefficient_exchange_bound_of_closure
    (n d : ℕ) (α β : Fin n →₀ ℕ) (i : Fin n) (C : ℝ)
    (hbound : ∀ g : LorentzianPolynomials.H n d,
      g ∈ LorentzianPolynomials.Ŀ n d →
        g.1.coeff α * g.1.coeff β ≤
          C * ∑ j ∈ Finset.univ.filter (fun j => α j < β j),
            g.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
              g.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1))
    {f : LorentzianPolynomials.H n d}
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n d)) :
    f.1.coeff α * f.1.coeff β ≤
      C * ∑ j ∈ Finset.univ.filter (fun j => α j < β j),
        f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1) := by
  apply closure_minimal (fun g hg => hbound g hg) _ hf
  apply isClosed_le
    ((coefficient_continuous n d α).mul (coefficient_continuous n d β))
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  exact (coefficient_continuous n d _).mul (coefficient_continuous n d _)
theorem closure_strict_support_mconvex_of_uniform_exchange (n d : ℕ)
    (hexchange : ∀ (α β : Fin n →₀ ℕ) (i : Fin n),
      Finsupp.weight 1 α = d → Finsupp.weight 1 β = d → β i < α i →
        ∃ C : ℝ, ∀ g : LorentzianPolynomials.H n d,
          g ∈ LorentzianPolynomials.Ŀ n d →
            g.1.coeff α * g.1.coeff β ≤
              C * ∑ j ∈ Finset.univ.filter (fun j => α j < β j),
                g.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
                  g.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1))
    {f : LorentzianPolynomials.H n d}
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n d)) :
    LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) := by
  classical
  intro α hα β hβ i hi
  have hαc : f.1.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have hβc : f.1.coeff β ≠ 0 := MvPolynomial.mem_support_iff.mp hβ
  obtain ⟨C, hC⟩ := hexchange α β i (f.2 hαc) (f.2 hβc) hi
  have hb := coefficient_exchange_bound_of_closure n d α β i C hC hf
  by_contra hnone
  have hz : ∀ j ∈ Finset.univ.filter (fun j => α j < β j),
      f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) = 0 := by
    intro j hj
    by_contra hne
    apply hnone
    exact ⟨j, (Finset.mem_filter.mp hj).2, MvPolynomial.mem_support_iff.mpr hne⟩
  have hsum : (∑ j ∈ Finset.univ.filter (fun j => α j < β j),
      f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
        f.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz j hj, zero_mul]
  rw [hsum, mul_zero] at hb
  have hcoeff := closure_strict_coefficients_nonnegative n d hf
  exact (not_le_of_gt
    (mul_pos (lt_of_le_of_ne (hcoeff α) (Ne.symm hαc))
      (lt_of_le_of_ne (hcoeff β) (Ne.symm hβc)))) hb
theorem hessian_entry_continuous (n : ℕ) (i j : Fin n) :
    Continuous (fun f : LorentzianPolynomials.H n 2 => f.hessian i j) := by
  by_cases hij : i = j
  · simp only [LorentzianPolynomials.H.hessian, if_pos hij]
    exact continuous_const.mul (coefficient_continuous n 2 (Finsupp.single i 2))
  · simp only [LorentzianPolynomials.H.hessian, if_neg hij]
    exact coefficient_continuous n 2 (Finsupp.single i 1 + Finsupp.single j 1)
theorem hessian_pairing_continuous (n : ℕ) (x y : Fin n → ℝ) :
    Continuous (fun f : LorentzianPolynomials.H n 2 =>
      dotProduct x (f.hessian.mulVec y)) := by
  change Continuous (fun f : LorentzianPolynomials.H n 2 =>
    ∑ i : Fin n, x i * ∑ j : Fin n, f.hessian i j * y j)
  apply continuous_finsetSum
  intro i hi
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  exact (hessian_entry_continuous n i j).mul continuous_const
theorem quadratic_hessian_discriminant_of_closure (n : ℕ)
    (hstrict : ∀ g : LorentzianPolynomials.H n 2,
      g ∈ LorentzianPolynomials.Ŀ n 2 →
        ∀ x y : Fin n → ℝ, (∀ i, 0 < y i) →
          dotProduct x (g.hessian.mulVec x) * dotProduct y (g.hessian.mulVec y) ≤
            dotProduct x (g.hessian.mulVec y) ^ 2)
    {f : LorentzianPolynomials.H n 2}
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n 2)) :
    ∀ x y : Fin n → ℝ, (∀ i, 0 < y i) →
      dotProduct x (f.hessian.mulVec x) * dotProduct y (f.hessian.mulVec y) ≤
        dotProduct x (f.hessian.mulVec y) ^ 2 := by
  intro x y hy
  exact closure_minimal (fun g hg => hstrict g hg x y hy)
    (isClosed_le
      ((hessian_pairing_continuous n x x).mul (hessian_pairing_continuous n y y))
      ((hessian_pairing_continuous n x y).pow 2)) hf
theorem closure_strict_subset_of_nontrivial_bridges
    (hquadratic : ∀ n : ℕ, 1 < n →
      ∀ f : LorentzianPolynomials.H n 2,
        f ∈ closure (LorentzianPolynomials.Ŀ n 2) →
          LorentzianPolynomials.IsStable f.1)
    (hsupport : ∀ n d : ℕ, 1 < n →
      ∀ f : LorentzianPolynomials.H n (d + 3),
        f ∈ closure (LorentzianPolynomials.Ŀ n (d + 3)) →
          LorentzianPolynomials.IsMConvex
            (f.1.support : Set (Fin n →₀ ℕ))) :
    ∀ n d : ℕ, 0 < n →
      closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  apply closure_strict_subset_of_bridges
  · intro n hn f hf
    by_cases hn1 : n = 1
    · subst n
      exact one_variable_homogeneous_stable 2 f
    · exact hquadratic n (by omega) f hf
  · intro n d hn f hf
    by_cases hn1 : n = 1
    · subst n
      exact one_variable_homogeneous_support_mconvex (d + 3) f
    · exact hsupport n d (by omega) f hf
theorem matrix_discriminant_of_nonpositive_kernel (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hker : ∀ v : Fin n → ℝ, l v = 0 → dotProduct v (A.mulVec v) ≤ 0)
    (x y : Fin n → ℝ) (hy : 0 < dotProduct y (A.mulVec y)) :
    dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) ≤
      dotProduct x (A.mulVec y) ^ 2 := by
  have hly : l y ≠ 0 := by
    intro hz
    exact (not_le_of_gt hy) (hker y hz)
  have hw := hker (l y • x - l x • y) (by simp [mul_comm])
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    hA.dotProduct_mulVec_comm (x := y) (y := x)] at hw
  have hmult := mul_nonpos_of_nonpos_of_nonneg hw hy.le
  have hs := sq_nonneg (l x * dotProduct y (A.mulVec y) -
    l y * dotProduct x (A.mulVec y))
  have hprod : (dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) -
      dotProduct x (A.mulVec y) ^ 2) * (l y) ^ 2 ≤ 0 := by
    nlinarith [hmult, hs]
  by_contra h
  have hp := mul_pos (by linarith : 0 < dotProduct x (A.mulVec x) *
    dotProduct y (A.mulVec y) - dotProduct x (A.mulVec y) ^ 2) (sq_pos_of_ne_zero hly)
  exact (not_le_of_gt hp) hprod
theorem hermitian_quadratic_eigenvalue_expansion (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x : Fin n → ℝ) :
    dotProduct x (A.mulVec x) = ∑ i : Fin n, hA.eigenvalues i *
      ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).mulVec x i) ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem hermitian_nonpositive_kernel_of_one_positive_root (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hcard : (A.charpoly.roots.filter (0 < ·)).card = 1) :
    ∃ l : (Fin n → ℝ) →ₗ[ℝ] ℝ,
      ∀ v : Fin n → ℝ, l v = 0 → dotProduct v (A.mulVec v) ≤ 0 := by
  classical
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map] at hcard
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] at hcard
  change (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card = 1 at hcard
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj p).comp
    (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).mulVecLin
  refine ⟨l, ?_⟩
  intro v hv
  rw [hermitian_quadratic_eigenvalue_expansion n A hA v]
  apply Finset.sum_nonpos
  intro i hi
  by_cases hip : i = p
  · subst i
    change (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)).mulVec v p = 0 at hv
    simp only [hv, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    by_contra hpos
    have hm : i ∈ Finset.univ.filter (fun i => 0 < hA.eigenvalues i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hpos⟩
    rw [hp] at hm
    exact hip (Finset.mem_singleton.mp hm)
theorem hermitian_discriminant_of_one_positive_root (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hcard : (A.charpoly.roots.filter (0 < ·)).card = 1)
    (x y : Fin n → ℝ) (hy : 0 < dotProduct y (A.mulVec y)) :
    dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) ≤
      dotProduct x (A.mulVec y) ^ 2 := by
  obtain ⟨l, hl⟩ := hermitian_nonpositive_kernel_of_one_positive_root n A hA hcard
  exact matrix_discriminant_of_nonpositive_kernel n A hA.isSymm l hl x y hy
theorem forward_hessian_isHermitian (n : ℕ) (f : LorentzianPolynomials.H n 2) :
    f.hessian.IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  by_cases hij : i = j
  · subst j
    rfl
  · simp [LorentzianPolynomials.H.hessian, hij, Ne.symm hij, add_comm]
theorem strict_hessian_entries_positive (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.Ŀ n 2)
    (i j : Fin n) : 0 < f.hessian i j := by
  by_cases hij : i = j
  · subst j
    simp only [LorentzianPolynomials.H.hessian, if_pos rfl]
    exact mul_pos (by norm_num) (hf.1 _ (by simp [Finsupp.weight_single]))
  · simp only [LorentzianPolynomials.H.hessian, if_neg hij]
    exact hf.1 _ (by simp [Finsupp.weight_single])
theorem strict_hessian_positive_pairing (n : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.Ŀ n 2)
    (y : Fin n → ℝ) (hy : ∀ i, 0 < y i) :
    0 < dotProduct y (f.hessian.mulVec y) := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  change 0 < ∑ i : Fin n, y i * ∑ j : Fin n, f.hessian i j * y j
  have hrow : ∀ i : Fin n, 0 < ∑ j : Fin n, f.hessian i j * y j := by
    intro i
    apply Finset.sum_pos'
    · intro j hj
      exact (mul_pos (strict_hessian_entries_positive n f hf i j) (hy j)).le
    · exact ⟨i₀, Finset.mem_univ _,
        mul_pos (strict_hessian_entries_positive n f hf i i₀) (hy i₀)⟩
  apply Finset.sum_pos'
  · intro i hi
    exact (mul_pos (hy i) (hrow i)).le
  · exact ⟨i₀, Finset.mem_univ _, mul_pos (hy i₀) (hrow i₀)⟩
theorem strict_quadratic_hessian_discriminant (n : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.Ŀ n 2) :
    ∀ x y : Fin n → ℝ, (∀ i, 0 < y i) →
      dotProduct x (f.hessian.mulVec x) * dotProduct y (f.hessian.mulVec y) ≤
        dotProduct x (f.hessian.mulVec y) ^ 2 := by
  intro x y hy
  exact hermitian_discriminant_of_one_positive_root n f.hessian
    (forward_hessian_isHermitian n f) hf.2.2 x y
    (strict_hessian_positive_pairing n hn f hf y hy)
theorem closure_strict_quadratic_hessian_discriminant (n : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n 2)
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n 2)) :
    ∀ x y : Fin n → ℝ, (∀ i, 0 < y i) →
      dotProduct x (f.hessian.mulVec x) * dotProduct y (f.hessian.mulVec y) ≤
        dotProduct x (f.hessian.mulVec y) ^ 2 :=
  quadratic_hessian_discriminant_of_closure n
    (fun g hg => strict_quadratic_hessian_discriminant n hn g hg) hf
theorem forward_quadratic_pderiv_coefficient (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (i j : Fin n) :
    (f.1.pderiv i).coeff (Finsupp.single j 1) = f.hessian i j := by
  rw [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    simp [LorentzianPolynomials.H.hessian, ← Finsupp.single_add, mul_comm]
    norm_num
  · simp [LorentzianPolynomials.H.hessian, hij, Ne.symm hij, add_comm]
theorem forward_quadratic_hessian_polynomial_identity (n : ℕ)
    (f : LorentzianPolynomials.H n 2) :
    (2 : ℝ) • f.1 = ∑ i : Fin n, ∑ j : Fin n,
      MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (f.hessian i j) := by
  have hd : ∀ i : Fin n, f.1.pderiv i = ∑ j : Fin n,
      MvPolynomial.X j * MvPolynomial.C (f.hessian i j) := by
    intro i
    simpa only [forward_quadratic_pderiv_coefficient] using
      homogeneous_degree_one_eq_sum n
        (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n 1)
  simpa only [two_smul, hd, Finset.mul_sum, mul_assoc] using
    f.2.sum_X_mul_pderiv.symm
theorem forward_quadratic_hessian_aeval (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (z : Fin n → ℂ) :
    2 * MvPolynomial.aeval z f.1 = ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * (f.hessian i j : ℂ) := by
  have h := congrArg (fun p : MvPolynomial (Fin n) ℝ => MvPolynomial.aeval z p)
    (forward_quadratic_hessian_polynomial_identity n f)
  simpa using h
theorem forward_complex_quadratic_re (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, z i * z j * (A i j : ℂ)).re =
      dotProduct (fun i => (z i).re) (A.mulVec (fun i => (z i).re)) -
        dotProduct (fun i => (z i).im) (A.mulVec (fun i => (z i).im)) := by
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring
theorem forward_complex_quadratic_im (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (z : Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, z i * z j * (A i j : ℂ)).im =
      2 * dotProduct (fun i => (z i).re) (A.mulVec (fun i => (z i).im)) := by
  have heq : (∑ i : Fin n, ∑ j : Fin n, z i * z j * (A i j : ℂ)).im =
      dotProduct (fun i => (z i).re) (A.mulVec (fun i => (z i).im)) +
        dotProduct (fun i => (z i).im) (A.mulVec (fun i => (z i).re)) := by
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, hA.dotProduct_mulVec_comm (x := fun i => (z i).im)]
  ring
theorem forward_hessian_eq_zero_imp_polynomial_zero (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : f.hessian = 0) : f.1 = 0 := by
  have h := forward_quadratic_hessian_polynomial_identity n f
  simp only [hf, Matrix.zero_apply, MvPolynomial.C_0, mul_zero,
    Finset.sum_const_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)
theorem forward_hessian_entries_nonnegative (n : ℕ)
    (f : LorentzianPolynomials.H n 2)
    (hc : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) (i j : Fin n) :
    0 ≤ f.hessian i j := by
  by_cases hij : i = j
  · simp only [LorentzianPolynomials.H.hessian, if_pos hij]
    exact mul_nonneg (by norm_num) (hc _)
  · simp only [LorentzianPolynomials.H.hessian, if_neg hij]
    exact hc _
theorem nonzero_nonnegative_matrix_positive_pairing (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ≠ 0)
    (hnonneg : ∀ i j, 0 ≤ A i j) (y : Fin n → ℝ) (hy : ∀ i, 0 < y i) :
    0 < dotProduct y (A.mulVec y) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hA
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  have hpos : 0 < A i j := lt_of_le_of_ne (hnonneg i j) (Ne.symm hij)
  have hrow_nonneg : ∀ k : Fin n, 0 ≤ ∑ l : Fin n, A k l * y l := by
    intro k
    exact Finset.sum_nonneg fun l hl => mul_nonneg (hnonneg k l) (hy l).le
  have hrow_pos : 0 < ∑ l : Fin n, A i l * y l :=
    Finset.sum_pos' (fun l hl => mul_nonneg (hnonneg i l) (hy l).le)
      ⟨j, Finset.mem_univ _, mul_pos hpos (hy j)⟩
  change 0 < ∑ k : Fin n, y k * ∑ l : Fin n, A k l * y l
  exact Finset.sum_pos' (fun k hk => mul_nonneg (hy k).le (hrow_nonneg k))
    ⟨i, Finset.mem_univ _, mul_pos (hy i) hrow_pos⟩
theorem forward_quadratic_stable_of_hessian_discriminant (n : ℕ)
    (f : LorentzianPolynomials.H n 2)
    (hc : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m)
    (hd : ∀ x y : Fin n → ℝ, (∀ i, 0 < y i) →
      dotProduct x (f.hessian.mulVec x) * dotProduct y (f.hessian.mulVec y) ≤
        dotProduct x (f.hessian.mulVec y) ^ 2) : LorentzianPolynomials.IsStable f.1 := by
  by_cases hf : f.1 = 0
  · exact Or.inl hf
  right
  intro z hz
  have hA : f.hessian ≠ 0 := fun h => hf (forward_hessian_eq_zero_imp_polynomial_zero n f h)
  let x : Fin n → ℝ := fun i => (z i : ℂ).re
  let y : Fin n → ℝ := fun i => (z i : ℂ).im
  have hy : ∀ i, 0 < y i := fun i => (z i).im_pos
  have hpos := nonzero_nonnegative_matrix_positive_pairing n f.hessian hA
    (forward_hessian_entries_nonnegative n f hc) y hy
  have heval : MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = 0 := hz
  have hs : (∑ i : Fin n, ∑ j : Fin n,
      (z i : ℂ) * (z j : ℂ) * (f.hessian i j : ℂ)) = 0 := by
    rw [← forward_quadratic_hessian_aeval n f (fun i => (z i : ℂ)), heval, mul_zero]
  have hreal : dotProduct x (f.hessian.mulVec x) -
      dotProduct y (f.hessian.mulVec y) = 0 := by
    rw [← forward_complex_quadratic_re n f.hessian (fun i => (z i : ℂ)), hs]
    rfl
  have him : 2 * dotProduct x (f.hessian.mulVec y) = 0 := by
    rw [← forward_complex_quadratic_im n f.hessian
      (forward_hessian_isHermitian n f).isSymm (fun i => (z i : ℂ)), hs]
    rfl
  have hdisc := hd x y hy
  have hxy : dotProduct x (f.hessian.mulVec y) = 0 := by linarith
  rw [hxy, zero_pow (by decide : 2 ≠ 0)] at hdisc
  nlinarith [sq_pos_of_pos hpos]
theorem closure_strict_subset_lorentzian_degree_two (n : ℕ) (hn : 0 < n) :
    closure (LorentzianPolynomials.Ŀ n 2) ⊆ LorentzianPolynomials.L n 2 := by
  intro f hf
  have hc := closure_strict_coefficients_nonnegative n 2 hf
  exact ⟨forward_quadratic_stable_of_hessian_discriminant n f hc
    (closure_strict_quadratic_hessian_discriminant n hn f hf), hc⟩
theorem closure_strict_subset_lorentzian_degree_le_two (n d : ℕ) (hn : 0 < n)
    (hd : d ≤ 2) :
    closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  match d with
  | 0 => exact closure_strict_subset_lorentzian_degree_zero n
  | 1 => exact closure_strict_subset_lorentzian_degree_one n
  | 2 => exact closure_strict_subset_lorentzian_degree_two n hn
  | d + 3 => omega
theorem closure_strict_subset_of_support_limits
    (hsupport : ∀ n d : ℕ, 1 < n →
      ∀ f : LorentzianPolynomials.H n (d + 3),
        f ∈ closure (LorentzianPolynomials.Ŀ n (d + 3)) →
          LorentzianPolynomials.IsMConvex
            (f.1.support : Set (Fin n →₀ ℕ))) :
    ∀ n d : ℕ, 0 < n →
      closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  apply closure_strict_subset_of_nontrivial_bridges
  · intro n hn f hf
    exact (closure_strict_subset_lorentzian_degree_two n (by omega) hf).1
  · exact hsupport
theorem support_pderiv_sub_single (n : ℕ)
    (f : MvPolynomial (Fin n) ℝ) (α : Fin n →₀ ℕ) (k : Fin n)
    (hα : α ∈ f.support) (hk : 0 < α k) :
    α - Finsupp.single k 1 ∈ (f.pderiv k).support := by
  apply MvPolynomial.mem_support_iff.mpr
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hk)]
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hα) (by positivity)
theorem support_pderiv_add_single (n : ℕ)
    (f : MvPolynomial (Fin n) ℝ) (α : Fin n →₀ ℕ) (k : Fin n)
    (hα : α ∈ (f.pderiv k).support) :
    α + Finsupp.single k 1 ∈ f.support := by
  apply MvPolynomial.mem_support_iff.mpr
  have hc := MvPolynomial.mem_support_iff.mp hα
  rw [MvPolynomial.coeff_pderiv] at hc
  exact (mul_ne_zero_iff.mp hc).1
theorem support_exchange_of_common_positive_coordinate (n : ℕ)
    (f : MvPolynomial (Fin n) ℝ)
    (hderiv : ∀ k : Fin n, LorentzianPolynomials.IsMConvex
      ((f.pderiv k).support : Set (Fin n →₀ ℕ)))
    (α β : Fin n →₀ ℕ) (hα : α ∈ f.support) (hβ : β ∈ f.support)
    (i k : Fin n) (hi : β i < α i) (hαk : 0 < α k) (hβk : 0 < β k) :
    ∃ j, α j < β j ∧ α - Finsupp.single i 1 + Finsupp.single j 1 ∈ f.support := by
  have hi' : (β - Finsupp.single k 1 : Fin n →₀ ℕ) i < (α - Finsupp.single k 1 : Fin n →₀ ℕ) i := by
    by_cases hik : i = k
    · subst i
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simpa [Finsupp.tsub_apply, Finsupp.single_apply, hik, Ne.symm hik] using hi
  obtain ⟨j, hj, hmem⟩ := hderiv k (α - Finsupp.single k 1)
    (support_pderiv_sub_single n f α k hα hαk) (β - Finsupp.single k 1)
    (support_pderiv_sub_single n f β k hβ hβk) i hi'
  have hj' : α j < β j := by
    by_cases hjk : j = k
    · subst j
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hj
      omega
    · simpa [Finsupp.tsub_apply, Finsupp.single_apply, hjk, Ne.symm hjk] using hj
  refine ⟨j, hj', ?_⟩
  have hshift := support_pderiv_add_single n f _ k hmem
  have heq : (α - Finsupp.single k 1 - Finsupp.single i 1 + Finsupp.single j 1) +
      Finsupp.single k 1 = α - Finsupp.single i 1 + Finsupp.single j 1 := by
    ext l
    by_cases hlk : l = k
    · subst l
      by_cases hik : i = k
      · subst i
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs <;> omega
      · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hik]
        omega
    · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm hlk]
  simpa only [heq] using hshift
theorem support_mconvex_of_derivatives_and_disjoint_exchange (n : ℕ)
    (f : MvPolynomial (Fin n) ℝ)
    (hderiv : ∀ k : Fin n, LorentzianPolynomials.IsMConvex
      ((f.pderiv k).support : Set (Fin n →₀ ℕ)))
    (hdisjoint : ∀ (α β : Fin n →₀ ℕ), α ∈ f.support → β ∈ f.support →
      (∀ k : Fin n, α k = 0 ∨ β k = 0) →
      ∀ i : Fin n, β i < α i → ∃ j : Fin n,
        α j < β j ∧ α - Finsupp.single i 1 + Finsupp.single j 1 ∈ f.support) :
    LorentzianPolynomials.IsMConvex (f.support : Set (Fin n →₀ ℕ)) := by
  intro α hα β hβ i hi
  by_cases hcommon : ∃ k : Fin n, 0 < α k ∧ 0 < β k
  · obtain ⟨k, hαk, hβk⟩ := hcommon
    exact support_exchange_of_common_positive_coordinate n f hderiv α β hα hβ
      i k hi hαk hβk
  · apply hdisjoint α β hα hβ _ i hi
    intro k
    by_cases hαk : α k = 0
    · exact Or.inl hαk
    · right
      by_contra hβk
      exact hcommon ⟨k, Nat.pos_of_ne_zero hαk, Nat.pos_of_ne_zero hβk⟩
noncomputable def coefficientExchangeDistance {n : ℕ} (α β : Fin n →₀ ℕ) : ℕ :=
  Finsupp.weight (1 : Fin n → ℕ) (α - β)
lemma exchange_weight_sum {n : ℕ} (α : Fin n →₀ ℕ) :
    Finsupp.weight (1 : Fin n → ℕ) α = ∑ k : Fin n, α k := by
  simp [Finsupp.weight_eq_sum]
lemma exchange_weight_move {n : ℕ} (α : Fin n →₀ ℕ) (i j : Fin n)
    (hi : 0 < α i) :
    Finsupp.weight (1 : Fin n → ℕ) (α - Finsupp.single i 1 + Finsupp.single j 1) = Finsupp.weight (1 : Fin n → ℕ) α := by
  have h := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hi)
  simpa [map_add, Finsupp.weight_single] using h
lemma exchange_distance_symm {n : ℕ} (α β : Fin n →₀ ℕ)
    (h : Finsupp.weight (1 : Fin n → ℕ) α = Finsupp.weight (1 : Fin n → ℕ) β) :
    coefficientExchangeDistance α β = coefficientExchangeDistance β α := by
  unfold coefficientExchangeDistance
  simp only [exchange_weight_sum, Finsupp.coe_tsub, Pi.sub_apply] at *
  have heq : (∑ k : Fin n, (α k - β k)) + (∑ k : Fin n, β k) =
      (∑ k : Fin n, (β k - α k)) + (∑ k : Fin n, α k) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    omega
  omega
lemma exchange_distance_move {n : ℕ} (α β : Fin n →₀ ℕ) (c b : Fin n)
    (hc : β c < α c) (hb : α b < β b) :
    coefficientExchangeDistance (α - Finsupp.single c 1 + Finsupp.single b 1) β + 1 =
      coefficientExchangeDistance α β := by
  classical
  have hcb : c ≠ b := by intro h; subst b; omega
  unfold coefficientExchangeDistance
  simp only [exchange_weight_sum, Finsupp.coe_tsub, Pi.sub_apply]
  have heq : ∀ k : Fin n,
      (α - Finsupp.single c 1 + Finsupp.single b 1 : Fin n →₀ ℕ) k - β k + (if k = c then 1 else 0) =
        α k - β k := by
    intro k
    by_cases hkc : k = c
    · subst k
      simp [Ne.symm hcb]
      omega
    · by_cases hkb : k = b
      · subst k
        simp [Ne.symm hcb]
        omega
      · simp [hkc, hkb]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun k _ => heq k)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finsupp.coe_tsub, Pi.sub_apply] using hsum
lemma exchange_distance_remove {n : ℕ} (α β : Fin n →₀ ℕ) (i : Fin n)
    (hi : β i < α i) :
    coefficientExchangeDistance (α - Finsupp.single i 1) β + 1 =
      coefficientExchangeDistance α β := by
  classical
  unfold coefficientExchangeDistance
  simp only [exchange_weight_sum, Finsupp.coe_tsub, Pi.sub_apply]
  have heq : ∀ k : Fin n,
      (α - Finsupp.single i 1 : Fin n →₀ ℕ) k - β k + (if k = i then 1 else 0) =
        α k - β k := by
    intro k
    by_cases hki : k = i
    · subst k
      simp
      omega
    · simp [hki]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun k _ => heq k)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finsupp.coe_tsub, Pi.sub_apply] using hsum
lemma exchange_surplus_exists {n : ℕ} (α β : Fin n →₀ ℕ)
    (hD : 0 < coefficientExchangeDistance α β) : ∃ c, β c < α c := by
  by_contra! h
  have hzero : α - β = 0 := by
    ext k
    simp [Nat.sub_eq_zero_of_le (h k)]
  simp [coefficientExchangeDistance, hzero] at hD
lemma exchange_deficit_exists {n : ℕ} (α β : Fin n →₀ ℕ)
    (h : Finsupp.weight (1 : Fin n → ℕ) α = Finsupp.weight (1 : Fin n → ℕ) β)
    (i : Fin n) (hi : β i < α i) : ∃ b, α b < β b := by
  apply exchange_surplus_exists β α
  rw [← exchange_distance_symm α β h]
  have hle := Finsupp.le_weight (1 : Fin n → ℕ) (s := i) (by simp) (α - β)
  have hpos : 0 < (α - β) i := by simpa using Nat.sub_pos_of_lt hi
  exact lt_of_lt_of_le hpos hle
lemma exchange_distance_one {n : ℕ} (α β : Fin n →₀ ℕ)
    (hD : coefficientExchangeDistance α β = 1) (i : Fin n) (hi : β i < α i) :
    α - β = Finsupp.single i 1 := by
  have hd : (α - β).degree = 1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hD
  have hmem : α - β ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
    rw [Finsupp.range_single_one]
    exact hd
  obtain ⟨j, hj⟩ := hmem
  have hji : j = i := by
    by_contra hne
    have he := congrArg (fun δ : Fin n →₀ ℕ => δ i) hj
    simp [Ne.symm hne] at he
    omega
  simpa [hji] using hj.symm
lemma exchange_distance_one_move {n : ℕ} (α β : Fin n →₀ ℕ)
    (h : Finsupp.weight (1 : Fin n → ℕ) α = Finsupp.weight (1 : Fin n → ℕ) β)
    (hD : coefficientExchangeDistance α β = 1) (i b : Fin n)
    (hi : β i < α i) (hb : α b < β b) :
    α - Finsupp.single i 1 + Finsupp.single b 1 = β := by
  classical
  have hi' := exchange_distance_one α β hD i hi
  have hb' := exchange_distance_one β α ((exchange_distance_symm α β h).symm.trans hD) b hb
  ext k
  have he1 := congrArg (fun δ : Fin n →₀ ℕ => δ k) hi'
  have he2 := congrArg (fun δ : Fin n →₀ ℕ => δ k) hb'
  by_cases hki : k = i <;> by_cases hkb : k = b <;>
    simp [hki, hkb] at * <;> omega
lemma exchange_move_preserves_surplus {n : ℕ} (α β : Fin n →₀ ℕ)
    (i c b : Fin n) (hi : β i < α i)
    (hc : β c < (α - Finsupp.single i 1 : Fin n →₀ ℕ) c) (hb : α b < β b) :
    β i < (α - Finsupp.single c 1 + Finsupp.single b 1 : Fin n →₀ ℕ) i := by
  classical
  have hbi : b ≠ i := by intro h; subst b; omega
  by_cases hci : c = i
  · subst c
    simpa [hbi] using hc
  · simpa [Ne.symm hci, Ne.symm hbi] using hi
lemma exchange_move_deficit_subset {n : ℕ} (α β : Fin n →₀ ℕ)
    (c b : Fin n) (hc : β c < α c) :
    {j : Fin n | (α - Finsupp.single c 1 + Finsupp.single b 1 : Fin n →₀ ℕ) j < β j} ⊆
      {j : Fin n | α j < β j} := by
  classical
  intro j hj
  change (α - Finsupp.single c 1 + Finsupp.single b 1 : Fin n →₀ ℕ) j < β j at hj
  change α j < β j
  by_cases hjc : j = c
  · subst j
    simp at hj
    omega
  · simp [Ne.symm hjc] at hj
    omega
lemma exchange_move_commute {n : ℕ} (α : Fin n →₀ ℕ) (i c b j : Fin n)
    (hi : 0 < α i) (hc : 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) c) :
    (α - Finsupp.single c 1 + Finsupp.single b 1) - Finsupp.single i 1 +
        Finsupp.single j 1 =
      α - Finsupp.single i 1 - Finsupp.single c 1 + Finsupp.single b 1 +
        Finsupp.single j 1 := by
  classical
  ext k
  by_cases hki : k = i
  · subst k
    by_cases hic : i = c
    · subst c
      simp at hc
      simp
      omega
    · simp [Ne.symm hic]
      omega
  · simp [Ne.symm hki]
lemma positive_array_exchange_of_local_four_point
    (n r : ℕ) (a : (Fin n →₀ ℕ) → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (ha : ∀ α, Finsupp.weight (1 : Fin n → ℕ) α = r → 0 < a α)
    (hlocal : ∀ α, Finsupp.weight (1 : Fin n → ℕ) α = r →
      ∀ i c : Fin n, 0 < α i → 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) c →
      ∀ b j : Fin n,
      a α * a (α - Finsupp.single i 1 - Finsupp.single c 1 +
          Finsupp.single b 1 + Finsupp.single j 1) ≤
        K * (a (α - Finsupp.single i 1 + Finsupp.single b 1) *
            a (α - Finsupp.single c 1 + Finsupp.single j 1) +
          a (α - Finsupp.single i 1 + Finsupp.single j 1) *
            a (α - Finsupp.single c 1 + Finsupp.single b 1))) :
    ∀ α β, Finsupp.weight (1 : Fin n → ℕ) α = r →
      Finsupp.weight (1 : Fin n → ℕ) β = r → ∀ i : Fin n, β i < α i →
      a α * a β ≤ (2 * K) ^ r *
        ∑ j : Fin n, if α j < β j then
          a (α - Finsupp.single i 1 + Finsupp.single j 1) *
            a (β - Finsupp.single j 1 + Finsupp.single i 1) else 0 := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have h2K : 1 ≤ 2 * K := by linarith
  let S (α β : Fin n →₀ ℕ) : Finset (Fin n) :=
    Finset.univ.filter fun j => α j < β j
  have hSmem : ∀ α β j, j ∈ S α β ↔ α j < β j := by simp [S]
  have hsumpos : ∀ α β i, Finsupp.weight (1 : Fin n → ℕ) α = r →
      Finsupp.weight (1 : Fin n → ℕ) β = r → 0 < α i →
      ∀ j ∈ S α β,
        0 ≤ a (α - Finsupp.single i 1 + Finsupp.single j 1) *
          a (β - Finsupp.single j 1 + Finsupp.single i 1) := by
    intro α β i hα hβ hi j hj
    have hj' := (hSmem α β j).mp hj
    exact mul_nonneg
      (ha _ ((exchange_weight_move α i j hi).trans hα)).le
      (ha _ ((exchange_weight_move β j i (by omega)).trans hβ)).le
  have main : ∀ m : ℕ, ∀ α β : Fin n →₀ ℕ,
      Finsupp.weight (1 : Fin n → ℕ) α = r →
      Finsupp.weight (1 : Fin n → ℕ) β = r →
      coefficientExchangeDistance α β = m → ∀ i : Fin n, β i < α i →
      a α * a β ≤ (2 * K) ^ m *
        ∑ j ∈ S α β, a (α - Finsupp.single i 1 + Finsupp.single j 1) *
          a (β - Finsupp.single j 1 + Finsupp.single i 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro α β hα hβ hD i hi
      have hi0 : 0 < α i := by omega
      have hw : Finsupp.weight (1 : Fin n → ℕ) α =
          Finsupp.weight (1 : Fin n → ℕ) β := hα.trans hβ.symm
      obtain ⟨b₀, hb₀⟩ := exchange_deficit_exists α β hw i hi
      have hSne : (S α β).Nonempty := ⟨b₀, (hSmem α β b₀).mpr hb₀⟩
      have hDpos : 0 < m := by
        have hle := Finsupp.le_weight (1 : Fin n → ℕ) (s := i) (by simp) (α - β)
        have hpos : 0 < (α - β) i := by simpa using Nat.sub_pos_of_lt hi
        change (α - β) i ≤ coefficientExchangeDistance α β at hle
        omega
      by_cases hm : m = 1
      · have hmove := exchange_distance_one_move α β hw (hD.trans hm) i b₀ hi hb₀
        have hmove' := exchange_distance_one_move β α hw.symm
          ((exchange_distance_symm α β hw).symm.trans (hD.trans hm)) b₀ i hb₀ hi
        have hterm : a α * a β ≤
            ∑ j ∈ S α β, a (α - Finsupp.single i 1 + Finsupp.single j 1) *
              a (β - Finsupp.single j 1 + Finsupp.single i 1) := by
          have hle := Finset.single_le_sum (hsumpos α β i hα hβ hi0)
            ((hSmem α β b₀).mpr hb₀)
          simpa [hmove, hmove', mul_comm] using hle
        calc
          a α * a β ≤ _ := hterm
          _ ≤ _ := le_mul_of_one_le_left (Finset.sum_nonneg (hsumpos α β i hα hβ hi0))
            (by simpa [hm] using h2K)
      · have hrem := exchange_distance_remove α β i hi
        obtain ⟨c, hc⟩ := exchange_surplus_exists (α - Finsupp.single i 1) β
          (by omega)
        have hc0 : 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) c := by omega
        have hc' : β c < α c := by
          have hle : (α - Finsupp.single i 1 : Fin n →₀ ℕ) c ≤ α c := by simp
          omega
        have hcα : 0 < α c := by omega
        let U (j : Fin n) := α - Finsupp.single c 1 + Finsupp.single j 1
        let X (j : Fin n) := a (α - Finsupp.single i 1 + Finsupp.single j 1)
        let Y (j : Fin n) := a (β - Finsupp.single j 1 + Finsupp.single i 1)
        let W (b j : Fin n) := α - Finsupp.single i 1 - Finsupp.single c 1 +
          Finsupp.single b 1 + Finsupp.single j 1
        have hUw : ∀ j, Finsupp.weight (1 : Fin n → ℕ) (U j) = r :=
          fun j => (exchange_weight_move α c j hcα).trans hα
        have hUp : ∀ j, 0 < a (U j) := fun j => ha _ (hUw j)
        obtain ⟨b, hb, hmin⟩ := (S α β).exists_min_image (fun j => X j / a (U j)) hSne
        have hb' := (hSmem α β b).mp hb
        have hmin' : ∀ j ∈ S α β, X b * a (U j) ≤ X j * a (U b) := by
          intro j hj
          exact (div_le_div_iff₀ (hUp b) (hUp j)).mp (hmin j hj)
        have hiU : β i < U b i := exchange_move_preserves_surplus α β i c b hi hc hb'
        have hdist := exchange_distance_move α β c b hc' hb'
        change coefficientExchangeDistance (U b) β + 1 = coefficientExchangeDistance α β at hdist
        have hsub : S (U b) β ⊆ S α β := by
          intro j hj
          apply (hSmem α β j).mpr
          exact exchange_move_deficit_subset α β c b hc' ((hSmem (U b) β j).mp hj)
        have hW : ∀ j, U b - Finsupp.single i 1 + Finsupp.single j 1 = W b j :=
          fun j => exchange_move_commute α i c b j hi0 hc0
        have hWp : ∀ j, 0 < a (W b j) := by
          intro j
          rw [← hW j]
          exact ha _ ((exchange_weight_move (U b) i j (by omega)).trans (hUw b))
        have hYp : ∀ j ∈ S α β, 0 < Y j := by
          intro j hj
          exact ha _ ((exchange_weight_move β j i (by have := (hSmem α β j).mp hj; omega)).trans hβ)
        have hind := ih (coefficientExchangeDistance (U b) β) (by omega)
          (U b) β (hUw b) hβ rfl i hiU
        simp_rw [hW] at hind
        have hind' : a (U b) * a β ≤ (2 * K) ^ coefficientExchangeDistance (U b) β *
            ∑ j ∈ S α β, a (W b j) * Y j := by
          apply hind.trans
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => mul_nonneg (hWp j).le (hYp j hj).le)
        have hlocal' : ∀ j ∈ S α β,
            a α * (a (W b j) * Y j) ≤ (2 * K * a (U b)) * (X j * Y j) := by
          intro j hj
          have hh := hlocal α hα i c hi0 hc0 b j
          have hh' : a α * a (W b j) ≤ 2 * K * a (U b) * X j := by
            calc
              a α * a (W b j) ≤ K * (X b * a (U j) + X j * a (U b)) := hh
              _ ≤ K * (X j * a (U b) + X j * a (U b)) :=
                mul_le_mul_of_nonneg_left (add_le_add (hmin' j hj) le_rfl) hK0
              _ = _ := by ring
          have hy := mul_le_mul_of_nonneg_right hh' (hYp j hj).le
          nlinarith
        have hsum : a α * (∑ j ∈ S α β, a (W b j) * Y j) ≤
            (2 * K * a (U b)) * (∑ j ∈ S α β, X j * Y j) := by
          simpa only [Finset.mul_sum] using Finset.sum_le_sum hlocal'
        apply (mul_le_mul_iff_right₀ (hUp b)).mp
        calc
          a (U b) * (a α * a β) = a α * (a (U b) * a β) := by ring
          _ ≤ a α * ((2 * K) ^ coefficientExchangeDistance (U b) β *
              ∑ j ∈ S α β, a (W b j) * Y j) :=
            mul_le_mul_of_nonneg_left hind' (ha α hα).le
          _ = (2 * K) ^ coefficientExchangeDistance (U b) β *
              (a α * (∑ j ∈ S α β, a (W b j) * Y j)) := by ring
          _ ≤ (2 * K) ^ coefficientExchangeDistance (U b) β *
              ((2 * K * a (U b)) * (∑ j ∈ S α β, X j * Y j)) :=
            mul_le_mul_of_nonneg_left hsum (pow_nonneg (by linarith) _)
          _ = a (U b) * ((2 * K) ^ m * (∑ j ∈ S α β, X j * Y j)) := by
            have hd : m = coefficientExchangeDistance (U b) β + 1 := by
              omega
            rw [hd, pow_succ]
            ring
  intro α β hα hβ i hi
  have hmain := main (coefficientExchangeDistance α β) α β hα hβ rfl i hi
  have hDr : coefficientExchangeDistance α β ≤ r := by
    rw [← hα]
    unfold coefficientExchangeDistance
    simp only [exchange_weight_sum, Finsupp.coe_tsub, Pi.sub_apply]
    exact Finset.sum_le_sum fun j _ => Nat.sub_le _ _
  have hpow := pow_le_pow_right₀ h2K hDr
  have hh := hmain.trans (mul_le_mul_of_nonneg_right hpow
    (Finset.sum_nonneg (hsumpos α β i hα hβ (by omega))))
  simpa [S, Finset.sum_filter] using hh
lemma bilinear_four_point_of_negative_kernel
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (u v w z : V)
    (hn : ∀ x, B u x = 0 → B x x ≤ 0)
    (huv : 0 < B u v) (huw : 0 < B u w) (huz : 0 < B u z)
    (hvv : 0 ≤ B v v) (hww : 0 ≤ B w w) (hzz : 0 ≤ B z z) :
    B u v * B w z ≤ 2 * (B u w * B v z + B u z * B v w) := by
  let x := (2 * B u w * B u z) • v - (B u v * B u z) • w -
    (B u v * B u w) • z
  have hrow : B u x = 0 := by
    dsimp [x]
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hneg := hn x hrow
  have hsymwv := hB w v
  have hsymzv := hB z v
  have hsymzw := hB z w
  have heq : B x x =
      (4 * (B u w) ^ 2 * (B u z) ^ 2 * B v v +
        (B u v) ^ 2 * (B u z) ^ 2 * B w w +
        (B u v) ^ 2 * (B u w) ^ 2 * B z z) +
      (2 * B u v * B u w * B u z) *
        (B u v * B w z - 2 * (B u w * B v z + B u z * B v w)) := by
    dsimp [x]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hsymwv, hsymzv, hsymzw]
    ring
  rw [heq] at hneg
  have hdiag : 0 ≤ 4 * (B u w) ^ 2 * (B u z) ^ 2 * B v v +
      (B u v) ^ 2 * (B u z) ^ 2 * B w w +
      (B u v) ^ 2 * (B u w) ^ 2 * B z z := by positivity
  have hprod : 0 < 2 * B u v * B u w * B u z := by positivity
  have hsmall : (2 * B u v * B u w * B u z) *
      (B u v * B w z - 2 * (B u w * B v z + B u z * B v w)) ≤ 0 := by
    linarith
  have hdiff : B u v * B w z - 2 * (B u w * B v z + B u z * B v w) ≤ 0 :=
    (mul_le_mul_iff_right₀ hprod).mp (by simpa using hsmall)
  linarith
lemma matrix_four_point_of_negative_kernel
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : A.IsSymm) (hpos : ∀ i j, 0 < A i j)
    (hneg : ∀ i (x : Fin n → ℝ),
      A.toBilin' (Pi.single i 1) x = 0 → A.toBilin' x x ≤ 0) :
    ∀ i j k l, A i j * A k l ≤ 2 * (A i k * A j l + A i l * A j k) := by
  intro i j k l
  have hsym' : ∀ x y, A.toBilin' x y = A.toBilin' y x :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hsym).eq
  simpa only [Matrix.toBilin'_single] using
    bilinear_four_point_of_negative_kernel (Fin n → ℝ) A.toBilin' hsym'
      (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
      (hneg i) (by simpa using hpos i j) (by simpa using hpos i k)
      (by simpa using hpos i l) (by simpa using (hpos j j).le)
      (by simpa using (hpos k k).le) (by simpa using (hpos l l).le)
def strictCoefficientFourPointBound (n r : ℕ) (K : ℝ) : Prop :=
  ∀ f : LorentzianPolynomials.H n r, f ∈ LorentzianPolynomials.Ŀ n r →
    ∀ α : Fin n →₀ ℕ, Finsupp.weight (1 : Fin n → ℕ) α = r →
    ∀ i c : Fin n, 0 < α i → 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) c →
    ∀ b j : Fin n,
    f.1.coeff α * f.1.coeff (α - Finsupp.single i 1 - Finsupp.single c 1 +
        Finsupp.single b 1 + Finsupp.single j 1) ≤
      K * (f.1.coeff (α - Finsupp.single i 1 + Finsupp.single b 1) *
          f.1.coeff (α - Finsupp.single c 1 + Finsupp.single j 1) +
        f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (α - Finsupp.single c 1 + Finsupp.single b 1))
lemma strict_uniform_coefficient_exchange_of_local_four_point
    (hlocal : ∀ n d : ℕ, 0 < n → ∃ K : ℝ, 1 ≤ K ∧
      strictCoefficientFourPointBound n (d + 3) K) :
    ∀ n d : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧
      ∀ f : LorentzianPolynomials.H n (d + 3),
      f ∈ LorentzianPolynomials.Ŀ n (d + 3) →
      ∀ α β : Fin n →₀ ℕ, Finsupp.weight 1 α = d + 3 →
      Finsupp.weight 1 β = d + 3 → ∀ i : Fin n, β i < α i →
      f.1.coeff α * f.1.coeff β ≤ C * Finset.sum Finset.univ
        (fun j : Fin n => if α j < β j then
          f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1) else 0) := by
  intro n d hn
  obtain ⟨K, hK, hbound⟩ := hlocal n d hn
  refine ⟨(2 * K) ^ (d + 3), by positivity, ?_⟩
  intro f hf
  have hp : f ∈ LorentzianPolynomials.P n (d + 3) := hf.1
  exact positive_array_exchange_of_local_four_point n (d + 3) f.1.coeff K hK
    (fun α hα => hp α hα) (hbound f hf)
lemma exchange_spectral_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (x : Fin n → ℝ) :
    A.toBilin' x x = ∑ k, hA.eigenvalues k *
      (((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec x) k) ^ 2 := by
  rw [Matrix.toBilin'_apply']
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply,
    RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.sum_congr rfl
  intro k _
  ring
lemma exchange_negative_kernel_of_one_positive_root {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hroot : (A.charpoly.roots.filter (0 < ·)).card = 1)
    (u : Fin n → ℝ) (hu : 0 < A.toBilin' u u) :
    ∀ x : Fin n → ℝ, A.toBilin' u x = 0 → A.toBilin' x x ≤ 0 := by
  classical
  have hcard : (Finset.univ.filter (fun k => 0 < hA.eigenvalues k)).card = 1 := by
    rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map] at hroot
    simpa only [Finset.card, Finset.filter_val, Function.comp_apply,
      RCLike.ofReal_real_eq_id, id_eq] using hroot
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hothers : ∀ j, j ≠ k → hA.eigenvalues j ≤ 0 := by
    intro j hj
    by_contra! hpos
    have hmem : j ∈ Finset.univ.filter (fun q => 0 < hA.eigenvalues q) := by
      simpa using hpos
    rw [hk] at hmem
    exact hj (Finset.mem_singleton.mp hmem)
  let T (v : Fin n → ℝ) :=
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec v
  have hkill : ∀ v, T v k = 0 → A.toBilin' v v ≤ 0 := by
    intro v hv
    rw [exchange_spectral_expansion A hA v]
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : j = k
    · subst j
      change hA.eigenvalues k * (T v k) ^ 2 ≤ 0
      simp [hv]
    · exact mul_nonpos_of_nonpos_of_nonneg (hothers j hj) (sq_nonneg _)
  have huk : T u k ≠ 0 := by
    intro hz
    have := hkill u hz
    linarith
  have hsym : ∀ v w, A.toBilin' v w = A.toBilin' w v :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (by simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA)).eq
  intro x hx
  let y := (T x k) • u - (T u k) • x
  have hy : T y k = 0 := by
    dsimp [T, y]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hny := hkill y hy
  have heq : A.toBilin' y y = (T x k) ^ 2 * A.toBilin' u u +
      (T u k) ^ 2 * A.toBilin' x x := by
    dsimp [y]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hsym x u, hx]
    ring
  rw [heq] at hny
  have hspos : 0 < (T u k) ^ 2 := sq_pos_of_ne_zero huk
  have hnonneg : 0 ≤ (T x k) ^ 2 * A.toBilin' u u := mul_nonneg (sq_nonneg _) hu.le
  by_contra! hpos
  have := mul_pos hspos hpos
  linarith
lemma exchange_quadratic_hessian_isHermitian {n : ℕ}
    (f : LorentzianPolynomials.H n 2) : f.hessian.IsHermitian := by
  classical
  apply Matrix.isHermitian_iff_isSymm.mpr
  apply Matrix.IsSymm.ext
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [LorentzianPolynomials.H.hessian, h, Ne.symm h, add_comm]
lemma exchange_quadratic_hessian_entries_positive {n : ℕ}
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.Ŀ n 2) :
    ∀ i j, 0 < f.hessian i j := by
  classical
  intro i j
  have hp : f ∈ LorentzianPolynomials.P n 2 := hf.1
  by_cases h : i = j
  · subst j
    have hh := hp (Finsupp.single i 2) (by simp [Finsupp.weight_single])
    simpa [LorentzianPolynomials.H.hessian] using mul_pos (by norm_num : (0 : ℝ) < 2) hh
  · simpa [LorentzianPolynomials.H.hessian, h] using
      hp (Finsupp.single i 1 + Finsupp.single j 1) (by simp [Finsupp.weight_single])
lemma exchange_quadratic_coefficient_four_point {n : ℕ}
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.Ŀ n 2)
    (i c b j : Fin n) :
    f.1.coeff (Finsupp.single i 1 + Finsupp.single c 1) *
        f.1.coeff (Finsupp.single b 1 + Finsupp.single j 1) ≤
      8 * (f.1.coeff (Finsupp.single i 1 + Finsupp.single b 1) *
          f.1.coeff (Finsupp.single c 1 + Finsupp.single j 1) +
        f.1.coeff (Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (Finsupp.single c 1 + Finsupp.single b 1)) := by
  classical
  let a (p q : Fin n) := f.1.coeff (Finsupp.single p 1 + Finsupp.single q 1)
  have hA := exchange_quadratic_hessian_isHermitian f
  have hpos := exchange_quadratic_hessian_entries_positive f hf
  have hp : ∀ p q, 0 < a p q := fun p q => hf.1 _ (by simp [Finsupp.weight_single])
  have hlo : ∀ p q, a p q ≤ f.hessian p q := by
    intro p q
    by_cases h : p = q
    · subst q
      have he : Finsupp.single p 1 + Finsupp.single p 1 =
          (Finsupp.single p 2 : Fin n →₀ ℕ) := by rw [← Finsupp.single_add]
      dsimp [a]
      rw [he]
      have hcoef := hf.1 (Finsupp.single p 2) (by simp [Finsupp.weight_single])
      simpa [LorentzianPolynomials.H.hessian] using
        (show f.1.coeff (Finsupp.single p 2) ≤ 2 * f.1.coeff (Finsupp.single p 2) by linarith)
    · simp [a, LorentzianPolynomials.H.hessian, h]
  have hhi : ∀ p q, f.hessian p q ≤ 2 * a p q := by
    intro p q
    by_cases h : p = q
    · subst q
      simp [a, LorentzianPolynomials.H.hessian, ← Finsupp.single_add]
    · have hcoef := hp p q
      rw [show f.hessian p q = a p q by simp [LorentzianPolynomials.H.hessian, h, a]]
      change a p q ≤ 2 * a p q
      linarith
  have hprodlo : ∀ p q r s, a p q * a r s ≤ f.hessian p q * f.hessian r s :=
    fun p q r s => mul_le_mul (hlo p q) (hlo r s) (hp r s).le (hpos p q).le
  have hprodhi : ∀ p q r s, f.hessian p q * f.hessian r s ≤
      (2 * a p q) * (2 * a r s) :=
    fun p q r s => mul_le_mul (hhi p q) (hhi r s) (hpos r s).le (mul_nonneg (by norm_num) (hp p q).le)
  have hfour := matrix_four_point_of_negative_kernel n f.hessian hA.isSymm hpos
    (fun p => exchange_negative_kernel_of_one_positive_root f.hessian hA hf.2.2
      (Pi.single p 1) (by simpa only [Matrix.toBilin'_single] using hpos p p)) i c b j
  change a i c * a b j ≤ 8 * (a i b * a c j + a i j * a c b)
  calc
    a i c * a b j ≤ f.hessian i c * f.hessian b j := hprodlo i c b j
    _ ≤ 2 * (f.hessian i b * f.hessian c j + f.hessian i j * f.hessian c b) := hfour
    _ ≤ 2 * ((2 * a i b) * (2 * a c j) + (2 * a i j) * (2 * a c b)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hprodhi i b c j) (hprodhi i j c b)) (by norm_num)
    _ = _ := by ring
lemma exchange_four_point_transfer {I : Type*} (a A : I → I → ℝ) (K R : ℝ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (ha : ∀ p q, 0 ≤ a p q)
    (hlo : ∀ p q, a p q ≤ A p q) (hhi : ∀ p q, A p q ≤ R * a p q)
    (i c b j : I)
    (hfour : A i c * A b j ≤ K * (A i b * A c j + A i j * A c b)) :
    a i c * a b j ≤ (K * R ^ 2) * (a i b * a c j + a i j * a c b) := by
  have hA : ∀ p q, 0 ≤ A p q := fun p q => (ha p q).trans (hlo p q)
  have hprodlo := mul_le_mul (hlo i c) (hlo b j) (ha b j) (hA i c)
  have hprodhi : ∀ p q r s, A p q * A r s ≤ (R * a p q) * (R * a r s) :=
    fun p q r s => mul_le_mul (hhi p q) (hhi r s) (hA r s) (mul_nonneg hR (ha p q))
  calc
    a i c * a b j ≤ A i c * A b j := hprodlo
    _ ≤ K * (A i b * A c j + A i j * A c b) := hfour
    _ ≤ K * ((R * a i b) * (R * a c j) + (R * a i j) * (R * a c b)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hprodhi i b c j) (hprodhi i j c b)) hK
    _ = _ := by ring
def strictCommonCoefficientFourPointBound (n d : ℕ) (K : ℝ) : Prop :=
  ∀ f : LorentzianPolynomials.H n (d + 2), f ∈ LorentzianPolynomials.Ŀ n (d + 2) →
    ∀ γ : Fin n →₀ ℕ, Finsupp.weight (1 : Fin n → ℕ) γ = d →
    ∀ i c b j : Fin n,
    f.1.coeff (γ + Finsupp.single i 1 + Finsupp.single c 1) *
        f.1.coeff (γ + Finsupp.single b 1 + Finsupp.single j 1) ≤
      K * (f.1.coeff (γ + Finsupp.single i 1 + Finsupp.single b 1) *
          f.1.coeff (γ + Finsupp.single c 1 + Finsupp.single j 1) +
        f.1.coeff (γ + Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (γ + Finsupp.single c 1 + Finsupp.single b 1))
lemma strict_common_coefficient_four_point_bound (n d : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ strictCommonCoefficientFourPointBound n d K := by
  induction d with
  | zero =>
    refine ⟨8, by norm_num, ?_⟩
    intro f hf γ hγ i c b j
    have hzero : γ = 0 := by
      ext k
      have hle := Finsupp.le_weight (1 : Fin n → ℕ) (s := k) (by simp) γ
      simp only [hγ] at hle
      simpa using hle
    subst γ
    simpa only [zero_add] using exchange_quadratic_coefficient_four_point f hf i c b j
  | succ d ih =>
    obtain ⟨K, hK, hbound⟩ := ih
    have hR : (1 : ℝ) ≤ (d + 3 : ℕ) := by exact_mod_cast (by omega : 1 ≤ d + 3)
    refine ⟨K * ((d + 3 : ℕ) : ℝ) ^ 2, ?_, ?_⟩
    · have hs : (1 : ℝ) ≤ ((d + 3 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hR
      nlinarith
    · intro f hf γ hγ i c b j
      obtain ⟨k, hk⟩ := exchange_surplus_exists γ 0 (by
        simp only [coefficientExchangeDistance, tsub_zero, hγ]
        omega)
      have hk0 : 0 < γ k := by simpa using hk
      let δ := γ - Finsupp.single k 1
      have hδ : Finsupp.weight (1 : Fin n → ℕ) δ = d := by
        have hh := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ))
          (Nat.ne_of_gt hk0)
        change Finsupp.weight (1 : Fin n → ℕ) δ + 1 =
          Finsupp.weight (1 : Fin n → ℕ) γ at hh
        omega
      have hcancel : δ + Finsupp.single k 1 = γ :=
        Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hk0)
      let g : LorentzianPolynomials.H n (d + 2) := ⟨f.1.pderiv k, f.2.pderiv⟩
      have hg : g ∈ LorentzianPolynomials.Ŀ n (d + 2) := hf.2 k
      let a (p q : Fin n) := f.1.coeff (γ + Finsupp.single p 1 + Finsupp.single q 1)
      let A (p q : Fin n) := g.1.coeff (δ + Finsupp.single p 1 + Finsupp.single q 1)
      have hsum : ∀ p q, (δ + Finsupp.single p 1 + Finsupp.single q 1) +
          Finsupp.single k 1 = γ + Finsupp.single p 1 + Finsupp.single q 1 := by
        intro p q
        calc
          _ = (δ + Finsupp.single k 1) + Finsupp.single p 1 + Finsupp.single q 1 := by ac_rfl
          _ = _ := by rw [hcancel]
      have ha : ∀ p q, 0 ≤ a p q := by
        intro p q
        apply le_of_lt
        apply hf.1
        simp only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one, hγ]
      have heq : ∀ p q, A p q = a p q *
          (↑((δ + Finsupp.single p 1 + Finsupp.single q 1 : Fin n →₀ ℕ) k) + 1) := by
        intro p q
        dsimp [A, g, a]
        rw [MvPolynomial.coeff_pderiv, hsum]
        simp only [Finsupp.add_apply]
      have hlo : ∀ p q, a p q ≤ A p q := by
        intro p q
        rw [heq]
        apply le_mul_of_one_le_right (ha p q)
        linarith [Nat.cast_nonneg ((δ + Finsupp.single p 1 + Finsupp.single q 1 : Fin n →₀ ℕ) k) (α := ℝ)]
      have hhi : ∀ p q, A p q ≤ ((d + 3 : ℕ) : ℝ) * a p q := by
        intro p q
        rw [heq, mul_comm (((d + 3 : ℕ) : ℝ))]
        apply mul_le_mul_of_nonneg_left _ (ha p q)
        have hle := Finsupp.le_weight (1 : Fin n → ℕ) (s := k) (by simp)
          (δ + Finsupp.single p 1 + Finsupp.single q 1)
        have hw : Finsupp.weight (1 : Fin n → ℕ)
            (δ + Finsupp.single p 1 + Finsupp.single q 1) = d + 2 := by
          simp [map_add, Finsupp.weight_single, hδ]
        have hle' : (δ + Finsupp.single p 1 + Finsupp.single q 1 : Fin n →₀ ℕ) k + 1 ≤
            d + 3 := by omega
        exact_mod_cast hle'
      exact exchange_four_point_transfer a A K ((d + 3 : ℕ) : ℝ)
        (by linarith) (by positivity) ha hlo hhi i c b j (hbound g hg δ hδ i c b j)
lemma strict_coefficient_four_point_bound (n d : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ strictCoefficientFourPointBound n (d + 3) K := by
  obtain ⟨K, hK, hbound⟩ := strict_common_coefficient_four_point_bound n (d + 1)
  refine ⟨K, hK, ?_⟩
  intro f hf α hα i c hi hc b j
  let γ := α - Finsupp.single i 1 - Finsupp.single c 1
  have hγ : Finsupp.weight (1 : Fin n → ℕ) γ = d + 1 := by
    have h1 := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hi)
    have h2 := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hc)
    change Finsupp.weight (1 : Fin n → ℕ) (α - Finsupp.single i 1) + 1 =
      Finsupp.weight (1 : Fin n → ℕ) α at h1
    change Finsupp.weight (1 : Fin n → ℕ) γ + 1 =
      Finsupp.weight (1 : Fin n → ℕ) (α - Finsupp.single i 1) at h2
    omega
  have hcancelc : γ + Finsupp.single c 1 = α - Finsupp.single i 1 :=
    Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hc)
  have hcancel : γ + Finsupp.single c 1 + Finsupp.single i 1 = α := by
    rw [hcancelc]
    exact Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hi)
  have hcanceli : γ + Finsupp.single i 1 = α - Finsupp.single c 1 := by
    have hipos : 0 < (α - Finsupp.single c 1 : Fin n →₀ ℕ) i := by
      by_cases hic : i = c
      · subst c
        simpa using hc
      · simpa [Ne.symm hic] using hi
    change (α - Finsupp.single i 1 - Finsupp.single c 1) + Finsupp.single i 1 = _
    rw [tsub_right_comm]
    exact Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hipos)
  have hh := hbound f hf γ hγ c i b j
  rw [hcancel, hcancelc, hcanceli] at hh
  exact hh
theorem strict_uniform_coefficient_exchange :
    ∀ (n d : ℕ), 0 < n → ∃ C : ℝ, 0 < C ∧
      ∀ f : LorentzianPolynomials.H n (d + 3),
      f ∈ LorentzianPolynomials.Ŀ n (d + 3) →
      ∀ α β : Fin n →₀ ℕ, Finsupp.weight 1 α = d + 3 →
      Finsupp.weight 1 β = d + 3 → ∀ i : Fin n, β i < α i →
      f.1.coeff α * f.1.coeff β ≤ C * Finset.sum Finset.univ
        (fun j : Fin n => if α j < β j then
          f.1.coeff (α - Finsupp.single i 1 + Finsupp.single j 1) *
          f.1.coeff (β - Finsupp.single j 1 + Finsupp.single i 1) else 0) := by
  exact strict_uniform_coefficient_exchange_of_local_four_point
    (fun n d _ => strict_coefficient_four_point_bound n d)
theorem closure_strict_support_isMConvex (n d : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n (d + 3))
    (hf : f ∈ closure (LorentzianPolynomials.Ŀ n (d + 3))) :
    LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := strict_uniform_coefficient_exchange n d hn
  apply closure_strict_support_mconvex_of_uniform_exchange n (d + 3) ?_ hf
  intro α β i hα hβ hi
  refine ⟨C, ?_⟩
  intro g hg
  simpa only [Finset.sum_filter] using hbound g hg α β hα hβ i hi
theorem closure_strict_subset_lorentzian (n d : ℕ) (hn : 0 < n) :
    closure (LorentzianPolynomials.Ŀ n d) ⊆ LorentzianPolynomials.L n d := by
  apply closure_strict_subset_of_support_limits ?_ n d hn
  intro m e hm f hf
  exact closure_strict_support_isMConvex m e (by omega) f hf
noncomputable def positiveCoefficientSeed (n d : ℕ) : LorentzianPolynomials.H n d := by
  classical
  let s := (Finsupp.finite_of_nat_weight_eq (1 : Fin n → ℕ) (by simp) d).toFinset
  refine ⟨∑ m ∈ s, MvPolynomial.monomial m (1 : ℝ), ?_⟩
  apply Submodule.sum_mem
  intro m hm
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  change Finsupp.weight (1 : Fin n → ℕ) m = d
  simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hm
lemma positiveCoefficientSeed_coeff (n d : ℕ) (m : Fin n →₀ ℕ)
    (hm : Finsupp.weight (1 : Fin n → ℕ) m = d) :
    (positiveCoefficientSeed n d).1.coeff m = 1 := by
  classical
  simp [positiveCoefficientSeed, MvPolynomial.coeff_monomial, hm]
lemma nonnegative_subset_closure_positive (n d : ℕ) :
    {f : LorentzianPolynomials.H n d | ∀ m, 0 ≤ f.1.coeff m} ⊆
      closure (LorentzianPolynomials.P n d) := by
  let V := MvPolynomial.homogeneousSubmodule (Fin n) ℝ d
  let : TopologicalSpace V := moduleTopology ℝ V
  have : ContinuousAdd V :=
    IsModuleTopology.toContinuousAdd ℝ _
  intro f hf
  let g : ℝ → V := fun t => (show V from f) + t • (show V from positiveCoefficientSeed n d)
  have hcont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (show V from f)) := by
    have hlim₀ : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (g 0)) :=
      (hcont.tendsto 0).mono_left inf_le_left
    have hg₀ : g 0 = (show V from f) := by
      apply Subtype.ext
      change f.1 + (0 : ℝ) • (positiveCoefficientSeed n d).1 = f.1
      simp
    rw [hg₀] at hlim₀
    exact hlim₀
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro m hm
  change 0 < f.1.coeff m + t * (positiveCoefficientSeed n d).1.coeff m
  rw [positiveCoefficientSeed_coeff n d m hm, mul_one]
  exact add_pos_of_nonneg_of_pos (hf m) ht
theorem stable_quadratic_nonpositive_kernel (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    ∀ x : Fin n → ℝ, f.hessian.toBilin' u x = 0 → f.hessian.toBilin' x x ≤ 0 := by
  classical
  by_cases hzero : f.1 = 0
  · intro x _
    simp [LorentzianPolynomials.H.hessian, hzero, Matrix.toBilin'_apply',
      Matrix.mulVec, dotProduct]
  have hA : f.hessian ≠ 0 :=
    fun h => hzero (forward_hessian_eq_zero_imp_polynomial_zero n f h)
  have hqu : 0 < f.hessian.toBilin' u u := by
    simpa only [Matrix.toBilin'_apply'] using
      nonzero_nonnegative_matrix_positive_pairing n f.hessian hA
        (forward_hessian_entries_nonnegative n f hf.2) u hu
  have hsym : ∀ v w, f.hessian.toBilin' v w = f.hessian.toBilin' w v :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (forward_hessian_isHermitian n f).isSymm).eq
  intro x hux
  by_contra! hx
  let t : ℝ := Real.sqrt (f.hessian.toBilin' u u / f.hessian.toBilin' x x)
  have ht : t ^ 2 = f.hessian.toBilin' u u / f.hessian.toBilin' x x :=
    Real.sq_sqrt (div_pos hqu hx).le
  have hq : t ^ 2 * f.hessian.toBilin' x x = f.hessian.toBilin' u u := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt hx)]
  have hscale : f.hessian.toBilin' (t • x) (t • x) =
      t ^ 2 * f.hessian.toBilin' x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hxu : f.hessian.toBilin' x u = 0 := (hsym x u).trans hux
  let z : Fin n → UpperHalfPlane := fun i => ⟨⟨t * x i, u i⟩, hu i⟩
  let S : ℂ := ∑ i : Fin n, ∑ j : Fin n,
    (z i : ℂ) * (z j : ℂ) * (f.hessian i j : ℂ)
  have hreal : S.re = 0 := by
    rw [forward_complex_quadratic_re, ← Matrix.toBilin'_apply', ← Matrix.toBilin'_apply']
    change f.hessian.toBilin' (t • x) (t • x) - f.hessian.toBilin' u u = 0
    rw [hscale, hq, sub_self]
  have him : S.im = 0 := by
    rw [forward_complex_quadratic_im n f.hessian (forward_hessian_isHermitian n f).isSymm,
      ← Matrix.toBilin'_apply']
    change 2 * f.hessian.toBilin' (t • x) u = 0
    simp [hxu]
  have hS : S = 0 := Complex.ext hreal him
  have heval : MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = 0 := by
    have h := forward_quadratic_hessian_aeval n f (fun i => (z i : ℂ))
    change 2 * MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = S at h
    rw [hS] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  exact (hf.1.resolve_left hzero z) heval
lemma reverse_eigenvector_dotProduct {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i j : Fin n) :
    dotProduct (hA.eigenvectorBasis i : Fin n → ℝ) (hA.eigenvectorBasis j : Fin n → ℝ) =
      if i = j then 1 else 0 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
    (hA.eigenvectorBasis.inner_eq_ite j i).trans (by simp only [eq_comm])
lemma reverse_eigenvector_pairing {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i j : Fin n) :
    A.toBilin' (hA.eigenvectorBasis i : Fin n → ℝ) (hA.eigenvectorBasis j : Fin n → ℝ) =
      if i = j then hA.eigenvalues j else 0 := by
  rw [Matrix.toBilin'_apply', hA.mulVec_eigenvectorBasis, dotProduct_smul,
    reverse_eigenvector_dotProduct]
  split_ifs <;> simp
theorem matrix_strict_signature_of_negative_hyperplane {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hneg : ∀ x : Fin n → ℝ, x ≠ 0 → l x = 0 → A.toBilin' x x < 0)
    (u : Fin n → ℝ) (hu : 0 < A.toBilin' u u) :
    IsUnit A ∧ (A.charpoly.roots.filter (0 < ·)).card = 1 := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, 0 < hA.eigenvalues k := by
    by_contra! hnonpos
    have hq : A.toBilin' u u ≤ 0 := by
      rw [exchange_spectral_expansion A hA u]
      exact Finset.sum_nonpos fun i _ =>
        mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (sq_nonneg _)
    linarith
  let v : Fin n → Fin n → ℝ := fun i => hA.eigenvectorBasis i
  have hvk : v k ≠ 0 := by
    intro h
    have hp : A.toBilin' (v k) (v k) = hA.eigenvalues k := by
      simpa only [ite_true] using reverse_eigenvector_pairing A hA k k
    rw [h] at hp
    simp only [map_zero, LinearMap.zero_apply] at hp
    linarith
  have hlk : l (v k) ≠ 0 := by
    intro h
    have hq := hneg (v k) hvk h
    have hp : A.toBilin' (v k) (v k) = hA.eigenvalues k := by
      simpa only [ite_true] using reverse_eigenvector_pairing A hA k k
    linarith
  have hothers : ∀ j, j ≠ k → hA.eigenvalues j < 0 := by
    intro j hj
    by_contra! hjpos
    let x := l (v k) • v j - l (v j) • v k
    have hx : x ≠ 0 := by
      intro hzero
      have hh := congrArg (fun w : Fin n → ℝ => dotProduct w (v j)) hzero
      dsimp [x] at hh
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] at hh
      change l (v k) * dotProduct (v j) (v j) -
        l (v j) * dotProduct (v k) (v j) = 0 at hh
      rw [reverse_eigenvector_dotProduct A hA j j,
        reverse_eigenvector_dotProduct A hA k j] at hh
      simp only [ite_true, if_neg (Ne.symm hj), mul_one, mul_zero, sub_zero] at hh
      exact hlk hh
    have hlx : l x = 0 := by simp [x, mul_comm]
    have hqx := hneg x hx hlx
    have heq : A.toBilin' x x = l (v k) ^ 2 * hA.eigenvalues j +
        l (v j) ^ 2 * hA.eigenvalues k := by
      dsimp [x]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [reverse_eigenvector_pairing A hA j j,
        reverse_eigenvector_pairing A hA j k,
        reverse_eigenvector_pairing A hA k j,
        reverse_eigenvector_pairing A hA k k]
      simp only [ite_true, if_neg hj, if_neg (Ne.symm hj)]
      ring
    rw [heq] at hqx
    have h1 := mul_nonneg (sq_nonneg (l (v k))) hjpos
    have h2 := mul_nonneg (sq_nonneg (l (v j))) hk.le
    linarith
  constructor
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, hA.det_eq_prod_eigenvalues]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    by_cases hj : j = k
    · subst j
      exact ne_of_gt hk
    · exact ne_of_lt (hothers j hj)
  · rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
    change (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card = 1
    have heq : Finset.univ.filter (fun i => 0 < hA.eigenvalues i) = {k} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hpos
        by_contra hj
        exact (hothers j hj).not_gt hpos
      · rintro rfl
        exact hk
    rw [heq, Finset.card_singleton]
noncomputable def quadraticFromMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    LorentzianPolynomials.H n 2 := by
  classical
  refine ⟨(1 / 2 : ℝ) • ∑ i : Fin n, ∑ j : Fin n,
    MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (A i j), ?_⟩
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  simpa using ((MvPolynomial.isHomogeneous_X ℝ i).mul
    (MvPolynomial.isHomogeneous_X ℝ j)).mul (MvPolynomial.isHomogeneous_C (Fin n) (A i j))
lemma quadraticFromMatrix_hessian (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) : (quadraticFromMatrix n A).hessian = A := by
  classical
  change Fin n → Fin n → ℝ at A
  ext i j
  rw [← forward_quadratic_pderiv_coefficient]
  have hsecond : ((quadraticFromMatrix n A).1.pderiv i).coeff (Finsupp.single j 1) =
      (((quadraticFromMatrix n A).1.pderiv i).pderiv j).coeff 0 := by
    simp [MvPolynomial.coeff_pderiv]
  rw [hsecond]
  change (MvPolynomial.pderiv j (MvPolynomial.pderiv i ((1 / 2 : ℝ) •
    ∑ a : Fin n, ∑ b : Fin n,
      MvPolynomial.X a * MvPolynomial.X b * MvPolynomial.C (A a b)))).coeff 0 = A i j
  simp [MvPolynomial.pderiv_mul, Pi.single_apply, ite_mul, mul_ite,
    apply_ite (MvPolynomial.pderiv j),
    apply_ite (fun p : MvPolynomial (Fin n) ℝ => p.coeff 0), Finset.sum_add_distrib]
  simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
  try simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [hA.apply j i]
  ring
lemma quadraticFromMatrix_hessian_self (n : ℕ) (f : LorentzianPolynomials.H n 2) :
    quadraticFromMatrix n f.hessian = f := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n,
    MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (f.hessian i j)) = f.1
  rw [← forward_quadratic_hessian_polynomial_identity n f, smul_smul]
  norm_num
lemma quadraticFromMatrix_continuous (n : ℕ) : Continuous (quadraticFromMatrix n) := by
  let V := MvPolynomial.homogeneousSubmodule (Fin n) ℝ 2
  let : TopologicalSpace V := moduleTopology ℝ V
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ _
  have : IsModuleTopology ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (IsModuleTopology ℝ (Fin n → Fin n → ℝ))
  let Q : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] V :=
    { toFun := fun A => quadraticFromMatrix n A
      map_add' := by
        intro A B
        apply Subtype.ext
        simp [quadraticFromMatrix, mul_add, Finset.sum_add_distrib, smul_add]
      map_smul' := by
        intro c A
        apply Subtype.ext
        change (1 / 2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n,
          MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (c * A i j)) =
          c • ((1 / 2 : ℝ) • ∑ i : Fin n, ∑ j : Fin n,
            MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.C (A i j))
        rw [smul_comm c (1 / 2 : ℝ)]
        congr 1
        simp_rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [MvPolynomial.C_mul, MvPolynomial.smul_eq_C_mul]
        ring }
  exact IsModuleTopology.continuous_of_linearMap Q
lemma degree_two_exponent (n : ℕ) (m : Fin n →₀ ℕ)
    (hm : Finsupp.weight (1 : Fin n → ℕ) m = 2) :
    ∃ i j : Fin n, m = Finsupp.single i 1 + Finsupp.single j 1 := by
  have hpos : 0 < coefficientExchangeDistance m 0 := by
    simpa only [coefficientExchangeDistance, tsub_zero, hm] using (by decide : 0 < 2)
  obtain ⟨i, hi⟩ := exchange_surplus_exists m 0 hpos
  have hi' : 0 < m i := by simpa using hi
  have hr : (m - Finsupp.single i 1).degree = 1 := by
    rw [Finsupp.degree_eq_weight_one]
    have h := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hi')
    change Finsupp.weight (1 : Fin n → ℕ) (m - Finsupp.single i 1) + 1 =
      Finsupp.weight (1 : Fin n → ℕ) m at h
    change Finsupp.weight (1 : Fin n → ℕ) (m - Finsupp.single i 1) = 1
    omega
  have hrange : m - Finsupp.single i 1 ∈
      Set.range (fun j : Fin n => Finsupp.single j 1) := by
    rw [Finsupp.range_single_one]
    exact hr
  obtain ⟨j, hj⟩ := hrange
  change Finsupp.single j 1 = m - Finsupp.single i 1 at hj
  refine ⟨i, j, ?_⟩
  rw [add_comm, hj]
  exact (Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hi')).symm
lemma positive_hessian_entries_positive_coefficients (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : ∀ i j, 0 < f.hessian i j) :
    f ∈ LorentzianPolynomials.P n 2 := by
  intro m hm
  obtain ⟨i, j, rfl⟩ := degree_two_exponent n m hm
  have h := hf i j
  by_cases hij : i = j
  · subst j
    simp only [LorentzianPolynomials.H.hessian, ite_true] at h
    rw [← Finsupp.single_add]
    norm_num at h ⊢
    linarith
  · simpa only [LorentzianPolynomials.H.hessian, ite_eq_right hij] using h
def mixingMatrix (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if i = j then 1 else 0) + t
noncomputable def quadraticMatrixApprox {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (mixingMatrix n t).transpose * A * mixingMatrix n t -
    (t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A i j) / 2) • 1
lemma quadraticMatrixApprox_continuous {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (quadraticMatrixApprox A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [quadraticMatrixApprox, mixingMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop
lemma quadraticMatrixApprox_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    quadraticMatrixApprox A 0 = A := by
  have hz : mixingMatrix n 0 = 1 := by ext i j; simp [mixingMatrix, Matrix.one_apply]
  simp [quadraticMatrixApprox, hz]
lemma quadraticMatrixApprox_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (t : ℝ) : (quadraticMatrixApprox A t).IsHermitian := by
  have hcong : ((mixingMatrix n t).transpose * A * mixingMatrix n t).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul (mixingMatrix n t) hA
  have hscalar : IsSelfAdjoint (t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A i j) / 2) := rfl
  exact hcong.sub (Matrix.isHermitian_one.smul hscalar)
lemma quadraticMatrixApprox_entries_positive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hS : 0 < ∑ i : Fin n, ∑ j : Fin n, A i j) (t : ℝ) (ht : 0 < t) :
    ∀ i j, 0 < quadraticMatrixApprox A t i j := by
  classical
  let B := mixingMatrix n t
  have hB : ∀ i j, t ≤ B i j := by
    intro i j
    dsimp [B, mixingMatrix]
    split_ifs <;> linarith
  have hBnonneg : ∀ i j, 0 ≤ B i j := fun i j => ht.le.trans (hB i j)
  have hbound : ∀ i j,
      t ^ 2 * (∑ k : Fin n, ∑ l : Fin n, A k l) ≤ (B.transpose * A * B) i j := by
    intro i j
    have hs : (∑ k : Fin n, ∑ l : Fin n, t ^ 2 * A l k) =
        t ^ 2 * (∑ k : Fin n, ∑ l : Fin n, A k l) := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [← hs]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro l _
    calc
      t ^ 2 * A l k = (t * A l k) * t := by ring
      _ ≤ (B l i * A l k) * B k j :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hB l i) (hA l k))
          (hB k j) ht.le (mul_nonneg (hBnonneg l i) (hA l k))
  intro i j
  have hb := hbound i j
  have hp : 0 < t ^ 2 * (∑ k : Fin n, ∑ l : Fin n, A k l) :=
    mul_pos (sq_pos_of_pos ht) hS
  by_cases hij : i = j
  · simp only [quadraticMatrixApprox, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, ite_eq_left hij, smul_eq_mul, mul_one]
    change 0 < (B.transpose * A * B) i j -
      t ^ 2 * (∑ k : Fin n, ∑ l : Fin n, A k l) / 2
    linarith
  · simp only [quadraticMatrixApprox, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, ite_eq_right hij, smul_eq_mul, mul_zero, sub_zero]
    exact hp.trans_le hb
lemma quadraticMatrixApprox_negative_hyperplane {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hS : 0 < ∑ i : Fin n, ∑ j : Fin n, A i j)
    (u : Fin n → ℝ)
    (hkernel : ∀ y : Fin n → ℝ, A.toBilin' u y = 0 → A.toBilin' y y ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      ((A.toBilin' u).comp (mixingMatrix n t).toLin') x = 0 →
        (quadraticMatrixApprox A t).toBilin' x x < 0 := by
  classical
  intro x hx hlx
  have hnonpos : A.toBilin' ((mixingMatrix n t).mulVec x)
      ((mixingMatrix n t).mulVec x) ≤ 0 := hkernel _ hlx
  have hnorm : 0 < dotProduct x x := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hi' : x i ≠ 0 := hi
    change 0 < ∑ j : Fin n, x j * x j
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi'⟩
  have hδ : 0 < t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A i j) / 2 :=
    div_pos (mul_pos (sq_pos_of_pos ht) hS) (by norm_num)
  have hcong : ((mixingMatrix n t).transpose * A * mixingMatrix n t).toBilin' x x =
      A.toBilin' ((mixingMatrix n t).mulVec x) ((mixingMatrix n t).mulVec x) := by
    rw [← Matrix.toBilin'_comp]
    rfl
  have heq : (quadraticMatrixApprox A t).toBilin' x x =
      A.toBilin' ((mixingMatrix n t).mulVec x) ((mixingMatrix n t).mulVec x) -
        (t ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A i j) / 2) * dotProduct x x := by
    rw [quadraticMatrixApprox, Matrix.toBilin'_apply', Matrix.sub_mulVec,
      dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      ← Matrix.toBilin'_apply', hcong]
    rfl
  rw [heq]
  exact sub_neg.mpr (lt_of_le_of_lt hnonpos (mul_pos hδ hnorm))
lemma positive_matrix_quadratic_strict {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j)
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hneg : ∀ x : Fin n → ℝ, x ≠ 0 → l x = 0 → A.toBilin' x x < 0) :
    quadraticFromMatrix n A ∈ LorentzianPolynomials.Ŀ n 2 := by
  have hAzero : A ≠ 0 := by
    intro hz
    have h := hpos ⟨0, hn⟩ ⟨0, hn⟩
    simp [hz] at h
  have hq : 0 < A.toBilin' (fun _ => 1) (fun _ => 1) := by
    rw [Matrix.toBilin'_apply']
    exact nonzero_nonnegative_matrix_positive_pairing n A hAzero
      (fun i j => (hpos i j).le) (fun _ => 1) (by intro i; norm_num)
  have hsig := matrix_strict_signature_of_negative_hyperplane A hA l hneg (fun _ => 1) hq
  have hh := quadraticFromMatrix_hessian n A hA.isSymm
  refine ⟨positive_hessian_entries_positive_coefficients n _ ?_, ?_⟩
  · intro i j
    rw [hh]
    exact hpos i j
  · change IsUnit (quadraticFromMatrix n A).hessian ∧ _
    rw [hh]
    exact hsig
lemma quadraticMatrixApprox_strict {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hcoeff : ∀ i j, 0 ≤ A i j) (hS : 0 < ∑ i : Fin n, ∑ j : Fin n, A i j)
    (u : Fin n → ℝ)
    (hkernel : ∀ y : Fin n → ℝ, A.toBilin' u y = 0 → A.toBilin' y y ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    quadraticFromMatrix n (quadraticMatrixApprox A t) ∈ LorentzianPolynomials.Ŀ n 2 := by
  let G := quadraticMatrixApprox A t
  have hG : G.IsHermitian := quadraticMatrixApprox_isHermitian A hA t
  have hpos : ∀ i j, 0 < G i j := quadraticMatrixApprox_entries_positive A hcoeff hS t ht
  exact positive_matrix_quadratic_strict hn G hG hpos
    ((A.toBilin' u).comp (mixingMatrix n t).toLin')
    (quadraticMatrixApprox_negative_hyperplane A hS u hkernel t ht)
theorem nonzero_lorentzian_subset_closure_strict_degree_two (n : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (hzero : f.1 ≠ 0) : f ∈ closure (LorentzianPolynomials.Ŀ n 2) := by
  have hA : f.hessian ≠ 0 :=
    fun h => hzero (forward_hessian_eq_zero_imp_polynomial_zero n f h)
  have hS : 0 < ∑ i : Fin n, ∑ j : Fin n, f.hessian i j := by
    simpa only [dotProduct, Matrix.mulVec, one_mul, mul_one] using
      nonzero_nonnegative_matrix_positive_pairing n f.hessian hA
        (forward_hessian_entries_nonnegative n f hf.2) (fun _ => 1) (by intro i; norm_num)
  let g : ℝ → LorentzianPolynomials.H n 2 :=
    fun t => quadraticFromMatrix n (quadraticMatrixApprox f.hessian t)
  have hcont : Continuous g :=
    (quadraticFromMatrix_continuous n).comp (quadraticMatrixApprox_continuous f.hessian)
  have hg₀ : g 0 = f := by
    dsimp [g]
    rw [quadraticMatrixApprox_zero, quadraticFromMatrix_hessian_self]
  have hlim : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds f) := by
    rw [← hg₀]
    exact (hcont.tendsto 0).mono_left inf_le_left
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact quadraticMatrixApprox_strict hn f.hessian (forward_hessian_isHermitian n f)
    (forward_hessian_entries_nonnegative n f hf.2) hS (fun _ => 1)
    (stable_quadratic_nonpositive_kernel n f hf (fun _ => 1) (by intro i; norm_num)) t ht
lemma positive_matrix_quadratic_strict_smul {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hpos : ∀ i j, 0 < A i j)
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hneg : ∀ x : Fin n → ℝ, x ≠ 0 → l x = 0 → A.toBilin' x x < 0)
    (t : ℝ) (ht : 0 < t) :
    quadraticFromMatrix n (t • A) ∈ LorentzianPolynomials.Ŀ n 2 := by
  apply positive_matrix_quadratic_strict hn (t • A) (hA.smul (show IsSelfAdjoint t from rfl))
    (fun i j => mul_pos ht (hpos i j)) l
  intro x hx hlx
  rw [Matrix.toBilin'_apply', Matrix.smul_mulVec, dotProduct_smul,
    ← Matrix.toBilin'_apply']
  exact mul_neg_of_pos_of_neg ht (hneg x hx hlx)
theorem zero_mem_closure_strict_degree_two (n : ℕ) (hn : 0 < n) :
    (⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ 2⟩ : LorentzianPolynomials.H n 2) ∈
      closure (LorentzianPolynomials.Ŀ n 2) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => 1)
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    rfl
  have hS : 0 < ∑ i : Fin n, ∑ j : Fin n, A i j := by
    dsimp [A]
    simp only [Matrix.of_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    exact mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)
  have hkernel : ∀ x : Fin n → ℝ, A.toBilin' (fun _ => 1) x = 0 →
      A.toBilin' x x ≤ 0 := by
    intro x hx
    have hsum : ∑ i : Fin n, x i = 0 := by
      have hx' : (n : ℝ) * (∑ i : Fin n, x i) = 0 := by
        simpa [Matrix.toBilin'_apply, A, ← Finset.mul_sum] using hx
      exact (mul_eq_zero.mp hx').resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    simp [Matrix.toBilin'_apply, A, ← Finset.mul_sum, hsum]
  let G := quadraticMatrixApprox A 1
  have hG : G.IsHermitian := quadraticMatrixApprox_isHermitian A hA 1
  have hpos : ∀ i j, 0 < G i j :=
    quadraticMatrixApprox_entries_positive A (by intro i j; exact zero_le_one) hS 1 zero_lt_one
  let l := (A.toBilin' (fun _ => 1)).comp (mixingMatrix n 1).toLin'
  have hneg : ∀ x : Fin n → ℝ, x ≠ 0 → l x = 0 → G.toBilin' x x < 0 :=
    quadraticMatrixApprox_negative_hyperplane A hS (fun _ => 1) hkernel 1 zero_lt_one
  let g : ℝ → LorentzianPolynomials.H n 2 := fun t => quadraticFromMatrix n (t • G)
  have hcont : Continuous g := (quadraticFromMatrix_continuous n).comp
    (continuous_id.smul continuous_const)
  have hg₀ : g 0 = ⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ 2⟩ := by
    apply Subtype.ext
    simp [g, quadraticFromMatrix]
  have hlim : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ 2⟩ : LorentzianPolynomials.H n 2)) := by
    rw [← hg₀]
    exact (hcont.tendsto 0).mono_left inf_le_left
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact positive_matrix_quadratic_strict_smul hn G hG hpos l hneg t ht
theorem lorentzian_subset_closure_strict_degree_two (n : ℕ) (hn : 0 < n) :
    LorentzianPolynomials.L n 2 ⊆ closure (LorentzianPolynomials.Ŀ n 2) := by
  intro f hf
  by_cases hz : f.1 = 0
  · have hfzero : f = ⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ 2⟩ := Subtype.ext hz
    rw [hfzero]
    exact zero_mem_closure_strict_degree_two n hn
  · exact nonzero_lorentzian_subset_closure_strict_degree_two n hn f hf hz
theorem lorentzian_subset_closure_strict_degree_zero (n : ℕ) :
    LorentzianPolynomials.L n 0 ⊆ closure (LorentzianPolynomials.Ŀ n 0) := by
  intro f hf
  exact nonnegative_subset_closure_positive n 0 hf.2
theorem lorentzian_subset_closure_strict_degree_one (n : ℕ) :
    LorentzianPolynomials.L n 1 ⊆ closure (LorentzianPolynomials.Ŀ n 1) := by
  intro f hf
  exact nonnegative_subset_closure_positive n 1 hf.2
theorem lorentzian_subset_closure_strict_degree_le_two (n d : ℕ) (hn : 0 < n)
    (hd : d ≤ 2) :
    LorentzianPolynomials.L n d ⊆ closure (LorentzianPolynomials.Ŀ n d) := by
  interval_cases d
  · exact lorentzian_subset_closure_strict_degree_zero n
  · exact lorentzian_subset_closure_strict_degree_one n
  · exact lorentzian_subset_closure_strict_degree_two n hn
def strictificationWeight {n : ℕ} (a : Fin n → ℕ) (m : Fin n →₀ ℕ) : ℕ :=
  ∑ i : Fin n, (m i ^ 2 + a i * m i)
noncomputable def coefficientStrictification (n d : ℕ) (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n d) : LorentzianPolynomials.H n d := by
  classical
  refine ⟨∑ m ∈ f.1.support,
    MvPolynomial.monomial m (t ^ strictificationWeight a m * f.1.coeff m), ?_⟩
  apply Submodule.sum_mem
  intro m hm
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact f.2 (MvPolynomial.mem_support_iff.mp hm)
lemma coefficientStrictification_coeff (n d : ℕ) (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n d) (m : Fin n →₀ ℕ) :
    (coefficientStrictification n d a t f).1.coeff m =
      t ^ strictificationWeight a m * f.1.coeff m := by
  classical
  simp only [coefficientStrictification, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  by_cases hm : m ∈ f.1.support
  · simp [hm]
  · simp [hm, MvPolynomial.notMem_support_iff.mp hm]
lemma strictificationWeight_add_single {n : ℕ}
    (a : Fin n → ℕ) (m : Fin n →₀ ℕ) (i : Fin n) :
    strictificationWeight a (m + Finsupp.single i 1) =
      strictificationWeight (fun k => a k + if k = i then 2 else 0) m + (a i + 1) := by
  classical
  unfold strictificationWeight
  have hterm : ∀ k : Fin n,
      (m + Finsupp.single i 1 : Fin n →₀ ℕ) k ^ 2 +
        a k * (m + Finsupp.single i 1 : Fin n →₀ ℕ) k =
        (m k ^ 2 + (a k + if k = i then 2 else 0) * m k) +
          if k = i then a i + 1 else 0 := by
    intro k
    by_cases hki : k = i
    · subst k
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ite_true]
      ring
    · simp [hki]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp
lemma coefficientStrictification_pderiv (n d : ℕ) (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n (d + 1)) (i : Fin n) :
    (coefficientStrictification n (d + 1) a t f).1.pderiv i =
      t ^ (a i + 1) •
        (coefficientStrictification n d (fun k => a k + if k = i then 2 else 0) t
          ⟨f.1.pderiv i, f.2.pderiv⟩).1 := by
  apply MvPolynomial.ext
  intro m
  erw [MvPolynomial.coeff_smul, smul_eq_mul,
    coefficientStrictification_coeff n d,
    MvPolynomial.coeff_pderiv, coefficientStrictification_coeff,
    MvPolynomial.coeff_pderiv, strictificationWeight_add_single, pow_add]
  ring
lemma coefficientStrictification_positive (n d : ℕ) (a : Fin n → ℕ) (t : ℝ)
    (ht : 0 < t) (f : LorentzianPolynomials.H n d)
    (hf : f ∈ LorentzianPolynomials.P n d) :
    coefficientStrictification n d a t f ∈ LorentzianPolynomials.P n d := by
  intro m hm
  rw [coefficientStrictification_coeff]
  exact mul_pos (pow_pos ht _) (hf m hm)
lemma coefficientStrictification_continuous (n d : ℕ) (a : Fin n → ℕ)
    (f : LorentzianPolynomials.H n d) :
    Continuous (fun t : ℝ => coefficientStrictification n d a t f) := by
  classical
  let V := MvPolynomial.homogeneousSubmodule (Fin n) ℝ d
  let : TopologicalSpace V := moduleTopology ℝ V
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ _
  let mon (m : Fin n →₀ ℕ) (hm : Finsupp.weight (1 : Fin n → ℕ) m = d) : ℝ →ₗ[ℝ] V :=
    { toFun := fun c => ⟨MvPolynomial.monomial m c,
        MvPolynomial.isHomogeneous_monomial c (by
          rw [Finsupp.degree_eq_weight_one]
          change Finsupp.weight (1 : Fin n → ℕ) m = d
          exact hm)⟩
      map_add' := by intro c b; apply Subtype.ext; simp
      map_smul' := by
        intro c b
        apply Subtype.ext
        apply MvPolynomial.ext
        intro k
        simp [MvPolynomial.coeff_monomial, mul_ite] }
  have hsum : Continuous (fun t : ℝ =>
      ∑ m ∈ f.1.support.attach, mon m.1 (f.2 (MvPolynomial.mem_support_iff.mp m.2))
        (t ^ strictificationWeight a m.1 * f.1.coeff m.1)) := by
    apply continuous_finsetSum
    intro m hm
    exact (IsModuleTopology.continuous_of_linearMap (mon m.1 (f.2 (MvPolynomial.mem_support_iff.mp m.2)))).comp
      ((continuous_id.pow _).mul continuous_const)
  have heq : (fun t : ℝ => coefficientStrictification n d a t f) =
      (fun t : ℝ => ∑ m ∈ f.1.support.attach,
        mon m.1 (f.2 (MvPolynomial.mem_support_iff.mp m.2))
          (t ^ strictificationWeight a m.1 * f.1.coeff m.1)) := by
    funext t
    apply Subtype.ext
    simp only [coefficientStrictification, Submodule.coe_sum, mon, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (Finset.sum_attach _ _).symm
  rw [heq]
  exact hsum
lemma coefficientStrictification_one (n d : ℕ) (a : Fin n → ℕ)
    (f : LorentzianPolynomials.H n d) : coefficientStrictification n d a 1 f = f := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro m
  rw [coefficientStrictification_coeff, one_pow, one_mul]
noncomputable def homogeneousScale (n d : ℕ) (c : ℝ)
    (f : LorentzianPolynomials.H n d) : LorentzianPolynomials.H n d :=
  ⟨c • f.1, (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d).smul_mem c f.2⟩
lemma homogeneousScale_positive (n d : ℕ) (c : ℝ) (hc : 0 < c)
    (f : LorentzianPolynomials.H n d) (hf : f ∈ LorentzianPolynomials.P n d) :
    homogeneousScale n d c f ∈ LorentzianPolynomials.P n d := by
  intro m hm
  exact mul_pos hc (hf m hm)
lemma strictificationWeight_single {n : ℕ} (a : Fin n → ℕ) (i : Fin n) (k : ℕ) :
    strictificationWeight a (Finsupp.single i k) = k ^ 2 + a i * k := by
  classical
  simp [strictificationWeight, Finsupp.single_apply, ite_pow, mul_ite,
    Finset.sum_add_distrib, eq_comm]
lemma coefficientStrictification_hessian_diagonal {n : ℕ} (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n 2) (i : Fin n) :
    (coefficientStrictification n 2 a t f).hessian i i =
      t ^ (4 + 2 * a i) * f.hessian i i := by
  simp only [LorentzianPolynomials.H.hessian, ite_true, coefficientStrictification_coeff,
    strictificationWeight_single]
  norm_num [mul_comm]
  ring
lemma coefficientStrictification_hessian_off_diagonal {n : ℕ} (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n 2) (i j : Fin n) (hij : i ≠ j) :
    (coefficientStrictification n 2 a t f).hessian i j =
      t ^ (2 + a i + a j) * f.hessian i j := by
  have hw : strictificationWeight a (Finsupp.single i 1 + Finsupp.single j 1) =
      2 + a i + a j := by
    rw [strictificationWeight_add_single, strictificationWeight_single]
    simp [hij]
    omega
  simp only [LorentzianPolynomials.H.hessian, ite_eq_right hij,
    coefficientStrictification_coeff, hw]
lemma coefficientStrictification_hessian_matrix {n : ℕ} (a : Fin n → ℕ) (t : ℝ)
    (f : LorentzianPolynomials.H n 2) :
    (coefficientStrictification n 2 a t f).hessian =
      (Matrix.diagonal (fun i => t ^ (a i + 1))) * f.hessian *
        (Matrix.diagonal (fun i => t ^ (a i + 1))) -
      Matrix.diagonal (fun i => (1 - t ^ 2) * (t ^ (a i + 1)) ^ 2 * f.hessian i i) := by
  classical
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    rw [coefficientStrictification_hessian_diagonal, Matrix.diagonal_apply_eq]
    have hp : 4 + 2 * a i = 2 + ((a i + 1) + (a i + 1)) := by omega
    rw [hp, pow_add, pow_add]
    ring
  · rw [coefficientStrictification_hessian_off_diagonal a t f i j hij,
      Matrix.diagonal_apply_ne _ hij]
    have hp : 2 + a i + a j = (a i + 1) + (a j + 1) := by omega
    rw [hp, pow_add]
    ring
lemma diagonal_congruence_sub_pos_negative_hyperplane {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (hkernel : ∀ y : Fin n → ℝ, A.toBilin' u y = 0 → A.toBilin' y y ≤ 0)
    (v e : Fin n → ℝ) (he : ∀ i, 0 < e i) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      ((A.toBilin' u).comp (Matrix.diagonal v).toLin') x = 0 →
      (Matrix.diagonal v * A * Matrix.diagonal v - Matrix.diagonal e).toBilin' x x < 0 := by
  classical
  intro x hx hlx
  have hnonpos : A.toBilin' ((Matrix.diagonal v).mulVec x)
      ((Matrix.diagonal v).mulVec x) ≤ 0 := hkernel _ hlx
  have hpos : 0 < ∑ i : Fin n, e i * x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => mul_nonneg (he j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (he i) (sq_pos_of_ne_zero hi)⟩
  have hcong : (Matrix.diagonal v * A * Matrix.diagonal v).toBilin' x x =
      A.toBilin' ((Matrix.diagonal v).mulVec x) ((Matrix.diagonal v).mulVec x) := by
    have htrans : (Matrix.diagonal v).transpose = Matrix.diagonal v :=
      Matrix.diagonal_transpose v
    calc
      _ = ((Matrix.diagonal v).transpose * A * Matrix.diagonal v).toBilin' x x := by
        rw [htrans]
      _ = _ := by
        rw [← Matrix.toBilin'_comp]
        rfl
  have hdiag : (Matrix.diagonal e).toBilin' x x = ∑ i : Fin n, e i * x i ^ 2 := by
    simp only [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heq : (Matrix.diagonal v * A * Matrix.diagonal v - Matrix.diagonal e).toBilin' x x =
      (Matrix.diagonal v * A * Matrix.diagonal v).toBilin' x x -
        (Matrix.diagonal e).toBilin' x x := by
    simp only [Matrix.toBilin'_apply', Matrix.sub_mulVec, dotProduct_sub]
  rw [heq, hcong, hdiag]
  linarith
lemma coefficientStrictification_negative_hyperplane {n : ℕ}
    (a : Fin n → ℕ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (hp : f ∈ LorentzianPolynomials.P n 2) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      ((f.hessian.toBilin' (fun _ => 1)).comp
        (Matrix.diagonal (fun i => t ^ (a i + 1))).toLin') x = 0 →
      (coefficientStrictification n 2 a t f).hessian.toBilin' x x < 0 := by
  rw [coefficientStrictification_hessian_matrix]
  apply diagonal_congruence_sub_pos_negative_hyperplane f.hessian (fun _ => 1)
    (stable_quadratic_nonpositive_kernel n f hf (fun _ => 1) (by intro i; norm_num))
  intro i
  have hpos : 0 < f.hessian i i := by
    simp only [LorentzianPolynomials.H.hessian, ite_true]
    exact mul_pos (by norm_num) (hp _ (by simp [Finsupp.weight_single]))
  exact mul_pos (mul_pos (by nlinarith : 0 < 1 - t ^ 2)
    (sq_pos_of_pos (pow_pos ht _))) hpos
lemma homogeneousScale_hessian {n : ℕ} (c : ℝ) (f : LorentzianPolynomials.H n 2) :
    (homogeneousScale n 2 c f).hessian = c • f.hessian := by
  classical
  ext i j
  by_cases hij : i = j <;>
    simp [LorentzianPolynomials.H.hessian, homogeneousScale, hij, mul_left_comm]
lemma coefficientStrictification_scaled_strict_degree_two (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℕ) (t c : ℝ) (ht : 0 < t) (ht1 : t < 1) (hc : 0 < c)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (hp : f ∈ LorentzianPolynomials.P n 2) :
    homogeneousScale n 2 c (coefficientStrictification n 2 a t f) ∈
      LorentzianPolynomials.Ŀ n 2 := by
  let g := coefficientStrictification n 2 a t f
  have hg : g ∈ LorentzianPolynomials.P n 2 := coefficientStrictification_positive n 2 a t ht f hp
  have hpos : ∀ i j, 0 < g.hessian i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [LorentzianPolynomials.H.hessian, ite_true]
      exact mul_pos (by norm_num) (hg _ (by simp [Finsupp.weight_single]))
    · simpa only [LorentzianPolynomials.H.hessian, ite_eq_right hij] using
        hg (Finsupp.single i 1 + Finsupp.single j 1) (by simp [Finsupp.weight_single])
  have hstrict := positive_matrix_quadratic_strict_smul hn g.hessian
    (forward_hessian_isHermitian n g) hpos
    ((f.hessian.toBilin' (fun _ => 1)).comp
      (Matrix.diagonal (fun i => t ^ (a i + 1))).toLin')
    (coefficientStrictification_negative_hyperplane a t ht ht1 f hf hp) c hc
  have heq : quadraticFromMatrix n (c • g.hessian) = homogeneousScale n 2 c g := by
    rw [← homogeneousScale_hessian, quadraticFromMatrix_hessian_self]
  rw [heq] at hstrict
  exact hstrict
lemma positive_pderiv (n d : ℕ) (f : LorentzianPolynomials.H n (d + 1))
    (hf : f ∈ LorentzianPolynomials.P n (d + 1)) (i : Fin n) :
    (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n d) ∈ LorentzianPolynomials.P n d := by
  intro m hm
  change 0 < (f.1.pderiv i).coeff m
  rw [MvPolynomial.coeff_pderiv]
  exact mul_pos (hf _ (by simp [map_add, Finsupp.weight_single, hm])) (by positivity)
lemma coefficientStrictification_scaled_strict (n d : ℕ) (hn : 0 < n)
    (a : Fin n → ℕ) (t c : ℝ) (ht : 0 < t) (ht1 : t < 1) (hc : 0 < c)
    (f : LorentzianPolynomials.H n d) (hf : f ∈ LorentzianPolynomials.L n d)
    (hp : f ∈ LorentzianPolynomials.P n d) :
    homogeneousScale n d c (coefficientStrictification n d a t f) ∈
      LorentzianPolynomials.Ŀ n d := by
  induction d using Nat.strong_induction_on generalizing a c with
  | h d ih =>
    match d with
    | 0 =>
      exact homogeneousScale_positive n 0 c hc _
        (coefficientStrictification_positive n 0 a t ht f hp)
    | 1 =>
      exact homogeneousScale_positive n 1 c hc _
        (coefficientStrictification_positive n 1 a t ht f hp)
    | 2 => exact coefficientStrictification_scaled_strict_degree_two n hn a t c ht ht1 hc f hf hp
    | d + 3 =>
      refine ⟨homogeneousScale_positive n (d + 3) c hc _
        (coefficientStrictification_positive n (d + 3) a t ht f hp), ?_⟩
      intro i
      have hderiv := ih (d + 2) (by omega)
        (fun k => a k + if k = i then 2 else 0) (c * t ^ (a i + 1))
        (mul_pos hc (pow_pos ht _))
        (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n (d + 2))
        (hf.2 i) (positive_pderiv n (d + 2) f hp i)
      have heq : (⟨(homogeneousScale n (d + 3) c
          (coefficientStrictification n (d + 3) a t f)).1.pderiv i,
          (homogeneousScale n (d + 3) c (coefficientStrictification n (d + 3) a t f)).2.pderiv⟩ :
          LorentzianPolynomials.H n (d + 2)) =
          homogeneousScale n (d + 2) (c * t ^ (a i + 1))
            (coefficientStrictification n (d + 2) (fun k => a k + if k = i then 2 else 0) t
              ⟨f.1.pderiv i, f.2.pderiv⟩) := by
        apply Subtype.ext
        change (c • (coefficientStrictification n (d + 3) a t f).1).pderiv i = _
        rw [(MvPolynomial.pderiv i).map_smul, coefficientStrictification_pderiv]
        exact smul_smul c (t ^ (a i + 1)) _
      rw [heq]
      exact hderiv
lemma positive_lorentzian_subset_closure_strict (n d : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n d) (hf : f ∈ LorentzianPolynomials.L n d)
    (hp : f ∈ LorentzianPolynomials.P n d) :
    f ∈ closure (LorentzianPolynomials.Ŀ n d) := by
  let g : ℝ → LorentzianPolynomials.H n d := fun t =>
    coefficientStrictification n d (fun _ => 0) t f
  have hlim : Filter.Tendsto g (nhdsWithin 1 (Set.Iio 1)) (nhds f) := by
    have h := ((coefficientStrictification_continuous n d (fun _ => 0) f).tendsto 1).mono_left
      (show nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds 1 from inf_le_left)
    simpa only [coefficientStrictification_one] using h
  apply mem_closure_of_tendsto hlim
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < t :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hpos] with t ht htpos
  have hs := coefficientStrictification_scaled_strict n d hn (fun _ => 0) t 1
    htpos ht (by norm_num) f hf hp
  change homogeneousScale n d 1 (g t) ∈ LorentzianPolynomials.Ŀ n d at hs
  have heq : homogeneousScale n d 1 (g t) = g t := by
    apply Subtype.ext
    exact one_smul ℝ (g t).1
  rwa [heq] at hs
lemma positive_support_isMConvex (n d : ℕ) (f : LorentzianPolynomials.H n d)
    (hf : f ∈ LorentzianPolynomials.P n d) :
    LorentzianPolynomials.IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) := by
  intro α hα β hβ i hi
  have hαw := f.2 (MvPolynomial.mem_support_iff.mp hα)
  have hβw := f.2 (MvPolynomial.mem_support_iff.mp hβ)
  obtain ⟨j, hj⟩ : ∃ j, α j < β j := by
    by_contra! h
    have hsum : ∑ k : Fin n, β k < ∑ k : Fin n, α k := by
      exact Finset.sum_lt_sum (fun k _ => h k) ⟨i, Finset.mem_univ i, hi⟩
    have hwα := exchange_weight_sum α
    have hwβ := exchange_weight_sum β
    change Finsupp.weight (1 : Fin n → ℕ) α = d at hαw
    change Finsupp.weight (1 : Fin n → ℕ) β = d at hβw
    omega
  refine ⟨j, hj, MvPolynomial.mem_support_iff.mpr (ne_of_gt (hf _ ?_))⟩
  exact (exchange_weight_move α i j (by omega)).trans hαw
noncomputable def rankOneSeed (n d : ℕ) (c : ℝ) : LorentzianPolynomials.H n d := by
  classical
  refine ⟨c • (∑ i : Fin n, MvPolynomial.X i) ^ d, ?_⟩
  apply (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d).smul_mem
  have hhom : MvPolynomial.IsHomogeneous (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) 1 := by
    change (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin n) ℝ 1
    apply Submodule.sum_mem
    intro i _
    exact MvPolynomial.isHomogeneous_X ℝ i
  change MvPolynomial.IsHomogeneous _ d
  simpa only [one_mul] using hhom.pow d
lemma rankOneSeed_positive (n d : ℕ) (c : ℝ) (hc : 0 < c) :
    rankOneSeed n d c ∈ LorentzianPolynomials.P n d := by
  intro m hm
  change 0 < (c • (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) ^ d).coeff m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_sum_X_pow_of_fintype]
  have hw : m.sum (fun _ k => k) = d := by
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using hm
  rw [ite_eq_left hw]
  exact mul_pos hc (by exact_mod_cast (Nat.multinomial_pos m.support m))
lemma rankOneSeed_stable (n d : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 < c) :
    LorentzianPolynomials.IsStable (rankOneSeed n d c).1 := by
  classical
  right
  intro z
  change (MvPolynomial.aeval (fun i : Fin n => (z i : ℂ))
    (c • (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)) ^ d) : ℂ) ≠ 0
  rw [Algebra.smul_def, map_mul, map_pow, map_sum]
  rw [(MvPolynomial.aeval (fun i : Fin n => (z i : ℂ))).commutes c]
  simp only [MvPolynomial.aeval_X]
  change (c : ℂ) * (∑ i : Fin n, (z i : ℂ)) ^ d ≠ 0
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hc
  · apply pow_ne_zero
    have him : 0 < (∑ i : Fin n, (z i : ℂ)).im := by
      rw [Complex.im_sum]
      exact Finset.sum_pos (fun i _ => (z i).im_pos) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    intro hz
    simp [hz] at him
lemma rankOneSeed_pderiv (n d : ℕ) (c : ℝ) (i : Fin n) :
    (rankOneSeed n (d + 1) c).1.pderiv i = (rankOneSeed n d (c * (d + 1))).1 := by
  classical
  change (c • (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) ^ (d + 1)).pderiv i = _
  rw [(MvPolynomial.pderiv i).map_smul, MvPolynomial.pderiv_pow]
  have hder : (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)).pderiv i = 1 := by
    change (MvPolynomial.pderiv i).toLinearMap (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) = 1
    rw [map_sum]
    simp [MvPolynomial.pderiv_X]
  rw [hder, mul_one, Nat.add_sub_cancel]
  change c • (↑(d + 1) * (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) ^ d) =
    (c * (d + 1)) • (∑ j : Fin n, (MvPolynomial.X j : MvPolynomial (Fin n) ℝ)) ^ d
  simp [Algebra.smul_def, map_mul, mul_assoc]
lemma rankOneSeed_mem_lorentzian (n d : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 < c) :
    rankOneSeed n d c ∈ LorentzianPolynomials.L n d := by
  induction d using Nat.strong_induction_on generalizing c with
  | h d ih =>
    have hp := rankOneSeed_positive n d c hc
    have hnn := positive_coefficients_nonnegative n d hp
    match d with
    | 0 => exact ⟨rankOneSeed_stable n 0 hn c hc, hnn⟩
    | 1 => exact ⟨rankOneSeed_stable n 1 hn c hc, hnn⟩
    | 2 => exact ⟨rankOneSeed_stable n 2 hn c hc, hnn⟩
    | d + 3 =>
      refine ⟨⟨positive_support_isMConvex n (d + 3) _ hp, hnn⟩, ?_⟩
      intro i
      have hderiv := ih (d + 2) (by omega) (c * ((d + 2 : ℕ) + 1))
        (mul_pos hc (by positivity))
      have heq : (⟨(rankOneSeed n (d + 3) c).1.pderiv i,
          (rankOneSeed n (d + 3) c).2.pderiv⟩ : LorentzianPolynomials.H n (d + 2)) =
          rankOneSeed n (d + 2) (c * ((d + 2 : ℕ) + 1)) := by
        apply Subtype.ext
        exact rankOneSeed_pderiv n (d + 2) c i
      rwa [heq]
lemma zero_mem_closure_strict (n d : ℕ) (hn : 0 < n) :
    (⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ d⟩ : LorentzianPolynomials.H n d) ∈
      closure (LorentzianPolynomials.Ŀ n d) := by
  let V := MvPolynomial.homogeneousSubmodule (Fin n) ℝ d
  let : TopologicalSpace V := moduleTopology ℝ V
  let p := rankOneSeed n d 1
  let q := coefficientStrictification n d (fun _ => 0) (1 / 2) p
  let g : ℝ → V := fun c => c • (show V from q)
  have hcont : Continuous g := continuous_id.smul continuous_const
  have hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0))
      (nhds (0 : V)) := by
    have h := (hcont.tendsto 0).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
    have heq : g 0 = (0 : V) := by
      apply Subtype.ext
      exact zero_smul ℝ q.1
    rwa [heq] at h
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with c hc
  change homogeneousScale n d c q ∈ LorentzianPolynomials.Ŀ n d
  exact coefficientStrictification_scaled_strict n d hn (fun _ => 0) (1 / 2) c
    (by norm_num) (by norm_num) hc p
    (rankOneSeed_mem_lorentzian n d hn 1 (by norm_num))
    (rankOneSeed_positive n d 1 (by norm_num))
lemma lorentzian_coefficients_nonnegative (n d : ℕ)
    (f : LorentzianPolynomials.H n d) (hf : f ∈ LorentzianPolynomials.L n d) :
    ∀ m, 0 ≤ f.1.coeff m := by
  match d with
  | 0 => exact hf.2
  | 1 => exact hf.2
  | 2 => exact hf.2
  | d + 3 => exact hf.1.2
lemma lorentzian_subset_closure_strict_one_variable (d : ℕ) :
    LorentzianPolynomials.L 1 d ⊆ closure (LorentzianPolynomials.Ŀ 1 d) := by
  intro f hf
  by_cases hz : f.1 = 0
  · have heq : f = ⟨0, MvPolynomial.isHomogeneous_zero (Fin 1) ℝ d⟩ := Subtype.ext hz
    rw [heq]
    exact zero_mem_closure_strict 1 d (by norm_num)
  have hnn := lorentzian_coefficients_nonnegative 1 d f hf
  have hcoeff : f.1.coeff (Finsupp.single (0 : Fin 1) d) ≠ 0 := by
    intro h
    apply hz
    rw [one_variable_homogeneous_eq_monomial d f, h]
    simp
  apply positive_lorentzian_subset_closure_strict 1 d (by norm_num) f hf
  intro m hm
  rw [one_variable_exponent d m hm]
  exact lt_of_le_of_ne (hnn _) (Ne.symm hcoeff)
lemma closure_positive_lorentzian_subset_closure_strict (n d : ℕ) (hn : 0 < n) :
    closure (LorentzianPolynomials.L n d ∩ LorentzianPolynomials.P n d) ⊆
      closure (LorentzianPolynomials.Ŀ n d) := by
  apply closure_minimal
  · intro f hf
    exact positive_lorentzian_subset_closure_strict n d hn f hf.1 hf.2
  · exact isClosed_closure
lemma closure_positive_lorentzian_eq_closure_strict (n d : ℕ) (hn : 0 < n) :
    closure (LorentzianPolynomials.L n d ∩ LorentzianPolynomials.P n d) =
      closure (LorentzianPolynomials.Ŀ n d) := by
  apply Set.Subset.antisymm (closure_positive_lorentzian_subset_closure_strict n d hn)
  apply closure_mono
  intro f hf
  exact ⟨closure_strict_subset_lorentzian n d hn (subset_closure hf),
    strict_subset_positive n d hf⟩
lemma mixing_coeff_one_nonneg {n : ℕ} (m : Fin n →₀ ℕ) :
    0 ≤ (1 : MvPolynomial (Fin n) ℝ).coeff m := by
  classical
  simp only [MvPolynomial.coeff_one]
  split_ifs <;> norm_num
lemma mixing_coeff_mul_comparison {n : ℕ}
    {p q r s : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hr : ∀ m, 0 ≤ r.coeff m)
    (hpq : ∀ m, p.coeff m ≤ q.coeff m)
    (hrs : ∀ m, r.coeff m ≤ s.coeff m) :
    (∀ m, 0 ≤ (p * r).coeff m) ∧
      ∀ m, (p * r).coeff m ≤ (q * s).coeff m := by
  classical
  constructor
  · intro m
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hr _)
  · intro m
    rw [MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
    exact Finset.sum_le_sum fun x _ =>
      mul_le_mul (hpq _) (hrs _) (hr _) ((hp _).trans (hpq _))
lemma mixing_coeff_pow_comparison {n : ℕ}
    {p q : MvPolynomial (Fin n) ℝ}
    (hp : ∀ m, 0 ≤ p.coeff m) (hpq : ∀ m, p.coeff m ≤ q.coeff m)
    (k : ℕ) : (∀ m, 0 ≤ (p ^ k).coeff m) ∧
      ∀ m, (p ^ k).coeff m ≤ (q ^ k).coeff m := by
  induction k with
  | zero => simp only [pow_zero]; exact ⟨mixing_coeff_one_nonneg, fun _ => le_rfl⟩
  | succ k ih =>
    simpa only [pow_succ] using mixing_coeff_mul_comparison ih.1 hp ih.2 hpq
lemma mixing_coeff_prod_comparison {n : ℕ} {I : Type*}
    (S : Finset I) (p q : I → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i ∈ S, ∀ m, 0 ≤ (p i).coeff m)
    (hpq : ∀ i ∈ S, ∀ m, (p i).coeff m ≤ (q i).coeff m) :
    (∀ m, 0 ≤ (∏ i ∈ S, p i).coeff m) ∧
      ∀ m, (∏ i ∈ S, p i).coeff m ≤ (∏ i ∈ S, q i).coeff m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨mixing_coeff_one_nonneg, fun _ => le_rfl⟩
  | @insert i S hi ih =>
    obtain ⟨h0, hle⟩ := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hpq j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using
      mixing_coeff_mul_comparison (hp i (Finset.mem_insert_self _ _)) h0
        (hpq i (Finset.mem_insert_self _ _)) hle
lemma mixing_parameter_evaluation_continuous (n d : ℕ)
    (P : MvPolynomial (Fin n) (Polynomial ℝ)) (hP : P.IsHomogeneous d) :
    Continuous (Y := LorentzianPolynomials.H n d) (fun t : ℝ =>
      (⟨MvPolynomial.map (Polynomial.evalRingHom t) P,
        hP.map (Polynomial.evalRingHom t)⟩ : LorentzianPolynomials.H n d)) := by
  classical
  let : TopologicalSpace (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) :=
    moduleTopology ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d)
  let : ContinuousAdd (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d) :=
    IsModuleTopology.toContinuousAdd ℝ _
  change Continuous (fun t : ℝ =>
    (⟨MvPolynomial.map (Polynomial.evalRingHom t) P,
      hP.map (Polynomial.evalRingHom t)⟩ : MvPolynomial.homogeneousSubmodule (Fin n) ℝ d))
  let v : (Fin n →₀ ℕ) → MvPolynomial.homogeneousSubmodule (Fin n) ℝ d :=
    fun m => if hm : Finsupp.degree m = d then
      ⟨MvPolynomial.monomial m 1, MvPolynomial.isHomogeneous_monomial 1 hm⟩ else 0
  have heq : (fun t : ℝ =>
      (⟨MvPolynomial.map (Polynomial.evalRingHom t) P,
        hP.map (Polynomial.evalRingHom t)⟩ : MvPolynomial.homogeneousSubmodule (Fin n) ℝ d)) =
      fun t => ∑ m ∈ P.support, (P.coeff m).eval t • v m := by
    funext t
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmd : Finsupp.degree m = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hP (MvPolynomial.mem_support_iff.mp hm)
    simp [v, hmd, MvPolynomial.smul_monomial]
  rw [heq]
  exact continuous_finsetSum _ fun m _ => (P.coeff m).continuous.smul continuous_const
lemma mixing_sum_variables_nonnegative (n : ℕ) (m : Fin n →₀ ℕ) :
    0 ≤ (∑ i : Fin n, MvPolynomial.X (R := ℝ) i).coeff m := by
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro i _
  simp only [MvPolynomial.coeff_X]
  split_ifs <;> norm_num
lemma mixing_monomial_lower_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (α : Fin n →₀ ℕ) :
    (∀ m, 0 ≤ ((MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j) ^
      (α.sum fun _ k => k)).coeff m) ∧
    ∀ m, ((MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j) ^
      (α.sum fun _ k => k)).coeff m ≤
        (α.prod fun i k => (MvPolynomial.X i +
          MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j) ^ k).coeff m := by
  classical
  let B : MvPolynomial (Fin n) ℝ := MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j
  have hB : ∀ m, 0 ≤ B.coeff m := by
    intro m
    simpa only [B, MvPolynomial.coeff_C_mul] using
      mul_nonneg ht (mixing_sum_variables_nonnegative n m)
  have hbase : ∀ i : Fin n, ∀ m, B.coeff m ≤ (MvPolynomial.X i + B).coeff m := by
    intro i m
    simp only [AddMonoidAlgebra.coeff_add, Pi.add_apply]
    apply le_add_of_nonneg_left
    simp only [MvPolynomial.coeff_X]
    split_ifs <;> norm_num
  have h := mixing_coeff_prod_comparison α.support
    (fun i => B ^ α i) (fun i => (MvPolynomial.X i + B) ^ α i)
    (fun i _ => (mixing_coeff_pow_comparison hB (hbase i) (α i)).1)
    (fun i _ => (mixing_coeff_pow_comparison hB (hbase i) (α i)).2)
  simpa only [Finset.prod_pow_eq_pow_sum, Finsupp.sum, Finsupp.prod, B] using h
lemma mixing_sum_power_coeff_pos (n d : ℕ) (t : ℝ) (ht : 0 < t)
    (m : Fin n →₀ ℕ) (hm : Finsupp.weight 1 m = d) :
    0 < ((MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j) ^ d).coeff m := by
  classical
  have hmd : m.sum (fun _ k => k) = d := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using hm
  rw [mul_pow, ← map_pow, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hmd]
  exact mul_pos (pow_pos ht _) (Nat.cast_pos.mpr (Nat.multinomial_pos _ _))
lemma mixing_aeval_coeff_positive (n d : ℕ)
    (f : LorentzianPolynomials.H n d) (hf : f.1 ≠ 0)
    (hc : ∀ m, 0 ≤ f.1.coeff m) (t : ℝ) (ht : 0 < t) :
    ∀ m : Fin n →₀ ℕ, Finsupp.weight 1 m = d →
      0 < (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i +
        MvPolynomial.C t * ∑ j : Fin n, MvPolynomial.X j) f.1).coeff m := by
  classical
  intro m hm
  obtain ⟨α, hα⟩ := MvPolynomial.exists_coeff_ne_zero hf
  have hαs : α ∈ f.1.support := MvPolynomial.mem_support_iff.mpr hα
  have hαd : α.sum (fun _ k => k) = d := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using f.2 hα
  have hproduct : ∀ β : Fin n →₀ ℕ, 0 ≤
      (β.prod fun i k => (MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) ^ k).coeff m := by
    intro β
    obtain ⟨h0, hle⟩ := mixing_monomial_lower_bound n t ht.le β
    exact (h0 m).trans (hle m)
  conv => rhs; rw [f.1.as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun β _ => mul_nonneg (hc β) (hproduct β)) hαs)
  apply mul_pos (lt_of_le_of_ne (hc α) (Ne.symm hα))
  have hbound := (mixing_monomial_lower_bound n t ht.le α).2 m
  rw [hαd] at hbound
  exact (mixing_sum_power_coeff_pos n d t ht m hm).trans_le hbound
theorem positive_variable_mixing_curve :
    ∀ (n d : ℕ), 0 < n → ∀ f : LorentzianPolynomials.H n d,
    f.1 ≠ 0 → (∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m) →
    ∃ mix : ℝ → LorentzianPolynomials.H n d,
      Continuous mix ∧ mix 0 = f ∧
      (∀ t : ℝ, (mix t).1 = MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
          ∑ j : Fin n, MvPolynomial.X j) f.1) ∧
      ∀ t : ℝ, 0 < t → mix t ∈ LorentzianPolynomials.P n d := by
  classical
  intro n d hn f hf hc
  let φ : Fin n → MvPolynomial (Fin n) (Polynomial ℝ) :=
    fun i => MvPolynomial.X i + MvPolynomial.C Polynomial.X *
      ∑ j : Fin n, MvPolynomial.X j
  let P : MvPolynomial (Fin n) (Polynomial ℝ) := MvPolynomial.aeval φ f.1
  have hP : P.IsHomogeneous d := by
    simpa only [one_mul] using f.2.aeval φ (fun i =>
      (MvPolynomial.isHomogeneous_X _ i).add
        ((MvPolynomial.IsHomogeneous.sum Finset.univ
          (fun j : Fin n => MvPolynomial.X j) 1
          (fun j _ => MvPolynomial.isHomogeneous_X _ j)).C_mul Polynomial.X))
  let mix : ℝ → LorentzianPolynomials.H n d := fun t =>
    ⟨MvPolynomial.map (Polynomial.evalRingHom t) P,
      hP.map (Polynomial.evalRingHom t)⟩
  have hmix : ∀ t : ℝ, (mix t).1 = MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) f.1 := by
    intro t
    change MvPolynomial.map (Polynomial.evalRingHom t) (MvPolynomial.aeval φ f.1) = _
    exact (MvPolynomial.comp_aeval_apply φ
      (MvPolynomial.mapAlgHom (Polynomial.aeval t : Polynomial ℝ →ₐ[ℝ] ℝ)) f.1).trans (by
        apply congrArg (fun u : Fin n → MvPolynomial (Fin n) ℝ => MvPolynomial.aeval u f.1)
        funext i
        simp [φ])
  refine ⟨mix, mixing_parameter_evaluation_continuous n d P hP, ?_, hmix, ?_⟩
  · apply Subtype.ext
    rw [hmix]
    simp
  · intro t ht
    change ∀ m : Fin n →₀ ℕ, Finsupp.weight 1 m = d → 0 < (mix t).1.coeff m
    rw [hmix]
    exact mixing_aeval_coeff_positive n d f hf hc t ht
theorem directional_matrix_eigenvalue_abs_le_one (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hA : ∀ i j, 0 ≤ A i j) (hAu : A.mulVec u = u)
    (v : Fin n → ℝ) (hv : v ≠ 0) (r : ℝ) (hr : A.mulVec v = r • v) :
    |r| ≤ 1 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin n => |v j| / u j) ⟨k, Finset.mem_univ _⟩
  have hbound (j : Fin n) : |v j| ≤ (|v i| / u i) * u j :=
    (div_le_iff₀ (hu j)).mp (hmax j (Finset.mem_univ _))
  have hvi : 0 < |v i| := by
    by_contra! hz
    have heq : |v i| = 0 := le_antisymm hz (abs_nonneg _)
    have hb := hbound k
    rw [heq, zero_div, zero_mul] at hb
    exact hk (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  have hrow : ∑ j : Fin n, A i j * u j = u i := congrFun hAu i
  have heig : ∑ j : Fin n, A i j * v j = r * v i := congrFun hr i
  have hle : |r| * |v i| ≤ |v i| := by
    calc
      |r| * |v i| = |∑ j : Fin n, A i j * v j| := by rw [heig, abs_mul]
      _ ≤ ∑ j : Fin n, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, A i j * |v j| := by
        simp only [abs_mul, abs_of_nonneg (hA i _)]
      _ ≤ ∑ j : Fin n, A i j * ((|v i| / u i) * u j) :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hbound j) (hA i j)
      _ = (|v i| / u i) * u i := by
        rw [← hrow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = |v i| := div_mul_cancel₀ _ (ne_of_gt (hu i))
  nlinarith
theorem directional_matrix_fixed_space (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hA : ∀ i j, 0 ≤ A i j) (hAu : A.mulVec u = u)
    (hconnect : ∀ s : Finset (Fin n), s.Nonempty →
      (∃ j : Fin n, j ∉ s) → ∃ i ∈ s, ∃ j ∉ s, 0 < A i j)
    (v : Fin n → ℝ) (hv : A.mulVec v = v) :
    ∃ c : ℝ, v = c • u := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin n => v j / u j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let c : ℝ := v i / u i
  have hbound (j : Fin n) : v j ≤ c * u j :=
    (div_le_iff₀ (hu j)).mp (hmax j (Finset.mem_univ _))
  let s := Finset.univ.filter (fun j : Fin n => v j = c * u j)
  have hi' : i ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (div_mul_cancel₀ _ (ne_of_gt (hu i))).symm
  have hall : ∀ j : Fin n, j ∈ s := by
    by_contra! hnot
    obtain ⟨k, hks, j, hjs, hkj⟩ := hconnect s ⟨i, hi'⟩ hnot
    have hk : v k = c * u k := (Finset.mem_filter.mp hks).2
    have hsum : (∑ l : Fin n, A k l * (c * u l - v l)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have hu' : (∑ l : Fin n, A k l * (c * u l)) = c * u k := by
        calc
          _ = c * (∑ l : Fin n, A k l * u l) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l hl
            ring
          _ = c * u k := by rw [show (∑ l : Fin n, A k l * u l) = u k from congrFun hAu k]
      rw [hu', show (∑ l : Fin n, A k l * v l) = v k from congrFun hv k, hk, sub_self]
    have hzero : A k j * (c * u j - v j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun l hl => mul_nonneg (hA k l) (sub_nonneg.mpr (hbound l)))).mp hsum
        j (Finset.mem_univ _)
    have hj : v j = c * u j := by
      have := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hkj)
      linarith
    exact hjs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  refine ⟨c, ?_⟩
  ext j
  exact (Finset.mem_filter.mp (hall j)).2
theorem directional_matrix_nonpositive_kernel (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (u : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (hnonneg : ∀ i j, 0 ≤ A i j) (hAu : A.mulVec u = u)
    (hconnect : ∀ s : Finset (Fin n), s.Nonempty →
      (∃ j : Fin n, j ∉ s) → ∃ i ∈ s, ∃ j ∉ s, 0 < A i j)
    (hsquare : ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) ≤ dotProduct (A.mulVec x) (A.mulVec x)) :
    ∀ x : Fin n → ℝ, dotProduct u x = 0 → dotProduct x (A.mulVec x) ≤ 0 := by
  classical
  have hpositive (k : Fin n) (hk : 0 < hA.eigenvalues k) :
      hA.eigenvalues k = 1 := by
    let v : Fin n → ℝ := (hA.eigenvectorBasis k).ofLp
    have heig : A.mulVec v = hA.eigenvalues k • v := hA.mulVec_eigenvectorBasis k
    have hval : hA.eigenvalues k = dotProduct v (A.mulVec v) := by
      simpa only [star_trivial, RCLike.re_to_real] using hA.eigenvalues_eq k
    have hv : v ≠ 0 := by
      intro hz
      rw [hz] at hval
      simp only [zero_dotProduct] at hval
      linarith
    have hupper := le_trans (le_abs_self (hA.eigenvalues k))
      (directional_matrix_eigenvalue_abs_le_one n A u hu hnonneg hAu v hv _ heig)
    have hnorm : dotProduct v v = 1 := by
      rw [heig, dotProduct_smul, smul_eq_mul] at hval
      nlinarith
    have hsq := hsquare v
    rw [heig, dotProduct_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hnorm, mul_one] at hsq
    simp only [smul_eq_mul] at hsq
    nlinarith
  intro x hx
  rw [← Matrix.toBilin'_apply']
  rw [exchange_spectral_expansion A hA x]
  apply Finset.sum_nonpos
  intro k hk
  by_cases hpos : 0 < hA.eigenvalues k
  · have heig : A.mulVec (hA.eigenvectorBasis k).ofLp = (hA.eigenvectorBasis k).ofLp := by
      rw [hA.mulVec_eigenvectorBasis, hpositive k hpos, one_smul]
    obtain ⟨c, hc⟩ := directional_matrix_fixed_space n hn A u hu hnonneg hAu
      hconnect (hA.eigenvectorBasis k).ofLp heig
    have hz : ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec x) k = 0 := by
      change dotProduct ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose k) x = 0
      rw [hA.eigenvectorUnitary_transpose_apply, hc, smul_dotProduct, hx, smul_zero]
    simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos) (sq_nonneg _)
theorem directional_matrix_local_square (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (a u r : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i)
    (hu : ∀ i, u i = a i * r i) (hAu : A.mulVec u = u)
    (hdecomp : ∀ j k, A j k = ∑ i : Fin n, a i * B i j k)
    (hrow : ∀ i, (B i).mulVec u = r i • A i)
    (hdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((B i).mulVec x) * dotProduct u ((B i).mulVec u) ≤
        dotProduct x ((B i).mulVec u) ^ 2) :
    ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) ≤ dotProduct (A.mulVec x) (A.mulVec x) := by
  classical
  intro x
  have hlocal (i : Fin n) : a i * dotProduct x ((B i).mulVec x) ≤ (A.mulVec x i) ^ 2 := by
    have hp : dotProduct u ((B i).mulVec u) = r i * u i := by
      rw [hrow, dotProduct_smul]
      change r i * dotProduct u (A i) = r i * u i
      rw [dotProduct_comm u (A i), show dotProduct (A i) u = u i from congrFun hAu i]
    have hcross : dotProduct x ((B i).mulVec u) = r i * A.mulVec x i := by
      rw [hrow, dotProduct_smul]
      change r i * dotProduct x (A i) = r i * dotProduct (A i) x
      rw [dotProduct_comm]
    have h := hdisc i x
    rw [hp, hcross, hu] at h
    have hr2 : 0 < (r i) ^ 2 := sq_pos_of_pos (hr i)
    nlinarith
  have hsum : dotProduct x (A.mulVec x) =
      ∑ i : Fin n, a i * dotProduct x ((B i).mulVec x) := by
    simp only [dotProduct, Matrix.mulVec, hdecomp, Finset.sum_mul, Finset.mul_sum]
    conv_lhs =>
      arg 2
      intro j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  exact Finset.sum_le_sum fun i hi => by simpa [dotProduct, pow_two] using hlocal i
theorem directional_matrix_local_to_global (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (B : Fin n → Matrix (Fin n) (Fin n) ℝ) (a u r : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (hu : ∀ i, u i = a i * r i)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hAu : A.mulVec u = u)
    (hconnect : ∀ s : Finset (Fin n), s.Nonempty →
      (∃ j : Fin n, j ∉ s) → ∃ i ∈ s, ∃ j ∉ s, 0 < A i j)
    (hdecomp : ∀ j k, A j k = ∑ i : Fin n, a i * B i j k)
    (hrow : ∀ i, (B i).mulVec u = r i • A i)
    (hdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((B i).mulVec x) * dotProduct u ((B i).mulVec u) ≤
        dotProduct x ((B i).mulVec u) ^ 2) :
    ∀ x : Fin n → ℝ, dotProduct u x = 0 → dotProduct x (A.mulVec x) ≤ 0 := by
  exact directional_matrix_nonpositive_kernel n hn A hA u
    (fun i => by rw [hu]; exact mul_pos (ha i) (hr i)) hnonneg hAu hconnect
    (directional_matrix_local_square n A B a u r ha hr hu hAu hdecomp hrow hdisc)
noncomputable def directional_diagonal_congruence {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j / (r i * r j)
theorem directional_diagonal_congruence_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0)
    (x : Fin n → ℝ) :
    (directional_diagonal_congruence A r).mulVec (fun i => r i * x i) =
      fun i => A.mulVec x i / r i := by
  ext i
  change (∑ j : Fin n, A i j / (r i * r j) * (r j * x j)) =
    (∑ j : Fin n, A i j * x j) / r i
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp [hr i, hr j]
theorem directional_diagonal_congruence_pairing {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r x y : Fin n → ℝ) :
    dotProduct x ((directional_diagonal_congruence A r).mulVec y) =
      dotProduct (fun i => x i / r i) (A.mulVec (fun i => y i / r i)) := by
  simp only [dotProduct, Matrix.mulVec, directional_diagonal_congruence, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
theorem directional_cubic_matrix_discriminant (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (B : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hactive : ∀ i, 0 < A.mulVec a i)
    (hconnect : ∀ s : Finset (Fin n), s.Nonempty →
      (∃ j : Fin n, j ∉ s) → ∃ i ∈ s, ∃ j ∉ s, 0 < A i j)
    (hdecomp : ∀ j k, A j k = ∑ i : Fin n, a i * B i j k)
    (hrow : ∀ i, (B i).mulVec a = A i)
    (hdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((B i).mulVec x) * dotProduct a ((B i).mulVec a) ≤
        dotProduct x ((B i).mulVec a) ^ 2) :
    ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) * dotProduct a (A.mulVec a) ≤
        dotProduct x (A.mulVec a) ^ 2 := by
  classical
  let r : Fin n → ℝ := fun i => Real.sqrt (A.mulVec a i / a i)
  have hr : ∀ i, 0 < r i := fun i => Real.sqrt_pos.2 (div_pos (hactive i) (ha i))
  have hr0 : ∀ i, r i ≠ 0 := fun i => ne_of_gt (hr i)
  have hrsq (i : Fin n) : r i ^ 2 * a i = A.mulVec a i := by
    rw [show r i ^ 2 = A.mulVec a i / a i from
      Real.sq_sqrt (le_of_lt (div_pos (hactive i) (ha i)))]
    exact div_mul_cancel₀ _ (ne_of_gt (ha i))
  let N := directional_diagonal_congruence A r
  let C : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun i => directional_diagonal_congruence (B i) r
  let u : Fin n → ℝ := fun i => r i * a i
  have hu : ∀ i, u i = a i * r i := fun i => mul_comm _ _
  have hN : N.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    change A j i / (r j * r i) = A i j / (r i * r j)
    rw [hA.isSymm.apply j i, mul_comm (r j) (r i)]
  have hNu : N.mulVec u = u := by
    rw [show N = directional_diagonal_congruence A r from rfl,
      directional_diagonal_congruence_mulVec A r hr0 a]
    ext i
    change A.mulVec a i / r i = r i * a i
    apply (div_eq_iff (hr0 i)).mpr
    nlinarith [hrsq i]
  have hNnonneg : ∀ i j, 0 ≤ N i j := by
    intro i j
    exact div_nonneg (hnonneg i j) (mul_nonneg (hr i).le (hr j).le)
  have hNconnect : ∀ s : Finset (Fin n), s.Nonempty →
      (∃ j : Fin n, j ∉ s) → ∃ i ∈ s, ∃ j ∉ s, 0 < N i j := by
    intro s hs hj
    obtain ⟨i, hi, j, hj, hij⟩ := hconnect s hs hj
    exact ⟨i, hi, j, hj, div_pos hij (mul_pos (hr i) (hr j))⟩
  have hNdecomp : ∀ j k, N j k = ∑ i : Fin n, a i * C i j k := by
    intro j k
    change A j k / (r j * r k) = ∑ i : Fin n, a i * (B i j k / (r j * r k))
    rw [hdecomp, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hNrow : ∀ i, (C i).mulVec u = r i • N i := by
    intro i
    rw [show C i = directional_diagonal_congruence (B i) r from rfl,
      directional_diagonal_congruence_mulVec (B i) r hr0 a, hrow]
    ext j
    change A i j / r j = r i * (A i j / (r i * r j))
    field_simp [hr0 i, hr0 j]
  have hurd : (fun i => u i / r i) = a := by
    ext i
    exact mul_div_cancel_left₀ _ (hr0 i)
  have hNdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((C i).mulVec x) * dotProduct u ((C i).mulVec u) ≤
        dotProduct x ((C i).mulVec u) ^ 2 := by
    intro i x
    simp only [C, directional_diagonal_congruence_pairing, hurd]
    exact hdisc i (fun j => x j / r j)
  have hker := directional_matrix_local_to_global n hn N hN C a u r ha hr hu
    hNnonneg hNu hNconnect hNdecomp hNrow hNdisc
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => dotProduct (A.mulVec a) x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hker' : ∀ x : Fin n → ℝ, l x = 0 → dotProduct x (A.mulVec x) ≤ 0 := by
    intro x hx
    have hx' : dotProduct u (fun i => r i * x i) = 0 := by
      change (∑ i : Fin n, (r i * a i) * (r i * x i)) = 0
      change (∑ i : Fin n, A.mulVec a i * x i) = 0 at hx
      convert hx using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hrsq i]
      ring
    have h := hker (fun i => r i * x i) hx'
    rw [show N = directional_diagonal_congruence A r from rfl,
      directional_diagonal_congruence_pairing] at h
    have heq : (fun i => r i * x i / r i) = x := by
      ext i
      exact mul_div_cancel_left₀ _ (hr0 i)
    simpa only [heq] using h
  have hpos : 0 < dotProduct a (A.mulVec a) := by
    exact Finset.sum_pos (fun i hi => mul_pos (ha i) (hactive i))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  intro x
  exact matrix_discriminant_of_nonpositive_kernel n A hA.isSymm l hker' x a hpos
theorem directional_add_single_sub_single {n : ℕ}
    (α : Fin n →₀ ℕ) (p k : Fin n) (hk : 0 < α k) :
    α + Finsupp.single p 1 - Finsupp.single k 1 =
      α - Finsupp.single k 1 + Finsupp.single p 1 := by
  ext j
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  split_ifs <;> subst_vars <;> omega
theorem directional_shadow_mem_of_lift {n : ℕ}
    (J : Set (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) (j k : Fin n)
    (hk : 0 < α k) (hj : α + Finsupp.single j 1 ∈ J) :
    ∃ p : Fin n,
      (α - Finsupp.single k 1 + Finsupp.single j 1) + Finsupp.single p 1 ∈ J := by
  refine ⟨k, ?_⟩
  rw [add_right_comm, Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hk)]
  exact hj
theorem directional_shadow_exchange_same_lift {n : ℕ}
    (J : Set (Fin n →₀ ℕ)) (hJ : LorentzianPolynomials.IsMConvex J)
    (α β : Fin n →₀ ℕ) (p k : Fin n)
    (hα : α + Finsupp.single p 1 ∈ J) (hβ : β + Finsupp.single p 1 ∈ J)
    (hk : β k < α k) :
    ∃ j : Fin n, α j < β j ∧ ∃ q : Fin n,
      (α - Finsupp.single k 1 + Finsupp.single j 1) + Finsupp.single q 1 ∈ J := by
  have hk' : (β + Finsupp.single p 1 : Fin n →₀ ℕ) k <
      (α + Finsupp.single p 1 : Fin n →₀ ℕ) k := by
    simp only [Finsupp.add_apply]
    omega
  obtain ⟨j, hj, hmem⟩ := hJ _ hα _ hβ k hk'
  have hj' : α j < β j := by
    simp only [Finsupp.add_apply] at hj
    omega
  refine ⟨j, hj', p, ?_⟩
  rw [directional_add_single_sub_single α p k (by omega)] at hmem
  simpa only [add_right_comm] using hmem
theorem directional_shadow_isMConvex {n : ℕ}
    (J : Set (Fin n →₀ ℕ)) (hJ : LorentzianPolynomials.IsMConvex J) :
    LorentzianPolynomials.IsMConvex {α | ∃ p : Fin n, α + Finsupp.single p 1 ∈ J} := by
  intro α hα β hβ k hk
  obtain ⟨p, hp⟩ := hα
  obtain ⟨q, hq⟩ := hβ
  by_cases hpq : p = q
  · subst q
    exact directional_shadow_exchange_same_lift J hJ α β p k hp hq hk
  by_cases hpdef : α p < β p
  · exact ⟨p, hpdef, directional_shadow_mem_of_lift J α p k (by omega) hp⟩
  have hp' : (β + Finsupp.single q 1 : Fin n →₀ ℕ) p <
      (α + Finsupp.single p 1 : Fin n →₀ ℕ) p := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hpq]
    omega
  obtain ⟨j, hj, hjmem⟩ := hJ _ hp _ hq p hp'
  rw [add_tsub_cancel_right] at hjmem
  by_cases hjdef : α j < β j
  · exact ⟨j, hjdef, directional_shadow_mem_of_lift J α j k (by omega) hjmem⟩
  have hjq : j = q := by
    by_contra hjq
    simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hjq] at hj
    omega
  subst j
  exact directional_shadow_exchange_same_lift J hJ α β q k hjmem hq hk
theorem directional_derivative_coefficient {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ) (m : Fin n →₀ ℕ) :
    (∑ i : Fin n, a i • f.pderiv i).coeff m =
      ∑ i : Fin n, a i * (f.coeff (m + Finsupp.single i 1) * (m i + 1)) := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_pderiv,
    smul_eq_mul, Nat.cast_add, Nat.cast_one]
theorem directional_derivative_nonnegative_coefficients {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
    (hf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) (ha : ∀ i, 0 ≤ a i) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (∑ i : Fin n, a i • f.pderiv i).coeff m := by
  intro m
  rw [directional_derivative_coefficient]
  exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i) (mul_nonneg (hf _) (by positivity))
theorem directional_derivative_support_eq_shadow {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
    (hf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) (ha : ∀ i, 0 < a i) :
    ((∑ i : Fin n, a i • f.pderiv i).support : Set (Fin n →₀ ℕ)) =
      {m | ∃ i : Fin n, m + Finsupp.single i 1 ∈ f.support} := by
  classical
  ext m
  change m ∈ (∑ i : Fin n, a i • f.pderiv i).support ↔
    ∃ i : Fin n, m + Finsupp.single i 1 ∈ f.support
  rw [MvPolynomial.mem_support_iff]
  have hterm (i : Fin n) : 0 ≤ a i *
      (f.coeff (m + Finsupp.single i 1) * (m i + 1)) :=
    mul_nonneg (ha i).le (mul_nonneg (hf _) (by positivity))
  constructor
  · intro hm
    have hpos : 0 < (∑ i : Fin n, a i • f.pderiv i).coeff m :=
      lt_of_le_of_ne (directional_derivative_nonnegative_coefficients f a hf (fun i => (ha i).le) m)
        (Ne.symm hm)
    rw [directional_derivative_coefficient] at hpos
    obtain ⟨i, hi, hipos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun i hi => hterm i)).mp hpos
    refine ⟨i, MvPolynomial.mem_support_iff.mpr ?_⟩
    intro hz
    rw [hz, zero_mul, mul_zero] at hipos
    exact (lt_irrefl _) hipos
  · rintro ⟨i, hi⟩
    have hpos : 0 < f.coeff (m + Finsupp.single i 1) :=
      lt_of_le_of_ne (hf _) (Ne.symm (MvPolynomial.mem_support_iff.mp hi))
    apply ne_of_gt
    rw [directional_derivative_coefficient]
    exact Finset.sum_pos' (fun j hj => hterm j)
      ⟨i, Finset.mem_univ _, mul_pos (ha i) (mul_pos hpos (by positivity))⟩
theorem directional_derivative_support_isMConvex {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (a : Fin n → ℝ)
    (hf : ∀ m : Fin n →₀ ℕ, 0 ≤ f.coeff m) (ha : ∀ i, 0 < a i)
    (hJ : LorentzianPolynomials.IsMConvex (f.support : Set (Fin n →₀ ℕ))) :
    LorentzianPolynomials.IsMConvex
      ((∑ i : Fin n, a i • f.pderiv i).support : Set (Fin n →₀ ℕ)) := by
  rw [directional_derivative_support_eq_shadow f a hf ha]
  exact directional_shadow_isMConvex _ hJ
theorem directional_pderiv_commute {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
  rw [show m + Finsupp.single i 1 + Finsupp.single j 1 =
    m + Finsupp.single j 1 + Finsupp.single i 1 by ac_rfl]
  ring
noncomputable def directional_homogeneous_derivative (n d : ℕ)
    (f : LorentzianPolynomials.H n (d + 1)) (a : Fin n → ℝ) : LorentzianPolynomials.H n d :=
  ⟨∑ i : Fin n, a i • f.1.pderiv i,
    (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d).sum_mem (fun i hi =>
      (MvPolynomial.homogeneousSubmodule (Fin n) ℝ d).smul_mem (a i)
        (by
          change (f.1.pderiv i).IsHomogeneous d
          simpa only [Nat.add_sub_cancel] using f.2.pderiv))⟩
theorem directional_lorentzian_coefficients_nonnegative (n d : ℕ)
    (f : LorentzianPolynomials.H n d) (hf : f ∈ LorentzianPolynomials.L n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
  match d with
  | 0 => exact hf.2
  | 1 => exact hf.2
  | 2 => exact hf.2
  | d + 3 => exact hf.1.2
theorem positive_directional_derivative_of_cubic_stability
    (hcubic : ∀ n : ℕ, 0 < n → ∀ f : LorentzianPolynomials.H n 3,
      f ∈ LorentzianPolynomials.L n 3 → ∀ a : Fin n → ℝ, (∀ i, 0 < a i) →
        LorentzianPolynomials.IsStable (∑ i : Fin n, a i • f.1.pderiv i)) :
    ∀ (n d : ℕ), 0 < n → ∀ f : LorentzianPolynomials.H n (d + 1),
      f ∈ LorentzianPolynomials.L n (d + 1) → ∀ a : Fin n → ℝ, (∀ i, 0 < a i) →
        ∃ g : LorentzianPolynomials.H n d,
          g.1 = ∑ i : Fin n, a i • f.1.pderiv i ∧ g ∈ LorentzianPolynomials.L n d := by
  intro n d hn
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hf a ha
    let g := directional_homogeneous_derivative n d f a
    have hg : g.1 = ∑ i : Fin n, a i • f.1.pderiv i := rfl
    have hnonneg : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m := by
      rw [hg]
      exact directional_derivative_nonnegative_coefficients f.1 a
        (directional_lorentzian_coefficients_nonnegative n (d + 1) f hf) (fun i => (ha i).le)
    refine ⟨g, hg, ?_⟩
    rcases d with _ | _ | _ | d
    · exact ⟨homogeneous_degree_zero_stable n g, hnonneg⟩
    · exact ⟨homogeneous_degree_one_stable n g hnonneg, hnonneg⟩
    ·
      refine ⟨?_, hnonneg⟩
      rw [hg]
      exact hcubic n hn f hf a ha
    ·
      refine ⟨⟨?_, hnonneg⟩, ?_⟩
      · rw [hg]
        exact directional_derivative_support_isMConvex f.1 a
          (directional_lorentzian_coefficients_nonnegative n (d + 3 + 1) f hf) ha hf.1.1
      · intro i
        let fi : LorentzianPolynomials.H n (d + 3) := ⟨f.1.pderiv i, f.2.pderiv⟩
        have hfi : fi ∈ LorentzianPolynomials.L n (d + 3) := hf.2 i
        obtain ⟨gi, hgi, hgiL⟩ := ih (d + 2) (by omega) fi hfi a ha
        have heq : (⟨g.1.pderiv i, g.2.pderiv⟩ : LorentzianPolynomials.H n (d + 2)) = gi := by
          apply Subtype.ext
          change MvPolynomial.pderiv i g.1 = gi.1
          rw [hg, map_sum]
          rw [hgi]
          apply Finset.sum_congr rfl
          intro j hj
          rw [(MvPolynomial.pderiv i).map_smul]
          exact congrArg (fun p : MvPolynomial (Fin n) ℝ => a j • p)
            (directional_pderiv_commute f.1 i j)
        rw [heq]
        exact hgiL
theorem directional_mconvex_support_connects {n : ℕ}
    (J : Set (Fin n →₀ ℕ)) (hJ : LorentzianPolynomials.IsMConvex J)
    (hdegree : ∀ α ∈ J, 2 ≤ Finsupp.weight 1 α)
    (hactive : ∀ i : Fin n, ∃ α ∈ J, 0 < α i)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hedge : ∀ α ∈ J, ∀ i j : Fin n, i ≠ j → 0 < α i → 0 < α j → 0 < A i j) :
    ∀ s : Finset (Fin n), s.Nonempty → (∃ j : Fin n, j ∉ s) →
      ∃ i ∈ s, ∃ j ∉ s, 0 < A i j := by
  classical
  intro s hs hsc
  by_cases hcross : ∃ α ∈ J, ∃ i ∈ s, ∃ j ∉ s, 0 < α i ∧ 0 < α j
  · obtain ⟨α, hα, i, hi, j, hj, hαi, hαj⟩ := hcross
    exact ⟨i, hi, j, hj, hedge α hα i j (fun h => hj (h ▸ hi)) hαi hαj⟩
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := hsc
  obtain ⟨α, hα, hαi⟩ := hactive i
  obtain ⟨β, hβ, hβj⟩ := hactive j
  have hαoutside : ∀ k : Fin n, k ∉ s → α k = 0 := by
    intro k hk
    by_contra hne
    exact hcross ⟨α, hα, i, hi, k, hk, hαi, Nat.pos_of_ne_zero hne⟩
  have hβinside : ∀ k : Fin n, k ∈ s → β k = 0 := by
    intro k hk
    by_contra hne
    exact hcross ⟨β, hβ, k, hk, j, hj, Nat.pos_of_ne_zero hne, hβj⟩
  obtain ⟨l, hl, hmem⟩ := hJ α hα β hβ i (by rw [hβinside i hi]; exact hαi)
  have hls : l ∉ s := by
    intro hls
    rw [hβinside l hls] at hl
    omega
  have hremain : α - Finsupp.single i 1 ≠ 0 := by
    intro hz
    have hαeq : α = Finsupp.single i 1 := by
      have h := Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hαi)
      rw [hz, zero_add] at h
      exact h.symm
    have hdeg := hdegree α hα
    rw [hαeq, Finsupp.weight_single] at hdeg
    norm_num at hdeg
  obtain ⟨k, hk⟩ : ∃ k : Fin n, (α - Finsupp.single i 1 : Fin n →₀ ℕ) k ≠ 0 := by
    by_contra! hz
    apply hremain
    ext k
    exact hz k
  have hkpos : 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) k := Nat.pos_of_ne_zero hk
  have hαk : 0 < α k := by
    simp only [Finsupp.tsub_apply] at hkpos
    omega
  have hks : k ∈ s := by
    by_contra hks
    rw [hαoutside k hks] at hαk
    omega
  have hposk : 0 < (α - Finsupp.single i 1 + Finsupp.single l 1 : Fin n →₀ ℕ) k := by
    simp only [Finsupp.add_apply]
    omega
  have hposl : 0 < (α - Finsupp.single i 1 + Finsupp.single l 1 : Fin n →₀ ℕ) l := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  exact False.elim (hcross ⟨_, hmem, k, hks, l, hls, hposk, hposl⟩)
theorem directional_stable_quadratic_nonpositive_kernel (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    ∀ x : Fin n → ℝ, f.hessian.toBilin' u x = 0 → f.hessian.toBilin' x x ≤ 0 := by
  classical
  by_cases hzero : f.1 = 0
  · intro x _
    simp [LorentzianPolynomials.H.hessian, hzero, Matrix.toBilin'_apply',
      Matrix.mulVec, dotProduct]
  have hA : f.hessian ≠ 0 :=
    fun h => hzero (forward_hessian_eq_zero_imp_polynomial_zero n f h)
  have hqu : 0 < f.hessian.toBilin' u u := by
    simpa only [Matrix.toBilin'_apply'] using
      nonzero_nonnegative_matrix_positive_pairing n f.hessian hA
        (forward_hessian_entries_nonnegative n f hf.2) u hu
  have hsym : ∀ v w, f.hessian.toBilin' v w = f.hessian.toBilin' w v :=
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (forward_hessian_isHermitian n f).isSymm).eq
  intro x hux
  by_contra! hx
  let t : ℝ := Real.sqrt (f.hessian.toBilin' u u / f.hessian.toBilin' x x)
  have ht : t ^ 2 = f.hessian.toBilin' u u / f.hessian.toBilin' x x :=
    Real.sq_sqrt (div_pos hqu hx).le
  have hq : t ^ 2 * f.hessian.toBilin' x x = f.hessian.toBilin' u u := by
    rw [ht, div_mul_cancel₀ _ (ne_of_gt hx)]
  have hscale : f.hessian.toBilin' (t • x) (t • x) =
      t ^ 2 * f.hessian.toBilin' x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hxu : f.hessian.toBilin' x u = 0 := (hsym x u).trans hux
  let z : Fin n → UpperHalfPlane := fun i => ⟨⟨t * x i, u i⟩, hu i⟩
  let S : ℂ := ∑ i : Fin n, ∑ j : Fin n,
    (z i : ℂ) * (z j : ℂ) * (f.hessian i j : ℂ)
  have hreal : S.re = 0 := by
    rw [forward_complex_quadratic_re, ← Matrix.toBilin'_apply', ← Matrix.toBilin'_apply']
    change f.hessian.toBilin' (t • x) (t • x) - f.hessian.toBilin' u u = 0
    rw [hscale, hq, sub_self]
  have him : S.im = 0 := by
    rw [forward_complex_quadratic_im n f.hessian (forward_hessian_isHermitian n f).isSymm,
      ← Matrix.toBilin'_apply']
    change 2 * f.hessian.toBilin' (t • x) u = 0
    simp [hxu]
  have hS : S = 0 := Complex.ext hreal him
  have heval : MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = 0 := by
    have h := forward_quadratic_hessian_aeval n f (fun i => (z i : ℂ))
    change 2 * MvPolynomial.aeval (fun i => (z i : ℂ)) f.1 = S at h
    rw [hS] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  exact (hf.1.resolve_left hzero z) heval
theorem directional_stable_quadratic_discriminant (n : ℕ)
    (f : LorentzianPolynomials.H n 2) (hf : f ∈ LorentzianPolynomials.L n 2)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (x : Fin n → ℝ) :
    dotProduct x (f.hessian.mulVec x) * dotProduct a (f.hessian.mulVec a) ≤
      dotProduct x (f.hessian.mulVec a) ^ 2 := by
  by_cases hz : f.hessian = 0
  · simp [hz]
  have hp := nonzero_nonnegative_matrix_positive_pairing n f.hessian hz
    (forward_hessian_entries_nonnegative n f hf.2) a ha
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := f.hessian.toBilin' a
  apply matrix_discriminant_of_nonpositive_kernel n f.hessian
    (forward_hessian_isHermitian n f).isSymm l ?_ x a hp
  intro v hv
  simpa only [Matrix.toBilin'_apply'] using
    directional_stable_quadratic_nonpositive_kernel n f hf a ha v hv
theorem directional_cubic_tensor_symmetry {n : ℕ}
    (f : LorentzianPolynomials.H n 3) (i j k : Fin n) :
    LorentzianPolynomials.H.hessian (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n 2) j k =
      LorentzianPolynomials.H.hessian (⟨f.1.pderiv j, f.2.pderiv⟩ : LorentzianPolynomials.H n 2) i k := by
  let fi : LorentzianPolynomials.H n 2 := ⟨f.1.pderiv i, f.2.pderiv⟩
  let fj : LorentzianPolynomials.H n 2 := ⟨f.1.pderiv j, f.2.pderiv⟩
  calc
    _ = (MvPolynomial.pderiv j (MvPolynomial.pderiv i f.1)).coeff (Finsupp.single k 1) :=
      (forward_quadratic_pderiv_coefficient n fi j k).symm
    _ = (MvPolynomial.pderiv i (MvPolynomial.pderiv j f.1)).coeff (Finsupp.single k 1) :=
      congrArg (fun p : MvPolynomial (Fin n) ℝ => p.coeff (Finsupp.single k 1))
        (directional_pderiv_commute f.1 j i)
    _ = _ := forward_quadratic_pderiv_coefficient n fj i k
theorem directional_hessian_decomposition {n : ℕ}
    (f : LorentzianPolynomials.H n 3) (a : Fin n → ℝ) (j k : Fin n) :
    (directional_homogeneous_derivative n 2 f a).hessian j k =
      ∑ i : Fin n, a i *
        LorentzianPolynomials.H.hessian (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n 2) j k := by
  classical
  rw [← forward_quadratic_pderiv_coefficient]
  change (MvPolynomial.pderiv j (∑ i : Fin n, a i • f.1.pderiv i)).coeff
    (Finsupp.single k 1) = _
  simp only [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(MvPolynomial.pderiv j).map_smul, MvPolynomial.coeff_smul, smul_eq_mul,
    forward_quadratic_pderiv_coefficient n
      (⟨f.1.pderiv i, f.2.pderiv⟩ : LorentzianPolynomials.H n 2)]
theorem directional_weight_two_exponent {n : ℕ} (α : Fin n →₀ ℕ)
    (hα : Finsupp.weight 1 α = 2) (i j : Fin n) (hij : i ≠ j)
    (hi : 0 < α i) (hj : 0 < α j) :
    α = Finsupp.single i 1 + Finsupp.single j 1 := by
  have hsubi := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hi)
  have hj' : 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) j := by
    simpa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Ne.symm hij)] using hj
  have hsubj := Finsupp.weight_sub_single_add (w := (1 : Fin n → ℕ)) (Nat.ne_of_gt hj')
  have hz : Finsupp.weight (1 : Fin n → ℕ)
      (α - Finsupp.single i 1 - Finsupp.single j 1) = 0 := by
    simp only [Pi.one_apply] at hsubi hsubj
    omega
  have heq : α - Finsupp.single i 1 - Finsupp.single j 1 = 0 := by
    ext k
    have hk := Finsupp.le_weight (1 : Fin n → ℕ) (s := k) (by simp)
      (α - Finsupp.single i 1 - Finsupp.single j 1)
    rw [hz] at hk
    exact Nat.eq_zero_of_le_zero hk
  have hrecj := Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hj')
  have hreci := Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hi)
  rw [heq, zero_add] at hrecj
  rw [← hreci, ← hrecj, add_comm]
theorem directional_sum_active {n m : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (e : Fin m → Fin n) (he : Function.Injective e) (hemem : ∀ i, p (e i))
    (hecover : ∀ j, p j → ∃ i, e i = j) (f : Fin n → ℝ)
    (hz : ∀ j, ¬p j → f j = 0) :
    (∑ i : Fin m, f (e i)) = ∑ j : Fin n, f j := by
  classical
  calc
    (∑ i : Fin m, f (e i)) = ∑ j ∈ Finset.univ.filter p, f j := by
      apply Finset.sum_bij (fun i _ => e i)
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hemem i⟩
      · intro i hi j hj hij
        exact he hij
      · intro j hj
        obtain ⟨i, hi⟩ := hecover j (Finset.mem_filter.mp hj).2
        exact ⟨i, Finset.mem_univ _, hi⟩
      · intro i hi
        rfl
    _ = ∑ j : Fin n, f j := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjp
      exact hz j (fun hp => hjp (Finset.mem_filter.mpr ⟨hj, hp⟩))
theorem directional_restrict_pairing {n m : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (e : Fin m → Fin n) (he : Function.Injective e) (hemem : ∀ i, p (e i))
    (hecover : ∀ j, p j → ∃ i, e i = j)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hz : ∀ i j, ¬p i ∨ ¬p j → A i j = 0) (x y : Fin n → ℝ) :
    dotProduct (fun i => x (e i))
      (Matrix.mulVec (fun i j => A (e i) (e j)) (fun i => y (e i))) =
      dotProduct x (A.mulVec y) := by
  classical
  have hrow (i : Fin n) : (∑ j : Fin m, A i (e j) * y (e j)) = A.mulVec y i := by
    change (∑ j : Fin m, A i (e j) * y (e j)) = ∑ j : Fin n, A i j * y j
    apply directional_sum_active p e he hemem hecover (fun j => A i j * y j)
    intro j hj
    rw [hz i j (Or.inr hj), zero_mul]
  change (∑ i : Fin m, x (e i) * ∑ j : Fin m, A (e i) (e j) * y (e j)) = _
  simp only [hrow]
  change (∑ i : Fin m, x (e i) * A.mulVec y (e i)) = ∑ j : Fin n, x j * A.mulVec y j
  apply directional_sum_active p e he hemem hecover (fun j => x j * A.mulVec y j)
  intro j hj
  simp only [Matrix.mulVec, dotProduct]
  simp [hz j _ (Or.inl hj)]
theorem directional_cubic_matrix_discriminant_with_zeros (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (B : Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hBnonneg : ∀ i j k, 0 ≤ B i j k)
    (hdecomp : ∀ j k, A j k = ∑ i : Fin n, a i * B i j k)
    (htensor : ∀ i j k, B i j k = B j i k)
    (hrow : ∀ i, (B i).mulVec a = A i)
    (hconnect : ∀ s : Finset (Fin n),
      (∃ i ∈ s, 0 < A.mulVec a i) → (∃ j ∉ s, 0 < A.mulVec a j) →
      ∃ i ∈ s, ∃ j ∉ s, 0 < A i j)
    (hdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((B i).mulVec x) * dotProduct a ((B i).mulVec a) ≤
        dotProduct x ((B i).mulVec a) ^ 2) :
    ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) * dotProduct a (A.mulVec a) ≤
        dotProduct x (A.mulVec a) ^ 2 := by
  classical
  have hnonneg (i j : Fin n) : 0 ≤ A i j := by
    rw [hdecomp]
    exact Finset.sum_nonneg fun k hk => mul_nonneg (ha k).le (hBnonneg k i j)
  by_cases hAz : A = 0
  · simp [hAz]
  let p : Fin n → Prop := fun i => 0 < A.mulVec a i
  have hzeroRow (i : Fin n) (hi : ¬p i) (j : Fin n) : A i j = 0 := by
    have hs : (∑ k : Fin n, A i k * a k) = 0 :=
      le_antisymm (le_of_not_gt hi)
        (Finset.sum_nonneg fun k hk => mul_nonneg (hnonneg i k) (ha k).le)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => mul_nonneg (hnonneg i k) (ha k).le)).mp hs j (Finset.mem_univ _)
    exact (mul_eq_zero.mp hj).resolve_right (ne_of_gt (ha j))
  have hzero (i j : Fin n) (h : ¬p i ∨ ¬p j) : A i j = 0 := by
    rcases h with hi | hj
    · exact hzeroRow i hi j
    · exact (hA.isSymm.apply j i).trans (hzeroRow j hj i)
  have hBzero (i j k : Fin n) (h : ¬p j ∨ ¬p k) : B i j k = 0 := by
    have hs : (∑ l : Fin n, a l * B l j k) = 0 := (hdecomp j k).symm.trans (hzero j k h)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l hl => mul_nonneg (ha l).le (hBnonneg l j k))).mp hs i (Finset.mem_univ _)
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (ha i))
  have hpnonempty : ∃ i, p i := by
    by_contra! h
    apply hAz
    ext i j
    exact hzeroRow i (h i) j
  let I := {i : Fin n // p i}
  let m := Fintype.card I
  let e : Fin m → Fin n := fun i => ((Fintype.equivFin I).symm i).1
  have hm : 0 < m := Fintype.card_pos_iff.mpr
    (by obtain ⟨i, hi⟩ := hpnonempty; exact ⟨⟨i, hi⟩⟩)
  have he : Function.Injective e := by
    intro i j hij
    apply (Fintype.equivFin I).symm.injective
    exact Subtype.ext hij
  have hemem (i : Fin m) : p (e i) := ((Fintype.equivFin I).symm i).2
  have hecover (j : Fin n) (hj : p j) : ∃ i : Fin m, e i = j :=
    ⟨Fintype.equivFin I ⟨j, hj⟩, by simp [e]⟩
  let A' : Matrix (Fin m) (Fin m) ℝ := fun i j => A (e i) (e j)
  let B' : Fin m → Matrix (Fin m) (Fin m) ℝ := fun i j k => B (e i) (e j) (e k)
  let a' : Fin m → ℝ := fun i => a (e i)
  have hmul (i : Fin m) : A'.mulVec a' i = A.mulVec a (e i) := by
    change (∑ j : Fin m, A (e i) (e j) * a (e j)) = ∑ j : Fin n, A (e i) j * a j
    apply directional_sum_active p e he hemem hecover (fun j => A (e i) j * a j)
    intro j hj
    rw [hzero (e i) j (Or.inr hj), zero_mul]
  have hA' : A'.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    exact Matrix.IsSymm.ext fun i j => hA.isSymm.apply (e i) (e j)
  have hdecomp' (j k : Fin m) : A' j k = ∑ i : Fin m, a' i * B' i j k := by
    rw [show A' j k = A (e j) (e k) from rfl, hdecomp]
    symm
    apply directional_sum_active p e he hemem hecover (fun i => a i * B i (e j) (e k))
    intro i hi
    rw [htensor i (e j) (e k), hBzero (e j) i (e k) (Or.inl hi), mul_zero]
  have hrow' (i : Fin m) : (B' i).mulVec a' = A' i := by
    ext j
    change (∑ k : Fin m, B (e i) (e j) (e k) * a (e k)) = A (e i) (e j)
    rw [directional_sum_active p e he hemem hecover
      (fun k => B (e i) (e j) k * a k)
      (fun k hk => by rw [hBzero (e i) (e j) k (Or.inr hk), zero_mul])]
    exact congrFun (hrow (e i)) (e j)
  have hconnect' : ∀ s : Finset (Fin m), s.Nonempty → (∃ j : Fin m, j ∉ s) →
      ∃ i ∈ s, ∃ j ∉ s, 0 < A' i j := by
    intro s hs hj
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := hj
    have hjimage : e j ∉ s.image e := by
      simpa only [Finset.mem_image, he.eq_iff, exists_eq_right] using hj
    obtain ⟨k, hk, l, hl, hkl⟩ := hconnect (s.image e)
      ⟨e i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hemem i⟩ ⟨e j, hjimage, hemem j⟩
    obtain ⟨k', hk', hkeq⟩ := Finset.mem_image.mp hk
    have hpl : p l := by
      by_contra hpl
      rw [hzero k l (Or.inr hpl)] at hkl
      exact (lt_irrefl _) hkl
    obtain ⟨l', hleq⟩ := hecover l hpl
    refine ⟨k', hk', l', ?_, ?_⟩
    · intro hls
      exact hl (Finset.mem_image.mpr ⟨l', hls, hleq⟩)
    · change 0 < A (e k') (e l')
      rwa [hkeq, hleq]
  have hdisc' (i : Fin m) (x : Fin m → ℝ) :
      dotProduct x ((B' i).mulVec x) * dotProduct a' ((B' i).mulVec a') ≤
        dotProduct x ((B' i).mulVec a') ^ 2 := by
    let v : Fin n → ℝ := fun j => if h : p j then x (Classical.choose (hecover j h)) else 0
    have hv (j : Fin m) : v (e j) = x j := by
      simp only [v, dif_pos (hemem j)]
      congr 1
      apply he
      exact Classical.choose_spec (hecover (e j) (hemem j))
    have hxx := directional_restrict_pairing p e he hemem hecover
      (B (e i)) (hBzero (e i)) v v
    have haa := directional_restrict_pairing p e he hemem hecover
      (B (e i)) (hBzero (e i)) a a
    have hxa := directional_restrict_pairing p e he hemem hecover
      (B (e i)) (hBzero (e i)) v a
    have hd := hdisc (e i) v
    rw [← hxx, ← haa, ← hxa] at hd
    simpa only [hv] using hd
  have hd := directional_cubic_matrix_discriminant m hm A' hA' B' a'
    (fun i => ha (e i)) (fun i j => hnonneg (e i) (e j))
    (fun i => by rw [hmul]; exact hemem i) hconnect' hdecomp' hrow' hdisc'
  intro x
  have hxx := directional_restrict_pairing p e he hemem hecover A hzero x x
  have haa := directional_restrict_pairing p e he hemem hecover A hzero a a
  have hxa := directional_restrict_pairing p e he hemem hecover A hzero x a
  have hx := hd (fun i => x (e i))
  rw [hxx, haa, hxa] at hx
  exact hx
theorem directional_mconvex_support_connects_active {n : ℕ}
    (J : Set (Fin n →₀ ℕ)) (hJ : LorentzianPolynomials.IsMConvex J)
    (hdegree : ∀ α ∈ J, 2 ≤ Finsupp.weight 1 α)
    (p : Fin n → Prop) (hactive : ∀ i : Fin n, p i → ∃ α ∈ J, 0 < α i)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hedge : ∀ α ∈ J, ∀ i j : Fin n, i ≠ j → 0 < α i → 0 < α j → 0 < A i j) :
    ∀ s : Finset (Fin n), (∃ i ∈ s, p i) → (∃ j ∉ s, p j) →
      ∃ i ∈ s, ∃ j ∉ s, 0 < A i j := by
  classical
  intro s hs hsc
  by_cases hcross : ∃ α ∈ J, ∃ i ∈ s, ∃ j ∉ s, 0 < α i ∧ 0 < α j
  · obtain ⟨α, hα, i, hi, j, hj, hαi, hαj⟩ := hcross
    exact ⟨i, hi, j, hj, hedge α hα i j (fun h => hj (h ▸ hi)) hαi hαj⟩
  obtain ⟨i, hi, hpi⟩ := hs
  obtain ⟨j, hj, hpj⟩ := hsc
  obtain ⟨α, hα, hαi⟩ := hactive i hpi
  obtain ⟨β, hβ, hβj⟩ := hactive j hpj
  have hαoutside : ∀ k : Fin n, k ∉ s → α k = 0 := by
    intro k hk
    by_contra hne
    exact hcross ⟨α, hα, i, hi, k, hk, hαi, Nat.pos_of_ne_zero hne⟩
  have hβinside : ∀ k : Fin n, k ∈ s → β k = 0 := by
    intro k hk
    by_contra hne
    exact hcross ⟨β, hβ, k, hk, j, hj, Nat.pos_of_ne_zero hne, hβj⟩
  obtain ⟨l, hl, hmem⟩ := hJ α hα β hβ i (by rw [hβinside i hi]; exact hαi)
  have hls : l ∉ s := by
    intro hls
    rw [hβinside l hls] at hl
    omega
  have hremain : α - Finsupp.single i 1 ≠ 0 := by
    intro hz
    have hαeq : α = Finsupp.single i 1 := by
      have h := Finsupp.sub_add_single_one_cancel (Nat.ne_of_gt hαi)
      rw [hz, zero_add] at h
      exact h.symm
    have hdeg := hdegree α hα
    rw [hαeq, Finsupp.weight_single] at hdeg
    norm_num at hdeg
  obtain ⟨k, hk⟩ : ∃ k : Fin n, (α - Finsupp.single i 1 : Fin n →₀ ℕ) k ≠ 0 := by
    by_contra! hz
    apply hremain
    ext k
    exact hz k
  have hkpos : 0 < (α - Finsupp.single i 1 : Fin n →₀ ℕ) k := Nat.pos_of_ne_zero hk
  have hαk : 0 < α k := by
    simp only [Finsupp.tsub_apply] at hkpos
    omega
  have hks : k ∈ s := by
    by_contra hks
    rw [hαoutside k hks] at hαk
    omega
  have hposk : 0 < (α - Finsupp.single i 1 + Finsupp.single l 1 : Fin n →₀ ℕ) k := by
    simp only [Finsupp.add_apply]
    omega
  have hposl : 0 < (α - Finsupp.single i 1 + Finsupp.single l 1 : Fin n →₀ ℕ) l := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  exact False.elim (hcross ⟨_, hmem, k, hks, l, hls, hposk, hposl⟩)
theorem directional_quadratic_support_connects {n : ℕ}
    (g : LorentzianPolynomials.H n 2)
    (hc : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m)
    (hJ : LorentzianPolynomials.IsMConvex (g.1.support : Set (Fin n →₀ ℕ)))
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ s : Finset (Fin n),
      (∃ i ∈ s, 0 < g.hessian.mulVec a i) →
      (∃ j ∉ s, 0 < g.hessian.mulVec a j) →
      ∃ i ∈ s, ∃ j ∉ s, 0 < g.hessian i j := by
  classical
  have hdegree (α : Fin n →₀ ℕ) (hα : α ∈ g.1.support) :
      Finsupp.weight 1 α = 2 := by
    by_contra h
    exact MvPolynomial.mem_support_iff.mp hα
      (MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero g.2 α h)
  have hnonneg := forward_hessian_entries_nonnegative n g hc
  apply directional_mconvex_support_connects_active (g.1.support : Set (Fin n →₀ ℕ)) hJ
    (fun α hα => (hdegree α hα).ge)
    (fun i => 0 < g.hessian.mulVec a i) ?_ g.hessian ?_
  · intro i hi
    change 0 < ∑ j : Fin n, g.hessian i j * a j at hi
    obtain ⟨j, hj, hijpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun j hj => mul_nonneg (hnonneg i j) (ha j).le)).mp hi
    have hpos : 0 < g.hessian i j := by
      by_contra! h
      have hz : g.hessian i j = 0 := le_antisymm h (hnonneg i j)
      rw [hz, zero_mul] at hijpos
      exact (lt_irrefl _) hijpos
    by_cases hij : i = j
    · subst j
      have hp : 0 < g.1.coeff (Finsupp.single i 2) := by
        change 0 < (if i = i then 2 * g.1.coeff (Finsupp.single i 2) else _) at hpos
        rw [if_pos rfl] at hpos
        linarith
      refine ⟨Finsupp.single i 2, MvPolynomial.mem_support_iff.mpr (ne_of_gt hp), ?_⟩
      simp
    · have hp : 0 < g.1.coeff (Finsupp.single i 1 + Finsupp.single j 1) := by
        simpa only [LorentzianPolynomials.H.hessian, if_neg hij] using hpos
      refine ⟨Finsupp.single i 1 + Finsupp.single j 1,
        MvPolynomial.mem_support_iff.mpr (ne_of_gt hp), ?_⟩
      simp [Finsupp.add_apply, Finsupp.single_eq_of_ne hij]
  · intro α hα i j hij hi hj
    have heq := directional_weight_two_exponent α (hdegree α hα) i j hij hi hj
    have hp : 0 < g.1.coeff α := lt_of_le_of_ne (hc α)
      (Ne.symm (MvPolynomial.mem_support_iff.mp hα))
    simpa only [LorentzianPolynomials.H.hessian, if_neg hij, heq] using hp
theorem directional_cubic_stability (n : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n 3) (hf : f ∈ LorentzianPolynomials.L n 3)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    LorentzianPolynomials.IsStable (∑ i : Fin n, a i • f.1.pderiv i) := by
  classical
  let g := directional_homogeneous_derivative n 2 f a
  let fi : Fin n → LorentzianPolynomials.H n 2 := fun i => ⟨f.1.pderiv i, f.2.pderiv⟩
  let B : Fin n → Matrix (Fin n) (Fin n) ℝ := fun i => (fi i).hessian
  have hfi (i : Fin n) : fi i ∈ LorentzianPolynomials.L n 2 := hf.2 i
  have hc : ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m :=
    directional_derivative_nonnegative_coefficients f.1 a hf.1.2 (fun i => (ha i).le)
  have hJ : LorentzianPolynomials.IsMConvex (g.1.support : Set (Fin n →₀ ℕ)) :=
    directional_derivative_support_isMConvex f.1 a hf.1.2 ha hf.1.1
  have hdecomp (j k : Fin n) : g.hessian j k = ∑ i : Fin n, a i * B i j k :=
    directional_hessian_decomposition f a j k
  have htensor (i j k : Fin n) : B i j k = B j i k :=
    directional_cubic_tensor_symmetry f i j k
  have hBnonneg (i j k : Fin n) : 0 ≤ B i j k :=
    forward_hessian_entries_nonnegative n (fi i) (hfi i).2 j k
  have hrow (i : Fin n) : (B i).mulVec a = g.hessian i := by
    ext k
    change (∑ j : Fin n, B i k j * a j) = g.hessian i k
    rw [hdecomp]
    apply Finset.sum_congr rfl
    intro j hj
    have hs : B i k j = B i j k :=
      (forward_hessian_isHermitian n (fi i)).isSymm.apply j k
    rw [hs, htensor i j k]
    exact mul_comm _ _
  have hdisc : ∀ (i : Fin n) (x : Fin n → ℝ),
      dotProduct x ((B i).mulVec x) * dotProduct a ((B i).mulVec a) ≤
        dotProduct x ((B i).mulVec a) ^ 2 := by
    intro i x
    exact directional_stable_quadratic_discriminant n (fi i) (hfi i) a ha x
  have hd := directional_cubic_matrix_discriminant_with_zeros n g.hessian
    (forward_hessian_isHermitian n g) B a ha hBnonneg hdecomp htensor hrow
    (directional_quadratic_support_connects g hc hJ a ha) hdisc
  change LorentzianPolynomials.IsStable g.1
  apply forward_quadratic_stable_of_hessian_discriminant n g hc
  intro x y hy
  by_cases hzero : g.hessian = 0
  · simp [hzero]
  have hnonneg := forward_hessian_entries_nonnegative n g hc
  have hp := nonzero_nonnegative_matrix_positive_pairing n g.hessian hzero hnonneg a ha
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := g.hessian.toBilin' a
  apply matrix_discriminant_of_nonpositive_kernel n g.hessian
    (forward_hessian_isHermitian n g).isSymm l ?_ x y
    (nonzero_nonnegative_matrix_positive_pairing n g.hessian hzero hnonneg y hy)
  intro v hv
  have hz : dotProduct v (g.hessian.mulVec a) = 0 := by
    have hv' : g.hessian.toBilin' a v = 0 := hv
    rw [Matrix.toBilin'_apply'] at hv'
    rwa [(forward_hessian_isHermitian n g).isSymm.dotProduct_mulVec_comm] at hv'
  have h := hd v
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  nlinarith
theorem positive_directional_derivative_mem_lorentzian :
    ∀ (n d : ℕ), 0 < n → ∀ f : LorentzianPolynomials.H n (d + 1),
      f ∈ LorentzianPolynomials.L n (d + 1) → ∀ a : Fin n → ℝ,
        (∀ i : Fin n, 0 < a i) → ∃ g : LorentzianPolynomials.H n d,
          g.1 = ∑ i : Fin n, a i • (MvPolynomial.pderiv i f.1) ∧
            g ∈ LorentzianPolynomials.L n d := by
  exact positive_directional_derivative_of_cubic_stability directional_cubic_stability
theorem positive_variable_mixing_mem_lorentzian :
    ∀ (n d : ℕ), 0 < n → ∀ t : ℝ, 0 < t →
      ∀ f : LorentzianPolynomials.H n d, f ∈ LorentzianPolynomials.L n d →
      ∀ g : LorentzianPolynomials.H n d,
      g.1 = MvPolynomial.aeval (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C t *
        ∑ j : Fin n, MvPolynomial.X j) f.1 → g ∈ LorentzianPolynomials.L n d := by
  intro n d hn t ht
  apply positive_mixing_preservation_induction n t ht ?_ (positive_support_isMConvex n) ?_ ?_ d
  · intro e
    exact closure_strict_subset_lorentzian n e hn (zero_mem_closure_strict n e hn)
  · intro e f hf hc g hg
    obtain ⟨mix, hcont, hzero, hmix, hpositive⟩ :=
      positive_variable_mixing_curve n e hn f hf hc
    have heq : g = mix t := Subtype.ext (hg.trans (hmix t).symm)
    rw [heq]
    exact hpositive t ht
  · intro e f hf a ha
    exact positive_directional_derivative_mem_lorentzian n e hn f hf a ha
theorem nonzero_lorentzian_mem_closure_positive (n d : ℕ) (hn : 0 < n)
    (f : LorentzianPolynomials.H n (d + 3))
    (hf : f ∈ LorentzianPolynomials.L n (d + 3)) (hzero : f.1 ≠ 0) :
    f ∈ closure (LorentzianPolynomials.L n (d + 3) ∩
      LorentzianPolynomials.P n (d + 3)) := by
  have hcoeff := lorentzian_coefficients_nonnegative n (d + 3) f hf
  obtain ⟨mix, hcont, hzeroMix, hmix, hpositive⟩ :=
    positive_variable_mixing_curve n (d + 3) hn f hzero hcoeff
  have hlim : Filter.Tendsto mix (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds f) := by
    have h := (hcont.tendsto 0).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
    simpa only [hzeroMix] using h
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hL : mix t ∈ LorentzianPolynomials.L n (d + 3) :=
    positive_variable_mixing_mem_lorentzian n (d + 3) hn t ht f hf (mix t) (hmix t)
  exact ⟨hL, hpositive t ht⟩
theorem lorentzian_subset_closure_strict (n d : ℕ) (hn : 0 < n) :
    LorentzianPolynomials.L n d ⊆ closure (LorentzianPolynomials.Ŀ n d) := by
  match d with
  | 0 => exact lorentzian_subset_closure_strict_degree_zero n
  | 1 => exact lorentzian_subset_closure_strict_degree_one n
  | 2 => exact lorentzian_subset_closure_strict_degree_two n hn
  | d + 3 =>
    intro f hf
    by_cases hzero : f.1 = 0
    · have hfzero : f = ⟨0, MvPolynomial.isHomogeneous_zero (Fin n) ℝ (d + 3)⟩ :=
        Subtype.ext hzero
      rw [hfzero]
      exact zero_mem_closure_strict n (d + 3) hn
    · rw [← closure_positive_lorentzian_eq_closure_strict n (d + 3) hn]
      exact nonzero_lorentzian_mem_closure_positive n d hn f hf hzero
theorem closure_strict_eq_lorentzian (n d : ℕ) (hn : 0 < n) :
    closure (LorentzianPolynomials.Ŀ n d) = LorentzianPolynomials.L n d := by
  exact Set.Subset.antisymm (closure_strict_subset_lorentzian n d hn)
    (lorentzian_subset_closure_strict n d hn)
end Submission.Helpers
