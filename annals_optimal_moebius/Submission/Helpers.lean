import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import ChallengeDeps
namespace Submission.Helpers

theorem no_antipodal_square_circle
    (F : unitInterval × unitInterval → Circle) (hF : Continuous F)
    (hdiag : ∀ t : unitInterval, F (t, t) = 1)
    (hedge : ∀ t : unitInterval, F (t, 1) = -F (0, t)) : False := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨θ, ⟨hbase, hlift⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨F, hF⟩ (0, 0) 0 (by simpa using (hdiag 0).symm)
  have hθ : ∀ x, Circle.exp (θ x) = F x := congrFun hlift
  have hdiag_const : θ (1, 1) = θ (0, 0) := by
    apply Circle.isCoveringMap_exp.const_of_comp
      (g := fun t : unitInterval => θ (t, t))
      (by fun_prop) (fun t s => by rw [hθ, hθ, hdiag, hdiag])
  have hedges_const : θ (1, 1) - θ (0, 1) = θ (0, 1) - θ (0, 0) := by
    apply Circle.isCoveringMap_exp.const_of_comp
      (g := fun t : unitInterval => θ (t, 1) - θ (0, t))
      (by fun_prop)
    intro t s
    simp only [Circle.exp_sub, hθ, hedge, neg_div, div_self']
  have hcorner : θ (0, 1) = 0 := by linarith
  have hone : F (0, 1) = 1 := by rw [← hθ, hcorner, Circle.exp_zero]
  have hneg : F (0, 1) = -(1 : Circle) := by rw [hedge, hdiag]
  exact Circle.neg_ne_self (1 : Circle) (hneg.symm.trans hone)
theorem antipodal_square_zero
    (F : unitInterval × unitInterval → ℂ) (hF : Continuous F)
    (hdiag : ∀ t : unitInterval, ∃ r : ℝ, 0 < r ∧ F (t, t) = r)
    (hedge : ∀ t : unitInterval, F (t, 1) = -F (0, t)) :
    ∃ p, F p = 0 := by
  classical
  by_contra hzero
  have hn : ∀ p, F p ≠ 0 := by simpa only [not_exists] using hzero
  let G : unitInterval × unitInterval → Circle := fun p =>
    ⟨F p / (‖F p‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr (hn p))])⟩
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    exact hF.div (Complex.continuous_ofReal.comp hF.norm)
      (fun p => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn p)))
  apply no_antipodal_square_circle G hG
  · intro t
    obtain ⟨r, hr, heq⟩ := hdiag t
    apply Circle.ext
    change F (t, t) / (‖F (t, t)‖ : ℂ) = 1
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      div_self (Complex.ofReal_ne_zero.mpr hr.ne')]
  · intro t
    apply Circle.ext
    change F (t, 1) / (‖F (t, 1)‖ : ℂ) = -(F (0, t) / (‖F (0, t)‖ : ℂ))
    rw [hedge, norm_neg, neg_div]
def scalarTriple (u v w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
    u 2 * (v 0 * w 1 - v 1 * w 0)
theorem orthogonal_coplanar_decomposition
    (u v w : EuclideanSpace ℝ (Fin 3)) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℝ u v = 0) (hcoplanar : scalarTriple w u v = 0) :
    ∃ α β : ℝ, w = α • u + β • v := by
  have hpair : LinearIndependent ℝ ![u, v] := by
    apply (LinearIndependent.pair_iff' hu).mpr
    intro r heq
    have heqv := congrArg (fun z => inner ℝ z v) heq
    simp only [real_inner_smul_left, huv, mul_zero, real_inner_self_eq_norm_sq] at heqv
    exact (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hv))) heqv.symm
  have hwspan : w ∈ Submodule.span ℝ ({u, v} : Set _) := by
    by_contra hnot
    have htriple : LinearIndependent ℝ ![w, u, v] :=
      hpair.finCons (by simpa only [Matrix.range_cons_cons_empty] using hnot)
    let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
    have hplain : LinearIndependent ℝ (e ∘ ![w, u, v]) :=
      htriple.map' e.toLinearMap e.ker
    let A : Matrix (Fin 3) (Fin 3) ℝ :=
      Matrix.of ![WithLp.ofLp w, WithLp.ofLp u, WithLp.ofLp v]
    have hdet : A.det ≠ 0 := by
      apply Matrix.nonsingular_iff_det_ne_zero.mp
      apply Matrix.linearIndependent_row_iff.mp
      convert hplain using 1
      ext i j
      fin_cases i <;> rfl
    have hAdet : A.det = scalarTriple w u v := by
      rw [Matrix.det_fin_three]
      dsimp [A, scalarTriple]
      ring
    exact hdet (hAdet.trans hcoplanar)
  obtain ⟨α, β, heq⟩ := Submodule.mem_span_pair.mp hwspan
  exact ⟨α, β, heq.symm⟩
theorem orthogonal_disjoint_side
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℝ u v = 0)
    (hspan : ∃ α β : ℝ, w = α • u + β • v)
    (hdisjoint : ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      r • u ≠ w + t • v) :
    0 ≤ inner ℝ w v ∨ inner ℝ w v ≤ -(‖v‖ ^ 2) ∨
      ‖u‖ ^ 2 ≤ inner ℝ w u ∨ inner ℝ w u ≤ 0 := by
  by_contra hside
  simp only [not_or, not_le] at hside
  obtain ⟨α, β, hw⟩ := hspan
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have hwv : inner ℝ w v = β * ‖v‖ ^ 2 := by
    rw [hw]
    simp [inner_add_left, real_inner_smul_left, huv]
  have hwu : inner ℝ w u = α * ‖u‖ ^ 2 := by
    rw [hw]
    simp [inner_add_left, real_inner_smul_left, hvu]
  have hu_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hv_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hside.2.2.1, hside.2.2.2]
  have hβ : -β ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> nlinarith [hside.1, hside.2.1]
  apply hdisjoint α hα (-β) hβ
  rw [hw]
  module
theorem coplanar_disjoint_segments_side
    (p₀ p₁ q₀ q₁ : EuclideanSpace ℝ (Fin 3))
    (hp : p₁ ≠ p₀) (hq : q₁ ≠ q₀)
    (hperp : inner ℝ (p₁ - p₀) (q₁ - q₀) = 0)
    (hcoplanar : scalarTriple (q₀ - p₀) (p₁ - p₀) (q₁ - q₀) = 0)
    (hdisjoint : ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      p₀ + r • (p₁ - p₀) ≠ q₀ + t • (q₁ - q₀)) :
    0 ≤ inner ℝ (q₀ - p₀) (q₁ - q₀) ∨
      inner ℝ (q₀ - p₀) (q₁ - q₀) ≤ -(‖q₁ - q₀‖ ^ 2) ∨
      ‖p₁ - p₀‖ ^ 2 ≤ inner ℝ (q₀ - p₀) (p₁ - p₀) ∨
      inner ℝ (q₀ - p₀) (p₁ - p₀) ≤ 0 := by
  apply orthogonal_disjoint_side (p₁ - p₀) (q₁ - q₀) (q₀ - p₀)
    (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hq) hperp
    (orthogonal_coplanar_decomposition (p₁ - p₀) (q₁ - q₀) (q₀ - p₀)
      (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hq) hperp hcoplanar)
  intro r hr t ht heq
  apply hdisjoint r hr t ht
  have h := congrArg (fun z => p₀ + z) heq
  convert h using 1
  module
theorem exists_orthogonal_coplanar_pair
    (c d : unitInterval → EuclideanSpace ℝ (Fin 3))
    (hc : Continuous c) (hd : Continuous d)
    (hclosed : c 1 = c 0) (hreverse : d 1 = -d 0)
    (hne : ∀ t, d t ≠ 0) :
    ∃ s t : unitInterval, inner ℝ (d s) (d t) = 0 ∧
      scalarTriple (c t - c s) (d s) (d t) = 0 := by
  let F : unitInterval × unitInterval → ℂ := fun p =>
    (inner ℝ (d p.1) (d p.2) : ℂ) +
      (scalarTriple (c p.2 - c p.1) (d p.1) (d p.2) : ℂ) * Complex.I
  have hF : Continuous F := by
    dsimp [F, scalarTriple]
    fun_prop
  obtain ⟨⟨s, t⟩, hzero⟩ := antipodal_square_zero F hF
    (fun t => ⟨‖d t‖ ^ 2, sq_pos_of_pos (norm_pos_iff.mpr (hne t)), by
      simp [F, scalarTriple]⟩)
    (fun t => by
      dsimp [F]
      rw [hclosed, hreverse, inner_neg_right, real_inner_comm (d t) (d 0)]
      simp only [scalarTriple, PiLp.sub_apply, PiLp.neg_apply, Complex.ofReal_neg,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
      ring)
  refine ⟨s, t, ?_, ?_⟩
  · have hreal := congrArg Complex.re hzero
    simpa [F] using hreal
  · have himag := congrArg Complex.im hzero
    simpa [F] using himag
theorem exists_ordered_orthogonal_coplanar_pair
    (c d : unitInterval → EuclideanSpace ℝ (Fin 3))
    (hc : Continuous c) (hd : Continuous d)
    (hclosed : c 1 = c 0) (hreverse : d 1 = -d 0)
    (hne : ∀ t, d t ≠ 0) :
    ∃ s t : unitInterval, s < t ∧ inner ℝ (d s) (d t) = 0 ∧
      scalarTriple (c t - c s) (d s) (d t) = 0 := by
  obtain ⟨s, t, hperp, hcoplanar⟩ :=
    exists_orthogonal_coplanar_pair c d hc hd hclosed hreverse hne
  have hst : s ≠ t := by
    intro heq
    subst t
    exact hne s (inner_self_eq_zero.mp hperp)
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact ⟨s, t, hlt, hperp, hcoplanar⟩
  · refine ⟨t, s, hgt, ?_, ?_⟩
    · rwa [real_inner_comm]
    · have heq : scalarTriple (c s - c t) (d t) (d s) =
          scalarTriple (c t - c s) (d s) (d t) := by
        simp only [scalarTriple, PiLp.sub_apply]
        ring
      rwa [heq]
theorem period_mem_unitStrip
    (a : ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ OptimalMoebius.unitStrip) :
    OptimalMoebius.period a x ∈ OptimalMoebius.unitStrip := by
  change 0 ≤ x 0 ∧ x 0 ≤ 1 at hx
  change 0 ≤ 1 - x 0 ∧ 1 - x 0 ≤ 1
  exact ⟨sub_nonneg.mpr hx.2, sub_le_self 1 hx.1⟩
theorem period_twice_invariant
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ OptimalMoebius.unitStrip) :
    f (OptimalMoebius.period a (OptimalMoebius.period a x)) = f x := by
  exact (hf.periodic (OptimalMoebius.period a x) (period_mem_unitStrip a x hx)).trans
    (hf.periodic x hx)
theorem fderivWithin_inner
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ OptimalMoebius.unitStrip)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ ((fderivWithin ℝ f OptimalMoebius.unitStrip x) v)
      ((fderivWithin ℝ f OptimalMoebius.unitStrip x) w) = inner ℝ v w := by
  exact ((fderivWithin ℝ f OptimalMoebius.unitStrip x).toLinearMap.toLinearIsometry
    (hf.isometry x hx)).inner_map_map v w
theorem aspect_ratio_of_squared_budgets (a b : ℝ) (ha : 0 < a)
    (hfirst : 1 + b ^ 2 ≤ (a + b) ^ 2)
    (hsecond : 5 + b ^ 2 < (a - b) ^ 2) :
    Real.sqrt 3 < a := by
  apply (Real.sqrt_lt' ha).2
  nlinarith
theorem orthogonal_offset_strict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v w : E) (huv : inner ℝ u v = 0)
    (hwv : 0 ≤ inner ℝ w v) (hv : 0 < ‖v‖)
    (hw : w ≠ (1 / 2 : ℝ) • u) :
    ‖u‖ ^ 2 + 4 * ‖v‖ ^ 2 < (‖w + v‖ + ‖w + v - u‖) ^ 2 := by
  let X := (1 / 2 : ℝ) • u + v
  let Y := v - (1 / 2 : ℝ) • u
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have hXsq : ‖X‖ ^ 2 = ‖u‖ ^ 2 / 4 + ‖v‖ ^ 2 := by
    dsimp [X]
    rw [norm_add_sq_real]
    simp only [real_inner_smul_left, huv, mul_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hYsq : ‖Y‖ ^ 2 = ‖u‖ ^ 2 / 4 + ‖v‖ ^ 2 := by
    dsimp [Y]
    rw [norm_sub_sq_real]
    simp only [real_inner_smul_right, hvu, mul_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  have hYX : ‖Y‖ = ‖X‖ := by
    nlinarith [norm_nonneg X, norm_nonneg Y]
  have hXpos : 0 < ‖X‖ := by
    nlinarith [norm_nonneg X, sq_nonneg ‖u‖, sq_pos_of_pos hv]
  have hsum_inner :
      inner ℝ (w + v) X + inner ℝ (w + v - u) Y =
        2 * ‖X‖ ^ 2 + 2 * inner ℝ w v := by
    simp only [X, Y, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, huv, hvu]
    nlinarith [hXsq]
  have hc₁ := real_inner_le_norm (w + v) X
  have hc₂ := real_inner_le_norm (w + v - u) Y
  rw [hYX] at hc₂
  have hsum : 2 * ‖X‖ ≤ ‖w + v‖ + ‖w + v - u‖ := by
    nlinarith
  have hsum_strict : 2 * ‖X‖ < ‖w + v‖ + ‖w + v - u‖ := by
    apply lt_of_le_of_ne hsum
    intro heq
    have hwv_zero : inner ℝ w v = 0 := by nlinarith
    have heq₁ : inner ℝ (w + v) X = ‖w + v‖ * ‖X‖ := by nlinarith
    have hparallel := inner_eq_norm_mul_iff_real.mp heq₁
    have hvpair := congrArg (fun z : E => inner ℝ z v) hparallel
    simp only [real_inner_smul_left, inner_add_left, X,
      real_inner_smul_left, huv, hwv_zero, real_inner_self_eq_norm_sq] at hvpair
    have hnormA : ‖w + v‖ = ‖X‖ := by
      nlinarith [sq_pos_of_pos hv]
    rw [hnormA] at hparallel
    have hAX : w + v = X := smul_right_injective E (ne_of_gt hXpos) hparallel
    apply hw
    dsimp [X] at hAX
    exact add_right_cancel hAX
  nlinarith [sq_nonneg (‖w + v‖ + ‖w + v - u‖ - 2 * ‖X‖)]
theorem perpendicular_segments_strict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p₀ p₁ q₀ q₁ : E)
    (hperp : inner ℝ (p₁ - p₀) (q₁ - q₀) = 0)
    (hside : 0 ≤ inner ℝ (q₀ - p₀) (q₁ - q₀))
    (hpositive : 0 < ‖q₁ - q₀‖)
    (hmid : q₀ ≠ (1 / 2 : ℝ) • (p₀ + p₁)) :
    ‖p₁ - p₀‖ ^ 2 + 4 * ‖q₁ - q₀‖ ^ 2 <
      (dist p₀ q₁ + dist q₁ p₁) ^ 2 := by
  have hne : q₀ - p₀ ≠ (1 / 2 : ℝ) • (p₁ - p₀) := by
    intro heq
    apply hmid
    calc
      q₀ = (q₀ - p₀) + p₀ := (sub_add_cancel q₀ p₀).symm
      _ = (1 / 2 : ℝ) • (p₁ - p₀) + p₀ := by rw [heq]
      _ = (1 / 2 : ℝ) • (p₀ + p₁) := by module
  have hA : q₀ - p₀ + (q₁ - q₀) = q₁ - p₀ := by module
  have hB : q₀ - p₀ + (q₁ - q₀) - (p₁ - p₀) = q₁ - p₁ := by module
  have h := orthogonal_offset_strict (p₁ - p₀) (q₁ - q₀) (q₀ - p₀)
    hperp hside hpositive hne
  rw [hB, hA] at h
  simpa only [dist_eq_norm, norm_sub_rev p₀ q₁] using h
theorem aspect_ratio_of_finite_certificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : ℝ) (ha : 0 < a) (p₀ p₁ q₀ q₁ : E)
    (hlength : ‖p₁ - p₀‖ ^ 2 = 1 + b ^ 2)
    (hwidth : 1 ≤ ‖q₁ - q₀‖)
    (hperp : inner ℝ (p₁ - p₀) (q₁ - q₀) = 0)
    (hside : 0 ≤ inner ℝ (q₀ - p₀) (q₁ - q₀))
    (hmid : q₀ ≠ (1 / 2 : ℝ) • (p₀ + p₁))
    (hbudget₀ : dist p₀ q₀ + dist q₀ p₁ ≤ a + b)
    (hbudget₁ : dist p₀ q₁ + dist q₁ p₁ ≤ a - b) :
    Real.sqrt 3 < a := by
  apply aspect_ratio_of_squared_budgets a b ha
  · have htri := dist_triangle p₀ q₀ p₁
    have hnorm : ‖p₁ - p₀‖ ≤ a + b := by
      rw [← dist_eq_norm, dist_comm]
      exact htri.trans hbudget₀
    nlinarith [norm_nonneg (p₁ - p₀)]
  · have hstrict := perpendicular_segments_strict p₀ p₁ q₀ q₁ hperp hside
      (lt_of_lt_of_le zero_lt_one hwidth) hmid
    have hsum_nonneg : 0 ≤ dist p₀ q₁ + dist q₁ p₁ :=
      add_nonneg dist_nonneg dist_nonneg
    nlinarith [sq_nonneg (‖q₁ - q₀‖ - 1)]
theorem aspect_ratio_of_cyclic_certificate
    (a b c : ℝ) (ha : 0 < a)
    (p₀ p₁ q₀ q₁ : EuclideanSpace ℝ (Fin 3))
    (hlengthP : ‖p₁ - p₀‖ ^ 2 = 1 + b ^ 2)
    (hlengthQ : ‖q₁ - q₀‖ ^ 2 = 1 + c ^ 2)
    (hperp : inner ℝ (p₁ - p₀) (q₁ - q₀) = 0)
    (hcoplanar : scalarTriple (q₀ - p₀) (p₁ - p₀) (q₁ - q₀) = 0)
    (hdisjoint : ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      p₀ + r • (p₁ - p₀) ≠ q₀ + t • (q₁ - q₀))
    (hmidP : ∀ q ∈ ({q₀, q₁} : Set _), q ≠ (1 / 2 : ℝ) • (p₀ + p₁))
    (hmidQ : ∀ p ∈ ({p₀, p₁} : Set _), p ≠ (1 / 2 : ℝ) • (q₀ + q₁))
    (hbudget₀ : dist p₀ q₀ + dist q₀ p₁ ≤ a + b)
    (hbudget₁ : dist p₀ q₁ + dist q₁ p₁ ≤ a - b)
    (hbudget₂ : dist q₀ p₁ + dist p₁ q₁ ≤ a + c)
    (hbudget₃ : dist q₀ p₀ + dist p₀ q₁ ≤ a - c) :
    Real.sqrt 3 < a := by
  have hwidthP : 1 ≤ ‖p₁ - p₀‖ := by
    nlinarith [norm_nonneg (p₁ - p₀), sq_nonneg b]
  have hwidthQ : 1 ≤ ‖q₁ - q₀‖ := by
    nlinarith [norm_nonneg (q₁ - q₀), sq_nonneg c]
  have hp : p₁ ≠ p₀ := by
    intro heq
    rw [heq, sub_self, norm_zero] at hwidthP
    norm_num at hwidthP
  have hq : q₁ ≠ q₀ := by
    intro heq
    rw [heq, sub_self, norm_zero] at hwidthQ
    norm_num at hwidthQ
  have hrevP : p₀ - p₁ = -(p₁ - p₀) := by module
  have hrevQ : q₀ - q₁ = -(q₁ - q₀) := by module
  have hvu : inner ℝ (q₁ - q₀) (p₁ - p₀) = 0 := by rw [real_inner_comm, hperp]
  rcases coplanar_disjoint_segments_side p₀ p₁ q₀ q₁ hp hq hperp hcoplanar hdisjoint with
    hside | hside | hside | hside
  · exact aspect_ratio_of_finite_certificate a b ha p₀ p₁ q₀ q₁ hlengthP hwidthQ
      hperp hside (hmidP q₀ (by simp)) hbudget₀ hbudget₁
  · apply aspect_ratio_of_finite_certificate a (-b) ha p₁ p₀ q₁ q₀
    · simpa only [hrevP, norm_neg, neg_sq] using hlengthP
    · simpa only [hrevQ, norm_neg] using hwidthQ
    · simp only [hrevP, hrevQ, inner_neg_left, inner_neg_right, hperp, neg_zero]
    · have hvec : q₁ - p₁ = (q₀ - p₀) + (q₁ - q₀) - (p₁ - p₀) := by module
      rw [hvec, hrevQ]
      rw [inner_neg_right, inner_sub_left, inner_add_left, hperp,
        real_inner_self_eq_norm_sq]
      linarith
    · simpa only [add_comm p₁ p₀] using hmidP q₁ (by simp)
    · simpa only [dist_comm p₁ q₁, dist_comm q₁ p₀, add_comm, sub_eq_add_neg] using hbudget₁
    · simpa only [dist_comm p₁ q₀, dist_comm q₀ p₀, add_comm, sub_neg_eq_add] using hbudget₀
  · apply aspect_ratio_of_finite_certificate a c ha q₀ q₁ p₁ p₀ hlengthQ
    · simpa only [hrevP, norm_neg] using hwidthP
    · simp only [hrevP, inner_neg_right, hvu, neg_zero]
    · have hvec : p₁ - q₀ = (p₁ - p₀) - (q₀ - p₀) := by module
      rw [hvec, hrevP]
      rw [inner_neg_right, inner_sub_left, real_inner_self_eq_norm_sq]
      linarith
    · exact hmidQ p₁ (by simp)
    · exact hbudget₂
    · exact hbudget₃
  · apply aspect_ratio_of_finite_certificate a (-c) ha q₁ q₀ p₀ p₁
    · simpa only [hrevQ, norm_neg, neg_sq] using hlengthQ
    · exact hwidthP
    · simp only [hrevQ, inner_neg_left, hvu, neg_zero]
    · have hvec : p₀ - q₁ = -(q₀ - p₀) - (q₁ - q₀) := by module
      rw [hvec]
      rw [inner_sub_left, inner_neg_left, hvu, sub_zero]
      linarith
    · simpa only [add_comm q₁ q₀] using hmidQ p₀ (by simp)
    · simpa only [dist_comm q₁ p₀, dist_comm p₀ q₀, add_comm, sub_eq_add_neg] using hbudget₃
    · simpa only [dist_comm q₁ p₁, dist_comm p₁ q₀, add_comm, sub_neg_eq_add] using hbudget₂
theorem convex_unitStrip : Convex ℝ OptimalMoebius.unitStrip := by
  intro x hx y hy r s hr hs hrs
  change 0 ≤ x 0 ∧ x 0 ≤ 1 at hx
  change 0 ≤ y 0 ∧ y 0 ≤ 1 at hy
  change 0 ≤ r * x 0 + s * y 0 ∧ r * x 0 + s * y 0 ≤ 1
  constructor
  · exact add_nonneg (mul_nonneg hr hx.1) (mul_nonneg hs hy.1)
  · nlinarith [mul_le_mul_of_nonneg_left hx.2 hr,
      mul_le_mul_of_nonneg_left hy.2 hs]
theorem embedding_dist_le
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x y : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ OptimalMoebius.unitStrip) (hy : y ∈ OptimalMoebius.unitStrip) :
    dist (f x) (f y) ≤ dist x y := by
  have hbound : ∀ z ∈ OptimalMoebius.unitStrip,
      ‖fderivWithin ℝ f OptimalMoebius.unitStrip z‖ ≤ 1 := by
    intro z hz
    apply (fderivWithin ℝ f OptimalMoebius.unitStrip z).opNorm_le_bound (by norm_num)
    intro v
    have hn := (hf.isometry z hz).norm_map_of_map_zero
      (fderivWithin ℝ f OptimalMoebius.unitStrip z).map_zero v
    simpa only [one_mul] using hn.le
  have h := convex_unitStrip.norm_image_sub_le_of_norm_fderivWithin_le
    (hf.smooth.differentiableOn (by simp)) hbound hy hx
  simpa only [one_mul, dist_eq_norm] using h
theorem dist_vertical (c s t : ℝ) :
    dist (!₂[c, s] : EuclideanSpace ℝ (Fin 2)) !₂[c, t] = |s - t| := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs]
theorem boundary_distance_budget
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (c s t r : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hst : s ≤ t) (htr : t ≤ r) :
    dist (f !₂[c, s]) (f !₂[c, t]) + dist (f !₂[c, t]) (f !₂[c, r]) ≤ r - s := by
  have h₁ := embedding_dist_le a f hf !₂[c, s] !₂[c, t] hc hc
  have h₂ := embedding_dist_le a f hf !₂[c, t] !₂[c, r] hc hc
  rw [dist_vertical, abs_of_nonpos (sub_nonpos.mpr hst)] at h₁
  rw [dist_vertical, abs_of_nonpos (sub_nonpos.mpr htr)] at h₂
  linarith
theorem aspect_ratio_of_lifted_certificate
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s b t₀ t₁ : ℝ)
    (horder₀ : s ≤ t₀ ∧ t₀ ≤ s + a + b)
    (horder₁ : s + b ≤ t₁ ∧ t₁ ≤ s + a)
    (hlength : ‖f !₂[1, s + b] - f !₂[0, s]‖ ^ 2 = 1 + b ^ 2)
    (hwidth : 1 ≤ ‖f !₂[1, t₁] - f !₂[0, t₀]‖)
    (hperp : inner ℝ (f !₂[1, s + b] - f !₂[0, s])
      (f !₂[1, t₁] - f !₂[0, t₀]) = 0)
    (hside : 0 ≤ inner ℝ (f !₂[0, t₀] - f !₂[0, s])
      (f !₂[1, t₁] - f !₂[0, t₀]))
    (hmid : f !₂[0, t₀] ≠ (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, s + b])) :
    Real.sqrt 3 < a := by
  have hseam₀ : f !₂[0, s + a + b] = f !₂[1, s + b] := by
    have h := hf.periodic !₂[1, s + b] (by change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1; norm_num)
    simpa [OptimalMoebius.period, add_right_comm s b a] using h
  have hseam₁ : f !₂[1, s + a] = f !₂[0, s] := by
    have h := hf.periodic !₂[0, s] (by change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1; norm_num)
    simpa [OptimalMoebius.period] using h
  apply aspect_ratio_of_finite_certificate a b ha
    (f !₂[0, s]) (f !₂[1, s + b]) (f !₂[0, t₀]) (f !₂[1, t₁])
    hlength hwidth hperp hside hmid
  · have h := boundary_distance_budget a f hf 0 s t₀ (s + a + b)
      (by constructor <;> norm_num) horder₀.1 horder₀.2
    rw [hseam₀] at h
    linarith
  · have h := boundary_distance_budget a f hf 1 (s + b) t₁ (s + a)
      (by constructor <;> norm_num) horder₁.1 horder₁.2
    rw [hseam₁, dist_comm (f !₂[1, s + b]) (f !₂[1, t₁]),
      dist_comm (f !₂[1, t₁]) (f !₂[0, s])] at h
    linarith
theorem affine_segment_image_norm
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (p d : EuclideanSpace ℝ (Fin 2)) (q v : EuclideanSpace ℝ (Fin 3))
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • d ∈ OptimalMoebius.unitStrip)
    (haffine : ∀ t ∈ Set.Icc (0 : ℝ) 1, f (p + t • d) = q + t • v) :
    ‖v‖ = ‖d‖ := by
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hnhds : Set.Icc (0 : ℝ) 1 ∈ nhds (1 / 2 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hd : HasDerivAt (fun t : ℝ => p + t • d) d (1 / 2 : ℝ) := by
    simpa only [one_smul, id_eq] using
      HasDerivAt.const_add p ((hasDerivAt_id (1 / 2 : ℝ)).smul_const d)
  have hv : HasDerivAt (fun t : ℝ => q + t • v) v (1 / 2 : ℝ) := by
    simpa only [one_smul, id_eq] using
      HasDerivAt.const_add q ((hasDerivAt_id (1 / 2 : ℝ)).smul_const v)
  have hDf := ((hf.smooth.differentiableOn (by simp)) _ (hpath _ ht)).hasFDerivWithinAt
  have hcomp := hDf.comp_hasDerivWithinAt (1 / 2 : ℝ) hd.hasDerivWithinAt hpath
  have hcomp' : HasDerivWithinAt (fun t : ℝ => q + t • v)
      ((fderivWithin ℝ f OptimalMoebius.unitStrip (p + (1 / 2 : ℝ) • d)) d)
      (Set.Icc (0 : ℝ) 1) (1 / 2 : ℝ) :=
    hcomp.congr (fun t ht => (haffine t ht).symm) (haffine _ ht).symm
  have hvalue := (hcomp'.hasDerivAt hnhds).unique hv
  have hnorm := (hf.isometry _ (hpath _ ht)).norm_map_of_map_zero
    (fderivWithin ℝ f OptimalMoebius.unitStrip (p + (1 / 2 : ℝ) • d)).map_zero d
  rwa [hvalue] at hnorm
theorem affine_segment_image_dist
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (p r : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ OptimalMoebius.unitStrip) (hr : r ∈ OptimalMoebius.unitStrip)
    (haffine : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f (p + t • (r - p)) = f p + t • (f r - f p)) :
    dist (f p) (f r) = dist p r := by
  have hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • (r - p) ∈ OptimalMoebius.unitStrip := by
    intro t ht
    have h := convex_unitStrip hp hr (sub_nonneg.mpr ht.2) ht.1
      (sub_add_cancel 1 t)
    have heq : (1 - t) • p + t • r = p + t • (r - p) := by module
    rwa [heq] at h
  have hn := affine_segment_image_norm a f hf p (r - p) (f p) (f r - f p)
    hpath haffine
  rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f p) (f r), norm_sub_rev p r]
  exact hn
theorem straight_ruling_length_sq
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s t : ℝ)
    (hstraight : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, s] + r • (!₂[1, t] - !₂[0, s])) =
        f !₂[0, s] + r • (f !₂[1, t] - f !₂[0, s])) :
    ‖f !₂[1, t] - f !₂[0, s]‖ ^ 2 = 1 + (t - s) ^ 2 := by
  have hd := affine_segment_image_dist a f hf !₂[0, s] !₂[1, t]
    (by change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1; norm_num)
    (by change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1; norm_num) hstraight
  have hsq := congrArg (fun x : ℝ => x ^ 2) hd
  rw [dist_eq_norm, norm_sub_rev (f !₂[0, s]) (f !₂[1, t])] at hsq
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two] at hsq
  simp [Real.dist_eq] at hsq
  nlinarith [hsq]
def RulingPair (a : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ s b t₀ t₁ : ℝ,
  (s ≤ t₀ ∧ t₀ ≤ s + a + b) ∧
  (s + b ≤ t₁ ∧ t₁ ≤ s + a) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) 1,
    f (!₂[0, s] + r • (!₂[1, s + b] - !₂[0, s])) =
      f !₂[0, s] + r • (f !₂[1, s + b] - f !₂[0, s])) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) 1,
    f (!₂[0, t₀] + r • (!₂[1, t₁] - !₂[0, t₀])) =
      f !₂[0, t₀] + r • (f !₂[1, t₁] - f !₂[0, t₀])) ∧
  inner ℝ (f !₂[1, s + b] - f !₂[0, s]) (f !₂[1, t₁] - f !₂[0, t₀]) = 0 ∧
  0 ≤ inner ℝ (f !₂[0, t₀] - f !₂[0, s]) (f !₂[1, t₁] - f !₂[0, t₀]) ∧
  f !₂[0, t₀] ≠ (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, s + b])
theorem aspect_ratio_of_ruling_pair
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c : RulingPair a f) :
    Real.sqrt 3 < a := by
  rcases c with ⟨s, b, t₀, t₁, horder₀, horder₁, hstraight₀, hstraight₁,
    hperp, hside, hmid⟩
  have hlength := straight_ruling_length_sq a f hf s (s + b) hstraight₀
  have hwidth_sq := straight_ruling_length_sq a f hf t₀ t₁ hstraight₁
  have hwidth : 1 ≤ ‖f !₂[1, t₁] - f !₂[0, t₀]‖ := by
    nlinarith [norm_nonneg (f !₂[1, t₁] - f !₂[0, t₀]), sq_nonneg (t₁ - t₀)]
  apply aspect_ratio_of_lifted_certificate a ha f hf s b t₀ t₁
    horder₀ horder₁ ?_ hwidth hperp hside hmid
  simpa only [add_sub_cancel_left] using hlength
theorem vertical_periodic
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Function.Periodic (fun t : ℝ => f !₂[c, t]) (2 * a) := by
  intro t
  have h := period_twice_invariant a f hf !₂[c, t] hc
  simpa [OptimalMoebius.period, two_mul, add_assoc] using h
theorem exists_fundamental_representative
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c s : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ d t : ℝ, (d = c ∨ d = 1 - c) ∧ t ∈ Set.Ico (0 : ℝ) a ∧
      f !₂[d, t] = f !₂[c, s] := by
  obtain ⟨m, hm, _⟩ := existsUnique_sub_zsmul_mem_Ico (by linarith : 0 < 2 * a) s 0
  let t : ℝ := s - m • (2 * a)
  have ht₀ : 0 ≤ t := hm.1
  have ht₂ : t < 2 * a := by simpa only [zero_add] using hm.2
  have hvalue : f !₂[c, t] = f !₂[c, s] :=
    (vertical_periodic a f hf c hc).sub_zsmul_eq m
  by_cases ht : t < a
  · exact ⟨c, t, Or.inl rfl, ⟨ht₀, ht⟩, hvalue⟩
  · refine ⟨1 - c, t - a, Or.inr rfl, ⟨by linarith, by linarith⟩, ?_⟩
    have hstrip : (!₂[1 - c, t - a] : EuclideanSpace ℝ (Fin 2)) ∈
        OptimalMoebius.unitStrip := by
      change 0 ≤ 1 - c ∧ 1 - c ≤ 1
      constructor <;> linarith [hc.1, hc.2]
    have hperiod := hf.periodic !₂[1 - c, t - a] hstrip
    have heq : f !₂[c, t] = f !₂[1 - c, t - a] := by
      simpa [OptimalMoebius.period] using hperiod
    exact heq.symm.trans hvalue
theorem boundary_image_ne_interior
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c d s t : ℝ)
    (hc : c = 0 ∨ c = 1) (hd : 0 < d ∧ d < 1) :
    f !₂[c, s] ≠ f !₂[d, t] := by
  have hcstrip : c ∈ Set.Icc (0 : ℝ) 1 := by rcases hc with rfl | rfl <;> norm_num
  obtain ⟨c', s', hc', hs', hfcs⟩ := exists_fundamental_representative a ha f hf c s hcstrip
  obtain ⟨d', t', hd', ht', hfdt⟩ :=
    exists_fundamental_representative a ha f hf d t ⟨hd.1.le, hd.2.le⟩
  have hc'boundary : c' = 0 ∨ c' = 1 := by
    rcases hc' with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num
  have hd'interior : 0 < d' ∧ d' < 1 := by
    rcases hd' with rfl | rfl
    · exact hd
    · constructor <;> linarith [hd.1, hd.2]
  intro heq
  have hpoints := hf.embedding (show !₂[c', s'] ∈ OptimalMoebius.fundamentalDomain a from
      ⟨by rcases hc'boundary with rfl | rfl <;> norm_num, hs'⟩)
    (show !₂[d', t'] ∈ OptimalMoebius.fundamentalDomain a from
      ⟨⟨hd'interior.1.le, hd'interior.2.le⟩, ht'⟩)
    (hfcs.trans (heq.trans hfdt.symm))
  have hcoord : c' = d' := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hpoints
  rcases hc'boundary with hzero | hone <;> linarith [hd'interior.1, hd'interior.2]
theorem straight_ruling_not_midpoint
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s b t : ℝ)
    (hstraight : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, s] + r • (!₂[1, s + b] - !₂[0, s])) =
        f !₂[0, s] + r • (f !₂[1, s + b] - f !₂[0, s])) :
    f !₂[0, t] ≠ (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, s + b]) := by
  have hpoint : (!₂[0, s] : EuclideanSpace ℝ (Fin 2)) +
      (1 / 2 : ℝ) • (!₂[1, s + b] - !₂[0, s]) = !₂[1 / 2, s + b / 2] := by
    ext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
  have hmidimage := hstraight (1 / 2 : ℝ) (by constructor <;> norm_num)
  rw [hpoint] at hmidimage
  have hvalue : f !₂[1 / 2, s + b / 2] =
      (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, s + b]) := by
    rw [hmidimage]
    module
  intro heq
  apply boundary_image_ne_interior a ha f hf 0 (1 / 2) t (s + b / 2)
    (Or.inl rfl) (by constructor <;> norm_num)
  exact heq.trans hvalue.symm
theorem aspect_ratio_of_straight_pair
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s b t₀ t₁ : ℝ)
    (horder₀ : s ≤ t₀ ∧ t₀ ≤ s + a + b)
    (horder₁ : s + b ≤ t₁ ∧ t₁ ≤ s + a)
    (hstraight₀ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, s] + r • (!₂[1, s + b] - !₂[0, s])) =
        f !₂[0, s] + r • (f !₂[1, s + b] - f !₂[0, s]))
    (hstraight₁ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, t₀] + r • (!₂[1, t₁] - !₂[0, t₀])) =
        f !₂[0, t₀] + r • (f !₂[1, t₁] - f !₂[0, t₀]))
    (hperp : inner ℝ (f !₂[1, s + b] - f !₂[0, s])
      (f !₂[1, t₁] - f !₂[0, t₀]) = 0)
    (hside : 0 ≤ inner ℝ (f !₂[0, t₀] - f !₂[0, s])
      (f !₂[1, t₁] - f !₂[0, t₀])) :
    Real.sqrt 3 < a := by
  apply aspect_ratio_of_ruling_pair a ha f hf
  exact ⟨s, b, t₀, t₁, horder₀, horder₁, hstraight₀, hstraight₁, hperp, hside,
    straight_ruling_not_midpoint a ha f hf s b t₀ hstraight₀⟩
theorem boundary_period_values
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s : ℝ) :
    f !₂[0, s + a] = f !₂[1, s] ∧ f !₂[1, s + a] = f !₂[0, s] := by
  constructor
  · simpa [OptimalMoebius.period] using hf.periodic !₂[1, s]
      (show !₂[1, s] ∈ OptimalMoebius.unitStrip from ⟨by norm_num, by norm_num⟩)
  · simpa [OptimalMoebius.period] using hf.periodic !₂[0, s]
      (show !₂[0, s] ∈ OptimalMoebius.unitStrip from ⟨by norm_num, by norm_num⟩)
theorem cyclic_boundary_budgets
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (L R : unitInterval → ℝ) (hL : Monotone L) (hR : Monotone R)
    (hseamL : L 1 = R 0 + a) (hseamR : R 1 = L 0 + a)
    (s t : unitInterval) (hst : s ≤ t) :
    (dist (f !₂[0, L s]) (f !₂[0, L t]) +
      dist (f !₂[0, L t]) (f !₂[1, R s]) ≤ a + (R s - L s)) ∧
    (dist (f !₂[0, L s]) (f !₂[1, R t]) +
      dist (f !₂[1, R t]) (f !₂[1, R s]) ≤ a - (R s - L s)) ∧
    (dist (f !₂[0, L t]) (f !₂[1, R s]) +
      dist (f !₂[1, R s]) (f !₂[1, R t]) ≤ a + (R t - L t)) ∧
    (dist (f !₂[0, L t]) (f !₂[0, L s]) +
      dist (f !₂[0, L s]) (f !₂[1, R t]) ≤ a - (R t - L t)) := by
  have hLsLt : L s ≤ L t := hL hst
  have hRsRt : R s ≤ R t := hR hst
  have hLtRs : L t ≤ R s + a := by
    have h₁ := hL (show t ≤ 1 from t.2.2)
    have h₂ := hR (show 0 ≤ s from s.2.1)
    rw [hseamL] at h₁
    linarith
  have hRtLs : R t ≤ L s + a := by
    have h₁ := hR (show t ≤ 1 from t.2.2)
    have h₂ := hL (show 0 ≤ s from s.2.1)
    rw [hseamR] at h₁
    linarith
  have h₀ := boundary_distance_budget a f hf 0 (L s) (L t) (R s + a)
    (by norm_num) hLsLt hLtRs
  rw [(boundary_period_values a f hf (R s)).1] at h₀
  have h₁ := boundary_distance_budget a f hf 1 (R s) (R t) (L s + a)
    (by norm_num) hRsRt hRtLs
  rw [(boundary_period_values a f hf (L s)).2,
    dist_comm (f !₂[1, R s]) (f !₂[1, R t]),
    dist_comm (f !₂[1, R t]) (f !₂[0, L s])] at h₁
  have h₂ := boundary_distance_budget a f hf 0 (L t) (R s + a) (R t + a)
    (by norm_num) hLtRs (by linarith)
  rw [(boundary_period_values a f hf (R s)).1,
    (boundary_period_values a f hf (R t)).1] at h₂
  have h₃ := boundary_distance_budget a f hf 1 (R t) (L s + a) (L t + a)
    (by norm_num) hRtLs (by linarith)
  rw [(boundary_period_values a f hf (L s)).2,
    (boundary_period_values a f hf (L t)).2,
    dist_comm (f !₂[1, R t]) (f !₂[0, L s]),
    dist_comm (f !₂[0, L s]) (f !₂[0, L t])] at h₃
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
theorem straight_ruling_boundary_not_midpoint
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (s t c u : ℝ)
    (hc : c = 0 ∨ c = 1)
    (hstraight : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, s] + r • (!₂[1, t] - !₂[0, s])) =
        f !₂[0, s] + r • (f !₂[1, t] - f !₂[0, s])) :
    f !₂[c, u] ≠ (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, t]) := by
  have hmid : ∀ v : ℝ, f !₂[0, v] ≠
      (1 / 2 : ℝ) • (f !₂[0, s] + f !₂[1, t]) := by
    intro v
    simpa only [show s + (t - s) = t by ring] using
      straight_ruling_not_midpoint a ha f hf s (t - s) v
        (by simpa only [show s + (t - s) = t by ring] using hstraight)
  rcases hc with rfl | rfl
  · exact hmid u
  · rw [← (boundary_period_values a f hf u).1]
    exact hmid (u + a)
theorem exists_fundamental_representative_with_shift
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c s : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∃ d t : ℝ, ∃ n : ℤ, t ∈ Set.Ico (0 : ℝ) a ∧
      f !₂[d, t] = f !₂[c, s] ∧
      ((d = c ∧ s - t = (n : ℝ) * (2 * a)) ∨
        (d = 1 - c ∧ s - t = (2 * (n : ℝ) + 1) * a)) := by
  obtain ⟨m, hm, _⟩ := existsUnique_sub_zsmul_mem_Ico (by linarith : 0 < 2 * a) s 0
  let t : ℝ := s - m • (2 * a)
  have ht₀ : 0 ≤ t := hm.1
  have ht₂ : t < 2 * a := by simpa only [zero_add] using hm.2
  have hvalue : f !₂[c, t] = f !₂[c, s] :=
    (vertical_periodic a f hf c hc).sub_zsmul_eq m
  have htdef : s - t = (m : ℝ) * (2 * a) := by dsimp [t]; simp
  by_cases ht : t < a
  · exact ⟨c, t, m, ⟨ht₀, ht⟩, hvalue, Or.inl ⟨rfl, htdef⟩⟩
  · refine ⟨1 - c, t - a, m, ⟨by linarith, by linarith⟩, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · have hstrip : (!₂[1 - c, t - a] : EuclideanSpace ℝ (Fin 2)) ∈
          OptimalMoebius.unitStrip := by
        change 0 ≤ 1 - c ∧ 1 - c ≤ 1
        constructor <;> linarith [hc.1, hc.2]
      have hperiod := hf.periodic !₂[1 - c, t - a] hstrip
      have heq : f !₂[c, t] = f !₂[1 - c, t - a] := by
        simpa [OptimalMoebius.period] using hperiod
      exact heq.symm.trans hvalue
    · nlinarith [htdef]
theorem embedding_fiber_classification
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (c d s t : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (heq : f !₂[c, s] = f !₂[d, t]) :
    (c = d ∧ ∃ n : ℤ, s - t = (n : ℝ) * (2 * a)) ∨
      (c = 1 - d ∧ ∃ n : ℤ, s - t = (2 * (n : ℝ) + 1) * a) := by
  obtain ⟨c', s', m, hs', hcs, hshiftS⟩ :=
    exists_fundamental_representative_with_shift a ha f hf c s hc
  obtain ⟨d', t', n, ht', hdt, hshiftT⟩ :=
    exists_fundamental_representative_with_shift a ha f hf d t hd
  have hc' : c' ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hshiftS with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hc
    · constructor <;> linarith [hc.1, hc.2]
  have hd' : d' ∈ Set.Icc (0 : ℝ) 1 := by
    rcases hshiftT with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hd
    · constructor <;> linarith [hd.1, hd.2]
  have hpoints := hf.embedding
    (show !₂[c', s'] ∈ OptimalMoebius.fundamentalDomain a from ⟨hc', hs'⟩)
    (show !₂[d', t'] ∈ OptimalMoebius.fundamentalDomain a from ⟨hd', ht'⟩)
    (hcs.trans (heq.trans hdt.symm))
  have hcoord₀ : c' = d' := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hpoints
  have hcoord₁ : s' = t' := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hpoints
  rcases hshiftS with ⟨hcs', hs⟩ | ⟨hcs', hs⟩ <;>
    rcases hshiftT with ⟨hdt', ht⟩ | ⟨hdt', ht⟩
  · refine Or.inl ⟨by linarith, m - n, ?_⟩
    simp only [Int.cast_sub]
    nlinarith [hs, ht]
  · refine Or.inr ⟨by linarith, m - n - 1, ?_⟩
    simp only [Int.cast_sub, Int.cast_one]
    nlinarith [hs, ht]
  · refine Or.inr ⟨by linarith, m - n, ?_⟩
    simp only [Int.cast_sub]
    nlinarith [hs, ht]
  · refine Or.inl ⟨by linarith, m - n, ?_⟩
    simp only [Int.cast_sub]
    nlinarith [hs, ht]
theorem ordered_ruling_fiber_endpoints
    (a l₀ r₀ l₁ r₁ x y : ℝ) (ha : 0 < a)
    (hL : l₀ ≤ l₁) (hR : r₀ ≤ r₁)
    (hcrossL : l₁ ≤ r₀ + a) (hcrossR : r₁ ≤ l₀ + a)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1)
    (hrelated :
      (x = y ∧ ∃ n : ℤ,
        (l₀ + x * (r₀ - l₀)) - (l₁ + y * (r₁ - l₁)) = (n : ℝ) * (2 * a)) ∨
      (x = 1 - y ∧ ∃ n : ℤ,
        (l₀ + x * (r₀ - l₀)) - (l₁ + y * (r₁ - l₁)) =
          (2 * (n : ℝ) + 1) * a)) :
    (l₀ = l₁ ∧ r₀ = r₁) ∨ (l₁ = r₀ + a ∧ r₁ = l₀ + a) := by
  have hx' : 0 < 1 - x := sub_pos.mpr hx.2
  have hLgap : 0 ≤ l₁ - l₀ := sub_nonneg.mpr hL
  have hRgap : 0 ≤ r₁ - r₀ := sub_nonneg.mpr hR
  rcases hrelated with ⟨rfl, n, hn⟩ | ⟨hxy, n, hn⟩
  · have hdelta_nonneg : 0 ≤ (l₁ + x * (r₁ - l₁)) - (l₀ + x * (r₀ - l₀)) := by
      nlinarith [mul_nonneg hx'.le hLgap, mul_nonneg hx.1.le hRgap]
    have hdelta_lt : (l₁ + x * (r₁ - l₁)) - (l₀ + x * (r₀ - l₀)) < 2 * a := by
      by_contra hnot
      have hremaining : x * (l₁ - l₀) + (1 - x) * (r₁ - r₀) ≤ 0 := by nlinarith
      have hlzero : l₁ - l₀ = 0 := by
        by_contra hne
        have hpos : 0 < l₁ - l₀ := lt_of_le_of_ne hLgap (Ne.symm hne)
        nlinarith [mul_pos hx.1 hpos, mul_nonneg hx'.le hRgap]
      have hrzero : r₁ - r₀ = 0 := by
        by_contra hne
        have hpos : 0 < r₁ - r₀ := lt_of_le_of_ne hRgap (Ne.symm hne)
        nlinarith [mul_nonneg hx.1.le hLgap, mul_pos hx' hpos]
      nlinarith
    have hnlow : (-1 : ℝ) < (n : ℝ) := by nlinarith
    have hnup : (n : ℝ) ≤ 0 := by nlinarith
    have hnlow' : (-1 : ℤ) < n := by exact_mod_cast hnlow
    have hnup' : n ≤ 0 := by exact_mod_cast hnup
    have hnzero : n = 0 := by omega
    subst n
    norm_num at hn
    refine Or.inl ⟨?_, ?_⟩
    · apply le_antisymm hL
      by_contra hnot
      have hpos : 0 < l₁ - l₀ := by linarith
      nlinarith [mul_pos hx' hpos, mul_nonneg hx.1.le hRgap]
    · apply le_antisymm hR
      by_contra hnot
      have hpos : 0 < r₁ - r₀ := by linarith
      nlinarith [mul_nonneg hx'.le hLgap, mul_pos hx.1 hpos]
  · have hyx : y = 1 - x := by linarith
    rw [hyx] at hn
    have hwidth₀ : 0 ≤ a + (r₀ - l₀) := by linarith
    have hwidth₁ : 0 ≤ a - (r₀ - l₀) := by linarith
    have hdelta_lower : -a <
        (l₁ + (1 - x) * (r₁ - l₁)) - (l₀ + x * (r₀ - l₀)) := by
      have hpositive : 0 < (1 - x) * (a + (r₀ - l₀)) + x * (a - (r₀ - l₀)) := by
        by_cases hw : 0 ≤ r₀ - l₀
        · nlinarith [mul_pos hx' (by linarith : 0 < a + (r₀ - l₀)),
            mul_nonneg hx.1.le hwidth₁]
        · nlinarith [mul_pos hx.1 (by linarith : 0 < a - (r₀ - l₀)),
            mul_nonneg hx'.le hwidth₀]
      nlinarith [mul_nonneg hx.1.le hLgap, mul_nonneg hx'.le hRgap]
    have hdelta_upper :
        (l₁ + (1 - x) * (r₁ - l₁)) - (l₀ + x * (r₀ - l₀)) ≤ a := by
      nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hcrossL),
        mul_nonneg hx'.le (sub_nonneg.mpr hcrossR)]
    have hnlow : (-1 : ℝ) ≤ (n : ℝ) := by nlinarith
    have hnup : (n : ℝ) < 0 := by nlinarith
    have hnlow' : (-1 : ℤ) ≤ n := by exact_mod_cast hnlow
    have hnup' : n < 0 := by exact_mod_cast hnup
    have hnneg : n = -1 := by omega
    subst n
    norm_num at hn
    refine Or.inr ⟨?_, ?_⟩
    · apply le_antisymm hcrossL
      by_contra hnot
      have hpos : 0 < r₀ + a - l₁ := by linarith
      nlinarith [mul_pos hx.1 hpos, mul_nonneg hx'.le (sub_nonneg.mpr hcrossR)]
    · apply le_antisymm hcrossR
      by_contra hnot
      have hpos : 0 < l₀ + a - r₁ := by linarith
      nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hcrossL), mul_pos hx' hpos]
theorem ordered_perpendicular_rulings_disjoint
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (l₀ r₀ l₁ r₁ : ℝ)
    (hL : l₀ ≤ l₁) (hR : r₀ ≤ r₁)
    (hcrossL : l₁ ≤ r₀ + a) (hcrossR : r₁ ≤ l₀ + a)
    (hstraight₀ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, l₀] + r • (!₂[1, r₀] - !₂[0, l₀])) =
        f !₂[0, l₀] + r • (f !₂[1, r₀] - f !₂[0, l₀]))
    (hstraight₁ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, l₁] + r • (!₂[1, r₁] - !₂[0, l₁])) =
        f !₂[0, l₁] + r • (f !₂[1, r₁] - f !₂[0, l₁]))
    (hperp : inner ℝ (f !₂[1, r₀] - f !₂[0, l₀])
      (f !₂[1, r₁] - f !₂[0, l₁]) = 0) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      f !₂[0, l₀] + x • (f !₂[1, r₀] - f !₂[0, l₀]) ≠
        f !₂[0, l₁] + y • (f !₂[1, r₁] - f !₂[0, l₁]) := by
  intro x hx y hy heq
  have hcoord₀ : (!₂[0, l₀] : EuclideanSpace ℝ (Fin 2)) +
      x • (!₂[1, r₀] - !₂[0, l₀]) = !₂[x, l₀ + x * (r₀ - l₀)] := by
    ext i
    fin_cases i <;> simp
  have hcoord₁ : (!₂[0, l₁] : EuclideanSpace ℝ (Fin 2)) +
      y • (!₂[1, r₁] - !₂[0, l₁]) = !₂[y, l₁ + y * (r₁ - l₁)] := by
    ext i
    fin_cases i <;> simp
  have hsource : f !₂[x, l₀ + x * (r₀ - l₀)] = f !₂[y, l₁ + y * (r₁ - l₁)] := by
    rw [← hcoord₀, ← hcoord₁, hstraight₀ x ⟨hx.1.le, hx.2.le⟩,
      hstraight₁ y ⟨hy.1.le, hy.2.le⟩]
    exact heq
  have hrelated := embedding_fiber_classification a ha f hf x y
    (l₀ + x * (r₀ - l₀)) (l₁ + y * (r₁ - l₁))
    ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hsource
  have hdne : f !₂[1, r₀] - f !₂[0, l₀] ≠ 0 := by
    intro hzero
    have hlength := straight_ruling_length_sq a f hf l₀ r₀ hstraight₀
    rw [hzero, norm_zero] at hlength
    nlinarith [sq_nonneg (r₀ - l₀)]
  rcases ordered_ruling_fiber_endpoints a l₀ r₀ l₁ r₁ x y ha hL hR hcrossL hcrossR
    hx hy hrelated with ⟨hLsame, hRsame⟩ | ⟨hLperiod, hRperiod⟩
  · rw [← hLsame, ← hRsame] at hperp
    exact hdne (inner_self_eq_zero.mp hperp)
  · rw [hLperiod, hRperiod, (boundary_period_values a f hf l₀).2,
      (boundary_period_values a f hf r₀).1] at hperp
    have hreverse : f !₂[0, l₀] - f !₂[1, r₀] =
        -(f !₂[1, r₀] - f !₂[0, l₀]) := by module
    rw [hreverse, inner_neg_right] at hperp
    exact hdne (inner_self_eq_zero.mp (neg_eq_zero.mp hperp))
def CyclicRulingFamily (a : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ L R : unitInterval → ℝ,
    Continuous L ∧ Continuous R ∧ Monotone L ∧ Monotone R ∧
    L 1 = R 0 + a ∧ R 1 = L 0 + a ∧
    (∀ t : unitInterval, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, L t] + r • (!₂[1, R t] - !₂[0, L t])) =
        f !₂[0, L t] + r • (f !₂[1, R t] - f !₂[0, L t])) ∧
    (∀ s t : unitInterval, s < t → (s ≠ 0 ∨ t ≠ 1) →
      ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        f !₂[0, L s] + r • (f !₂[1, R s] - f !₂[0, L s]) ≠
          f !₂[0, L t] + u • (f !₂[1, R t] - f !₂[0, L t]))
theorem aspect_ratio_of_ordered_straight_family
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (L R : unitInterval → ℝ) (hLcont : Continuous L) (hRcont : Continuous R)
    (hLmono : Monotone L) (hRmono : Monotone R)
    (hseamL : L 1 = R 0 + a) (hseamR : R 1 = L 0 + a)
    (hstraight : ∀ t : unitInterval, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, L t] + r • (!₂[1, R t] - !₂[0, L t])) =
        f !₂[0, L t] + r • (f !₂[1, R t] - f !₂[0, L t])) :
    Real.sqrt 3 < a := by
  let P : unitInterval → EuclideanSpace ℝ (Fin 3) := fun t => f !₂[0, L t]
  let Q : unitInterval → EuclideanSpace ℝ (Fin 3) := fun t => f !₂[1, R t]
  have hPcont : Continuous P := by
    apply hf.smooth.continuousOn.comp_continuous (by fun_prop)
    intro t
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1
    norm_num
  have hQcont : Continuous Q := by
    apply hf.smooth.continuousOn.comp_continuous (by fun_prop)
    intro t
    change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1
    norm_num
  have hPseam : P 1 = Q 0 := by
    dsimp [P, Q]
    rw [hseamL, (boundary_period_values a f hf (R 0)).1]
  have hQseam : Q 1 = P 0 := by
    dsimp [P, Q]
    rw [hseamR, (boundary_period_values a f hf (L 0)).2]
  let c : unitInterval → EuclideanSpace ℝ (Fin 3) := fun t => (1 / 2 : ℝ) • (P t + Q t)
  let d : unitInterval → EuclideanSpace ℝ (Fin 3) := fun t => Q t - P t
  have hc : Continuous c := by fun_prop
  have hd : Continuous d := by fun_prop
  have hcclosed : c 1 = c 0 := by
    dsimp [c]
    rw [hPseam, hQseam]
    module
  have hdreverse : d 1 = -d 0 := by
    dsimp [d]
    rw [hPseam, hQseam]
    module
  have hdne : ∀ t, d t ≠ 0 := by
    intro t heq
    have hlength := straight_ruling_length_sq a f hf (L t) (R t) (hstraight t)
    change ‖d t‖ ^ 2 = 1 + (R t - L t) ^ 2 at hlength
    rw [heq, norm_zero] at hlength
    nlinarith [sq_nonneg (R t - L t)]
  obtain ⟨s, t, hst, hperp, hcoplanar⟩ :=
    exists_ordered_orthogonal_coplanar_pair c d hc hd hcclosed hdreverse hdne
  have hcoplanar' : scalarTriple (P t - P s) (d s) (d t) = 0 := by
    have hcenter : scalarTriple (c t - c s) (d s) (d t) =
        scalarTriple (P t - P s) (d s) (d t) := by
      dsimp [c, d, scalarTriple]
      ring
    rwa [hcenter] at hcoplanar
  have hmidP : ∀ q ∈ ({P t, Q t} : Set _), q ≠ (1 / 2 : ℝ) • (P s + Q s) := by
    intro q hq
    rcases hq with rfl | hq
    · exact straight_ruling_boundary_not_midpoint a ha f hf (L s) (R s) 0 (L t)
        (Or.inl rfl) (hstraight s)
    · have heq : q = Q t := Set.mem_singleton_iff.mp hq
      rw [heq]
      exact straight_ruling_boundary_not_midpoint a ha f hf (L s) (R s) 1 (R t)
        (Or.inr rfl) (hstraight s)
  have hmidQ : ∀ p ∈ ({P s, Q s} : Set _), p ≠ (1 / 2 : ℝ) • (P t + Q t) := by
    intro p hp
    rcases hp with rfl | hp
    · exact straight_ruling_boundary_not_midpoint a ha f hf (L t) (R t) 0 (L s)
        (Or.inl rfl) (hstraight t)
    · have heq : p = Q s := Set.mem_singleton_iff.mp hp
      rw [heq]
      exact straight_ruling_boundary_not_midpoint a ha f hf (L t) (R t) 1 (R s)
        (Or.inr rfl) (hstraight t)
  obtain ⟨hbudget₀, hbudget₁, hbudget₂, hbudget₃⟩ :=
    cyclic_boundary_budgets a f hf L R hLmono hRmono hseamL hseamR s t hst.le
  have hcrossL : L t ≤ R s + a := by
    have h₁ := hLmono (show t ≤ 1 from t.2.2)
    have h₂ := hRmono (show 0 ≤ s from s.2.1)
    rw [hseamL] at h₁
    linarith
  have hcrossR : R t ≤ L s + a := by
    have h₁ := hRmono (show t ≤ 1 from t.2.2)
    have h₂ := hLmono (show 0 ≤ s from s.2.1)
    rw [hseamR] at h₁
    linarith
  have hdisjoint := ordered_perpendicular_rulings_disjoint a ha f hf
    (L s) (R s) (L t) (R t) (hLmono hst.le) (hRmono hst.le) hcrossL hcrossR
    (hstraight s) (hstraight t) hperp
  exact aspect_ratio_of_cyclic_certificate a (R s - L s) (R t - L t) ha
    (P s) (Q s) (P t) (Q t)
    (straight_ruling_length_sq a f hf (L s) (R s) (hstraight s))
    (straight_ruling_length_sq a f hf (L t) (R t) (hstraight t))
    hperp hcoplanar' hdisjoint hmidP hmidQ
    hbudget₀ hbudget₁ hbudget₂ hbudget₃
theorem aspect_ratio_of_cyclic_ruling_family
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (g : CyclicRulingFamily a f) :
    Real.sqrt 3 < a := by
  obtain ⟨L, R, hLcont, hRcont, hLmono, hRmono, hseamL, hseamR, hstraight, _⟩ := g
  exact aspect_ratio_of_ordered_straight_family a ha f hf L R hLcont hRcont
    hLmono hRmono hseamL hseamR hstraight
def OrderedStraightFamily (a : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ L R : unitInterval → ℝ,
    Continuous L ∧ Continuous R ∧ Monotone L ∧ Monotone R ∧
    L 1 = R 0 + a ∧ R 1 = L 0 + a ∧
    ∀ t : unitInterval, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, L t] + r • (!₂[1, R t] - !₂[0, L t])) =
        f !₂[0, L t] + r • (f !₂[1, R t] - f !₂[0, L t])
theorem aspect_ratio_of_ordered_straight_family_certificate
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (g : OrderedStraightFamily a f) :
    Real.sqrt 3 < a := by
  obtain ⟨L, R, hLcont, hRcont, hLmono, hRmono, hseamL, hseamR, hstraight⟩ := g
  exact aspect_ratio_of_ordered_straight_family a ha f hf L R hLcont hRcont
    hLmono hRmono hseamL hseamR hstraight
theorem period_twice_eq_longitudinal
    (a : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    OptimalMoebius.period a (OptimalMoebius.period a x) = x + !₂[0, a + a] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [OptimalMoebius.period]
  ring
theorem affine_generator_transverse
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ OptimalMoebius.unitStrip)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hline : ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      f (x + t • v) = f x + t • (fderivWithin ℝ f OptimalMoebius.unitStrip x) v) :
    v 0 ≠ 0 := by
  intro hv0
  have hv1 : v 1 ≠ 0 := by
    intro h
    apply hv
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hv0, h]
  have ht : (a + a) / v 1 ≠ 0 := div_ne_zero (ne_of_gt (add_pos ha ha)) hv1
  have hperiod :
      OptimalMoebius.period a (OptimalMoebius.period a x) =
        x + ((a + a) / v 1) • v := by
    rw [period_twice_eq_longitudinal]
    congr 1
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [hv0, hv1]
  have hmem : x + ((a + a) / v 1) • v ∈ OptimalMoebius.unitStrip := by
    rw [← hperiod]
    exact period_mem_unitStrip a _ (period_mem_unitStrip a x hx)
  have heq : f x + ((a + a) / v 1) •
      (fderivWithin ℝ f OptimalMoebius.unitStrip x) v = f x := by
    rw [← hline _ hmem, ← hperiod]
    exact period_twice_invariant a f hf x hx
  have hz : ((a + a) / v 1) •
      (fderivWithin ℝ f OptimalMoebius.unitStrip x) v = 0 :=
    (add_eq_left.mp heq)
  have hd : (fderivWithin ℝ f OptimalMoebius.unitStrip x) v = 0 :=
    (smul_eq_zero.mp hz).resolve_left ht
  apply hv
  apply (hf.isometry x hx).injective
  simpa using hd
theorem exists_spanning_ruling_of_affine_generator
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hline : ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      f (x + t • v) = f x + t • (fderivWithin ℝ f OptimalMoebius.unitStrip x) v) :
    ∃ l r : ℝ, x = (!₂[0, l] + (x 0) • (!₂[1, r] - !₂[0, l])) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l]) := by
  have hxstrip : x ∈ OptimalMoebius.unitStrip := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hv0 : v 0 ≠ 0 := affine_generator_transverse a ha f hf x hxstrip v hv hline
  let l : ℝ := x 1 + ((0 - x 0) / v 0) * v 1
  let r : ℝ := x 1 + ((1 - x 0) / v 0) * v 1
  have hparam (u : ℝ) :
      !₂[0, l] + u • (!₂[1, r] - !₂[0, l]) = x + ((u - x 0) / v 0) • v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [l, r] <;> field_simp <;> ring
  have hmem (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      x + ((u - x 0) / v 0) • v ∈ OptimalMoebius.unitStrip := by
    rw [← hparam]
    simpa [OptimalMoebius.unitStrip] using hu
  have hfparam (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
        f x + ((u - x 0) / v 0) • (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
    rw [hparam]
    exact hline _ (hmem u hu)
  refine ⟨l, r, ?_, ?_⟩
  · rw [hparam]
    simp
  · intro u hu
    have h0 := hfparam 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hfparam 1 ⟨zero_le_one, le_rfl⟩
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel] at h0 h1
    rw [hfparam u hu, h0, h1]
    module
theorem affine_generator_of_constant_directional_derivative
    (a : ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ OptimalMoebius.unitStrip)
    (v : EuclideanSpace ℝ (Fin 2))
    (hconst : ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
        (fderivWithin ℝ f OptimalMoebius.unitStrip x) v) :
    ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      f (x + t • v) = f x + t • (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  let s : Set ℝ := {t | x + t • v ∈ OptimalMoebius.unitStrip}
  let d := (fderivWithin ℝ f OptimalMoebius.unitStrip x) v
  have hs : Convex ℝ s := by
    intro t ht u hu c e hc he hce
    change 0 ≤ x 0 + t * v 0 ∧ x 0 + t * v 0 ≤ 1 at ht
    change 0 ≤ x 0 + u * v 0 ∧ x 0 + u * v 0 ≤ 1 at hu
    change 0 ≤ x 0 + (c * t + e * u) * v 0 ∧
      x 0 + (c * t + e * u) * v 0 ≤ 1
    have hcomb : x 0 + (c * t + e * u) * v 0 =
        c * (x 0 + t * v 0) + e * (x 0 + u * v 0) := by
      calc
        _ = (c + e) * x 0 + (c * t + e * u) * v 0 := by rw [hce]; ring
        _ = _ := by ring
    rw [hcomb]
    refine ⟨add_nonneg (mul_nonneg hc ht.1) (mul_nonneg he hu.1), ?_⟩
    simpa only [mul_one, hce] using
      add_le_add (mul_le_mul_of_nonneg_left ht.2 hc) (mul_le_mul_of_nonneg_left hu.2 he)
  have hzero : (0 : ℝ) ∈ s := by simpa [s] using hx
  have hdiff := hf.smooth.differentiableOn (by simp)
  have hderiv (t : ℝ) (ht : t ∈ s) :
      HasDerivWithinAt (fun u : ℝ => f (x + u • v) - u • d) 0 s t := by
    have hline : HasDerivAt (fun u : ℝ => x + u • v) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x)
    have hcomp := (hdiff _ ht).hasFDerivWithinAt.comp_hasDerivWithinAt t
      hline.hasDerivWithinAt (fun _ h => h)
    change HasDerivWithinAt (fun u : ℝ => f (x + u • v))
      ((fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v) s t at hcomp
    rw [hconst t ht] at hcomp
    have hmodel : HasDerivAt (fun u : ℝ => u • d) d t := by
      simpa using (hasDerivAt_id t).smul_const d
    convert hcomp.sub hmodel.hasDerivWithinAt using 1
    simp [d]
  intro t ht
  have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ => le_rfl) hzero ht
  have heq : (f (x + t • v) - t • d) - (f (x + (0 : ℝ) • v) - (0 : ℝ) • d) = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hbound) (norm_nonneg _)
  have hfinal : f (x + t • v) - t • d = f x := by
    simpa using sub_eq_zero.mp heq
  exact (sub_eq_iff_eq_add.mp hfinal)
theorem exists_spanning_ruling_of_constant_directional_derivative
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hconst : ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
        (fderivWithin ℝ f OptimalMoebius.unitStrip x) v) :
    ∃ l r : ℝ, x = (!₂[0, l] + (x 0) • (!₂[1, r] - !₂[0, l])) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l]) := by
  exact exists_spanning_ruling_of_affine_generator a ha f hf x hx v hv
    (affine_generator_of_constant_directional_derivative a f hf x
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩ v hconst)
theorem straight_segment_of_preserved_distance
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (p q : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ OptimalMoebius.unitStrip) (hq : q ∈ OptimalMoebius.unitStrip)
    (hdist : dist (f p) (f q) = dist p q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (p + t • (q - p)) = f p + t • (f q - f p) := by
  let z := p + t • (q - p)
  have hz : z ∈ OptimalMoebius.unitStrip := by
    have h := convex_unitStrip hp hq (sub_nonneg.mpr ht.2) ht.1
      (sub_add_cancel 1 t)
    convert h using 1
    dsimp [z]
    module
  have hpz : dist p z = t * dist p q := by
    simp only [z, dist_eq_norm, show p - (p + t • (q - p)) = -t • (q - p) by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1, norm_sub_rev p q]
  have hzq : dist z q = (1 - t) * dist p q := by
    simp only [z, dist_eq_norm,
      show p + t • (q - p) - q = (1 - t) • (p - q) by module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hleft := embedding_dist_le a f hf p z hp hz
  have hright := embedding_dist_le a f hf z q hz hq
  rw [hpz] at hleft
  rw [hzq] at hright
  have htri := dist_triangle (f p) (f z) (f q)
  rw [hdist] at htri
  have heq₀ : dist (f p) (f z) = t * dist (f p) (f q) := by rw [hdist]; linarith
  have heq₁ : dist (f z) (f q) = (1 - t) * dist (f p) (f q) := by rw [hdist]; linarith
  have heq := eq_lineMap_of_dist_eq_mul_of_dist_eq_mul heq₀ heq₁
  simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using heq
theorem affine_isometry_segment_of_endpoint_values
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hD : Isometry D) (b : EuclideanSpace ℝ (Fin 3))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ OptimalMoebius.unitStrip) (hq : q ∈ OptimalMoebius.unitStrip)
    (hfp : f p = b + D p) (hfq : f q = b + D q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (p + t • (q - p)) = b + D (p + t • (q - p)) := by
  have hdist : dist (f p) (f q) = dist p q := by
    rw [hfp, hfq, dist_add_left]
    exact hD.dist_eq p q
  rw [straight_segment_of_preserved_distance a f hf p q hp hq hdist t ht, hfp, hfq]
  simp only [map_add, map_smul, map_sub]
  module
theorem affine_segment_endpoint_values_at_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (p q : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ OptimalMoebius.unitStrip) (hq : q ∈ OptimalMoebius.unitStrip)
    (hstraight : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      f (p + t • (q - p)) = f p + t • (f q - f p))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    let x := p + t • (q - p)
    let D := fderivWithin ℝ f OptimalMoebius.unitStrip x
    f p = (f x - D x) + D p ∧ f q = (f x - D x) + D q := by
  let x := p + t • (q - p)
  let D := fderivWithin ℝ f OptimalMoebius.unitStrip x
  have hpath (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      p + s • (q - p) ∈ OptimalMoebius.unitStrip := by
    have h := convex_unitStrip hp hq (sub_nonneg.mpr hs.2) hs.1
      (sub_add_cancel 1 s)
    convert h using 1
    module
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (fun s : ℝ => p + s • (q - p)) (q - p) t := by
    simpa using ((hasDerivAt_id t).smul_const (q - p)).const_add p
  have hv : HasDerivAt (fun s : ℝ => f p + s • (f q - f p)) (f q - f p) t := by
    simpa using ((hasDerivAt_id t).smul_const (f q - f p)).const_add (f p)
  have hDf := ((hf.smooth.differentiableOn (by simp)) _ (hpath t htcc)).hasFDerivWithinAt
  have hcomp := hDf.comp_hasDerivWithinAt t hd.hasDerivWithinAt hpath
  have hcomp' : HasDerivWithinAt (fun s : ℝ => f p + s • (f q - f p))
      (D (q - p)) (Set.Icc (0 : ℝ) 1) t :=
    hcomp.congr (fun s hs => (hstraight s hs).symm) (hstraight t htcc).symm
  have hvalue : D (q - p) = f q - f p :=
    (hcomp'.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).unique hv
  have hximage : f x = f p + t • (f q - f p) := hstraight t htcc
  have hxD : D x = D p + t • (f q - f p) := by
    dsimp [x]
    rw [map_add, map_smul, hvalue]
  change f p = (f x - D x) + D p ∧ f q = (f x - D x) + D q
  rw [hximage, hxD]
  have hvalue' : D q - D p = f q - f p := by simpa only [map_sub] using hvalue
  constructor
  · module
  · calc
      f q = f p + (D q - D p) := by rw [hvalue']; module
      _ = _ := by module
theorem affine_isometry_vertical_interval_of_endpoint_values
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hD : Isometry D) (b : EuclideanSpace ℝ (Fin 3))
    (c s t : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hst : s < t)
    (hfs : f !₂[c, s] = b + D !₂[c, s])
    (hft : f !₂[c, t] = b + D !₂[c, t])
    (v : ℝ) (hv : v ∈ Set.Icc s t) :
    f !₂[c, v] = b + D !₂[c, v] := by
  let z : ℝ := (v - s) / (t - s)
  have hz : z ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr hst).le
    · exact (div_le_one (sub_pos.mpr hst)).mpr (by linarith [hv.2])
  have hparam : (!₂[c, s] : EuclideanSpace ℝ (Fin 2)) +
      z • (!₂[c, t] - !₂[c, s]) = !₂[c, v] := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp
    · simp [z, ne_of_gt (sub_pos.mpr hst)]
  have h := affine_isometry_segment_of_endpoint_values a f hf D hD b
    !₂[c, s] !₂[c, t] hc hc hfs hft z hz
  rwa [hparam] at h
theorem crossed_straight_rulings_rectangle
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) (l0 r0 l1 r1 : ℝ)
    (hstraight0 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, l0] + u • (!₂[1, r0] - !₂[0, l0])) =
        f !₂[0, l0] + u • (f !₂[1, r0] - f !₂[0, l0]))
    (hstraight1 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, l1] + u • (!₂[1, r1] - !₂[0, l1])) =
        f !₂[0, l1] + u • (f !₂[1, r1] - f !₂[0, l1]))
    (hL : l0 < l1) (hR : r1 < r0)
    (l : ℝ) (hl : l ∈ Set.Icc l0 l1) (r : ℝ) (hr : r ∈ Set.Icc r1 r0)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
      f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l]) := by
  let p0 : EuclideanSpace ℝ (Fin 2) := !₂[0, l0]
  let q0 : EuclideanSpace ℝ (Fin 2) := !₂[1, r0]
  let p1 : EuclideanSpace ℝ (Fin 2) := !₂[0, l1]
  let q1 : EuclideanSpace ℝ (Fin 2) := !₂[1, r1]
  let d : ℝ := l1 - l0 + (r0 - r1)
  have hd : 0 < d := by dsimp [d]; linarith
  let t : ℝ := (l1 - l0) / d
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hL) hd
    · exact (div_lt_one hd).mpr (by dsimp [d]; linarith)
  have hcross : p0 + t • (q0 - p0) = p1 + t • (q1 - p1) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [p0, q0, p1, q1]
    · change l0 + t * (r0 - l0) = l1 + t * (r1 - l1)
      dsimp [t]
      field_simp [ne_of_gt hd]
      dsimp [d]
      ring
  let x := p0 + t • (q0 - p0)
  let D := fderivWithin ℝ f OptimalMoebius.unitStrip x
  let b := f x - D x
  have hx : x ∈ OptimalMoebius.unitStrip := by
    simpa [x, p0, q0, OptimalMoebius.unitStrip] using
      (show t ∈ Set.Icc (0 : ℝ) 1 from ⟨ht.1.le, ht.2.le⟩)
  have hD : Isometry D := hf.isometry x hx
  have hv0 : f p0 = b + D p0 ∧ f q0 = b + D q0 :=
    affine_segment_endpoint_values_at_interior a f hf p0 q0
      (by change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1; norm_num)
      (by change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1; norm_num)
      hstraight0 t ht
  have hv1 : f p1 = b + D p1 ∧ f q1 = b + D q1 := by
    have h := affine_segment_endpoint_values_at_interior a f hf p1 q1
      (by change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1; norm_num)
      (by change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1; norm_num)
      hstraight1 t ht
    dsimp only at h
    rw [← hcross] at h
    exact h
  have hfl : f !₂[0, l] = b + D !₂[0, l] :=
    affine_isometry_vertical_interval_of_endpoint_values a f hf D hD b 0 l0 l1
      (by constructor <;> norm_num) hL hv0.1 hv1.1 l hl
  have hfr : f !₂[1, r] = b + D !₂[1, r] :=
    affine_isometry_vertical_interval_of_endpoint_values a f hf D hD b 1 r1 r0
      (by constructor <;> norm_num) hR hv1.2 hv0.2 r hr
  have hdist : dist (f !₂[0, l]) (f !₂[1, r]) =
      dist (!₂[0, l] : EuclideanSpace ℝ (Fin 2)) !₂[1, r] := by
    rw [hfl, hfr, dist_add_left]
    exact hD.dist_eq _ _
  exact straight_segment_of_preserved_distance a f hf !₂[0, l] !₂[1, r]
    (by change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1; norm_num)
    (by change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1; norm_num) hdist u hu
theorem endpoint_fiber_convex
    (K : Set (ℝ × ℝ))
    (hrect : ∀ l0 r0 l1 r1 : ℝ, (l0, r0) ∈ K → (l1, r1) ∈ K →
      l0 < l1 → r1 < r0 → ∀ l ∈ Set.Icc l0 l1, ∀ r ∈ Set.Icc r1 r0, (l, r) ∈ K)
    (c : ℝ) : Convex ℝ {l : ℝ | (l, 2 * c - l) ∈ K} := by
  apply convex_iff_ordConnected.mpr
  constructor
  intro l0 hl0 l1 hl1 l hl
  change (l, 2 * c - l) ∈ K
  by_cases heq : l0 = l1
  · have : l = l0 := by linarith [hl.1, hl.2]
    simpa [this] using hl0
  · have hlt : l0 < l1 := lt_of_le_of_ne (hl.1.trans hl.2) heq
    exact hrect l0 (2 * c - l0) l1 (2 * c - l1) hl0 hl1 hlt
      (by linarith) l hl (2 * c - l) ⟨by linarith [hl.2], by linarith [hl.1]⟩
theorem exists_endpoint_fiber_variational
    (K : Set (ℝ × ℝ)) (hclosed : IsClosed K)
    (hspan : ∀ c : ℝ, ∃ l r : ℝ, (l, r) ∈ K ∧ l + r = 2 * c)
    (hrect : ∀ l0 r0 l1 r1 : ℝ, (l0, r0) ∈ K → (l1, r1) ∈ K →
      l0 < l1 → r1 < r0 → ∀ l ∈ Set.Icc l0 l1, ∀ r ∈ Set.Icc r1 r0, (l, r) ∈ K)
    (c : ℝ) : ∃ l : ℝ, (l, 2 * c - l) ∈ K ∧
      ∀ v : ℝ, (v, 2 * c - v) ∈ K → (c - l) * (v - l) ≤ 0 := by
  let S : Set ℝ := {l | (l, 2 * c - l) ∈ K}
  have hSclosed : IsClosed S := hclosed.preimage (by fun_prop)
  have hSne : S.Nonempty := by
    obtain ⟨l, r, hlr, heq⟩ := hspan c
    refine ⟨l, ?_⟩
    have hr : r = 2 * c - l := by linarith
    simpa [S, hr] using hlr
  have hSconv : Convex ℝ S := endpoint_fiber_convex K hrect c
  obtain ⟨l, hl, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hSne
    hSclosed.isComplete hSconv c
  refine ⟨l, hl, ?_⟩
  intro v hv
  have h := (norm_eq_iInf_iff_real_inner_le_zero hSconv hl).mp hmin v hv
  simpa only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
    mul_comm] using h
theorem endpoint_variational_unique
    (K : Set (ℝ × ℝ)) (c l m : ℝ)
    (hl : (l, 2 * c - l) ∈ K) (hm : (m, 2 * c - m) ∈ K)
    (hoptl : ∀ v : ℝ, (v, 2 * c - v) ∈ K → (c - l) * (v - l) ≤ 0)
    (hoptm : ∀ v : ℝ, (v, 2 * c - v) ∈ K → (c - m) * (v - m) ≤ 0) :
    l = m := by
  have h₀ := hoptl m hm
  have h₁ := hoptm l hl
  have hsq : (l - m) ^ 2 = 0 := by nlinarith [sq_nonneg (l - m)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
theorem endpoint_variational_not_crossed
    (K : Set (ℝ × ℝ))
    (hrect : ∀ l0 r0 l1 r1 : ℝ, (l0, r0) ∈ K → (l1, r1) ∈ K →
      l0 < l1 → r1 < r0 → ∀ l ∈ Set.Icc l0 l1, ∀ r ∈ Set.Icc r1 r0, (l, r) ∈ K)
    (c0 c1 l0 r0 l1 r1 : ℝ)
    (h₀ : (l0, r0) ∈ K) (h₁ : (l1, r1) ∈ K)
    (hsum₀ : l0 + r0 = 2 * c0) (hsum₁ : l1 + r1 = 2 * c1)
    (hopt₀ : ∀ v : ℝ, (v, 2 * c0 - v) ∈ K → (c0 - l0) * (v - l0) ≤ 0)
    (hopt₁ : ∀ v : ℝ, (v, 2 * c1 - v) ∈ K → (c1 - l1) * (v - l1) ≤ 0)
    (hL : l0 < l1) (hR : r1 < r0) : False := by
  let δ : ℝ := min (l1 - l0) (r0 - r1)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hL) (sub_pos.mpr hR)
  have hδL : δ ≤ l1 - l0 := min_le_left _ _
  have hδR : δ ≤ r0 - r1 := min_le_right _ _
  have hmem₀ : (l0 + δ, 2 * c0 - (l0 + δ)) ∈ K := by
    apply hrect l0 r0 l1 r1 h₀ h₁ hL hR
    · constructor <;> linarith
    · constructor <;> linarith
  have hmem₁ : (l1 - δ, 2 * c1 - (l1 - δ)) ∈ K := by
    apply hrect l0 r0 l1 r1 h₀ h₁ hL hR
    · constructor <;> linarith
    · constructor <;> linarith
  have ho₀ := hopt₀ (l0 + δ) hmem₀
  have ho₁ := hopt₁ (l1 - δ) hmem₁
  have hc₀ : c0 ≤ l0 := by
    by_contra h
    have hpos := mul_pos (by linarith : 0 < c0 - l0) hδ
    nlinarith
  have hc₁ : l1 ≤ c1 := by
    by_contra h
    have hpos := mul_pos (by linarith : 0 < l1 - c1) hδ
    nlinarith
  linarith
theorem lipschitz_two_of_monotone_sum
    (L R : ℝ → ℝ) (hL : Monotone L) (hR : Monotone R)
    (hsum : ∀ c : ℝ, L c + R c = 2 * c) : LipschitzWith 2 L := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  change dist (L c) (L d) ≤ (2 : ℝ) * dist c d
  rcases le_total c d with hcd | hdc
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hL hcd)),
      abs_of_nonpos (sub_nonpos.mpr hcd)]
    linarith [hsum c, hsum d, hR hcd]
  · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hL hdc)),
      abs_of_nonneg (sub_nonneg.mpr hdc)]
    linarith [hsum c, hsum d, hR hdc]
theorem ordered_endpoints_of_closed_relation
    (a : ℝ) (K : Set (ℝ × ℝ)) (hclosed : IsClosed K)
    (hspan : ∀ c : ℝ, ∃ l r : ℝ, (l, r) ∈ K ∧ l + r = 2 * c)
    (hrect : ∀ l0 r0 l1 r1 : ℝ, (l0, r0) ∈ K → (l1, r1) ∈ K →
      l0 < l1 → r1 < r0 → ∀ l ∈ Set.Icc l0 l1, ∀ r ∈ Set.Icc r1 r0, (l, r) ∈ K)
    (hperiod : ∀ l r : ℝ, (l, r) ∈ K ↔ (r + a, l + a) ∈ K) :
    ∃ L R : ℝ → ℝ, LipschitzWith 2 L ∧ LipschitzWith 2 R ∧ Monotone L ∧ Monotone R ∧
      (∀ c : ℝ, L c + R c = 2 * c) ∧ (∀ c : ℝ, (L c, R c) ∈ K) ∧
      (∀ c : ℝ, L (c + a) = R c + a) ∧ (∀ c : ℝ, R (c + a) = L c + a) := by
  classical
  let L : ℝ → ℝ := fun c =>
    Classical.choose (exists_endpoint_fiber_variational K hclosed hspan hrect c)
  let R : ℝ → ℝ := fun c => 2 * c - L c
  have hspec (c : ℝ) : (L c, 2 * c - L c) ∈ K ∧
      ∀ v : ℝ, (v, 2 * c - v) ∈ K → (c - L c) * (v - L c) ≤ 0 :=
    Classical.choose_spec (exists_endpoint_fiber_variational K hclosed hspan hrect c)
  have hsum (c : ℝ) : L c + R c = 2 * c := by dsimp [R]; ring
  have hmem (c : ℝ) : (L c, R c) ∈ K := (hspec c).1
  have hopt (c v : ℝ) (hv : (v, 2 * c - v) ∈ K) :
      (c - L c) * (v - L c) ≤ 0 := (hspec c).2 v hv
  have hL : Monotone L := by
    intro c d hcd
    by_contra h
    have hLc : L d < L c := lt_of_not_ge h
    have hRc : R c < R d := by linarith [hsum c, hsum d]
    exact endpoint_variational_not_crossed K hrect d c (L d) (R d) (L c) (R c)
      (hmem d) (hmem c) (hsum d) (hsum c) (hopt d) (hopt c) hLc hRc
  have hR : Monotone R := by
    intro c d hcd
    by_contra h
    have hRc : R d < R c := lt_of_not_ge h
    have hLc : L c < L d := by linarith [hsum c, hsum d]
    exact endpoint_variational_not_crossed K hrect c d (L c) (R c) (L d) (R d)
      (hmem c) (hmem d) (hsum c) (hsum d) (hopt c) (hopt d) hLc hRc
  have hseamL (c : ℝ) : L (c + a) = R c + a := by
    have hm : (R c + a, 2 * (c + a) - (R c + a)) ∈ K := by
      have heq : 2 * (c + a) - (R c + a) = L c + a := by linarith [hsum c]
      rw [heq]
      exact (hperiod (L c) (R c)).mp (hmem c)
    have hoptm (v : ℝ) (hv : (v, 2 * (c + a) - v) ∈ K) :
        ((c + a) - (R c + a)) * (v - (R c + a)) ≤ 0 := by
      have hv' : (2 * c + a - v, 2 * c - (2 * c + a - v)) ∈ K := by
        apply (hperiod (2 * c + a - v) (2 * c - (2 * c + a - v))).mpr
        have heq₀ : 2 * c - (2 * c + a - v) + a = v := by ring
        have heq₁ : 2 * c + a - v + a = 2 * (c + a) - v := by ring
        rw [heq₀, heq₁]
        exact hv
      have h := hopt c (2 * c + a - v) hv'
      have heq : ((c + a) - (R c + a)) * (v - (R c + a)) =
          (c - L c) * ((2 * c + a - v) - L c) := by dsimp [R]; ring
      rwa [heq]
    exact endpoint_variational_unique K (c + a) (L (c + a)) (R c + a)
      (hspec (c + a)).1 hm (hopt (c + a)) hoptm
  have hseamR (c : ℝ) : R (c + a) = L c + a := by
    linarith [hsum (c + a), hsum c, hseamL c]
  exact ⟨L, R, lipschitz_two_of_monotone_sum L R hL hR hsum,
    lipschitz_two_of_monotone_sum R L hR hL (fun c => by linarith [hsum c]),
    hL, hR, hsum, hmem, hseamL, hseamR⟩
theorem unitStrip_mem_nhds_of_interior
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    OptimalMoebius.unitStrip ∈ nhds x := by
  have h := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.preimage_mem_nhds
    (Ioo_mem_nhds hx.1 hx.2)
  exact Filter.mem_of_superset h (fun y hy => ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
theorem embedding_contDiffAt_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    ContDiffAt ℝ n f x := by
  exact ((hf.smooth x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).contDiffAt
    (unitStrip_mem_nhds_of_interior x hx)).of_le (by simp)
theorem fderiv_inner_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ ((fderiv ℝ f x) v) ((fderiv ℝ f x) w) = inner ℝ v w := by
  rw [← fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_interior x hx)]
  exact fderivWithin_inner a f hf x ⟨le_of_lt hx.1, le_of_lt hx.2⟩ v w
theorem fderiv_clm_apply_const_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun y => (fderiv ℝ f y) v) x w =
      fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((embedding_contDiffAt_interior a f hf x hx 2).fderiv_right
    (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simp [fderiv_clm_apply hd (differentiableAt_const v)]
theorem metric_derivative_zero_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ ((fderiv ℝ f x) v) (fderiv ℝ (fderiv ℝ f) x u w) +
      inner ℝ (fderiv ℝ (fderiv ℝ f) x u v) ((fderiv ℝ f x) w) = 0 := by
  have hd := ((embedding_contDiffAt_interior a f hf x hx 2).fderiv_right
    (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (fun y => inner ℝ ((fderiv ℝ f y) v) ((fderiv ℝ f y) w)) =ᶠ[nhds x]
      (fun _ => inner ℝ v w) := by
    filter_upwards [(PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.preimage_mem_nhds
      (Ioo_mem_nhds hx.1 hx.2)] with y hy
    exact fderiv_inner_interior a f hf y hy v w
  have hzero := congrArg (fun L => L u) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_inner_apply ℝ (hd.clm_apply (differentiableAt_const v))
    (hd.clm_apply (differentiableAt_const w)) u,
    fderiv_clm_apply_const_interior a f hf x hx w u,
    fderiv_clm_apply_const_interior a f hf x hx v u] at hzero
  simpa using hzero
theorem hessian_normal_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (fderiv ℝ (fderiv ℝ f) x u v) ((fderiv ℝ f x) w) = 0 := by
  have hs := (embedding_contDiffAt_interior a f hf x hx 2).isSymmSndFDerivAt
    (by norm_num)
  have h1 := metric_derivative_zero_interior a f hf x hx u v w
  have h2 := metric_derivative_zero_interior a f hf x hx v w u
  have h3 := metric_derivative_zero_interior a f hf x hx w u v
  rw [real_inner_comm] at h1 h2 h3
  rw [hs.eq u w] at h1
  rw [hs.eq v u] at h2
  rw [hs.eq w v] at h3
  linarith
theorem hessian_gauss_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (fderiv ℝ (fderiv ℝ f) x v w) (fderiv ℝ (fderiv ℝ f) x u z) =
      inner ℝ (fderiv ℝ (fderiv ℝ f) x u w) (fderiv ℝ (fderiv ℝ f) x v z) := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ f) x :=
    (embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (by norm_num)
  have hd := hD.differentiableAt two_ne_zero
  have hH := (hD.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hH_apply (p q r : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ f) y p) q) x r =
        fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x r p q := by
    simp [fderiv_clm_apply (hH.clm_apply (differentiableAt_const p))
      (differentiableAt_const q), fderiv_clm_apply hH (differentiableAt_const p)]
  have hprod (p q r s : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ (fderiv ℝ (fderiv ℝ f) x p q) (fderiv ℝ (fderiv ℝ f) x r s) +
        inner ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x r p q) ((fderiv ℝ f x) s) = 0 := by
    have heq : (fun y => inner ℝ (fderiv ℝ (fderiv ℝ f) y p q) ((fderiv ℝ f y) s))
        =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds hx.1 hx.2)] with y hy
      exact hessian_normal_interior a f hf y hy p q s
    have hzero := congrArg (fun L => L r) (heq.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_inner_apply ℝ
      ((hH.clm_apply (differentiableAt_const p)).clm_apply (differentiableAt_const q))
      (hd.clm_apply (differentiableAt_const s)) r,
      hH_apply p q r, fderiv_clm_apply_const_interior a f hf x hx s r] at hzero
    simpa using hzero
  have hsym := hD.isSymmSndFDerivAt (by norm_num)
  have h1 := hprod v w u z
  have h2 := hprod u w v z
  have hthird := congrArg (fun L => L w) (hsym.eq u v)
  rw [hthird] at h1
  linarith
theorem hessian_collinear_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (p q : EuclideanSpace ℝ (Fin 2))
    (hpq : fderiv ℝ (fderiv ℝ f) x p q ≠ 0)
    (u v : EuclideanSpace ℝ (Fin 2)) :
    ∃ c : ℝ, fderiv ℝ (fderiv ℝ f) x u v = c • fderiv ℝ (fderiv ℝ f) x p q := by
  let K := (fderiv ℝ f x).toLinearMap.range
  have hDI : Function.Injective (fderiv ℝ f x) := by
    rw [← fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_interior x hx)]
    exact (hf.isometry x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).injective
  have hdimK : Module.finrank ℝ K = 2 := by
    simpa [K] using LinearMap.finrank_range_of_inj hDI
  have hdimN : Module.finrank ℝ K.orthogonal = 1 := by
    have hdim := K.finrank_add_finrank_orthogonal
    rw [hdimK] at hdim
    have hamb : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [hamb] at hdim
    omega
  have hnormal (r s : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ (fderiv ℝ f) x r s ∈ K.orthogonal := by
    rw [K.mem_orthogonal']
    intro y hy
    obtain ⟨w, rfl⟩ := hy
    exact hessian_normal_interior a f hf x hx r s w
  have heq := eq_span_singleton_of_mem_of_finrank_eq_one hdimN (hnormal p q) hpq
  have hmem := hnormal u v
  rw [heq, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩
theorem exists_hessian_kernel_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ w : EuclideanSpace ℝ (Fin 2), fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  let H := fderiv ℝ (fderiv ℝ f) x
  let e0 : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
  let e1 : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
  have hdecomp (w : EuclideanSpace ℝ (Fin 2)) : w = w 0 • e0 + w 1 • e1 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [e0, e1]
  have hs := (embedding_contDiffAt_interior a f hf x hx 2).isSymmSndFDerivAt
    (by norm_num)
  have hsym (p q : EuclideanSpace ℝ (Fin 2)) : H p q = H q p := hs.eq p q
  have hG : inner ℝ (H e0 e1) (H e0 e1) = inner ℝ (H e0 e0) (H e1 e1) := by
    have h := hessian_gauss_interior a f hf x hx e0 e1 e0 e1
    change inner ℝ (H e1 e0) (H e0 e1) = inner ℝ (H e0 e0) (H e1 e1) at h
    simpa only [hsym e1 e0] using h
  by_cases h00 : H e0 e0 = 0
  · have h01 : H e0 e1 = 0 := by
      rw [h00, inner_zero_left] at hG
      exact inner_self_eq_zero.mp hG
    refine ⟨e0, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
      simp [e0] at hc
    · intro w
      change H e0 w = 0
      rw [hdecomp w, map_add, map_smul, map_smul, h00, h01]
      simp
  · obtain ⟨c, hc⟩ := hessian_collinear_interior a f hf x hx e0 e0 h00 e0 e1
    obtain ⟨d, hd⟩ := hessian_collinear_interior a f hf x hx e0 e0 h00 e1 e1
    change H e0 e1 = c • H e0 e0 at hc
    change H e1 e1 = d • H e0 e0 at hd
    have hn : inner ℝ (H e0 e0) (H e0 e0) ≠ 0 := inner_self_ne_zero.mpr h00
    have hdc : d = c * c := by
      apply mul_right_cancel₀ hn
      rw [hc, hd, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right] at hG
      simpa [mul_assoc] using hG.symm
    let v : EuclideanSpace ℝ (Fin 2) := !₂[-c, 1]
    have hvform : v = (-c) • e0 + e1 := by
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [v, e0, e1]
    have hv0 : H v e0 = 0 := by
      rw [hvform]
      simp only [map_add, map_smul, add_apply, smul_apply]
      rw [hsym e1 e0, hc]
      module
    have hv1 : H v e1 = 0 := by
      rw [hvform]
      simp only [map_add, map_smul, add_apply, smul_apply]
      rw [hc, hd, hdc]
      module
    refine ⟨v, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simp [v] at hc
    · intro w
      change H v w = 0
      rw [hdecomp w, map_add, map_smul, map_smul, hv0, hv1]
      simp
theorem convex_interior_line_parameters
    (x v : EuclideanSpace ℝ (Fin 2)) :
    Convex ℝ {t : ℝ | (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1} := by
  intro t ht u hu c e hc he hce
  change x 0 + t * v 0 ∈ Set.Ioo (0 : ℝ) 1 at ht
  change x 0 + u * v 0 ∈ Set.Ioo (0 : ℝ) 1 at hu
  change x 0 + (c * t + e * u) * v 0 ∈ Set.Ioo (0 : ℝ) 1
  have hcomb : x 0 + (c * t + e * u) * v 0 =
      c * (x 0 + t * v 0) + e * (x 0 + u * v 0) := by
    calc
      _ = (c + e) * x 0 + (c * t + e * u) * v 0 := by rw [hce]; ring
      _ = _ := by ring
  rw [hcomb]
  exact convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1 ht hu hc he hce
theorem constant_directional_derivative_interior_of_zero_hessian
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2))
    (hzero : ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v = 0) :
    ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      (fderiv ℝ f (x + t • v)) v = (fderiv ℝ f x) v := by
  let s : Set ℝ := {t | (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1}
  have hs : Convex ℝ s := convex_interior_line_parameters x v
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using hx
  have hderiv (t : ℝ) (ht : t ∈ s) :
      HasDerivWithinAt (fun u : ℝ => (fderiv ℝ f (x + u • v)) v) 0 s t := by
    have hd := ((embedding_contDiffAt_interior a f hf (x + t • v) ht 2).fderiv_right
      (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have heval := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v (x + t • v))
    have hline : HasDerivAt (fun u : ℝ => x + u • v) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x)
    have hcomp := heval.comp_hasDerivAt t hline
    simpa [Function.comp_def, hzero t ht] using hcomp.hasDerivWithinAt (s := s)
  intro t ht
  have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
    (fun _ _ => le_rfl) h0 ht
  have : (fderiv ℝ f (x + t • v)) v - (fderiv ℝ f (x + (0 : ℝ) • v)) v = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hbound) (norm_nonneg _)
  simpa using sub_eq_zero.mp this
theorem affine_generator_of_interior_constant_directional_derivative
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2))
    (hconst : ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      (fderiv ℝ f (x + t • v)) v = (fderiv ℝ f x) v) :
    ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      f (x + t • v) = f x + t • (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  let s : Set ℝ := {t | (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1}
  let d := (fderiv ℝ f x) v
  have hs : Convex ℝ s := convex_interior_line_parameters x v
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using hx
  have hderiv (t : ℝ) (ht : t ∈ s) :
      HasDerivWithinAt (fun u : ℝ => f (x + u • v) - u • d) 0 s t := by
    have hd := (embedding_contDiffAt_interior a f hf (x + t • v) ht 1).differentiableAt
      one_ne_zero
    have hline : HasDerivAt (fun u : ℝ => x + u • v) v t := by
      simpa using (((hasDerivAt_id t).smul_const v).const_add x)
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt t hline
    have hmodel : HasDerivAt (fun u : ℝ => u • d) d t := by
      simpa using (hasDerivAt_id t).smul_const d
    change HasDerivAt (fun u : ℝ => f (x + u • v))
      ((fderiv ℝ f (x + t • v)) v) t at hcomp
    rw [hconst t ht] at hcomp
    convert hcomp.hasDerivWithinAt.sub hmodel.hasDerivWithinAt using 1
    simp [d]
  have hinterior (t : ℝ) (ht : t ∈ s) : f (x + t • v) = f x + t • d := by
    have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
      (fun _ _ => le_rfl) h0 ht
    have heq : (f (x + t • v) - t • d) - (f (x + (0 : ℝ) • v) - (0 : ℝ) • d) = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using hbound) (norm_nonneg _)
    have : f (x + t • v) - t • d = f x := by simpa using sub_eq_zero.mp heq
    exact sub_eq_iff_eq_add.mp this
  intro t ht
  have hmem (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      x + (u * t) • v ∈ OptimalMoebius.unitStrip := by
    change 0 ≤ x 0 + t * v 0 ∧ x 0 + t * v 0 ≤ 1 at ht
    change 0 ≤ x 0 + (u * t) * v 0 ∧ x 0 + (u * t) * v 0 ≤ 1
    have hcomb : x 0 + (u * t) * v 0 = (1 - u) * x 0 + u * (x 0 + t * v 0) := by ring
    rw [hcomb]
    have hc := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1)
      ⟨le_of_lt hx.1, le_of_lt hx.2⟩ ht (sub_nonneg.mpr hu.2) hu.1 (by ring)
    exact hc
  have hmem' (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) : (u * t) ∈ s := by
    change 0 ≤ x 0 + t * v 0 ∧ x 0 + t * v 0 ≤ 1 at ht
    change 0 < x 0 + (u * t) * v 0 ∧ x 0 + (u * t) * v 0 < 1
    have hcomb : x 0 + (u * t) * v 0 = (1 - u) * x 0 + u * (x 0 + t * v 0) := by ring
    rw [hcomb]
    have hleft := mul_pos (sub_pos.mpr hu.2) hx.1
    have hright := mul_nonneg (le_of_lt hu.1) ht.1
    have hgap := mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr hx.2)
    have hgap' := mul_nonneg (le_of_lt hu.1) (sub_nonneg.mpr ht.2)
    constructor <;> nlinarith
  have heq : Set.EqOn (fun u : ℝ => f (x + (u * t) • v))
      (fun u => f x + (u * t) • d) (Set.Ioo (0 : ℝ) 1) := by
    intro u hu
    exact hinterior _ (hmem' u hu)
  have hpath : Continuous (fun u : ℝ => x + (u * t) • v) := by fun_prop
  have hcont := hf.smooth.continuousOn.comp hpath.continuousOn hmem
  have hmodel : Continuous (fun u : ℝ => f x + (u * t) • d) := by fun_prop
  have heq' := heq.of_subset_closure hcont hmodel.continuousOn Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo zero_ne_one])
  have hfinal := heq' (x := 1) ⟨zero_le_one, le_rfl⟩
  rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_interior x hx)]
  simpa [d] using hfinal
theorem exists_spanning_ruling_of_zero_directional_hessian
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0)
    (hzero : ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v = 0) :
    ∃ l r : ℝ, x = (!₂[0, l] + (x 0) • (!₂[1, r] - !₂[0, l])) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l]) := by
  exact exists_spanning_ruling_of_affine_generator a ha f hf x hx v hv
    (affine_generator_of_interior_constant_directional_derivative a f hf x hx v
      (constant_directional_derivative_interior_of_zero_hessian a f hf x hx v hzero))
theorem straight_ruling_relation_closed_and_reflected
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) :
    let K : Set (ℝ × ℝ) := {p | ∀ u ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, p.1] + u • (!₂[1, p.2] - !₂[0, p.1])) =
        f !₂[0, p.1] + u • (f !₂[1, p.2] - f !₂[0, p.1])}
    IsClosed K ∧ ∀ l r : ℝ, (l, r) ∈ K ↔ (r + a, l + a) ∈ K := by
  dsimp only
  constructor
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro hu
    have hleft : Continuous (fun p : ℝ × ℝ =>
        f (!₂[0, p.1] + u • (!₂[1, p.2] - !₂[0, p.1]))) := by
      apply hf.smooth.continuousOn.comp_continuous (by fun_prop)
      intro p
      simpa [OptimalMoebius.unitStrip] using hu
    have hzero : Continuous (fun p : ℝ × ℝ => f !₂[0, p.1]) := by
      apply hf.smooth.continuousOn.comp_continuous (by fun_prop)
      intro p
      change 0 ≤ (0 : ℝ) ∧ 0 ≤ 1
      norm_num
    have hone : Continuous (fun p : ℝ × ℝ => f !₂[1, p.2]) := by
      apply hf.smooth.continuousOn.comp_continuous (by fun_prop)
      intro p
      change 0 ≤ (1 : ℝ) ∧ 1 ≤ 1
      norm_num
    exact isClosed_eq hleft (hzero.add ((hone.sub hzero).const_smul u))
  · intro l r
    have hperiod (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
        f (!₂[0, r + a] + (1 - u) • (!₂[1, l + a] - !₂[0, r + a])) =
          f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) := by
      have hx : (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) ∈
          OptimalMoebius.unitStrip := by
        simpa [OptimalMoebius.unitStrip] using hu
      have heq : OptimalMoebius.period a
          (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          !₂[0, r + a] + (1 - u) • (!₂[1, l + a] - !₂[0, r + a]) := by
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [OptimalMoebius.period]
        ring
      simpa only [heq] using hf.periodic _ hx
    change (∀ u ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
        f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l])) ↔
      (∀ u ∈ Set.Icc (0 : ℝ) 1,
      f (!₂[0, r + a] + u • (!₂[1, l + a] - !₂[0, r + a])) =
        f !₂[0, r + a] + u • (f !₂[1, l + a] - f !₂[0, r + a]))
    constructor
    · intro h u hu
      have hu' : 1 - u ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have hperiod' := hperiod (1 - u) hu'
      rw [sub_sub_cancel] at hperiod'
      rw [hperiod', h (1 - u) hu', (boundary_period_values a f hf r).1,
        (boundary_period_values a f hf l).2]
      module
    · intro h u hu
      rw [← hperiod u hu, h (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩,
        (boundary_period_values a f hf r).1, (boundary_period_values a f hf l).2]
      module
theorem orderedStraightFamily_of_midline_spanning
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (hspan : ∀ c : ℝ, ∃ l r : ℝ, l + r = 2 * c ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l])) :
    OrderedStraightFamily a f := by
  let K : Set (ℝ × ℝ) := {p | ∀ u ∈ Set.Icc (0 : ℝ) 1,
    f (!₂[0, p.1] + u • (!₂[1, p.2] - !₂[0, p.1])) =
      f !₂[0, p.1] + u • (f !₂[1, p.2] - f !₂[0, p.1])}
  have hclosed : IsClosed K := (straight_ruling_relation_closed_and_reflected a f hf).1
  have hperiod : ∀ l r : ℝ, (l, r) ∈ K ↔ (r + a, l + a) ∈ K :=
    (straight_ruling_relation_closed_and_reflected a f hf).2
  have hspan' (c : ℝ) : ∃ l r : ℝ, (l, r) ∈ K ∧ l + r = 2 * c := by
    obtain ⟨l, r, hsum, hstraight⟩ := hspan c
    exact ⟨l, r, hstraight, hsum⟩
  have hrect : ∀ l0 r0 l1 r1 : ℝ, (l0, r0) ∈ K → (l1, r1) ∈ K →
      l0 < l1 → r1 < r0 → ∀ l ∈ Set.Icc l0 l1, ∀ r ∈ Set.Icc r1 r0, (l, r) ∈ K := by
    intro l0 r0 l1 r1 hstraight0 hstraight1 hL hR l hl r hr
    exact crossed_straight_rulings_rectangle a f hf l0 r0 l1 r1
      hstraight0 hstraight1 hL hR l hl r hr
  obtain ⟨L, R, hLlip, hRlip, hLmono, hRmono, _, hmem, hseamL, hseamR⟩ :=
    ordered_endpoints_of_closed_relation a K hclosed hspan' hrect hperiod
  refine ⟨fun t : unitInterval => L (a * (t : ℝ)),
    fun t : unitInterval => R (a * (t : ℝ)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hLlip.continuous.comp (by fun_prop)
  · exact hRlip.continuous.comp (by fun_prop)
  · intro s t hst
    exact hLmono (mul_le_mul_of_nonneg_left hst ha.le)
  · intro s t hst
    exact hRmono (mul_le_mul_of_nonneg_left hst ha.le)
  · simpa using hseamL 0
  · simpa using hseamR 0
  · intro t u hu
    exact hmem (a * (t : ℝ)) u hu
theorem nonplanar_null_spanning_lines_ordered
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    let H := fun (x v w : EuclideanSpace ℝ (Fin 2)) =>
      (fderiv ℝ (fderiv ℝ f) x) v w
    let P := fun (l r u : ℝ) =>
      (!₂[0, l] + u • (!₂[1, r] - !₂[0, l]) : EuclideanSpace ℝ (Fin 2))
    ∀ l0 r0 l1 r1 : ℝ,
      (∀ u ∈ Set.Ioo (0 : ℝ) 1,
        (∃ p q : EuclideanSpace ℝ (Fin 2), H (P l0 r0 u) p q ≠ 0) ∧
          ∀ w : EuclideanSpace ℝ (Fin 2), H (P l0 r0 u) !₂[1, r0 - l0] w = 0) →
      (∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ w : EuclideanSpace ℝ (Fin 2),
        H (P l1 r1 u) !₂[1, r1 - l1] w = 0) →
      l0 < l1 → r0 ≤ r1 := by
  dsimp only
  intro l0 r0 l1 r1 hnull0 hnull1 hL
  by_contra hR
  have hR' : r1 < r0 := lt_of_not_ge hR
  let d : ℝ := l1 - l0 + (r0 - r1)
  have hd : 0 < d := by dsimp [d]; linarith
  let u : ℝ := (l1 - l0) / d
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (sub_pos.mpr hL) hd
    · exact (div_lt_one hd).mpr (by dsimp [d]; linarith)
  have hcross :
      (!₂[0, l0] + u • (!₂[1, r0] - !₂[0, l0]) : EuclideanSpace ℝ (Fin 2)) =
        !₂[0, l1] + u • (!₂[1, r1] - !₂[0, l1]) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp
    · change l0 + u * (r0 - l0) = l1 + u * (r1 - l1)
      dsimp [u]
      field_simp [ne_of_gt hd]
      dsimp [d]
      ring
  obtain ⟨⟨p, q, hpq⟩, hz0⟩ := hnull0 u hu
  have hz1 := hnull1 u hu
  rw [← hcross] at hz1
  have hs : (r0 - l0) - (r1 - l1) ≠ 0 := by
    apply ne_of_gt
    linarith
  let k : ℝ := (p 1 - p 0 * (r1 - l1)) / ((r0 - l0) - (r1 - l1))
  have hp : p = k • !₂[1, r0 - l0] + (p 0 - k) • !₂[1, r1 - l1] := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change p 0 = k * 1 + (p 0 - k) * 1
      ring
    · change p 1 = k * (r0 - l0) + (p 0 - k) * (r1 - l1)
      dsimp [k]
      field_simp [hs]
      ring
  apply hpq
  rw [hp]
  simp only [map_add, map_smul, add_apply, smul_apply]
  rw [hz0 q, hz1 q]
  simp
theorem fderiv_tangent_field_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    (fderiv ℝ (fun y => (fderiv ℝ f y) w) x) v =
      (fderiv ℝ (fderiv ℝ f) x) v w := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((embedding_contDiffAt_interior a f hf x hx 2).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hD (differentiableAt_const w)]
  simp
theorem hessian_metric_skew_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ ((fderiv ℝ (fderiv ℝ f) x) v u) ((fderiv ℝ f x) w) +
      inner ℝ ((fderiv ℝ f x) u) ((fderiv ℝ (fderiv ℝ f) x) v w) = 0 := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have heq : (fun y => inner ℝ ((fderiv ℝ f y) u) ((fderiv ℝ f y) w)) =ᶠ[nhds x]
      (fun _ => inner ℝ u w) := by
    filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx] with y hy
    exact fderiv_inner_interior a f hf y hy u w
  have hzero := congrArg (fun D => D v) (heq.fderiv_eq (𝕜 := ℝ))
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (embedding_contDiffAt_interior a f hf x hx 2).fderiv_right (by norm_num)
  have hu := (hD.clm_apply (contDiffAt_const (c := u))).differentiableAt (by simp)
  have hw := (hD.clm_apply (contDiffAt_const (c := w))).differentiableAt (by simp)
  rw [fderiv_inner_apply ℝ hu hw v] at hzero
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply] at hzero
  rw [fderiv_tangent_field_interior a f hf x hx v u,
    fderiv_tangent_field_interior a f hf x hx v w] at hzero
  linarith
theorem hessian_gauss_identity_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v z w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ ((fderiv ℝ (fderiv ℝ f) x) u v)
        ((fderiv ℝ (fderiv ℝ f) x) z w) =
      inner ℝ ((fderiv ℝ (fderiv ℝ f) x) z v)
        ((fderiv ℝ (fderiv ℝ f) x) u w) := by
  let U : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
    fun y => (fderiv ℝ f y) v
  let W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
    fun y => (fderiv ℝ f y) w
  have hD : ContDiffAt ℝ 2 (fderiv ℝ f) x :=
    (embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (by norm_num)
  have hU : ContDiffAt ℝ 2 U x := hD.clm_apply contDiffAt_const
  have hW : DifferentiableAt ℝ W x :=
    (hD.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hDU : DifferentiableAt ℝ (fderiv ℝ U) x :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hrel (p q : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ ((fderiv ℝ U x) p) ((fderiv ℝ W x) q) +
        inner ℝ ((fderiv ℝ (fderiv ℝ U) x) q p) (W x) = 0 := by
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
    have heq : (fun y => inner ℝ ((fderiv ℝ U y) p) (W y)) =ᶠ[nhds x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx] with y hy
      dsimp [U, W]
      rw [fderiv_tangent_field_interior a f hf y hy p v]
      exact hessian_normal_interior a f hf y hy p v w
    have hz := congrArg (fun D => D q) (heq.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_inner_apply ℝ (hDU.clm_apply (differentiableAt_const p)) hW q] at hz
    have hfield : (fderiv ℝ (fun y => (fderiv ℝ U y) p) x) q =
        (fderiv ℝ (fderiv ℝ U) x) q p := by
      rw [fderiv_clm_apply hDU (differentiableAt_const p)]
      simp
    rw [hfield] at hz
    simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using hz
  have h₁ := hrel u z
  have h₂ := hrel z u
  rw [(hU.isSymmSndFDerivAt (by norm_num)).eq u z] at h₂
  have hequal : inner ℝ ((fderiv ℝ U x) u) ((fderiv ℝ W x) z) =
      inner ℝ ((fderiv ℝ U x) z) ((fderiv ℝ W x) u) := by linarith
  dsimp [U, W] at hequal
  simpa only [fderiv_tangent_field_interior a f hf x hx] using hequal
theorem hessian_normal_space_finrank_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonal = 1 := by
  have hI : Isometry (fderiv ℝ f x) := by
    have h := hf.isometry x ⟨hx.1.le, hx.2.le⟩
    rwa [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_interior x hx)] at h
  have hdim := (LinearMap.range (fderiv ℝ f x).toLinearMap).finrank_add_finrank_orthogonal
  have hrange := LinearMap.finrank_range_of_inj hI.injective
  rw [hrange, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hdim
  omega
theorem hessian_values_collinear_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (p q u v : EuclideanSpace ℝ (Fin 2))
    (hpq : (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ c : ℝ, (fderiv ℝ (fderiv ℝ f) x) u v =
      c • (fderiv ℝ (fderiv ℝ f) x) p q := by
  let N := (LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonal
  have hmem (r s : EuclideanSpace ℝ (Fin 2)) :
      (fderiv ℝ (fderiv ℝ f) x) r s ∈ N := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    rintro _ ⟨w, rfl⟩
    exact hessian_normal_interior a f hf x hx r s w
  have hn : (⟨(fderiv ℝ (fderiv ℝ f) x) p q, hmem p q⟩ : N) ≠ 0 := by
    intro heq
    exact hpq (congrArg Subtype.val heq)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (hessian_normal_space_finrank_interior a f hf x hx) hn
    (⟨(fderiv ℝ (fderiv ℝ f) x) u v, hmem u v⟩ : N)
  exact ⟨c, (congrArg Subtype.val hc).symm⟩
theorem hessian_zero_of_normal_inner_zero_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (p q u v : EuclideanSpace ℝ (Fin 2))
    (hpq : (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0)
    (hinner : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) u v)
      ((fderiv ℝ (fderiv ℝ f) x) p q) = 0) :
    (fderiv ℝ (fderiv ℝ f) x) u v = 0 := by
  obtain ⟨c, hc⟩ := hessian_values_collinear_interior a f hf x hx p q u v hpq
  rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq] at hinner
  have hc0 : c = 0 := (mul_eq_zero.mp hinner).resolve_right
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hpq))
  simp [hc, hc0]
theorem exists_hessian_null_direction_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ w : EuclideanSpace ℝ (Fin 2), (fderiv ℝ (fderiv ℝ f) x) v w = 0 := by
  classical
  by_cases hzero : ∀ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q = 0
  · refine ⟨!₂[1, 0], ?_, hzero _⟩
    intro h
    have := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h
    norm_num at this
  · push Not at hzero
    obtain ⟨p, q, hpq⟩ := hzero
    let H := fderiv ℝ (fderiv ℝ f) x
    let n := H p q
    let A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ :=
      (((innerSL ℝ n).comp (H.flip q))).toLinearMap
    have hker : A.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
    obtain ⟨v, hvker, hv⟩ := A.ker.ne_bot_iff.mp hker
    have hvq : H v q = 0 := by
      apply hessian_zero_of_normal_inner_zero_interior a f hf x hx p q v q hpq
      have hA : A v = 0 := hvker
      change inner ℝ n (H v q) = 0 at hA
      rwa [real_inner_comm] at hA
    refine ⟨v, hv, ?_⟩
    intro w
    apply hessian_zero_of_normal_inner_zero_interior a f hf x hx p q v w hpq
    have hG := hessian_gauss_identity_interior a f hf x hx v w p q
    change inner ℝ (H v w) (H p q) = inner ℝ (H p w) (H v q) at hG
    simpa only [hvq, inner_zero_right] using hG
theorem uniqueDiffOn_unitStrip : UniqueDiffOn ℝ OptimalMoebius.unitStrip := by
  apply uniqueDiffOn_convex convex_unitStrip
  refine ⟨!₂[1 / 2, 0], mem_interior_iff_mem_nhds.mpr ?_⟩
  apply unitStrip_mem_nhds_of_interior
  constructor <;> norm_num
theorem constant_directional_derivative_of_hessian_null_line
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2))
    (hnull : ∀ s : ℝ, (x + s • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      (fderiv ℝ (fderiv ℝ f) (x + s • v)) v v = 0) :
    ∀ t : ℝ, x + t • v ∈ OptimalMoebius.unitStrip →
      (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
        (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  intro t ht
  let p : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => x + (u * t) • v
  let g : ℝ → EuclideanSpace ℝ (Fin 3) := fun u =>
    (fderivWithin ℝ f OptimalMoebius.unitStrip (p u)) v
  have hpclosed : ∀ u ∈ Set.Icc (0 : ℝ) 1, p u ∈ OptimalMoebius.unitStrip := by
    intro u hu
    have h := convex_unitStrip (show x ∈ OptimalMoebius.unitStrip from ⟨hx.1.le, hx.2.le⟩)
      ht (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
    convert h using 1
    dsimp [p]
    module
  have hpinterior : ∀ u ∈ Set.Ico (0 : ℝ) 1, (p u) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    change 0 ≤ x 0 + t * v 0 ∧ x 0 + t * v 0 ≤ 1 at ht
    change 0 < x 0 + (u * t) * v 0 ∧ x 0 + (u * t) * v 0 < 1
    have hl := mul_pos (sub_pos.mpr hu.2) hx.1
    have hr := mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr hx.2)
    constructor <;> nlinarith [mul_nonneg hu.1 ht.1,
      mul_nonneg hu.1 (sub_nonneg.mpr ht.2)]
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.clm_apply _ continuousOn_const
    exact (hf.smooth.continuousOn_fderivWithin uniqueDiffOn_unitStrip (by simp)).comp
      (by fun_prop) hpclosed
  have hderiv : ∀ u ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt g 0 (Set.Ici u) u := by
    intro u hu
    have hpu := hpinterior u hu
    have hD : DifferentiableAt ℝ (fderiv ℝ f) (p u) :=
      ((embedding_contDiffAt_interior a f hf (p u) hpu 2).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hpath : HasDerivAt p (t • v) u := by
      simpa only [p, one_mul, id_eq] using
        HasDerivAt.const_add x (((hasDerivAt_id u).mul_const t).smul_const v)
    have hd := (hD.clm_apply (differentiableAt_const v)).hasFDerivAt.comp_hasDerivAt u hpath
    rw [fderiv_tangent_field_interior a f hf (p u) hpu (t • v) v] at hd
    have hn : (fderiv ℝ (fderiv ℝ f) (p u)) (t • v) v = 0 := by
      simp only [map_smul, smul_apply]
      rw [hnull (u * t) hpu, smul_zero]
    rw [hn] at hd
    have hcont : Continuous (fun r : ℝ => (p r) 0) := by fun_prop
    have heq : g =ᶠ[nhds u] (fun r => (fderiv ℝ f (p r)) v) := by
      filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hpu] with r hr
      dsimp [g]
      rw [fderivWithin_of_mem_nhds (unitStrip_mem_nhds_of_interior (p r) hr)]
    exact (hd.congr_of_eventuallyEq heq).hasDerivWithinAt
  have heq := constant_of_has_deriv_right_zero hg hderiv 1 (by norm_num)
  simpa only [g, p, one_mul, zero_mul, zero_smul, add_zero] using heq
theorem fderiv_hessian_field_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ f) y) v w) x) u =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) u v w := by
  have hH : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    (((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply (hH.clm_apply (differentiableAt_const v)) (differentiableAt_const w)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [fderiv_clm_apply hH (differentiableAt_const v)]
  simp
theorem third_derivative_swap_last_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) u v w =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) u w v := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have heq : (fun y => (fderiv ℝ (fderiv ℝ f) y) v w) =ᶠ[nhds x]
      (fun y => (fderiv ℝ (fderiv ℝ f) y) w v) := by
    filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx] with y hy
    exact ((embedding_contDiffAt_interior a f hf y hy 2).isSymmSndFDerivAt
      (by norm_num)).eq v w
  have h := congrArg (fun D => D u) (heq.fderiv_eq (𝕜 := ℝ))
  simpa only [fderiv_hessian_field_interior a f hf x hx] using h
theorem third_derivative_swap_first_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (u v w : EuclideanSpace ℝ (Fin 2)) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) u v w =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) v u w := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ f) x :=
    (embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (by norm_num)
  exact congrArg (fun L => L w) ((hD.isSymmSndFDerivAt (by norm_num)).eq u v)
theorem hessian_null_field_self_derivative
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hV : DifferentiableAt ℝ V x)
    (hnull : ∀ᶠ y in nhds x, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) y) (V y) w = 0) :
    ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) ((fderiv ℝ V x) (V x)) w = 0 := by
  let H := fderiv ℝ (fderiv ℝ f)
  let T := fderiv ℝ H x
  have hH : DifferentiableAt ℝ H x :=
    (((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y => H y (V y)) =ᶠ[nhds x] (fun _ => 0) := by
    filter_upwards [hnull] with y hy
    apply ContinuousLinearMap.ext
    intro w
    exact hy w
  have hrel (z w : EuclideanSpace ℝ (Fin 2)) :
      H x ((fderiv ℝ V x) z) w + T z (V x) w = 0 := by
    have h := congrArg (fun D => D z w) (heq.fderiv_eq (𝕜 := ℝ))
    rw [fderiv_clm_apply hH hV] at h
    simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using h
  have hnullx := hnull.self_of_nhds
  intro w
  have h₁ := hrel (V x) w
  have h₂ := hrel w (V x)
  have hsym := (embedding_contDiffAt_interior a f hf x hx 2).isSymmSndFDerivAt
    (by norm_num)
  have hz : H x ((fderiv ℝ V x) w) (V x) = 0 := by
    dsimp [H]
    rw [hsym.eq]
    exact hnullx _
  rw [hz, zero_add] at h₂
  have hswap : T (V x) (V x) w = T w (V x) (V x) := by
    dsimp [T, H]
    rw [third_derivative_swap_last_interior a f hf x hx,
      third_derivative_swap_first_interior a f hf x hx]
  change H x ((fderiv ℝ V x) (V x)) w = 0
  rw [hswap, h₂, add_zero] at h₁
  exact h₁
theorem normalized_null_field_scalar_derivative_eq_zero
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2))
    (he : (fderiv ℝ (fderiv ℝ f) x) e e ≠ 0)
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hφ : DifferentiableAt ℝ φ x)
    (hnull : ∀ᶠ y in nhds x, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) y) (d + φ y • e) w = 0) :
    (fderiv ℝ φ x) (d + φ x • e) = 0 := by
  have hV : DifferentiableAt ℝ (fun y => d + φ y • e) x :=
    (differentiableAt_const d).add (hφ.smul_const e)
  have hn := hessian_null_field_self_derivative a f hf x hx
    (fun y => d + φ y • e) hV hnull e
  rw [fderiv_const_add, fderiv_smul_const hφ] at hn
  have hsmul : ((fderiv ℝ φ x) (d + φ x • e)) •
      ((fderiv ℝ (fderiv ℝ f) x) e e) = 0 := by
    simpa only [ContinuousLinearMap.smulRight_apply, map_smul, smul_apply] using hn
  exact (smul_eq_zero.mp hsmul).resolve_right he
theorem hessian_zero_of_transverse_test_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e u v : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0)
    (hinner : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) u v) n = 0) :
    (fderiv ℝ (fderiv ℝ f) x) u v = 0 := by
  have he : (fderiv ℝ (fderiv ℝ f) x) e e ≠ 0 := by
    intro h
    exact htest (by simp [h])
  obtain ⟨c, hc⟩ := hessian_values_collinear_interior a f hf x hx e e u v he
  rw [hc, real_inner_smul_left] at hinner
  have hc0 : c = 0 := (mul_eq_zero.mp hinner).resolve_right htest
  simp [hc, hc0]
theorem normalized_hessian_null_direction_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x)
        (d + (-(inner ℝ ((fderiv ℝ (fderiv ℝ f) x) d e) n /
          inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n)) • e) w = 0 := by
  let H := fderiv ℝ (fderiv ℝ f) x
  let V := d + (-(inner ℝ (H d e) n / inner ℝ (H e e) n)) • e
  have he : H e e ≠ 0 := by
    intro h
    exact htest (by simp only [← show H = fderiv ℝ (fderiv ℝ f) x from rfl, h,
      inner_zero_left])
  have hVe : H V e = 0 := by
    apply hessian_zero_of_transverse_test_interior a f hf x hx e V e n htest
    change inner ℝ (H V e) n = 0
    dsimp [V]
    simp only [map_add, map_smul, add_apply, smul_apply, inner_add_left, real_inner_smul_left]
    field_simp [show inner ℝ (H e e) n ≠ 0 from htest]
    ring
  intro w
  apply hessian_zero_of_normal_inner_zero_interior a f hf x hx e e V w he
  have hg := hessian_gauss_identity_interior a f hf x hx V w e e
  change inner ℝ (H V w) (H e e) = inner ℝ (H e w) (H V e) at hg
  simpa only [hVe, inner_zero_right] using hg
theorem normalized_hessian_slope_contDiffAt_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    ContDiffAt ℝ 1 (fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)) x := by
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hb := ((hH.clm_apply (contDiffAt_const (c := d))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  exact (hb.div hh htest).neg
theorem normalized_hessian_slope_equation_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
    (fderiv ℝ φ x) (d + φ x • e) = 0 := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  have hφ : DifferentiableAt ℝ φ x :=
    (normalized_hessian_slope_contDiffAt_interior a f hf x hx e d n htest).differentiableAt
      (by norm_num)
  have he : (fderiv ℝ (fderiv ℝ f) x) e e ≠ 0 := by
    intro he
    exact htest (by simp [he])
  apply normalized_null_field_scalar_derivative_eq_zero a f hf x hx e d he φ hφ
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx,
    hh.continuousAt.eventually_ne htest] with y hy htesty
  exact normalized_hessian_null_direction_interior a f hf y hy e d n htesty
theorem local_eq_const_of_eventually_hasDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg : ∀ᶠ t in nhds (0 : ℝ), HasDerivAt g 0 t) :
    g =ᶠ[nhds (0 : ℝ)] (fun _ => g 0) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  apply Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℝ) ε).isPreconnected
    (fun y hy => (hball y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hball y hy).deriv) ht (Metric.mem_ball_self hε)
theorem local_straight_of_zero_self_derivative
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) (hV : ContDiffAt ℝ 1 V x)
    (haccel : ∀ᶠ y in nhds x, (fderiv ℝ V y) (V y) = 0) :
    ∀ᶠ t : ℝ in nhds 0, V (x + t • V x) = V x := by
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hV.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hαevent : ∀ᶠ t in nhds (0 : ℝ), HasDerivAt α (V (α t)) t := by
    filter_upwards [Ioo_mem_nhds (by linarith : (0 : ℝ) - ε < 0)
      (by linarith : (0 : ℝ) < 0 + ε)] with t ht
    exact hα t ht
  have hαcont : Filter.Tendsto α (nhds 0) (nhds x) := by
    simpa only [hα0] using hαevent.self_of_nhds.continuousAt.tendsto
  have hVnear : ∀ᶠ t in nhds (0 : ℝ),
      DifferentiableAt ℝ V (α t) ∧ (fderiv ℝ V (α t)) (V (α t)) = 0 := by
    have hvnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ V y ∧ (fderiv ℝ V y) (V y) = 0 := by
      filter_upwards [hV.eventually (by norm_num), haccel] with y hy hya
      exact ⟨hy.differentiableAt (by norm_num), hya⟩
    exact hαcont.eventually hvnear
  have hVcurve : (fun t => V (α t)) =ᶠ[nhds 0] (fun _ => V x) := by
    have hz : ∀ᶠ t in nhds (0 : ℝ), HasDerivAt (fun t => V (α t)) 0 t := by
      filter_upwards [hαevent, hVnear] with t hαt hVt
      have h := hVt.1.hasFDerivAt.comp_hasDerivAt t hαt
      rwa [hVt.2] at h
    simpa only [hα0] using local_eq_const_of_eventually_hasDerivAt_zero _ hz
  have hlinear : ∀ᶠ t in nhds (0 : ℝ), α t = x + t • V x := by
    have hz : ∀ᶠ t in nhds (0 : ℝ),
        HasDerivAt (fun t => α t - t • V x) 0 t := by
      filter_upwards [hαevent, hVcurve] with t hαt hVt
      rw [hVt] at hαt
      have hd : HasDerivAt (fun r => r • V x) (V x) t := by
        simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const (V x)
      convert hαt.sub hd using 1
      simp only [sub_self]
    have hc := local_eq_const_of_eventually_hasDerivAt_zero _ hz
    filter_upwards [hc] with t ht
    simp only [hα0, zero_smul, sub_zero] at ht
    exact sub_eq_iff_eq_add.mp ht
  filter_upwards [hVcurve, hlinear] with t hVt ht
  rwa [ht] at hVt
theorem local_hessian_null_line_of_nonzero_diagonal
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2))
    (he : (fderiv ℝ (fderiv ℝ f) x) e e ≠ 0) :
    ∃ c : ℝ, ∀ᶠ t : ℝ in nhds 0, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) (x + t • (d + c • e))) (d + c • e) w = 0 := by
  let n := (fderiv ℝ (fderiv ℝ f) x) e e
  have htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0 := by
    exact ne_of_gt (by simpa only [n, real_inner_self_eq_norm_sq] using
      (sq_pos_of_pos (norm_pos_iff.mpr he)))
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  let V := fun y => d + φ y • e
  have hφ : ContDiffAt ℝ 1 φ x :=
    normalized_hessian_slope_contDiffAt_interior a f hf x hx e d n htest
  have hV : ContDiffAt ℝ 1 V x := contDiffAt_const.add (hφ.smul contDiffAt_const)
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hnear : ∀ᶠ y in nhds x, y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n ≠ 0 :=
    Filter.Eventually.and ((isOpen_Ioo.preimage hcont).mem_nhds hx)
      (hh.continuousAt.eventually_ne htest)
  have haccel : ∀ᶠ y in nhds x, (fderiv ℝ V y) (V y) = 0 := by
    filter_upwards [hnear] with y hy
    have hφy := (normalized_hessian_slope_contDiffAt_interior a f hf y hy.1 e d n
      hy.2).differentiableAt (by norm_num)
    have heq := normalized_hessian_slope_equation_interior a f hf y hy.1 e d n hy.2
    change (fderiv ℝ φ y) (V y) = 0 at heq
    dsimp [V]
    rw [fderiv_const_add, fderiv_smul_const hφy]
    change ((fderiv ℝ φ y) (d + φ y • e)) • e = 0
    rw [heq, zero_smul]
  have hstraight := local_straight_of_zero_self_derivative V x hV haccel
  have hpath : Filter.Tendsto (fun t : ℝ => x + t • V x) (nhds 0) (nhds x) := by
    have hc : Continuous (fun t : ℝ => x + t • V x) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  refine ⟨φ x, ?_⟩
  filter_upwards [hstraight, hpath.eventually hnear] with t ht hty
  intro w
  have hn := normalized_hessian_null_direction_interior a f hf _ hty.1 e d n hty.2 w
  change (fderiv ℝ (fderiv ℝ f) (x + t • V x)) (V (x + t • V x)) w = 0 at hn
  rwa [ht] at hn
theorem exists_nonzero_hessian_diagonal_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ e : EuclideanSpace ℝ (Fin 2), (fderiv ℝ (fderiv ℝ f) x) e e ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, q, hpq⟩ := hnonzero
  have hsum := h (p + q)
  have hsym := (embedding_contDiffAt_interior a f hf x hx 2).isSymmSndFDerivAt
    (by norm_num)
  simp only [map_add, add_apply, h p, h q, hsym.eq q p, zero_add, add_zero] at hsum
  have htwo : (2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) x) p q) = 0 := by
    simpa only [two_smul] using hsum
  exact hpq ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
theorem exists_local_hessian_null_generator_nonplanar
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ᶠ t : ℝ in nhds 0, ∀ w : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0 := by
  obtain ⟨e, he⟩ := exists_nonzero_hessian_diagonal_interior a f hf x hx hnonzero
  have he0 : e ≠ 0 := by
    intro h
    exact he (by simp [h])
  obtain ⟨d, hd⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := EuclideanSpace ℝ (Fin 2)) (by simp) he0
  obtain ⟨c, hc⟩ := local_hessian_null_line_of_nonzero_diagonal a f hf x hx e d he
  refine ⟨d + c • e, ?_, hc⟩
  intro h
  have hdce : (-c) • e = d := by
    have hd' := eq_neg_of_add_eq_zero_left h
    simpa only [neg_smul] using hd'.symm
  exact ((LinearIndependent.pair_iff' he0).mp hd (-c)) hdce
theorem local_constant_fderiv_of_hessian_null_line
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (v : EuclideanSpace ℝ (Fin 2))
    (hnull : ∀ᶠ t : ℝ in nhds 0, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0) :
    ∀ᶠ t : ℝ in nhds 0, fderiv ℝ f (x + t • v) = fderiv ℝ f x := by
  have hpath : Filter.Tendsto (fun t : ℝ => x + t • v) (nhds 0) (nhds x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have hnear := hpath.eventually ((isOpen_Ioo.preimage hcont).mem_nhds hx)
  have hz : ∀ᶠ t : ℝ in nhds 0,
      HasDerivAt (fun t => fderiv ℝ f (x + t • v)) 0 t := by
    filter_upwards [hnull, hnear] with t ht htx
    have hD : DifferentiableAt ℝ (fderiv ℝ f) (x + t • v) :=
      ((embedding_contDiffAt_interior a f hf _ htx 2).fderiv_right (m := 1)
        (by norm_num)).differentiableAt (by norm_num)
    have hd : HasDerivAt (fun r : ℝ => x + r • v) v t := by
      simpa only [one_smul, id_eq] using
        HasDerivAt.const_add x ((hasDerivAt_id t).smul_const v)
    have h := hD.hasFDerivAt.comp_hasDerivAt t hd
    have hh : (fderiv ℝ (fderiv ℝ f) (x + t • v)) v = 0 := by
      apply ContinuousLinearMap.ext
      exact ht
    rwa [hh] at h
  have hc := local_eq_const_of_eventually_hasDerivAt_zero _ hz
  filter_upwards [hc] with t ht
  simpa only [zero_smul, add_zero] using ht
theorem exists_local_constant_generator_nonplanar
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ᶠ t : ℝ in nhds 0, fderiv ℝ f (x + t • v) = fderiv ℝ f x := by
  obtain ⟨v, hv, hnull⟩ := exists_local_hessian_null_generator_nonplanar a f hf x hx hnonzero
  exact ⟨v, hv, local_constant_fderiv_of_hessian_null_line a f hf x hx v hnull⟩
theorem normalized_slope_riccati
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x e d : EuclideanSpace ℝ (Fin 2)) (hφ : ContDiffAt ℝ 2 φ x)
    (heq : ∀ᶠ y in nhds x, (fderiv ℝ φ y) (d + φ y • e) = 0) :
    (fderiv ℝ (fun y => (fderiv ℝ φ y) e) x) (d + φ x • e) =
      -((fderiv ℝ φ x) e) ^ 2 := by
  let V := fun y => d + φ y • e
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ' : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have hV : DifferentiableAt ℝ V x :=
    (differentiableAt_const d).add (hφ'.smul_const e)
  have heq' : (fun y => (fderiv ℝ φ y) (V y)) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := heq
  have hzero := congrArg (fun D => D e) (heq'.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_clm_apply hD hV] at hzero
  have hVderiv : (fderiv ℝ V x) e = ((fderiv ℝ φ x) e) • e := by
    dsimp [V]
    rw [fderiv_const_add, fderiv_smul_const hφ']
    rfl
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, hVderiv, map_smul,
    smul_eq_mul] at hzero
  have hsym := hφ.isSymmSndFDerivAt (by norm_num)
  rw [fderiv_clm_apply hD (differentiableAt_const e)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [hsym.eq]
  change (fderiv ℝ (fderiv ℝ φ) x) e (V x) = -((fderiv ℝ φ x) e) ^ 2
  nlinarith
theorem hessian_null_field_transport
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hV : DifferentiableAt ℝ V x)
    (hnull : ∀ᶠ y in nhds x, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) y) (V y) w = 0)
    (e : EuclideanSpace ℝ (Fin 2)) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) (V x) e e =
      -((fderiv ℝ (fderiv ℝ f) x) ((fderiv ℝ V x) e) e) := by
  let H := fderiv ℝ (fderiv ℝ f)
  have hH : DifferentiableAt ℝ H x :=
    (((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y => H y (V y)) =ᶠ[nhds x] (fun _ => 0) := by
    filter_upwards [hnull] with y hy
    apply ContinuousLinearMap.ext
    exact hy
  have h := congrArg (fun D => D e e) (heq.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_clm_apply hH hV] at h
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at h
  dsimp [H] at h
  rw [third_derivative_swap_first_interior a f hf x hx e (V x) e] at h
  exact eq_neg_of_add_eq_zero_right h
theorem normalized_hessian_slope_contDiffAt_order
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0)
    (k : ℕ) :
    ContDiffAt ℝ k (fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)) x := by
  have hH : ContDiffAt ℝ k (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx (k + 2)).fderiv_right (m := (k + 1))
      (by norm_cast)).fderiv_right (by norm_cast)
  have hb := ((hH.clm_apply (contDiffAt_const (c := d))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  exact (hb.div hh htest).neg
theorem normalized_hessian_curvature_equation_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
    let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
    (fderiv ℝ β x) (d + φ x • e) = -((fderiv ℝ φ x) e) * β x := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  let V := fun y => d + φ y • e
  have hφ : DifferentiableAt ℝ φ x :=
    (normalized_hessian_slope_contDiffAt_interior a f hf x hx e d n htest).differentiableAt
      (by norm_num)
  have hV : DifferentiableAt ℝ V x := (differentiableAt_const d).add (hφ.smul_const e)
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  have hnull : ∀ᶠ y in nhds x, ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) y) (V y) w = 0 := by
    filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx,
      hh.continuousAt.eventually_ne htest] with y hy htesty
    exact normalized_hessian_null_direction_interior a f hf y hy e d n htesty
  have htransport := hessian_null_field_transport a f hf x hx V hV hnull e
  have hVderiv : (fderiv ℝ V x) e = ((fderiv ℝ φ x) e) • e := by
    dsimp [V]
    rw [fderiv_const_add, fderiv_smul_const hφ]
    rfl
  rw [hVderiv, map_smul, smul_apply] at htransport
  have hcalc := fderiv_inner_apply ℝ
    (((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
      (contDiffAt_const (c := e))).differentiableAt (by norm_num))
    (differentiableAt_const n) (V x)
  rw [fderiv_hessian_field_interior a f hf x hx] at hcalc
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, inner_zero_right, zero_add] at hcalc
  rw [htransport, inner_neg_left, real_inner_smul_left] at hcalc
  simpa only [neg_mul, V, φ] using hcalc
theorem normalized_hessian_slope_riccati_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
    let ρ := fun y => (fderiv ℝ φ y) e
    (fderiv ℝ ρ x) (d + φ x • e) = -(ρ x) ^ 2 := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  have hφ : ContDiffAt ℝ 2 φ x :=
    normalized_hessian_slope_contDiffAt_order a f hf x hx e d n htest 2
  apply normalized_slope_riccati φ x e d hφ
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hh := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
  filter_upwards [(isOpen_Ioo.preimage hcont).mem_nhds hx,
    hh.continuousAt.eventually_ne htest] with y hy htesty
  exact normalized_hessian_slope_equation_interior a f hf y hy e d n htesty
theorem local_riccati_transport
    (β ρ : ℝ → ℝ) (hβ0 : β 0 ≠ 0)
    (hode : ∀ᶠ t : ℝ in nhds 0,
      HasDerivAt β (-(ρ t) * β t) t ∧ HasDerivAt ρ (-(ρ t) ^ 2) t) :
    ∀ᶠ t : ℝ in nhds 0,
      β t * (1 + t * ρ 0) = β 0 ∧ ρ t * (1 + t * ρ 0) = ρ 0 := by
  have hne : ∀ᶠ t : ℝ in nhds 0, β t ≠ 0 :=
    hode.self_of_nhds.1.continuousAt.eventually_ne hβ0
  have hratio : (fun t => ρ t / β t) =ᶠ[nhds 0] (fun _ => ρ 0 / β 0) := by
    have hz : ∀ᶠ t : ℝ in nhds 0, HasDerivAt (fun t => ρ t / β t) 0 t := by
      filter_upwards [hode, hne] with t ht hβt
      have h := ht.2.div ht.1 hβt
      convert h using 1; ring
    exact local_eq_const_of_eventually_hasDerivAt_zero _ hz
  have hinv : (fun t => 1 / β t - (ρ 0 / β 0) * t) =ᶠ[nhds 0]
      (fun _ => 1 / β 0) := by
    have hz : ∀ᶠ t : ℝ in nhds 0,
        HasDerivAt (fun t => 1 / β t - (ρ 0 / β 0) * t) 0 t := by
      filter_upwards [hode, hne, hratio] with t ht hβt hrt
      have hi := (hasDerivAt_const t (1 : ℝ)).div ht.1 hβt
      have hi' : HasDerivAt (fun t => 1 / β t) (ρ 0 / β 0) t := by
        convert hi using 1
        rw [← hrt]
        field_simp
        ring
      have hd : HasDerivAt (fun r : ℝ => (ρ 0 / β 0) * r) (ρ 0 / β 0) t := by
        simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul (ρ 0 / β 0)
      convert hi'.sub hd using 1
      ring
    have hc := local_eq_const_of_eventually_hasDerivAt_zero _ hz
    filter_upwards [hc] with t ht
    simpa only [mul_zero, sub_zero] using ht
  filter_upwards [hne, hratio, hinv] with t hβt hrt hit
  have hβeq : β t * (1 + t * ρ 0) = β 0 := by
    field_simp at hit
    nlinarith
  refine ⟨hβeq, ?_⟩
  have hρeq : ρ t * β 0 = ρ 0 * β t := (div_eq_div_iff hβt hβ0).mp hrt
  apply (mul_right_cancel₀ hβ0)
  calc
    ρ t * (1 + t * ρ 0) * β 0 = (ρ t * β 0) * (1 + t * ρ 0) := by ring
    _ = (ρ 0 * β t) * (1 + t * ρ 0) := by rw [hρeq]
    _ = ρ 0 * (β t * (1 + t * ρ 0)) := by ring
    _ = ρ 0 * β 0 := by rw [hβeq]
theorem global_riccati_transport
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (τ β φ ρ : X → ℝ) (hτ : Continuous τ) (hβ : Continuous β)
    (hφ : ∀ t, β t ≠ 0 → ContinuousAt φ t)
    (hρ : ∀ t, β t ≠ 0 → ContinuousAt ρ t)
    (o : X) (hτo : τ o = 0) (hβo : β o ≠ 0)
    (hloc : ∀ s, β s ≠ 0 → φ s = φ o →
      ∀ᶠ t in nhds s, φ t = φ s ∧
        β t * (1 + (τ t - τ s) * ρ s) = β s ∧
        ρ t * (1 + (τ t - τ s) * ρ s) = ρ s) :
    ∀ t, β t * (1 + τ t * ρ o) = β o ∧ φ t = φ o ∧
      ρ t * (1 + τ t * ρ o) = ρ o := by
  let T : Set X := {t | β t * (1 + τ t * ρ o) = β o ∧ φ t = φ o ∧
      ρ t * (1 + τ t * ρ o) = ρ o}
  have hne : ∀ t ∈ T, β t ≠ 0 := by
    intro t ht hbt
    exact hβo (by simpa only [hbt, zero_mul] using ht.1.symm)
  have hopen : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    filter_upwards [hloc s (hne s hs) hs.2.1] with t ht
    have hfactor : 1 + τ t * ρ o =
        (1 + τ s * ρ o) * (1 + (τ t - τ s) * ρ s) := by
      symm
      calc
        (1 + τ s * ρ o) * (1 + (τ t - τ s) * ρ s) =
            (1 + τ s * ρ o) + (τ t - τ s) * (ρ s * (1 + τ s * ρ o)) := by ring
        _ = 1 + τ t * ρ o := by rw [hs.2.2]; ring
    change β t * (1 + τ t * ρ o) = β o ∧ φ t = φ o ∧
      ρ t * (1 + τ t * ρ o) = ρ o
    refine ⟨?_, ht.1.trans hs.2.1, ?_⟩
    · rw [hfactor]
      calc
        β t * ((1 + τ s * ρ o) * (1 + (τ t - τ s) * ρ s)) =
            (β t * (1 + (τ t - τ s) * ρ s)) * (1 + τ s * ρ o) := by ring
        _ = β o := by rw [ht.2.1, hs.1]
    · rw [hfactor]
      calc
        ρ t * ((1 + τ s * ρ o) * (1 + (τ t - τ s) * ρ s)) =
            (ρ t * (1 + (τ t - τ s) * ρ s)) * (1 + τ s * ρ o) := by ring
        _ = ρ o := by rw [ht.2.2, hs.2.2]
  have hclosed : IsClosed T := by
    apply isClosed_of_closure_subset
    intro t ht
    have heq : ∀ (g : X → ℝ) (c : ℝ), ContinuousAt g t →
        (∀ s ∈ T, g s = c) → g t = c := by
      intro g c hg he
      have hm : g t ∈ closure ({c} : Set ℝ) :=
        hg.continuousWithinAt.mem_closure ht (fun s hs => he s hs)
      simpa only [closure_singleton, Set.mem_singleton_iff] using hm
    have hb := heq (fun t => β t * (1 + τ t * ρ o)) (β o)
      (by fun_prop) (fun s hs => hs.1)
    have hbt : β t ≠ 0 := by
      intro hz
      exact hβo (by simpa only [hz, zero_mul] using hb.symm)
    exact ⟨hb, heq φ (φ o) (hφ t hbt) (fun s hs => hs.2.1),
      heq (fun t => ρ t * (1 + τ t * ρ o)) (ρ o)
        ((hρ t hbt).mul (continuousAt_const.add (hτ.continuousAt.mul continuousAt_const)))
        (fun s hs => hs.2.2)⟩
  have ho : o ∈ T := by simp only [T, Set.mem_ofPred_eq, hτo, zero_mul, add_zero, mul_one,
    and_self]
  have hall : T = Set.univ := (show IsClopen T from ⟨hclosed, hopen⟩).eq_univ ⟨o, ho⟩
  intro t
  have ht : t ∈ T := by rw [hall]; exact Set.mem_univ t
  exact ht
theorem normalized_hessian_local_transport_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
    let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
    let ρ := fun y => (fderiv ℝ φ y) e
    let V := d + φ x • e
    ∀ᶠ t : ℝ in nhds 0, φ (x + t • V) = φ x ∧
      β (x + t • V) * (1 + t * ρ x) = β x ∧
      ρ (x + t • V) * (1 + t * ρ x) = ρ x := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
  let ρ := fun y => (fderiv ℝ φ y) e
  let V := fun y => d + φ y • e
  have hφ : ContDiffAt ℝ 1 φ x :=
    normalized_hessian_slope_contDiffAt_interior a f hf x hx e d n htest
  have hV : ContDiffAt ℝ 1 V x := contDiffAt_const.add (hφ.smul contDiffAt_const)
  have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x :=
    ((embedding_contDiffAt_interior a f hf x hx 3).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (by norm_num)
  have hb := ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
    (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hnear : ∀ᶠ y in nhds x, y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ β y ≠ 0 := by
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
    exact Filter.Eventually.and ((isOpen_Ioo.preimage hc).mem_nhds hx)
      (hb.continuousAt.eventually_ne htest)
  have haccel : ∀ᶠ y in nhds x, (fderiv ℝ V y) (V y) = 0 := by
    filter_upwards [hnear] with y hy
    have hφy := (normalized_hessian_slope_contDiffAt_interior a f hf y hy.1 e d n
      hy.2).differentiableAt (by norm_num)
    have heq := normalized_hessian_slope_equation_interior a f hf y hy.1 e d n hy.2
    change (fderiv ℝ φ y) (V y) = 0 at heq
    dsimp [V]
    rw [fderiv_const_add, fderiv_smul_const hφy]
    change ((fderiv ℝ φ y) (d + φ y • e)) • e = 0
    rw [heq, zero_smul]
  have hstraight := local_straight_of_zero_self_derivative V x hV haccel
  have hpath : Filter.Tendsto (fun t : ℝ => x + t • V x) (nhds 0) (nhds x) := by
    have hc : Continuous (fun t : ℝ => x + t • V x) := by fun_prop
    simpa using hc.continuousAt.tendsto (x := 0)
  have hpathderiv : ∀ t : ℝ, HasDerivAt (fun r : ℝ => x + r • V x) (V x) t := by
    intro t
    simpa only [one_smul, id_eq] using
      HasDerivAt.const_add x ((hasDerivAt_id t).smul_const (V x))
  have hode : ∀ᶠ t : ℝ in nhds 0,
      HasDerivAt (fun r => β (x + r • V x))
        (-(ρ (x + t • V x)) * β (x + t • V x)) t ∧
      HasDerivAt (fun r => ρ (x + r • V x)) (-(ρ (x + t • V x)) ^ 2) t := by
    filter_upwards [hstraight, hpath.eventually hnear] with t ht hty
    let y := x + t • V x
    have hHy : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) y :=
      ((embedding_contDiffAt_interior a f hf y hty.1 3).fderiv_right (m := 2)
        (by norm_num)).fderiv_right (by norm_num)
    have hβy : DifferentiableAt ℝ β y :=
      (((hHy.clm_apply (contDiffAt_const (c := e))).clm_apply
        (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))).differentiableAt
        (by norm_num)
    have hφy : ContDiffAt ℝ 2 φ y :=
      normalized_hessian_slope_contDiffAt_order a f hf y hty.1 e d n hty.2 2
    have hρy : DifferentiableAt ℝ ρ y :=
      ((hφy.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := e))).differentiableAt (by norm_num)
    have hβd := hβy.hasFDerivAt.comp_hasDerivAt t (hpathderiv t)
    have hρd := hρy.hasFDerivAt.comp_hasDerivAt t (hpathderiv t)
    have hβeq := normalized_hessian_curvature_equation_interior a f hf y hty.1 e d n hty.2
    have hρeq := normalized_hessian_slope_riccati_interior a f hf y hty.1 e d n hty.2
    change (fderiv ℝ β y) (V y) = -(ρ y) * β y at hβeq
    change (fderiv ℝ ρ y) (V y) = -(ρ y) ^ 2 at hρeq
    change V y = V x at ht
    rw [ht] at hβeq hρeq
    exact ⟨hβeq ▸ hβd, hρeq ▸ hρd⟩
  have hβ0 : (fun r : ℝ => β (x + r • V x)) 0 ≠ 0 := by
    simpa only [zero_smul, add_zero] using htest
  have hcon := local_riccati_transport _ _ hβ0 hode
  have he0 : e ≠ 0 := by
    intro he
    exact htest (by simp [he])
  filter_upwards [hstraight, hcon] with t ht hc
  refine ⟨?_, ?_⟩
  · apply smul_left_injective ℝ he0
    exact add_left_cancel (show d + φ (x + t • V x) • e = d + φ x • e from ht)
  · simpa only [zero_smul, add_zero] using hc
theorem normalized_hessian_global_transport_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
    let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
    let ρ := fun y => (fderiv ℝ φ y) e
    let v := d + φ x • e
    ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      β (x + t • v) * (1 + t * ρ x) = β x ∧ φ (x + t • v) = φ x ∧
      ρ (x + t • v) * (1 + t * ρ x) = ρ x := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
  let ρ := fun y => (fderiv ℝ φ y) e
  let v := d + φ x • e
  let I : Set ℝ := {t | (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1}
  have hI : Convex ℝ I := by
    intro t ht u hu b c hb hc hbc
    have hm := (convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1) ht hu hb hc hbc
    have heq : (x + (b • t + c • u) • v) 0 =
        b * (x + t • v) 0 + c * (x + u • v) 0 := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      calc
        x 0 + (b * t + c * u) * v 0 =
            (b + c) * x 0 + (b * t + c * u) * v 0 := by rw [hbc, one_mul]
        _ = b * (x 0 + t * v 0) + c * (x 0 + u * v 0) := by ring
    change (x + (b • t + c • u) • v) 0 ∈ Set.Ioo (0 : ℝ) 1
    rw [heq]
    exact hm
  haveI : PreconnectedSpace I := Subtype.preconnectedSpace hI.isPreconnected
  let L : I → EuclideanSpace ℝ (Fin 2) := fun t => x + (t : ℝ) • v
  have hL : Continuous L := by dsimp [L]; fun_prop
  let o : I := ⟨0, by simpa only [I, Set.mem_ofPred_eq, zero_smul, add_zero] using hx⟩
  have hLo : L o = x := by simp only [L, o, zero_smul, add_zero]
  have hφat : ∀ t : I, β (L t) ≠ 0 → ContDiffAt ℝ 2 φ (L t) := by
    intro t ht
    exact normalized_hessian_slope_contDiffAt_order a f hf (L t) t.property e d n ht 2
  have hβat : ∀ t : I, ContDiffAt ℝ 1 β (L t) := by
    intro t
    have hH : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) (L t) :=
      ((embedding_contDiffAt_interior a f hf (L t) t.property 3).fderiv_right (m := 2)
        (by norm_num)).fderiv_right (by norm_num)
    exact ((hH.clm_apply (contDiffAt_const (c := e))).clm_apply
      (contDiffAt_const (c := e))).inner ℝ (contDiffAt_const (c := n))
  have hβ : Continuous (fun t : I => β (L t)) := continuous_iff_continuousAt.mpr
    (fun t => (hβat t).continuousAt.comp hL.continuousAt)
  have hφ : ∀ t : I, β (L t) ≠ 0 → ContinuousAt (fun t : I => φ (L t)) t := by
    intro t ht
    exact (hφat t ht).continuousAt.comp hL.continuousAt
  have hρ : ∀ t : I, β (L t) ≠ 0 → ContinuousAt (fun t : I => ρ (L t)) t := by
    intro t ht
    have hρat : ContDiffAt ℝ 1 ρ (L t) :=
      ((hφat t ht).fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := e))
    exact hρat.continuousAt.comp hL.continuousAt
  have hloc : ∀ s : I, β (L s) ≠ 0 → φ (L s) = φ (L o) →
      ∀ᶠ t : I in nhds s, φ (L t) = φ (L s) ∧
        β (L t) * (1 + ((t : ℝ) - (s : ℝ)) * ρ (L s)) = β (L s) ∧
        ρ (L t) * (1 + ((t : ℝ) - (s : ℝ)) * ρ (L s)) = ρ (L s) := by
    intro s hs hφs
    have htransport := normalized_hessian_local_transport_interior a f hf (L s)
      s.property e d n hs
    have hshift : Filter.Tendsto (fun t : I => (t : ℝ) - (s : ℝ)) (nhds s) (nhds 0) := by
      have hc : Continuous (fun t : I => (t : ℝ) - (s : ℝ)) := by fun_prop
      simpa only [sub_self] using hc.continuousAt.tendsto (x := s)
    have hvs : d + φ (L s) • e = v := by rw [hφs, hLo]
    filter_upwards [hshift.eventually htransport] with t ht
    have hpoint : L s + ((t : ℝ) - (s : ℝ)) • (d + φ (L s) • e) = L t := by
      rw [hvs]
      dsimp [L]
      module
    simpa only [φ, β, ρ, hpoint] using ht
  have hglobal := global_riccati_transport (fun t : I => (t : ℝ))
    (fun t : I => β (L t)) (fun t : I => φ (L t)) (fun t : I => ρ (L t))
    continuous_subtype_val hβ hφ hρ o rfl (by simpa only [hLo] using htest) hloc
  change ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
    β (x + t • v) * (1 + t * ρ x) = β x ∧ φ (x + t • v) = φ x ∧
      ρ (x + t • v) * (1 + t * ρ x) = ρ x
  intro t ht
  simpa only [L, hLo] using hglobal ⟨t, ht⟩
theorem normalized_hessian_global_null_line_interior
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (e d : EuclideanSpace ℝ (Fin 2)) (n : EuclideanSpace ℝ (Fin 3))
    (htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0) :
    let c := -(inner ℝ ((fderiv ℝ (fderiv ℝ f) x) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n)
    ∀ t : ℝ, (x + t • (d + c • e)) 0 ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ w : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) (x + t • (d + c • e))) (d + c • e) w = 0 := by
  let φ := fun y => -(inner ℝ ((fderiv ℝ (fderiv ℝ f) y) d e) n /
      inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n)
  let β := fun y => inner ℝ ((fderiv ℝ (fderiv ℝ f) y) e e) n
  let ρ := fun y => (fderiv ℝ φ y) e
  let v := d + φ x • e
  change ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
    ∀ w : EuclideanSpace ℝ (Fin 2), (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0
  intro t ht w
  have hg := normalized_hessian_global_transport_interior a f hf x hx e d n htest t ht
  change β (x + t • v) * (1 + t * ρ x) = β x ∧ φ (x + t • v) = φ x ∧
    ρ (x + t • v) * (1 + t * ρ x) = ρ x at hg
  have hβt : β (x + t • v) ≠ 0 := by
    intro hz
    have hb := hg.1
    rw [hz, zero_mul] at hb
    exact htest hb.symm
  have hn := normalized_hessian_null_direction_interior a f hf (x + t • v) ht e d n hβt w
  change (fderiv ℝ (fderiv ℝ f) (x + t • v)) (d + φ (x + t • v) • e) w = 0 at hn
  rw [hg.2.1] at hn
  exact hn
theorem exists_global_hessian_null_generator_nonplanar
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        (∃ e : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (x + t • v)) e e ≠ 0) ∧
        ∀ w : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0 := by
  obtain ⟨e, he⟩ := exists_nonzero_hessian_diagonal_interior a f hf x hx hnonzero
  let n := (fderiv ℝ (fderiv ℝ f) x) e e
  have htest : inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n ≠ 0 := by
    exact ne_of_gt (by simpa only [n, real_inner_self_eq_norm_sq] using
      (sq_pos_of_pos (norm_pos_iff.mpr he)))
  have he0 : e ≠ 0 := by
    intro h
    exact he (by simp [h])
  obtain ⟨d, hd⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := EuclideanSpace ℝ (Fin 2)) (by simp) he0
  let c := -(inner ℝ ((fderiv ℝ (fderiv ℝ f) x) d e) n /
    inner ℝ ((fderiv ℝ (fderiv ℝ f) x) e e) n)
  let v := d + c • e
  have hv : v ≠ 0 := by
    intro h
    have hdce : (-c) • e = d := by
      have hd' := eq_neg_of_add_eq_zero_left h
      simpa only [neg_smul] using hd'.symm
    exact ((LinearIndependent.pair_iff' he0).mp hd (-c)) hdce
  refine ⟨v, hv, ?_⟩
  intro t ht
  refine ⟨⟨e, ?_⟩,
    normalized_hessian_global_null_line_interior a f hf x hx e d n htest t ht⟩
  intro hz
  have hg := (normalized_hessian_global_transport_interior a f hf x hx e d n htest t ht).1
  change inner ℝ ((fderiv ℝ (fderiv ℝ f) (x + t • v)) e e) n * _ = _ at hg
  rw [hz, inner_zero_left, zero_mul] at hg
  exact htest hg.symm
theorem exists_constant_directional_generator_nonplanar
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ ∀ t : ℝ,
      x + t • v ∈ OptimalMoebius.unitStrip →
        (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
          (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  obtain ⟨v, hv, hline⟩ := exists_global_hessian_null_generator_nonplanar a f hf x hx hnonzero
  exact ⟨v, hv, constant_directional_derivative_of_hessian_null_line a f hf x hx v
    (fun t ht => (hline t ht).2 v)⟩
theorem exists_unit_global_hessian_null_generator_nonplanar
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
      ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ w : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0 := by
  obtain ⟨v, hv, hline⟩ := exists_global_hessian_null_generator_nonplanar a f hf x hx hnonzero
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm]
  · intro t ht w
    have hp : x + t • (‖v‖⁻¹ • v) = x + (t * ‖v‖⁻¹) • v := by module
    rw [hp] at ht ⊢
    simp only [map_smul, smul_apply, (hline (t * ‖v‖⁻¹) ht).2 w, smul_zero]
theorem exists_global_hessian_null_generator_of_nonplanar_closure
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hxclosure : x ∈ closure {y : EuclideanSpace ℝ (Fin 2) |
      y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) y) p q ≠ 0}) :
    ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
      ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ w : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (x + t • v)) v w = 0 := by
  obtain ⟨z, hz, hztend⟩ := mem_closure_iff_seq_limit.mp hxclosure
  have hex : ∀ k : ℕ, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
      ∀ t : ℝ, (z k + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ w : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (z k + t • v)) v w = 0 := by
    intro k
    exact exists_unit_global_hessian_null_generator_nonplanar a f hf (z k) (hz k).1 (hz k).2
  choose v hv hline using hex
  have hvsphere : ∀ k : ℕ, v k ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro k
    simpa only [Metric.mem_sphere, dist_zero_right] using hv k
  obtain ⟨v₀, hv₀, σ, hσ, hvtend⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).tendsto_subseq hvsphere
  refine ⟨v₀, ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hv₀
  · intro t ht w
    have hpath : Filter.Tendsto (fun k => z (σ k) + t • v (σ k)) Filter.atTop
        (nhds (x + t • v₀)) :=
      (hztend.comp hσ.tendsto_atTop).add (tendsto_const_nhds.smul hvtend)
    have hc : Continuous (fun y : EuclideanSpace ℝ (Fin 2) => y 0) := by fun_prop
    have hnear : ∀ᶠ k in Filter.atTop,
        (z (σ k) + t • v (σ k)) 0 ∈ Set.Ioo (0 : ℝ) 1 :=
      hpath.eventually ((isOpen_Ioo.preimage hc).mem_nhds ht)
    have hH : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (x + t • v₀) :=
      (((embedding_contDiffAt_interior a f hf (x + t • v₀) ht 2).fderiv_right (m := 1)
        (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    have heval : ContinuousAt
        (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          (fderiv ℝ (fderiv ℝ f) p.1) p.2 w) (x + t • v₀, v₀) :=
      ((hH.comp (x := (x + t • v₀, v₀)) continuous_fst.continuousAt).clm_apply
        continuous_snd.continuousAt).clm_apply continuousAt_const
    have hpair : Filter.Tendsto
        (fun k => (z (σ k) + t • v (σ k), v (σ k))) Filter.atTop
        (nhds (x + t • v₀, v₀)) := hpath.prodMk_nhds hvtend
    have hval := heval.tendsto.comp hpair
    have hzero : ∀ᶠ k in Filter.atTop,
        (fderiv ℝ (fderiv ℝ f) (z (σ k) + t • v (σ k))) (v (σ k)) w = 0 := by
      filter_upwards [hnear] with k hk
      exact hline (σ k) t hk w
    have hzeroeq :
        (fun k => (fderiv ℝ (fderiv ℝ f) (z (σ k) + t • v (σ k))) (v (σ k)) w)
          =ᶠ[Filter.atTop] (fun _ => 0) := hzero
    have hzero' : Filter.Tendsto
        (fun k => (fderiv ℝ (fderiv ℝ f) (z (σ k) + t • v (σ k))) (v (σ k)) w)
        Filter.atTop (nhds 0) := tendsto_const_nhds.congr' hzeroeq.symm
    exact tendsto_nhds_unique hval hzero'
theorem exists_constant_directional_generator_of_nonplanar_closure
    (a : ℝ) (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hxclosure : x ∈ closure {y : EuclideanSpace ℝ (Fin 2) |
      y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) y) p q ≠ 0}) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ ∀ t : ℝ,
      x + t • v ∈ OptimalMoebius.unitStrip →
        (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
          (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  obtain ⟨v, hv, hline⟩ :=
    exists_global_hessian_null_generator_of_nonplanar_closure a f hf x hx hxclosure
  have hv0 : v ≠ 0 := by
    intro hz
    simpa only [hz, norm_zero, zero_ne_one] using hv
  exact ⟨v, hv0, constant_directional_derivative_of_hessian_null_line a f hf x hx v
    (fun t ht => hline t ht v)⟩
theorem exists_flat_neighborhood_of_not_nonplanar_closure
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 2))
    (hxclosure : x ∉ closure {y : EuclideanSpace ℝ (Fin 2) |
      y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) y) p q ≠ 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : EuclideanSpace ℝ (Fin 2), dist y x < ε →
      y 0 ∈ Set.Ioo (0 : ℝ) 1 → ∀ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) y) p q = 0 := by
  have hnb : (closure {y : EuclideanSpace ℝ (Fin 2) |
      y 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) y) p q ≠ 0})ᶜ ∈ nhds x :=
    isClosed_closure.isOpen_compl.mem_nhds hxclosure
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnb
  refine ⟨ε, hε, ?_⟩
  intro y hy hiy p q
  by_contra hpq
  have hcy := hball (show y ∈ Metric.ball x ε from hy)
  exact hcy (subset_closure ⟨hiy, p, q, hpq⟩)
theorem exists_comparable_endpoints_of_chain
    (K : Set (ℝ × ℝ))
    (hchain : ∀ p ∈ K, ∀ q ∈ K,
      (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2))
    (s c : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ l r : ℝ, c = (1 - s) * l + s * r ∧
      ∀ p ∈ K, (l ≤ p.1 ∧ r ≤ p.2) ∨ (p.1 ≤ l ∧ p.2 ≤ r) := by
  classical
  by_cases hne : K.Nonempty
  · let T : ℝ × ℝ → ℝ := fun p => (c - s * p.2) / (1 - s)
    let B : Set ℝ := (fun p : ℝ × ℝ => min p.1 (T p)) '' K
    have hbounds (p : ℝ × ℝ) (hp : p ∈ K) (q : ℝ × ℝ) (hq : q ∈ K) :
        min p.1 (T p) ≤ max q.1 (T q) := by
      rcases hchain p hp q hq with h | h
      · exact (min_le_left _ _).trans (h.1.trans (le_max_left _ _))
      · have hT : T p ≤ T q := by
          apply (div_le_div_iff_of_pos_right (sub_pos.mpr hs.2)).mpr
          nlinarith [mul_le_mul_of_nonneg_left h.2 hs.1.le]
        exact (min_le_right _ _).trans (hT.trans (le_max_right _ _))
    obtain ⟨p0, hp0⟩ := hne
    have hBne : B.Nonempty := ⟨_, ⟨p0, hp0, rfl⟩⟩
    have hBbdd : BddAbove B := by
      refine ⟨max p0.1 (T p0), ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact hbounds p hp p0 hp0
    let l : ℝ := sSup B
    let r : ℝ := (c - (1 - s) * l) / s
    have hsum : c = (1 - s) * l + s * r := by
      dsimp [r]
      field_simp [ne_of_gt hs.1]
      ring
    refine ⟨l, r, hsum, ?_⟩
    intro p hp
    have hmin : min p.1 (T p) ≤ l := le_csSup hBbdd ⟨p, hp, rfl⟩
    have hmax : l ≤ max p.1 (T p) := by
      apply csSup_le hBne
      rintro _ ⟨q, hq, rfl⟩
      exact hbounds q hq p hp
    have hTmul : (1 - s) * T p = c - s * p.2 := by
      dsimp [T]
      field_simp [ne_of_gt (sub_pos.mpr hs.2)]
    have hTle (h : T p ≤ l) : r ≤ p.2 := by
      apply (mul_le_mul_iff_right₀ hs.1).mp
      nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs.2.le)]
    have hleT (h : l ≤ T p) : p.2 ≤ r := by
      apply (mul_le_mul_iff_right₀ hs.1).mp
      nlinarith [mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hs.2.le)]
    rcases min_le_iff.mp hmin with hL | hT
    · rcases le_max_iff.mp hmax with hL' | hT'
      · rcases le_total r p.2 with hr | hr
        · exact Or.inl ⟨hL', hr⟩
        · exact Or.inr ⟨hL, hr⟩
      · exact Or.inr ⟨hL, hleT hT'⟩
    · rcases le_max_iff.mp hmax with hL' | hT'
      · exact Or.inl ⟨hL', hTle hT⟩
      · rcases le_total l p.1 with hL | hL
        · exact Or.inl ⟨hL, hTle hT⟩
        · exact Or.inr ⟨hL, hleT hT'⟩
  · refine ⟨c, c, by ring, ?_⟩
    intro p hp
    exact (hne ⟨p, hp⟩).elim
theorem exists_nonplanar_null_spanning_line_through
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f) x) p q ≠ 0) :
    ∃ l r : ℝ,
      x = (!₂[0, l] + x 0 • (!₂[1, r] - !₂[0, l])) ∧
      ∀ u ∈ Set.Ioo (0 : ℝ) 1,
        (∃ p q : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (!₂[0, l] + u • (!₂[1, r] - !₂[0, l]))) p q ≠ 0) ∧
        ∀ w : EuclideanSpace ℝ (Fin 2),
          (fderiv ℝ (fderiv ℝ f) (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])))
            !₂[1, r - l] w = 0 := by
  obtain ⟨v, hv, hnull⟩ := exists_global_hessian_null_generator_nonplanar a f hf x hx hnonzero
  have hz (t : ℝ) (ht : (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1) :
      (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v = 0 := (hnull t ht).2 v
  have hline := affine_generator_of_interior_constant_directional_derivative a f hf x hx v
    (constant_directional_derivative_interior_of_zero_hessian a f hf x hx v hz)
  have hv0 : v 0 ≠ 0 := affine_generator_transverse a ha f hf x ⟨hx.1.le, hx.2.le⟩ v hv hline
  let l : ℝ := x 1 + ((0 - x 0) / v 0) * v 1
  let r : ℝ := x 1 + ((1 - x 0) / v 0) * v 1
  have hparam (u : ℝ) :
      (!₂[0, l] + u • (!₂[1, r] - !₂[0, l]) : EuclideanSpace ℝ (Fin 2)) =
        x + ((u - x 0) / v 0) • v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [l, r] <;> field_simp <;> ring
  have hdir : (!₂[1, r - l] : EuclideanSpace ℝ (Fin 2)) = (v 0)⁻¹ • v := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [hv0]
    · simp [l, r]
      field_simp
      ring
  refine ⟨l, r, ?_, ?_⟩
  · rw [hparam]
    simp
  · intro u hu
    have hmem : (x + ((u - x 0) / v 0) • v) 0 ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [← hparam]
      simpa using hu
    obtain ⟨⟨e, he⟩, hn⟩ := hnull _ hmem
    rw [hparam]
    refine ⟨⟨e, e, he⟩, ?_⟩
    intro w
    rw [hdir]
    simp only [map_smul, smul_apply, hn w, smul_zero]
theorem comparable_endpoints_eq_of_interior_intersection
    (l r l' r' u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1)
    (hcomp : (l ≤ l' ∧ r ≤ r') ∨ (l' ≤ l ∧ r' ≤ r))
    (hpoint :
      (!₂[0, l] + u • (!₂[1, r] - !₂[0, l]) : EuclideanSpace ℝ (Fin 2)) =
        !₂[0, l'] + u • (!₂[1, r'] - !₂[0, l'])) :
    l = l' ∧ r = r' := by
  have hsum := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hpoint
  change l + u * (r - l) = l' + u * (r' - l') at hsum
  have hinj (b c b' c' : ℝ) (hb : b ≤ b') (hc : c ≤ c')
      (heq : b + u * (c - b) = b' + u * (c' - b')) : b = b' ∧ c = c' := by
    have hleft := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hu.2.le)
    have hright := mul_le_mul_of_nonneg_left hc hu.1.le
    have hb' : (1 - u) * b = (1 - u) * b' := by nlinarith
    have hc' : u * c = u * c' := by nlinarith
    exact ⟨mul_left_cancel₀ (ne_of_gt (sub_pos.mpr hu.2)) hb',
      mul_left_cancel₀ (ne_of_gt hu.1) hc'⟩
  rcases hcomp with h | h
  · exact hinj l r l' r' h.1 h.2 hsum
  · have heq := hinj l' r' l r h.1 h.2 hsum.symm
    exact ⟨heq.1.symm, heq.2.symm⟩
theorem exists_global_hessian_null_generator_interior
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v = 0 := by
  classical
  let K : Set (ℝ × ℝ) := {p | ∀ u ∈ Set.Ioo (0 : ℝ) 1,
    (∃ e d : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f)
        (!₂[0, p.1] + u • (!₂[1, p.2] - !₂[0, p.1]))) e d ≠ 0) ∧
    ∀ w : EuclideanSpace ℝ (Fin 2),
      (fderiv ℝ (fderiv ℝ f)
        (!₂[0, p.1] + u • (!₂[1, p.2] - !₂[0, p.1]))) !₂[1, p.2 - p.1] w = 0}
  have hchain : ∀ p ∈ K, ∀ q ∈ K,
      (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2) := by
    intro p hp q hq
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact Or.inl ⟨h.le, nonplanar_null_spanning_lines_ordered f p.1 p.2 q.1 q.2
        hp (fun u hu => (hq u hu).2) h⟩
    · rcases le_total p.2 q.2 with hr | hr
      · exact Or.inl ⟨h.le, hr⟩
      · exact Or.inr ⟨h.ge, hr⟩
    · exact Or.inr ⟨h.le, nonplanar_null_spanning_lines_ordered f q.1 q.2 p.1 p.2
        hq (fun u hu => (hp u hu).2) h⟩
  obtain ⟨l, r, hsum, hcomp⟩ :=
    exists_comparable_endpoints_of_chain K hchain (x 0) (x 1) hx
  have hxparam : x = (!₂[0, l] + x 0 • (!₂[1, r] - !₂[0, l])) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp
    · change x 1 = l + x 0 * (r - l)
      nlinarith [hsum]
  let v : EuclideanSpace ℝ (Fin 2) := !₂[1, r - l]
  refine ⟨v, ?_, ?_⟩
  · intro hzero
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hzero
    simp [v] at h
  · intro t ht
    have hy : x + t • v =
        !₂[0, l] + (x 0 + t) • (!₂[1, r] - !₂[0, l]) := by
      calc
        _ = (!₂[0, l] + x 0 • (!₂[1, r] - !₂[0, l])) + t • v :=
          congrArg (fun z => z + t • v) hxparam
        _ = _ := by
          apply PiLp.ext
          intro i
          fin_cases i <;> simp [v]
          ring
    have hu : x 0 + t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [hy] using ht
    by_cases hnonzero : ∃ p q : EuclideanSpace ℝ (Fin 2),
        (fderiv ℝ (fderiv ℝ f) (x + t • v)) p q ≠ 0
    · obtain ⟨l', r', hpoint, hK⟩ := exists_nonplanar_null_spanning_line_through
        a ha f hf (x + t • v) ht hnonzero
      have hintersect :
          (!₂[0, l] + (x 0 + t) • (!₂[1, r] - !₂[0, l]) :
            EuclideanSpace ℝ (Fin 2)) =
          !₂[0, l'] + (x 0 + t) • (!₂[1, r'] - !₂[0, l']) := by
        simpa [hy] using hpoint
      obtain ⟨hl, hr⟩ := comparable_endpoints_eq_of_interior_intersection
        l r l' r' (x 0 + t) hu (hcomp (l', r') hK) hintersect
      rw [hy]
      change (fderiv ℝ (fderiv ℝ f)
        (!₂[0, l] + (x 0 + t) • (!₂[1, r] - !₂[0, l]))) !₂[1, r - l] v = 0
      rw [hl, hr]
      exact (hK (x 0 + t) hu).2 v
    · by_contra hzero
      exact hnonzero ⟨v, v, hzero⟩
theorem exists_global_hessian_null_generator_of_flat_neighborhood
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1)
    (_hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ y : EuclideanSpace ℝ (Fin 2),
      dist y x < ε → y 0 ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ p q : EuclideanSpace ℝ (Fin 2), (fderiv ℝ (fderiv ℝ f) y) p q = 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ t : ℝ, (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1 →
        (fderiv ℝ (fderiv ℝ f) (x + t • v)) v v = 0 := by
  exact exists_global_hessian_null_generator_interior a ha f hf x hx
theorem exists_constant_directional_generator
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ ∀ t : ℝ,
      x + t • v ∈ OptimalMoebius.unitStrip →
        (fderivWithin ℝ f OptimalMoebius.unitStrip (x + t • v)) v =
          (fderivWithin ℝ f OptimalMoebius.unitStrip x) v := by
  obtain ⟨v, hv, hnull⟩ := exists_global_hessian_null_generator_interior a ha f hf x hx
  exact ⟨v, hv, constant_directional_derivative_of_hessian_null_line a f hf x hx v hnull⟩
theorem exists_spanning_ruling_through_interior
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x 0 ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ l r : ℝ, x = (!₂[0, l] + (x 0) • (!₂[1, r] - !₂[0, l])) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        f (!₂[0, l] + u • (!₂[1, r] - !₂[0, l])) =
          f !₂[0, l] + u • (f !₂[1, r] - f !₂[0, l]) := by
  obtain ⟨v, hv, hconst⟩ := exists_constant_directional_generator a ha f hf x hx
  exact exists_spanning_ruling_of_constant_directional_derivative a ha f hf x hx v hv hconst
theorem orderedStraightFamily_of_embedding
    (a : ℝ) (ha : 0 < a)
    (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hf : OptimalMoebius.IsMoebiusEmbedding a f) :
    OrderedStraightFamily a f := by
  apply orderedStraightFamily_of_midline_spanning a ha f hf
  intro c
  obtain ⟨l, r, hx, hstraight⟩ := exists_spanning_ruling_through_interior a ha f hf
    (!₂[(1 / 2 : ℝ), c]) (by norm_num)
  refine ⟨l, r, ?_, hstraight⟩
  have hheight := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hx
  simp at hheight
  linarith
end Submission.Helpers
