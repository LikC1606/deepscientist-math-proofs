import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Order.Zorn
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
namespace Submission.Helpers

theorem sqrt_coordinate_metric_chart_derivative_eq_norm : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2) →
      ∀ (x : M), x ∈ (extChartAt I p).source → ∀ v : TangentSpace I x,
        Real.sqrt (g (extChartAt I p x)
          (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v)
          (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v)) = ‖v‖ := by
  intro E _ _ H _ I M _ _ _ _ p g hg x hx v
  exact (open scoped Bundle in by
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    have hquad := hg (extChartAt I p x) ((extChartAt I p).map_source hx)
      (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v)
    have hinv : mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) (extChartAt I p x)
          (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v) = v :=
      congrArg (fun A => A v)
        (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) hx)
    rw [hinv, (extChartAt I p).left_inv hx] at hquad
    rw [hquad, Real.sqrt_sq (norm_nonneg v)])

theorem exists_smooth_test_integral_one : open MeasureTheory in
    ∀ (a b : ℝ), a < b → ∃ θ : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ Set.Ioo a b ∧ (∫ t : ℝ, θ t) = 1 := by
  intro a b hab
  let f : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  refine ⟨f.normed MeasureTheory.volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
    f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro t ht
  have ht' : |t - (a + b) / 2| ≤ (b - a) / 4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, f] using ht
  obtain ⟨hl, hr⟩ := abs_le.mp ht'
  constructor <;> linarith

theorem integrable_test_smul_of_locallyIntegrableOn : open MeasureTheory in
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {U : Set ℝ} {P : ℝ → F}, LocallyIntegrableOn P U →
      ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
      Integrable (fun t => φ t • P t) := by
  intro F _ _ U P hP φ hφ hc hs
  apply (MeasureTheory.integrableOn_iff_integrable_of_support_subset
    (show Function.support (fun t => φ t • P t) ⊆ tsupport φ from
      (Function.support_smul_subset_left φ P).trans (subset_tsupport φ))).mp
  exact (hP.integrableOn_compact_subset hs hc.isCompact).continuousOn_smul
    hφ.continuousOn hc.isCompact

theorem ae_eq_const_of_zero_mean_test_integral_zero : open MeasureTheory in
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (a b : ℝ), a < b → ∀ P : ℝ → F, LocallyIntegrableOn P (Set.Ioo a b) →
      (∀ φ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Set.Ioo a b → (∫ t : ℝ, φ t) = 0 →
        (∫ t : ℝ, φ t • P t) = 0) →
      ∃ C : F, ∀ᵐ t : ℝ, t ∈ Set.Ioo a b → P t = C := by
  intro F _ _ _ a b hab P hP hzero
  obtain ⟨θ, hθ, hcθ, hsθ, hiθ⟩ := exists_smooth_test_integral_one a b hab
  let C : F := ∫ t : ℝ, θ t • P t
  have hconst : MeasureTheory.LocallyIntegrableOn (fun _ : ℝ => C) (Set.Ioo a b) :=
    MeasureTheory.locallyIntegrableOn_const C
  have hvanish : ∀ φ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ Set.Ioo a b →
      (∫ t : ℝ, φ t • (P t - C)) = 0 := by
    intro φ hφ hcφ hsφ
    let k : ℝ := ∫ t : ℝ, φ t
    let η : ℝ → ℝ := fun t => φ t - k * θ t
    have hη : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) η :=
      hφ.sub (contDiff_const.mul hθ)
    have hcη : HasCompactSupport η := hcφ.sub hcθ.mul_left
    have hsη : tsupport η ⊆ Set.Ioo a b :=
      (tsupport_sub φ (fun t => k * θ t)).trans
        (Set.union_subset hsφ (tsupport_mul_subset_right.trans hsθ))
    have hiφ : MeasureTheory.Integrable φ :=
      hφ.continuous.integrable_of_hasCompactSupport hcφ
    have hiθ' : MeasureTheory.Integrable θ :=
      hθ.continuous.integrable_of_hasCompactSupport hcθ
    have hiη : (∫ t : ℝ, η t) = 0 := by
      rw [MeasureTheory.integral_sub hiφ (hiθ'.const_mul k)]
      simp only [MeasureTheory.integral_const_mul, hiθ, mul_one, k, sub_self]
    have heq := hzero η hη hcη hsη hiη
    have hiφP := integrable_test_smul_of_locallyIntegrableOn hP φ hφ.continuous hcφ hsφ
    have hiθP := integrable_test_smul_of_locallyIntegrableOn hP θ hθ.continuous hcθ hsθ
    have hpair : (∫ t : ℝ, φ t • P t) = k • C := by
      have hfun : (fun t => η t • P t) =
          (fun t => φ t • P t - k • (θ t • P t)) := by
        funext t
        simp only [η, sub_smul, mul_smul]
      rw [hfun] at heq
      have hiθPk : MeasureTheory.Integrable (fun t => k • (θ t • P t)) := by
        exact hiθP.fun_smul k
      rw [MeasureTheory.integral_sub hiφP hiθPk,
        MeasureTheory.integral_smul] at heq
      exact sub_eq_zero.mp heq
    have hiφC := hiφ.smul_const C
    simp_rw [smul_sub]
    rw [MeasureTheory.integral_sub hiφP hiφC, integral_smul_const, hpair]
    exact sub_self _
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hP.sub hconst) hvanish
  refine ⟨C, ?_⟩
  filter_upwards [hae] with t ht
  intro htab
  exact sub_eq_zero.mp (ht htab)



theorem radial_gauss_cauchy_schwarz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w : E, B v w = B w v)
    (hnonneg : ∀ v : E, 0 ≤ B v v)
    (L : E →L[ℝ] E) (u : E)
    (hGauss : ∀ w : E, B (L u) (L w) = B₀ u w) (w : E) :
    |B₀ u w| ≤ Real.sqrt (B₀ u u) * Real.sqrt (B (L w) (L w)) := by
  have hdisc := discrim_le_zero
    (a := B (L u) (L u)) (b := 2 * B (L u) (L w))
    (c := B (L w) (L w)) (fun t : ℝ => by
      have h := hnonneg (t • L u + L w)
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at h
      rw [hsymm (L w) (L u)] at h
      nlinarith)
  have hsq : B (L u) (L w) ^ 2 ≤ B (L u) (L u) * B (L w) (L w) := by
    dsimp [discrim] at hdisc
    nlinarith
  have h := Real.abs_le_sqrt hsq
  rw [Real.sqrt_mul (hnonneg (L u))] at h
  simpa only [hGauss] using h

theorem hasDerivAt_bilinear_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w : E, B₀ v w = B₀ w v)
    {γ : ℝ → E} {v : E} {t : ℝ} (hγ : HasDerivAt γ v t)
    (hpos : 0 < B₀ (γ t) (γ t)) :
    HasDerivAt (fun s => Real.sqrt (B₀ (γ s) (γ s)))
      (B₀ (γ t) v / Real.sqrt (B₀ (γ t) (γ t))) t := by
  have h := (B₀.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hγ
  have hq : HasDerivAt (fun s => B₀ (γ s) (γ s)) (2 * B₀ (γ t) v) t := by
    convert h using 1 <;> simp only [Function.comp_apply, hsymm v (γ t)] <;> ring
  convert hq.sqrt (ne_of_gt hpos) using 1 <;> field_simp

theorem radial_gauss_radius_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w : E, B v w = B w v)
    (hnonneg : ∀ v : E, 0 ≤ B v v)
    (hsymm₀ : ∀ v w : E, B₀ v w = B₀ w v)
    (L : E →L[ℝ] E) {γ : ℝ → E} {v : E} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hpos : 0 < B₀ (γ t) (γ t))
    (hGauss : ∀ w : E, B (L (γ t)) (L w) = B₀ (γ t) w) :
    HasDerivAt (fun s => Real.sqrt (B₀ (γ s) (γ s)))
      (B₀ (γ t) v / Real.sqrt (B₀ (γ t) (γ t))) t ∧
      |B₀ (γ t) v / Real.sqrt (B₀ (γ t) (γ t))| ≤
        Real.sqrt (B (L v) (L v)) := by
  refine ⟨hasDerivAt_bilinear_radius B₀ hsymm₀ hγ hpos, ?_⟩
  have hsqrt : 0 < Real.sqrt (B₀ (γ t) (γ t)) := Real.sqrt_pos.2 hpos
  rw [abs_div, abs_of_pos hsqrt, div_le_iff₀ hsqrt]
  simpa only [mul_comm] using
    radial_gauss_cauchy_schwarz B B₀ hsymm hnonneg L (γ t) hGauss v


theorem exists_smooth_compact_primitive_of_integral_zero : open MeasureTheory in
    ∀ (a b : ℝ) (hab : a < b) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcompact : HasCompactSupport φ) (hsub : tsupport φ ⊆ Set.Ioo a b)
    (hint : (∫ t : ℝ, φ t) = 0),
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧
      HasCompactSupport ψ ∧ tsupport ψ ⊆ Set.Ioo a b ∧
      ∀ t : ℝ, deriv ψ t = φ t := by
  intro a b hab φ hφ hcompact hsub hint
  classical
  let ψ : ℝ → ℝ := fun t => ∫ s in a..t, φ s
  have hderiv (t : ℝ) : HasDerivAt ψ (φ t) t :=
    (hφ.continuous.integral_hasStrictDerivAt a t).hasDerivAt
  have hderiv_eq : deriv ψ = φ := funext fun t => (hderiv t).deriv
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    contDiff_infty_iff_deriv.mpr
      ⟨fun t => (hderiv t).differentiableAt, hderiv_eq.symm ▸ hφ⟩
  by_cases hne : (tsupport φ).Nonempty
  · obtain ⟨c, hc⟩ := hcompact.isCompact.exists_isLeast hne
    obtain ⟨d, hd⟩ := hcompact.isCompact.exists_isGreatest hne
    have hac : a < c := (hsub hc.1).1
    have hdb : d < b := (hsub hd.1).2
    have hleft (t : ℝ) (ht : t < c) : ψ t = 0 := by
      change (∫ s in a..t, φ s) = 0
      calc
        (∫ s in a..t, φ s) = ∫ s in a..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr_uIoo
          intro s hs
          have hsc : s < c := lt_trans hs.2 (max_lt hac ht)
          by_contra hφs
          exact (not_le_of_gt hsc) (hc.2 (subset_tsupport φ hφs))
        _ = 0 := by simp
    have hright (t : ℝ) (ht : d < t) : ψ t = 0 := by
      change (∫ s in a..t, φ s) = 0
      refine (intervalIntegral.integral_eq_integral_of_support_subset ?_).trans hint
      intro s hs
      have hs' : s ∈ tsupport φ := subset_tsupport φ hs
      exact ⟨(hsub hs').1, (hd.2 hs').trans ht.le⟩
    have hsupport : Function.support ψ ⊆ Set.Icc c d := by
      intro t ht
      change ψ t ≠ 0 at ht
      constructor
      · by_contra hct
        exact ht (hleft t (lt_of_not_ge hct))
      · by_contra htd
        exact ht (hright t (lt_of_not_ge htd))
    have htsupport : tsupport ψ ⊆ Set.Icc c d :=
      closure_minimal hsupport isClosed_Icc
    refine ⟨ψ, hsmooth,
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport, ?_,
      fun t => (hderiv t).deriv⟩
    intro t ht
    exact ⟨hac.trans_le (htsupport ht).1, lt_of_le_of_lt (htsupport ht).2 hdb⟩
  · have hφzero : φ = 0 := tsupport_eq_empty_iff.mp
      (Set.not_nonempty_iff_eq_empty.mp hne)
    refine ⟨0, contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.of_support_subset_isCompact (K := (∅ : Set ℝ))
        isCompact_empty (by simp)
    · simp
    · intro t
      simp [hφzero]

theorem ae_eq_const_of_test_deriv_integral_zero : open MeasureTheory in
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (a b : ℝ), a < b → ∀ P : ℝ → F, LocallyIntegrableOn P (Set.Ioo a b) →
      (∀ φ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ Set.Ioo a b →
        (∫ t : ℝ, deriv φ t • P t) = 0) →
      ∃ C : F, ∀ᵐ t : ℝ, t ∈ Set.Ioo a b → P t = C := by
  intro F _ _ _ a b hab P hP hderiv
  apply ae_eq_const_of_zero_mean_test_integral_zero a b hab P hP
  intro φ hφ hcφ hsφ hiφ
  obtain ⟨ψ, hψ, hcψ, hsψ, hdψ⟩ :=
    exists_smooth_compact_primitive_of_integral_zero a b hab φ hφ hcφ hsφ hiφ
  simpa only [hdψ] using hderiv ψ hψ hcψ hsψ


theorem eq_affine_of_hasDerivAt_sq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (hA : A.comp A = 0) (S : Set ℝ)
    (hS : IsOpen S) (hconn : IsPreconnected S) (h0 : (0 : ℝ) ∈ S)
    (X : ℝ → E) (hX : ∀ t ∈ S, HasDerivAt X (A (X t)) t)
    (t : ℝ) (ht : t ∈ S) :
    X t = X 0 + t • A (X 0) := by
  have hAX : ∀ u ∈ S, HasDerivAt (fun s => A (X s)) 0 u := by
    intro u hu
    simpa only [Function.comp_def, ← ContinuousLinearMap.comp_apply, hA,
      zero_apply] using
      (A.hasFDerivAt.comp_hasDerivAt u (hX u hu))
  have hAX_const : ∀ u ∈ S, A (X u) = A (X 0) := by
    intro u hu
    exact hS.is_const_of_deriv_eq_zero hconn
      (fun s hs => (hAX s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hAX s hs).deriv) hu h0
  have hline : ∀ u : ℝ,
      HasDerivAt (fun s => X 0 + s • A (X 0)) (A (X 0)) u := by
    intro u
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id u).smul_const (A (X 0))).const_add (X 0)
  apply hS.eqOn_of_deriv_eq hconn
    (fun s hs => (hX s hs).differentiableAt.differentiableWithinAt)
    (fun s _ => (hline s).differentiableAt.differentiableWithinAt) ?_ h0
    (by simp) ht
  intro s hs
  rw [(hX s hs).deriv, (hline s).deriv]
  exact hAX_const s hs

theorem eq_const_of_lipschitz_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {T : Set E} {K : NNReal} {p : E} {a b : ℝ}
    (hF : LipschitzOnWith K F T) (hp : p ∈ T) (hFp : F p = 0)
    (h0 : (0 : ℝ) ∈ Set.Ioo a b) {X : ℝ → E}
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (F (X t)) t ∧ X t ∈ T)
    (hX0 : X 0 = p) : ∀ t ∈ Set.Ioo a b, X t = p := by
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => F) (s := fun _ => T)
    (g := fun _ => p) (fun _ _ => hF) h0 hX
    (fun t _ => ⟨by simpa only [hFp] using hasDerivAt_const t p, hp⟩) hX0


theorem differentiableAt_velocity_of_momentum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t)) (hx : DifferentiableAt ℝ x t)
    (hp : DifferentiableAt ℝ p t)
    (hinv : ∀ᶠ s in nhds t, (g (x s)).IsInvertible)
    (hpx : ∀ᶠ s in nhds t, p s = g (x s) (v s)) :
    DifferentiableAt ℝ v t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
  have hi₀ : DifferentiableAt ℝ
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] ℝ) →L[ℝ] E)
      (g (x t)) :=
    (hinv.self_of_nhds.contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)
  have hi : DifferentiableAt ℝ
      (fun s => ContinuousLinearMap.inverse (g (x s))) t := by
    simpa only [Function.comp_def] using
      (DifferentiableAt.comp (f := g ∘ x) (g := ContinuousLinearMap.inverse) t
        hi₀ (hg.comp t hx))
  apply (hi.clm_apply hp).congr_of_eventuallyEq
  filter_upwards [hinv, hpx] with s hs heq
  rw [heq, hs.inverse_apply_self]

theorem coordinate_geodesic_of_momentum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {p' : E →L[ℝ] ℝ} {t : ℝ}
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hg : HasFDerivAt g D (x t)) (hx : HasDerivAt x (v t) t)
    (hp : HasDerivAt p p' t)
    (hp' : ∀ z : E, p' z = (2 : ℝ)⁻¹ * D z (v t) (v t))
    (hinv : ∀ᶠ s in nhds t, (g (x s)).IsInvertible)
    (hpx : ∀ᶠ s in nhds t, p s = g (x s) (v s))
    (hΓ : ∀ z : E, 2 * g (x t) (Γ (v t) (v t)) z =
      D (v t) (v t) z + D (v t) (v t) z - D z (v t) (v t)) :
    HasDerivAt v (-Γ (v t) (v t)) t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  have hv : DifferentiableAt ℝ v t :=
    differentiableAt_velocity_of_momentum hg.differentiableAt hx.differentiableAt
      hp.differentiableAt hinv hpx
  have heq := ((hg.comp_hasDerivAt t hx).clm_apply hv.hasDerivAt
    ).congr_of_eventuallyEq hpx
  have hder := heq.unique hp
  have hmetric : g (x t) (deriv v t) = g (x t) (-Γ (v t) (v t)) := by
    ext z
    have h := congrArg (fun L : E →L[ℝ] ℝ => L z) hder
    change D (v t) (v t) z + g (x t) (deriv v t) z = p' z at h
    rw [hp'] at h
    have hK := hΓ z
    simp only [map_neg, neg_apply]
    norm_num at h
    linarith
  have hv' : deriv v t = -Γ (v t) (v t) := by
    simpa only [hinv.self_of_nhds.inverse_apply_self] using
      congrArg (ContinuousLinearMap.inverse (g (x t))) hmetric
  exact hv' ▸ hv.hasDerivAt

theorem hasDerivAt_of_lipschitzOn_ae_hasDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f v : ℝ → F} {a b t : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Set.uIcc a b)) (hv : Continuous v)
    (hfv : ∀ᵐ s, s ∈ Set.uIcc a b → HasDerivAt f (v s) s)
    (ht : t ∈ Set.Ioo (min a b) (max a b)) : HasDerivAt f (v t) t := by
  let P : ℝ → F := fun s => ∫ u in a..s, v u
  have hP (s : ℝ) : HasDerivAt P (v s) s :=
    (hv.integral_hasStrictDerivAt a s).hasDerivAt
  have hP₁ : ContDiff ℝ 1 P := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun s => (hP s).differentiableAt, ?_⟩
    convert hv using 1
    exact funext (fun s => (hP s).deriv)
  have hdiff : AbsolutelyContinuousOnInterval (fun s => f s - P s) a b :=
    hf.absolutelyContinuousOnInterval.sub
      hP₁.contDiffOn.absolutelyContinuousOnInterval
  have hzero : ∀ᵐ s, s ∈ Set.uIcc a b → HasDerivAt (fun u => f u - P u) 0 s := by
    filter_upwards [hfv] with s hs hsab
    change HasDerivAt (f - P) 0 s
    simpa only [sub_self] using (hs hsab).sub (hP s)
  obtain ⟨C, hC⟩ := hdiff.const_of_ae_hasDerivAt_zero hzero
  have heq : f =ᶠ[nhds t] fun s => C + P s := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    have h := hC s (by simpa only [Set.uIcc] using hs)
    exact sub_eq_iff_eq_add.mp h
  exact ((hP t).const_add C).congr_of_eventuallyEq heq

theorem hasDerivAt_of_lipschitzOn_ae_hasDerivAt_continuousOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f v : ℝ → F} {a b t : ℝ} {K : NNReal} (hab : a ≤ b)
    (hf : LipschitzOnWith K f (Set.Icc a b)) (hv : ContinuousOn v (Set.Icc a b))
    (hfv : ∀ᵐ s, s ∈ Set.Icc a b → HasDerivAt f (v s) s)
    (ht : t ∈ Set.Ioo a b) : HasDerivAt f (v t) t := by
  let c : ℝ → ℝ := fun s => max a (min b s)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hc_mem (s : ℝ) : c s ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hc_eq (s : ℝ) (hs : s ∈ Set.Icc a b) : c s = s := by
    simp only [c, min_eq_right hs.2, max_eq_right hs.1]
  have hvc : Continuous (v ∘ c) := hv.comp_continuous hc hc_mem
  have hfc : ∀ᵐ s, s ∈ Set.uIcc a b → HasDerivAt f ((v ∘ c) s) s := by
    filter_upwards [hfv] with s hs hsab
    rw [Set.uIcc_of_le hab] at hsab
    simpa only [Function.comp_apply, hc_eq s hsab] using hs hsab
  have H := hasDerivAt_of_lipschitzOn_ae_hasDerivAt
    (Set.uIcc_of_le hab ▸ hf) hvc hfc (by simpa [min_eq_left hab, max_eq_right hab] using ht)
  simpa only [Function.comp_apply, hc_eq t ⟨ht.1.le, ht.2.le⟩] using H

theorem hasDerivAt_of_lipschitzOn_ae_momentum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {x : ℝ → E} {G : ℝ → E →L[ℝ] E →L[ℝ] ℝ}
    {p : ℝ → E →L[ℝ] ℝ} {a b t : ℝ} {K : NNReal} (hab : a ≤ b)
    (hx : LipschitzOnWith K x (Set.Icc a b))
    (hG : ContinuousOn G (Set.Icc a b)) (hp : ContinuousOn p (Set.Icc a b))
    (hinv : ∀ s ∈ Set.Icc a b, (G s).IsInvertible)
    (hpx : ∀ᵐ s, s ∈ Set.Icc a b → p s = G s (deriv x s))
    (ht : t ∈ Set.Ioo a b) :
    HasDerivAt x ((G t).inverse (p t)) t := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E →L[ℝ] ℝ) (F := E) (σ₁₂ := RingHom.id ℝ)
  have hGi : ContinuousOn (fun s => (G s).inverse) (Set.Icc a b) := by
    intro s hs
    exact ((hinv s hs).contDiffAt_map_inverse (n := 1)).continuousAt.comp_continuousWithinAt
      (hG s hs)
  have hw : ContinuousOn (fun s => (G s).inverse (p s)) (Set.Icc a b) :=
    hGi.clm_apply hp
  apply hasDerivAt_of_lipschitzOn_ae_hasDerivAt_continuousOn hab hx hw ?_ ht
  have hda : ∀ᵐ s, s ≠ a := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton a : MeasureTheory.volume {a} = 0)
  have hdb : ∀ᵐ s, s ≠ b := by
    rw [MeasureTheory.ae_iff]
    simpa using (MeasureTheory.measure_singleton b : MeasureTheory.volume {b} = 0)
  filter_upwards [hx.ae_differentiableWithinAt_of_mem, hpx, hda, hdb] with s hs hm hsa hsb hsab
  have hxs : DifferentiableAt ℝ x s := (hs hsab).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hsab.1 (Ne.symm hsa)) (lt_of_le_of_ne hsab.2 hsb))
  rw [hm hsab, (hinv s hsab).inverse_apply_self]
  exact hxs.hasDerivAt

theorem coordinate_geodesic_of_ae_momentum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {p' : E →L[ℝ] ℝ} {a b t : ℝ} {K : NNReal}
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hab : a ≤ b) (ht : t ∈ Set.Ioo a b)
    (hx : LipschitzOnWith K x (Set.Icc a b))
    (hG : ContinuousOn (fun s => g (x s)) (Set.Icc a b))
    (hp_cont : ContinuousOn p (Set.Icc a b))
    (hinv : ∀ s ∈ Set.Icc a b, (g (x s)).IsInvertible)
    (hpx : ∀ᵐ s, s ∈ Set.Icc a b → p s = g (x s) (deriv x s))
    (hg : HasFDerivAt g D (x t)) (hp : HasDerivAt p p' t)
    (hp' : ∀ z : E, p' z = (2 : ℝ)⁻¹ * D z (deriv x t) (deriv x t))
    (hΓ : ∀ v z : E, 2 * g (x t) (Γ v v) z =
      D v v z + D v v z - D z v v) :
    let v : ℝ → E := fun s => (g (x s)).inverse (p s)
    HasDerivAt x (v t) t ∧ HasDerivAt v (-Γ (v t) (v t)) t := by
  let v : ℝ → E := fun s => (g (x s)).inverse (p s)
  have hx' : HasDerivAt x (v t) t :=
    hasDerivAt_of_lipschitzOn_ae_momentum hab hx hG hp_cont hinv hpx ht
  refine ⟨hx', coordinate_geodesic_of_momentum D Γ hg hx' hp ?_ ?_ ?_ (hΓ (v t))⟩
  · intro z
    rw [hp', hx'.deriv]
  · filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs using hinv s hs
  · filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact ((hinv s hs).self_apply_inverse (p s)).symm


theorem coordinate_metric_compatibility
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E → E)
    (hsym : ∀ u v, g u v = g v u)
    (hDsym : ∀ u v w, D u v w = D u w v)
    (hΓ : ∀ u v w, 2 * g (Γ u v) w = D u v w + D v u w - D w u v)
    (u v w : E) :
    D u v w = g (Γ u v) w + g v (Γ u w) := by
  have h₁ := hΓ u v w
  have h₂ := hΓ u w v
  rw [hsym v (Γ u w)]
  rw [hDsym u w v] at h₂
  linarith

theorem fderiv_metric_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {p : E}
    (hg : DifferentiableAt ℝ g p)
    (hsym : ∀ x u v, g x u v = g x v u) (w u v : E) :
    (fderiv ℝ g p w) u v = (fderiv ℝ g p w) v u := by
  have hu := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const u p)).clm_apply
    (hasFDerivAt_const v p)
  have hv := (hg.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).clm_apply
    (hasFDerivAt_const u p)
  have heq : (fun x => g x v u) =ᶠ[nhds p] (fun x => g x u v) :=
    Filter.Eventually.of_forall (fun x => hsym x v u)
  have he := (hu.congr_of_eventuallyEq heq).unique hv
  have hew := congrArg (fun A : E →L[ℝ] ℝ => A w) he
  simpa using hew

theorem hasDerivAt_coordinate_geodesic_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {x v J : ℝ → E} {W : E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ u w z, 2 * g (x t) (Γ (x t) u w) z =
      (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
        (fderiv ℝ g (x t) z) u w)
    (hx : HasDerivAt x (v t) t)
    (hv : HasDerivAt v (-Γ (x t) (v t) (v t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun s => g (x s) (v s) (J s))
      (g (x t) (v t) (W + Γ (x t) (v t) (J t))) t := by
  have hcg : HasDerivAt (fun s => g (x s)) (fderiv ℝ g (x t) (v t)) t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (l := g) (f := x) t hg.hasFDerivAt hx
  have hcgv : HasDerivAt (fun s => g (x s) (v s))
      ((fderiv ℝ g (x t) (v t)) (v t) + g (x t) (-Γ (x t) (v t) (v t))) t :=
    hcg.clm_apply hv
  have h : HasDerivAt (fun s => g (x s) (v s) (J s))
      (((fderiv ℝ g (x t) (v t)) (v t) + g (x t) (-Γ (x t) (v t) (v t))) (J t) +
        g (x t) (v t) W) t := hcgv.clm_apply hJ
  have hcompat := coordinate_metric_compatibility (g (x t)) (fderiv ℝ g (x t))
    (Γ (x t)) (hsym (x t)) (fderiv_metric_symmetric hg hsym) hΓ (v t) (v t) (J t)
  have heq :
      (((fderiv ℝ g (x t) (v t)) (v t) + g (x t) (-Γ (x t) (v t) (v t))) (J t) +
        g (x t) (v t) W) = g (x t) (v t) (W + Γ (x t) (v t) (J t)) := by
    simp only [add_apply, map_neg, map_add, neg_apply]
    linarith
  rw [heq] at h
  exact h

theorem hasDerivAt_coordinate_energy_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {x v : ℝ → E} {J W : E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ u w z, 2 * g (x t) (Γ (x t) u w) z =
      (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
        (fderiv ℝ g (x t) z) u w)
    (hx : HasDerivAt x J t) (hv : HasDerivAt v W t) :
    HasDerivAt (fun s => g (x s) (v s) (v s))
      (2 * g (x t) (v t) (W + Γ (x t) (v t) J)) t := by
  have hcg : HasDerivAt (fun s => g (x s)) (fderiv ℝ g (x t) J) t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (l := g) (f := x) t hg.hasFDerivAt hx
  have hcgv : HasDerivAt (fun s => g (x s) (v s))
      ((fderiv ℝ g (x t) J) (v t) + g (x t) W) t := hcg.clm_apply hv
  have h : HasDerivAt (fun s => g (x s) (v s) (v s))
      (((fderiv ℝ g (x t) J) (v t) + g (x t) W) (v t) +
        g (x t) (v t) W) t := hcgv.clm_apply hv
  have hkoszul := hΓ (v t) J (v t)
  rw [fderiv_metric_symmetric hg hsym (v t) J (v t),
    hsym (x t) (Γ (x t) (v t) J) (v t)] at hkoszul
  apply h.congr_deriv
  simp only [add_apply, map_add]
  rw [hsym (x t) W (v t)]
  linarith

theorem hasDerivAt_coordinate_geodesic_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {X V J : ℝ → ℝ → E} {W : E} {s t : ℝ}
    (hg : DifferentiableAt ℝ g (X s t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ u w z, 2 * g (X s t) (Γ (X s t) u w) z =
      (fderiv ℝ g (X s t) u) w z + (fderiv ℝ g (X s t) w) u z -
        (fderiv ℝ g (X s t) z) u w)
    (hXt : HasDerivAt (X s) (V s t) t)
    (hVt : HasDerivAt (V s) (-Γ (X s t) (V s t) (V s t)) t)
    (hJt : HasDerivAt (J s) W t)
    (hXs : HasDerivAt (fun r => X r t) (J s t) s)
    (hVs : HasDerivAt (fun r => V r t) W s) :
    HasDerivAt (fun r => g (X s r) (V s r) (J s r))
      ((1 / 2 : ℝ) * deriv (fun r => g (X r t) (V r t) (V r t)) s) t := by
  have hpair := hasDerivAt_coordinate_geodesic_pairing hg hsym hΓ hXt hVt hJt
  have henergy := hasDerivAt_coordinate_energy_variation
    (x := fun r => X r t) (v := fun r => V r t) (t := s) hg hsym hΓ hXs hVs
  rw [henergy.deriv]
  convert hpair using 1
  ring

theorem hasDerivAt_coordinate_mixed_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℝ × ℝ → E} {s t : ℝ} (hX : ContDiffAt ℝ 2 X (s, t)) :
    HasDerivAt (fun r => fderiv ℝ X (s, r) (1, 0))
      (fderiv ℝ (fun p => fderiv ℝ X p (0, 1)) (s, t) (1, 0)) t := by
  have hD : DifferentiableAt ℝ (fderiv ℝ X) (s, t) :=
    (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have ht : HasDerivAt (fun r : ℝ => (s, r)) (0, 1) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  have hDt : HasDerivAt (fun r => fderiv ℝ X (s, r))
      (fderiv ℝ (fderiv ℝ X) (s, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ × ℝ) (E := (ℝ × ℝ) →L[ℝ] E)
      (l := fderiv ℝ X) (f := fun r => (s, r)) t hD.hasFDerivAt ht
  have h := hDt.clm_apply (hasDerivAt_const t ((1, 0) : ℝ × ℝ))
  have hv := hD.hasFDerivAt.clm_apply (hasFDerivAt_const ((0, 1) : ℝ × ℝ) (s, t))
  have heq := congrArg (fun A : (ℝ × ℝ) →L[ℝ] E => A (1, 0)) hv.fderiv
  have heq' : fderiv ℝ (fun p => fderiv ℝ X p (0, 1)) (s, t) (1, 0) =
      fderiv ℝ (fderiv ℝ X) (s, t) (1, 0) (0, 1) := by simpa using heq
  apply h.congr_deriv
  simpa using ((hX.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (1, 0)).trans heq'.symm

theorem coordinate_geodesic_variation_pairing_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {X V J W : ℝ → ℝ → E} {s : ℝ} {S : Set ℝ} {c : ℝ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (h0 : 0 ∈ S)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (X s t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ t ∈ S, ∀ u w z, 2 * g (X s t) (Γ (X s t) u w) z =
      (fderiv ℝ g (X s t) u) w z + (fderiv ℝ g (X s t) w) u z -
        (fderiv ℝ g (X s t) z) u w)
    (hXt : ∀ t ∈ S, HasDerivAt (X s) (V s t) t)
    (hVt : ∀ t ∈ S, HasDerivAt (V s) (-Γ (X s t) (V s t) (V s t)) t)
    (hJt : ∀ t ∈ S, HasDerivAt (J s) (W s t) t)
    (hXs : ∀ t ∈ S, HasDerivAt (fun r => X r t) (J s t) s)
    (hVs : ∀ t ∈ S, HasDerivAt (fun r => V r t) (W s t) s)
    (henergy : ∀ t ∈ S, deriv (fun r => g (X r t) (V r t) (V r t)) s = 2 * c)
    (hJ0 : J s 0 = 0) :
    ∀ t ∈ S, g (X s t) (V s t) (J s t) = t * c := by
  let f : ℝ → ℝ := fun t => g (X s t) (V s t) (J s t)
  have hf : ∀ t ∈ S, HasDerivAt f c t := by
    intro t ht
    have h := hasDerivAt_coordinate_geodesic_variation (hg t ht) hsym (hΓ t ht)
      (hXt t ht) (hVt t ht) (hJt t ht) (hXs t ht) (hVs t ht)
    rw [henergy t ht] at h
    convert h using 1
    ring
  have hlin (t : ℝ) : HasDerivAt (fun r : ℝ => r * c) c t := by
    simpa using (hasDerivAt_id t).mul_const c
  apply hS.eqOn_of_deriv_eq hconn
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hlin t).differentiableAt.differentiableWithinAt)
    (fun t ht => (hf t ht).deriv.trans (hlin t).deriv.symm) h0
  simp [f, hJ0]

theorem hasDerivAt_coordinate_geodesic_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {x v : ℝ → E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ u w z, 2 * g (x t) (Γ (x t) u w) z =
      (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
        (fderiv ℝ g (x t) z) u w)
    (hx : HasDerivAt x (v t) t)
    (hv : HasDerivAt v (-Γ (x t) (v t) (v t)) t) :
    HasDerivAt (fun r => g (x r) (v r) (v r)) 0 t := by
  simpa using hasDerivAt_coordinate_energy_variation hg hsym hΓ hx hv

theorem coordinate_geodesic_energy_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {x v : ℝ → E} {S : Set ℝ}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (x t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ t ∈ S, ∀ u w z, 2 * g (x t) (Γ (x t) u w) z =
      (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
        (fderiv ℝ g (x t) z) u w)
    (hx : ∀ t ∈ S, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ S, HasDerivAt v (-Γ (x t) (v t) (v t)) t)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    g (x a) (v a) (v a) = g (x b) (v b) (v b) := by
  have hd (t : ℝ) (ht : t ∈ S) :=
    hasDerivAt_coordinate_geodesic_energy (hg t ht) hsym (hΓ t ht) (hx t ht) (hv t ht)
  exact hS.is_const_of_deriv_eq_zero hconn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) ha hb

theorem hasDerivAt_coordinate_energy_of_stationary_base
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : ℝ → E} {W : E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t))
    (hsym : ∀ u w, g (x t) u w = g (x t) w u)
    (hx : HasDerivAt x 0 t) (hv : HasDerivAt v W t) :
    HasDerivAt (fun r => g (x r) (v r) (v r)) (2 * g (x t) (v t) W) t := by
  have hcg : HasDerivAt (fun r => g (x r)) (fderiv ℝ g (x t) 0) t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
      (E := E →L[ℝ] E →L[ℝ] ℝ) (l := g) (f := x) t hg.hasFDerivAt hx
  have hcgv : HasDerivAt (fun r => g (x r) (v r))
      ((fderiv ℝ g (x t) 0) (v t) + g (x t) W) t := hcg.clm_apply hv
  have h := hcgv.clm_apply hv
  apply h.congr_deriv
  simp only [map_zero, zero_apply, zero_add]
  rw [hsym W (v t)]
  ring

theorem coordinate_gauss_radial_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {X V J W : ℝ → ℝ → E} {s : ℝ} {R S : Set ℝ}
    (hR : IsOpen R) (hs : s ∈ R)
    (hS : IsOpen S) (hconn : IsPreconnected S) (h0 : 0 ∈ S)
    (hg : ∀ r ∈ R, ∀ t ∈ S, DifferentiableAt ℝ g (X r t))
    (hsym : ∀ p u w, g p u w = g p w u)
    (hΓ : ∀ r ∈ R, ∀ t ∈ S, ∀ u w z, 2 * g (X r t) (Γ (X r t) u w) z =
      (fderiv ℝ g (X r t) u) w z + (fderiv ℝ g (X r t) w) u z -
        (fderiv ℝ g (X r t) z) u w)
    (hXt : ∀ r ∈ R, ∀ t ∈ S, HasDerivAt (X r) (V r t) t)
    (hVt : ∀ r ∈ R, ∀ t ∈ S, HasDerivAt (V r) (-Γ (X r t) (V r t) (V r t)) t)
    (hJt : ∀ t ∈ S, HasDerivAt (J s) (W s t) t)
    (hXs : ∀ t ∈ S, HasDerivAt (fun r => X r t) (J s t) s)
    (hVs : ∀ t ∈ S, HasDerivAt (fun r => V r t) (W s t) s)
    (hJ0 : J s 0 = 0) :
    ∀ t ∈ S, g (X s t) (V s t) (J s t) =
      t * g (X s 0) (V s 0) (W s 0) := by
  have hE0 : HasDerivAt (fun r => g (X r 0) (V r 0) (V r 0))
      (2 * g (X s 0) (V s 0) (W s 0)) s :=
    hasDerivAt_coordinate_energy_of_stationary_base (hg s hs 0 h0) (hsym (X s 0))
      (by simpa only [hJ0] using hXs 0 h0) (hVs 0 h0)
  have henergy (t : ℝ) (ht : t ∈ S) :
      deriv (fun r => g (X r t) (V r t) (V r t)) s =
        2 * g (X s 0) (V s 0) (W s 0) := by
    have heq : (fun r => g (X r t) (V r t) (V r t)) =ᶠ[nhds s]
        (fun r => g (X r 0) (V r 0) (V r 0)) := by
      filter_upwards [hR.mem_nhds hs] with r hr
      exact coordinate_geodesic_energy_eq hS hconn (hg r hr) hsym (hΓ r hr)
        (hXt r hr) (hVt r hr) ht h0
    exact heq.deriv_eq.trans hE0.deriv
  simpa only [mul_assoc] using coordinate_geodesic_variation_pairing_eq
    hS hconn h0 (hg s hs) hsym (hΓ s hs) (hXt s hs) (hVt s hs)
      hJt hXs hVs henergy hJ0


theorem hasDerivAt_coordinate_first_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun r => f (r, t)) (fderiv ℝ f (s, t) (1, 0)) s := by
  have hline : HasDerivAt (fun r : ℝ => (r, t)) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  simpa only [Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt s hline

theorem hasDerivAt_coordinate_second_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun r => f (s, r)) (fderiv ℝ f (s, t) (0, 1)) t := by
  have hline : HasDerivAt (fun r : ℝ => (s, r)) (0, 1) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  simpa only [Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt t hline

theorem coordinate_gauss_radial_pairing_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E → E → E}
    {X V : ℝ × ℝ → E} {R S : Set ℝ} {p v w : E}
    (hR : IsOpen R) (hS : IsOpen S) (hconn : IsPreconnected S) (h0 : 0 ∈ S)
    (hX : ContDiffOn ℝ 2 X (R ×ˢ S))
    (hV : ContDiffOn ℝ 1 V (R ×ˢ S))
    (hg : ∀ r ∈ R, ∀ t ∈ S, DifferentiableAt ℝ g (X (r, t)))
    (hsym : ∀ q u z, g q u z = g q z u)
    (hΓ : ∀ r ∈ R, ∀ t ∈ S, ∀ u z a,
      2 * g (X (r, t)) (Γ (X (r, t)) u z) a =
        (fderiv ℝ g (X (r, t)) u) z a + (fderiv ℝ g (X (r, t)) z) u a -
          (fderiv ℝ g (X (r, t)) a) u z)
    (hXt : ∀ r ∈ R, ∀ t ∈ S, HasDerivAt (fun τ => X (r, τ)) (V (r, t)) t)
    (hVt : ∀ r ∈ R, ∀ t ∈ S,
      HasDerivAt (fun τ => V (r, τ)) (-Γ (X (r, t)) (V (r, t)) (V (r, t))) t)
    (hX0 : ∀ r ∈ R, X (r, 0) = p)
    (hV0 : ∀ r ∈ R, V (r, 0) = v + r • w)
    {s : ℝ} (hs : s ∈ R) :
    ∀ t ∈ S, g (X (s, t)) (V (s, t)) (fderiv ℝ X (s, t) (1, 0)) =
      t * g p (v + s • w) w := by
  have hopen : IsOpen (R ×ˢ S) := hR.prod hS
  have hXat (r : ℝ) (hr : r ∈ R) (t : ℝ) (ht : t ∈ S) :
      ContDiffAt ℝ 2 X (r, t) := hX.contDiffAt (hopen.mem_nhds ⟨hr, ht⟩)
  have hVat (r : ℝ) (hr : r ∈ R) (t : ℝ) (ht : t ∈ S) :
      DifferentiableAt ℝ V (r, t) :=
    (hV.contDiffAt (hopen.mem_nhds ⟨hr, ht⟩)).differentiableAt one_ne_zero
  let J (r t : ℝ) := fderiv ℝ X (r, t) (1, 0)
  let W (r t : ℝ) := fderiv ℝ V (r, t) (1, 0)
  have hXs (t : ℝ) (ht : t ∈ S) : HasDerivAt (fun r => X (r, t)) (J s t) s :=
    hasDerivAt_coordinate_first_slice ((hXat s hs t ht).differentiableAt (by norm_num))
  have hVs (t : ℝ) (ht : t ∈ S) : HasDerivAt (fun r => V (r, t)) (W s t) s :=
    hasDerivAt_coordinate_first_slice (hVat s hs t ht)
  have hpartial (q : ℝ × ℝ) (hq : q ∈ R ×ˢ S) :
      fderiv ℝ X q (0, 1) = V q :=
    (hasDerivAt_coordinate_second_slice
      ((hXat q.1 hq.1 q.2 hq.2).differentiableAt (by norm_num))).unique
        (hXt q.1 hq.1 q.2 hq.2)
  have hJt (t : ℝ) (ht : t ∈ S) : HasDerivAt (J s) (W s t) t := by
    have heq : (fun q => fderiv ℝ X q (0, 1)) =ᶠ[nhds (s, t)] V := by
      filter_upwards [hopen.mem_nhds ⟨hs, ht⟩] with q hq
      exact hpartial q hq
    have h := hasDerivAt_coordinate_mixed_fderiv (hXat s hs t ht)
    rw [heq.fderiv_eq] at h
    exact h
  have hJ0 : J s 0 = 0 := by
    have heq : (fun r => X (r, 0)) =ᶠ[nhds s] (fun _ => p) := by
      filter_upwards [hR.mem_nhds hs] with r hr
      exact hX0 r hr
    exact ((hXs 0 h0).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s p)
  have hW0 : W s 0 = w := by
    have heq : (fun r => V (r, 0)) =ᶠ[nhds s] (fun r => v + r • w) := by
      filter_upwards [hR.mem_nhds hs] with r hr
      exact hV0 r hr
    have hlin : HasDerivAt (fun r : ℝ => v + r • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add v
    exact ((hVs 0 h0).congr_of_eventuallyEq heq.symm).unique hlin
  have h := coordinate_gauss_radial_pairing
    (X := fun r t => X (r, t)) (V := fun r t => V (r, t)) (J := J) (W := W)
    hR hs hS hconn h0 hg hsym hΓ hXt hVt hJt hXs hVs hJ0
  simpa only [hX0 s hs, hV0 s hs, hW0] using h


theorem hasDerivAt_flow_variation
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × P → E} {F : E → E} {z : ℝ × P} (v : P)
    (hΦ : ContDiffAt ℝ 2 Φ z) (hF : DifferentiableAt ℝ F (Φ z))
    (htime : ∀ᶠ w in nhds z,
      HasDerivAt (fun t : ℝ => Φ (t, w.2)) (F (Φ w)) w.1) :
    HasDerivAt (fun t : ℝ => fderiv ℝ Φ (t, z.2) (0, v))
      (fderiv ℝ F (Φ z) (fderiv ℝ Φ z (0, v))) z.1 := by
  have hΦ₁ : DifferentiableAt ℝ Φ z := hΦ.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) z :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hT : (fun w => fderiv ℝ Φ w (1, 0)) =ᶠ[nhds z] fun w => F (Φ w) := by
    filter_upwards [htime, hΦ.eventually (by norm_num)] with w hw hΦw
    have hi : HasDerivAt (fun t : ℝ => (t, w.2)) (1, 0) w.1 :=
      (hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)
    exact ((hΦw.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt w.1 hi).unique hw
  have hleft : HasFDerivAt (fun w => fderiv ℝ Φ w (1, 0))
      ((fderiv ℝ (fderiv ℝ Φ) z).flip (1, 0)) z := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hD.hasFDerivAt.clm_apply (hasFDerivAt_const (1, (0 : P)) z)
  have hright : HasFDerivAt (fun w => F (Φ w))
      ((fderiv ℝ F (Φ z)).comp (fderiv ℝ Φ z)) z :=
    HasFDerivAt.comp (g := F) (f := Φ) z hF.hasFDerivAt hΦ₁.hasFDerivAt
  have heq := (hT.hasFDerivAt_iff.mp hleft).unique hright
  have heqv := congrArg (fun L : (ℝ × P) →L[ℝ] E => L (0, v)) heq
  have hi : HasDerivAt (fun t : ℝ => (t, z.2)) (1, 0) z.1 :=
    (hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2)
  have hspace : HasFDerivAt (fun w => fderiv ℝ Φ w (0, v))
      ((fderiv ℝ (fderiv ℝ Φ) z).flip (0, v)) z := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, v) z)
  have hresult : HasDerivAt (fun t => fderiv ℝ Φ (t, z.2) (0, v))
      (((fderiv ℝ (fderiv ℝ Φ) z).flip (0, v)) (1, 0)) z.1 :=
    HasFDerivAt.comp_hasDerivAt (l := fun w : ℝ × P => fderiv ℝ Φ w (0, v))
      z.1 hspace hi
  have hsym := hΦ.isSymmSndFDerivAt (by norm_num) (1, 0) (0, v)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at heqv hresult
  rw [hsym, heqv] at hresult
  exact hresult

def coordinateSprayLinearization
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.snd ℝ E E).prod 0

theorem hasFDerivAt_coordinate_spray_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p : E}
    (hΓ : DifferentiableAt ℝ Γ p) :
    HasFDerivAt (fun z : E × E => (z.2, -(Γ z.1 z.2 z.2)))
      (coordinateSprayLinearization E) (p, 0) := by
  have hfst : HasFDerivAt (fun z : E × E => z.1)
      (ContinuousLinearMap.fst ℝ E E) (p, (0 : E)) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun z : E × E => z.2)
      (ContinuousLinearMap.snd ℝ E E) (p, (0 : E)) := hasFDerivAt_snd
  have hΓ' : HasFDerivAt (fun z : E × E => Γ z.1)
      ((fderiv ℝ Γ p).comp (ContinuousLinearMap.fst ℝ E E)) (p, (0 : E)) :=
    HasFDerivAt.comp (g := Γ) (p, (0 : E)) hΓ.hasFDerivAt hfst
  have hq := (hΓ'.clm_apply hsnd).clm_apply hsnd
  convert hsnd.prodMk
    hq.neg using 1 <;> simp [coordinateSprayLinearization]

theorem coordinateSprayLinearization_sq
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (coordinateSprayLinearization E).comp (coordinateSprayLinearization E) = 0 := by
  ext z <;> simp [coordinateSprayLinearization]


theorem coordinate_spray_energy_hasDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {x v : ℝ → E} {t : ℝ}
    (hg : DifferentiableAt ℝ g (x t))
    (hsym : ∀ u w : E, g (x t) u w = g (x t) w u)
    (hΓ : ∀ u w z : E,
      2 * g (x t) (Γ (x t) u w) z =
        (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
          (fderiv ℝ g (x t) z) u w)
    (hx : HasDerivAt x (v t) t)
    (hv : HasDerivAt v (-(Γ (x t) (v t) (v t))) t) :
    HasDerivAt (fun s => g (x s) (v s) (v s)) 0 t := by
  have hgx : HasDerivAt (fun s => g (x s)) (fderiv ℝ g (x t) (v t)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := g) (f := x) hg.hasFDerivAt hx
  have he := (hgx.clm_apply hv).clm_apply hv
  convert he using 1
  simp only [add_apply, map_neg, neg_apply]
  rw [hsym (v t) (Γ (x t) (v t) (v t))]
  have h := hΓ (v t) (v t) (v t)
  linarith


theorem coordinate_spray_energy_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {x v : ℝ → E} {S : Set ℝ}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    (hg : ∀ t ∈ S, DifferentiableAt ℝ g (x t))
    (hsym : ∀ t ∈ S, ∀ u w : E, g (x t) u w = g (x t) w u)
    (hΓ : ∀ t ∈ S, ∀ u w z : E,
      2 * g (x t) (Γ (x t) u w) z =
        (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
          (fderiv ℝ g (x t) z) u w)
    (hx : ∀ t ∈ S, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ S, HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    {s t : ℝ} (hs : s ∈ S) (ht : t ∈ S) :
    g (x s) (v s) (v s) = g (x t) (v t) (v t) := by
  have hE (t : ℝ) (ht : t ∈ S) := coordinate_spray_energy_hasDerivAt_zero
    g Γ (hg t ht) (hsym t ht) (hΓ t ht) (hx t ht) (hv t ht)
  exact hS.is_const_of_deriv_eq_zero hconn
    (fun t ht => (hE t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hE t ht).deriv) hs ht

theorem positive_bilinear_uniform_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < g v v) :
    ∃ k > (0 : ℝ), ∀ v : E, k * ‖v‖ ^ 2 ≤ g v v := by
  have hcont : Continuous (fun v : E => g v v) :=
    (g.continuous.clm_apply continuous_id)
  obtain ⟨k, hk, hlow⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hcont.continuousOn (a := (0 : ℝ)) (by
      intro v hv
      apply hpos v
      intro hv0
      simpa [hv0] using hv)
  refine ⟨k, hk, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnorm.le), inv_mul_cancel₀ hnorm.ne']
  have hl := hlow ((‖v‖⁻¹ : ℝ) • v) (by simpa [Metric.mem_sphere] using hu)
  simp only [map_smul, smul_apply, smul_eq_mul] at hl
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg ‖v‖)
  field_simp at hm
  nlinarith

theorem positive_metric_eventually_uniform_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E → E →L[ℝ] E →L[ℝ] ℝ) {p : E}
    (hg : ContinuousAt g p) (hpos : ∀ v : E, v ≠ 0 → 0 < g p v v) :
    ∃ k > (0 : ℝ), ∀ᶠ y in nhds p, ∀ v : E, k * ‖v‖ ^ 2 ≤ g y v v := by
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  obtain ⟨k, hk, hlower⟩ := positive_bilinear_uniform_lower_bound (g p) hpos
  refine ⟨k / 2, by linarith, ?_⟩
  have hev : ∀ᶠ y in nhds p, ‖g p - g y‖ < k / 2 := by
    have hcont : ContinuousAt (fun y => ‖g p - g y‖) p := (continuousAt_const.sub hg).norm
    have hk2 : 0 < k / 2 := by linarith
    exact hcont.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hk2))
  filter_upwards [hev] with y hy v
  have hnorm : |(g p - g y) v v| ≤ ‖g p - g y‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖(g p - g y) v‖ * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using ((g p - g y) v).le_opNorm v
      _ ≤ (‖g p - g y‖ * ‖v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((g p - g y).le_opNorm v) (norm_nonneg v)
      _ = _ := by ring
  have hd : g p v v - g y v v ≤ k / 2 * ‖v‖ ^ 2 := by
    calc
      _ ≤ |(g p - g y) v v| := by simpa only [sub_apply] using le_abs_self ((g p - g y) v v)
      _ ≤ ‖g p - g y‖ * ‖v‖ ^ 2 := hnorm
      _ ≤ k / 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hy.le (sq_nonneg ‖v‖)
  linarith [hlower v]

theorem endpoint_limit_of_eventually_bounded_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f d : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f (d t) t)
    (hbound : ∃ C : ℝ, ∀ᶠ t in nhdsWithin b (Set.Ioo a b), ‖d t‖ ≤ C) :
    ∃ p : E, Filter.Tendsto f (nhdsWithin b (Set.Ioo a b)) (nhds p) := by
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.mp hC
  let a' := max a (b - δ)
  have ha' : a' < b := max_lt hab (by linarith)
  have hsub : Set.Ioo a' b ⊆ Set.Ioo a b := by
    intro t ht
    exact ⟨(le_max_left a (b - δ)).trans_lt ht.1, ht.2⟩
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith K f (Set.Ioo a' b) := by
    apply (convex_Ioo a' b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hf t (hsub ht)).hasDerivWithinAt)
    intro t ht
    have htδ : t ∈ Metric.ball b δ ∩ Set.Ioo a b := by
      refine ⟨?_, hsub ht⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      have := (le_max_right a (b - δ)).trans_lt ht.1
      linarith
    change ‖d t‖ ≤ max C 0
    exact (hδC htδ).trans (le_max_left C 0)
  haveI := right_nhdsWithin_Ioo_neBot ha'
  have hcau : Cauchy (Filter.map f (nhdsWithin b (Set.Ioo a' b))) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le hLip.uniformContinuousOn inf_le_right
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp hcau
  refine ⟨p, ?_⟩
  simpa only [nhdsWithin_Ioo_eq_nhdsLT hab, nhdsWithin_Ioo_eq_nhdsLT ha'] using hp

theorem coordinate_spray_velocity_endpoint_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {x v : ℝ → E} {a b : ℝ} {p : E}
    (hab : a < b) (hg : ContinuousAt g p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < g p w w) (hΓ : ContinuousAt Γ p)
    (hx : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p))
    (A : ℝ) (henergy : ∀ t ∈ Set.Ioo a b, g (x t) (v t) (v t) = A)
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (-(Γ (x t) (v t) (v t))) t) :
    ∃ w : E, Filter.Tendsto v (nhdsWithin b (Set.Ioo a b)) (nhds w) := by
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] E) (σ₁₂ := RingHom.id ℝ)
  obtain ⟨k, hk, hcoercive⟩ := positive_metric_eventually_uniform_lower_bound g hg hpos
  let R := |A| / k + 1
  let C := ‖Γ p‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hΓbound : ∀ᶠ y in nhds p, ‖Γ y‖ < C :=
    hΓ.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  apply endpoint_limit_of_eventually_bounded_deriv hab hv
  refine ⟨C * R ^ 2, ?_⟩
  filter_upwards [hx.eventually hcoercive, hx.eventually hΓbound,
    self_mem_nhdsWithin] with t ht hΓt htS
  have hq2 : ‖v t‖ ^ 2 ≤ |A| / k := by
    apply (le_div_iff₀ hk).mpr
    have := ht (v t)
    rw [henergy t htS] at this
    nlinarith [le_abs_self A]
  have hq : ‖v t‖ ≤ R := by
    have hquot : 0 ≤ |A| / k := div_nonneg (abs_nonneg A) hk.le
    dsimp [R]
    nlinarith [sq_nonneg (‖v t‖ - 1)]
  calc
    ‖-(Γ (x t) (v t) (v t))‖ = ‖Γ (x t) (v t) (v t)‖ := norm_neg _
    _ ≤ ‖Γ (x t) (v t)‖ * ‖v t‖ := (Γ (x t) (v t)).le_opNorm (v t)
    _ ≤ (‖Γ (x t)‖ * ‖v t‖) * ‖v t‖ :=
      mul_le_mul_of_nonneg_right ((Γ (x t)).le_opNorm (v t)) (norm_nonneg _)
    _ = ‖Γ (x t)‖ * ‖v t‖ ^ 2 := by ring
    _ ≤ C * R ^ 2 := by gcongr

theorem coordinate_spray_phase_endpoint_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {x v : ℝ → E} {a b : ℝ} {p : E}
    (hab : a < b) (hgp : ContinuousAt g p)
    (hpos : ∀ w : E, w ≠ 0 → 0 < g p w w) (hΓp : ContinuousAt Γ p)
    (hg : ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ g (x t))
    (hsym : ∀ t ∈ Set.Ioo a b, ∀ u w : E, g (x t) u w = g (x t) w u)
    (hΓ : ∀ t ∈ Set.Ioo a b, ∀ u w z : E,
      2 * g (x t) (Γ (x t) u w) z =
        (fderiv ℝ g (x t) u) w z + (fderiv ℝ g (x t) w) u z -
          (fderiv ℝ g (x t) z) u w)
    (hx : ∀ t ∈ Set.Ioo a b, HasDerivAt x (v t) t)
    (hv : ∀ t ∈ Set.Ioo a b, HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hxlim : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p)) :
    ∃ w : E, Filter.Tendsto (fun t => (x t, v t))
      (nhdsWithin b (Set.Ioo a b)) (nhds (p, w)) := by
  let t₀ := (a + b) / 2
  have ht₀ : t₀ ∈ Set.Ioo a b := by dsimp [t₀]; constructor <;> linarith
  have henergy (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      g (x t) (v t) (v t) = g (x t₀) (v t₀) (v t₀) :=
    coordinate_spray_energy_eq g Γ isOpen_Ioo (convex_Ioo a b).isPreconnected
      hg hsym hΓ hx hv ht ht₀
  obtain ⟨w, hw⟩ := coordinate_spray_velocity_endpoint_limit g Γ hab hgp hpos hΓp hxlim
    (g (x t₀) (v t₀) (v t₀)) henergy hv
  exact ⟨w, hxlim.prodMk_nhds hw⟩

theorem contMDiffAt_clm_of_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} {f : M → F →L[ℝ] G} {x : M}
    (hf : ∀ v, ContMDiffAt I (modelWithCornersSelf ℝ G) n (fun y => f y v) x) :
    ContMDiffAt I (modelWithCornersSelf ℝ (F →L[ℝ] G)) n f x := by
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_clm_apply.mpr (fun v => (hf v).continuousAt), ?_⟩
  simpa only [extChartAt_self_apply, modelWithCornersSelf_coe, Function.comp_def,
    Function.id_def] using
    (contDiffWithinAt_clm_apply.mpr (fun v => (contMDiffAt_iff.mp (hf v)).2))
theorem exists_smooth_coordinate_metric : open scoped Bundle in open Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
      [RiemannianBundle (fun x : M => TangentSpace I x)]
      [IsContMDiffRiemannianBundle I (↑(⊤ : ℕ∞) : WithTop ℕ∞) E
        (fun x : M => TangentSpace I x)] (p : M),
      ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g (extChartAt I p).target ∧
        (∀ z u v, g z u v = g z v u) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v : E, v ≠ 0 → 0 < g z v v) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v : E,
          g z v v = ‖(mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I p).symm (Set.range I) z) v‖ ^ 2) := by
  intro E _ _ _ H _ I _ M _ _ _ _ _ p
  exact (open scoped Bundle in open Bundle ContinuousLinearMap in by
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    letI : (y : M) → InnerProductSpace ℝ (TangentSpace I y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := fun x : M => TangentSpace I x) y
    let e := trivializationAt E (TangentSpace I : M → Type _) p
    let A (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
      ((compL ℝ E (TangentSpace I y) ℝ).flip (e.symmL ℝ y)).comp
        ((innerSL ℝ).comp (e.symmL ℝ y))
    have hA (y : M) (hy : y ∈ e.baseSet) :
        ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) A y := by
      apply contMDiffAt_clm_of_apply
      intro u
      apply contMDiffAt_clm_of_apply
      intro v
      change ContMDiffAt I (modelWithCornersSelf ℝ ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q => inner ℝ (e.symmL ℝ q u) (e.symmL ℝ q v)) y
      have hZ (w : E) : ContMDiffAt I I.tangent (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q => TotalSpace.mk' E q (e.symmL ℝ q w)) y :=
        (e.contMDiffAt_symmL hy).clm_bundle_apply
          (contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩)
      exact ContMDiffAt.inner_bundle (F := E) (E := fun q : M => TangentSpace I q)
        (hZ u) (hZ v)
    let g : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => A ((extChartAt I p).symm z)
    have hbase {z : E} (hz : z ∈ (extChartAt I p).target) :
        (extChartAt I p).symm z ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt I p).map_target hz
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hA _ (hbase hz)).comp_contMDiffWithinAt z
        ((contMDiffOn_extChartAt_symm p) z hz)).contDiffWithinAt
    · intro z u v
      exact real_inner_comm (e.symmL ℝ ((extChartAt I p).symm z) u)
        (e.symmL ℝ ((extChartAt I p).symm z) v) |>.symm
    · intro z hz v hv
      change 0 < inner ℝ (e.symmL ℝ _ v) (e.symmL ℝ _ v)
      apply real_inner_self_pos.mpr
      intro heq
      have hh := congrArg (e.continuousLinearMapAt ℝ ((extChartAt I p).symm z)) heq
      exact hv (by simpa only [e.continuousLinearMapAt_symmL (hbase hz), map_zero] using hh)
    · intro z hz v
      have hsymm : e.symmL ℝ ((extChartAt I p).symm z) =
          mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
            (Set.range I) z := by
        rw [TangentBundle.symmL_trivializationAt (hbase hz)]
        rw [(extChartAt I p).right_inv hz]
      change inner ℝ (e.symmL ℝ _ v) (e.symmL ℝ _ v) = _
      rw [hsymm, real_inner_self_eq_norm_sq]
      rfl)


theorem contMDiffAt_tangent_of_inner : open Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      [IsContMDiffRiemannianBundle I (↑(⊤ : ℕ∞) : WithTop ℕ∞) E
        (fun x : M => TangentSpace I x)]
      {s : (x : M) → TangentSpace I x} {p : M},
      (∀ Z : (x : M) → TangentSpace I x,
        ContMDiffAt I I.tangent 2 (fun x => TotalSpace.mk' E x (Z x)) p →
        ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 1 (fun x => inner ℝ (s x) (Z x)) p) →
      ContMDiffAt I I.tangent 1 (fun x => TotalSpace.mk' E x (s x)) p :=
  by
  intros E _ _ _ H _ I M _ _ _ _ _ s p hs
  exact (open scoped Bundle in open Bundle ContinuousLinearMap in by
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    letI : (y : M) → InnerProductSpace ℝ (TangentSpace I y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := fun x : M => TangentSpace I x) y
    let e := trivializationAt E (TangentSpace I : M → Type _) p
    have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
    let Z (v : E) (y : M) : TangentSpace I y := e.symmL ℝ y v
    have hZ (v : E) : ContMDiffAt I I.tangent 2
        (fun y => TotalSpace.mk' E y (Z v y)) p := by
      exact (e.contMDiffAt_symmL (n := 2) hp).clm_bundle_apply
        (contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩)
    let A (y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
      ((compL ℝ E (TangentSpace I y) ℝ).flip (e.symmL ℝ y)).comp
        ((innerSL ℝ).comp (e.symmL ℝ y))
    have hA : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ)) 1 A p := by
      apply contMDiffAt_clm_of_apply
      intro u
      apply contMDiffAt_clm_of_apply
      intro v
      change ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 1
        (fun y => inner ℝ (Z u y) (Z v y)) p
      exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x)
        ((hZ u).of_le (m := 1) (by norm_num)) ((hZ v).of_le (m := 1) (by norm_num))
    have hAi (y : M) (hy : y ∈ e.baseSet) : (A y).IsInvertible := by
      let a := (e.continuousLinearEquivAt ℝ y hy).symm
      let b := (a.trans (InnerProductSpace.toDual ℝ (TangentSpace I y)).toContinuousLinearEquiv).trans
        (a.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      refine ⟨b, ?_⟩
      ext u v
      simp [b, a, A, ContinuousLinearEquiv.arrowCongr_apply,
        e.symmL_apply hy]
    have hInv : ContMDiffAt I (modelWithCornersSelf ℝ ((E →L[ℝ] ℝ) →L[ℝ] E)) 1
        (fun y => (A y).inverse) p :=
      (hAi p hp).contDiffAt_map_inverse.comp_contMDiffAt hA
    let K (y : M) : E →L[ℝ] ℝ :=
      (innerSL ℝ (s y)).comp (e.symmL ℝ y)
    have hK : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] ℝ)) 1 K p := by
      apply contMDiffAt_clm_of_apply
      intro v
      exact hs (Z v) (hZ v)
    apply (contMDiffAt_section p).mpr
    apply (hInv.clm_apply hK).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    change (e ⟨y, s y⟩).2 = (A y).inverse (K y)
    have heq : A y (e.continuousLinearMapAt ℝ y (s y)) = K y := by
      ext v
      change inner ℝ (e.symmL ℝ y (e.continuousLinearMapAt ℝ y (s y)))
        (e.symmL ℝ y v) = inner ℝ (s y) (e.symmL ℝ y v)
      rw [e.symmL_continuousLinearMapAt hy]
    rw [← heq, (hAi y hy).inverse_apply_self]
    exact (congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hy) (s y)).symm)
theorem contMDiffAt_mvfderiv_apply : open Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
      {f : M → ℝ} {X : (x : M) → TangentSpace I x} {p : M},
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2 f p →
      ContMDiffAt I I.tangent 1 (fun x => TotalSpace.mk' E x (X x)) p →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 1
        (fun x => mvfderiv I f x (X x)) p := by
  intros E _ _ H _ I M _ _ _ f X p hf hX
  set_option backward.isDefEq.respectTransparency false in
  exact (open Bundle in by
    have hD := hf.mfderiv_const (m := 1) (by norm_num)
    have hT := hD.clm_apply_of_inCoordinates hX (hf.of_le (m := 1) (by norm_num))
    have h := (contMDiffAt_totalSpace.mp hT).2
    change ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 1
      (fun x => mfderiv I (modelWithCornersSelf ℝ ℝ) f x (X x)) p
    simp only [trivializationAt_model_space_apply] at h
    convert! h using 1)
theorem leviCivita_apply_contMDiffAt_one : open Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      [IsContMDiffRiemannianBundle I (↑(⊤ : ℕ∞) : WithTop ℕ∞) E
        (fun x : M => TangentSpace I x)]
      {X Y : (x : M) → TangentSpace I x} {p : M},
      ContMDiffAt I I.tangent 2 (fun x => TotalSpace.mk' E x (X x)) p →
      ContMDiffAt I I.tangent 2 (fun x => TotalSpace.mk' E x (Y x)) p →
      ContMDiffAt I I.tangent 1
        (fun x => TotalSpace.mk' E x (CovariantDerivative.leviCivitaConnection I M Y x (X x))) p := by
  intros E _ _ _ H _ I M _ _ _ _ _ X Y p hX hY
  exact (open Bundle in by
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    letI : (y : M) → InnerProductSpace ℝ (TangentSpace I y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := fun x : M => TangentSpace I x) y
    letI : IsManifold I (minSmoothness ℝ 2) M :=
      IsManifold.of_le (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp [minSmoothness])
    letI : IsManifold I ((2 : ℕ∞) + 1) M :=
      IsManifold.of_le (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
    apply contMDiffAt_tangent_of_inner
    intro Z hZ
    have hX1 := hX.of_le (m := 1) (by norm_num)
    have hY1 := hY.of_le (m := 1) (by norm_num)
    have hZ1 := hZ.of_le (m := 1) (by norm_num)
    have hYZ := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hY hZ
    have hZX := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hZ hX
    have hXY := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hX hY
    have hd1 := contMDiffAt_mvfderiv_apply hYZ hX1
    have hd2 := contMDiffAt_mvfderiv_apply hZX hY1
    have hd3 := contMDiffAt_mvfderiv_apply hXY hZ1
    have hb1 := hX.mlieBracket_vectorField hZ (m := 1) (by norm_num [minSmoothness])
    have hb2 := hY.mlieBracket_vectorField hX (m := 1) (by norm_num [minSmoothness])
    have hb3 := hZ.mlieBracket_vectorField hY (m := 1) (by norm_num [minSmoothness])
    have hi1 := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hY1 hb1
    have hi2 := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hZ1 hb2
    have hi3 := ContMDiffAt.inner_bundle (F := E) (E := fun x : M => TangentSpace I x) hX1 hb3
    have hsum := ((((hd1.add hd2).sub hd3).sub hi1).sub hi2).add hi3
    apply ((contDiff_id.div_const (2 : ℝ)).contDiffAt.comp_contMDiffAt hsum)
      |>.congr_of_eventuallyEq
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hX,
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hY,
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ] with x hx hy hz
    exact CovariantDerivative.leviCivitaConnection_apply_inner I
      (hx.mdifferentiableAt (by norm_num)) (hy.mdifferentiableAt (by norm_num))
      (hz.mdifferentiableAt (by norm_num)))
theorem leviCivita_contMDiff_one : open Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
      (M : Type*) [EMetricSpace M] [ChartedSpace H M]
      [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      [IsContMDiffRiemannianBundle I (↑(⊤ : ℕ∞) : WithTop ℕ∞) E
        (fun x : M => TangentSpace I x)]
      [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
      [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M],
      CovariantDerivative.ContMDiffCovariantDerivative
        (CovariantDerivative.leviCivitaConnection I M) 1 := by
  intros E _ _ _ H _ I _ M _ _ _ _ _ _ _ _ _
  exact (open Bundle ContinuousLinearMap in by
    constructor
    constructor
    intro Y hY
    rw [contMDiffOn_univ] at hY ⊢
    intro p
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply contMDiffAt_clm_of_apply
    intro v
    let e := trivializationAt E (TangentSpace I : M → Type _) p
    have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
    let X (y : M) : TangentSpace I y := e.symmL ℝ y v
    have hX : ContMDiffAt I I.tangent 2 (fun y => TotalSpace.mk' E y (X y)) p :=
      (e.contMDiffAt_symmL (n := 2) hp).clm_bundle_apply
        (contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩)
    have hV := leviCivita_apply_contMDiffAt_one hX (hY p)
    apply ((contMDiffAt_section p).mp hV).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hp] with y hy
    change inCoordinates E (TangentSpace I) E (TangentSpace I) p y p y
      (CovariantDerivative.leviCivitaConnection I M Y y) v =
        (e ⟨y, CovariantDerivative.leviCivitaConnection I M Y y (X y)⟩).2
    simp only [inCoordinates, ContinuousLinearMap.comp_apply]
    exact congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hy)
      (CovariantDerivative.leviCivitaConnection I M Y y (X y)))
theorem positive_metric_duality_isInvertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ v : E, v ≠ 0 → 0 < g v v) : g.IsInvertible := by
  classical
  have hinj : Function.Injective g := by
    intro v w hvw
    by_contra hne
    have hz : g (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hp := hpos (v - w) (sub_ne_zero.mpr hne)
    simp [hz] at hp
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap :
      Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq, Subspace.dual_finrank_eq]
  let e := (LinearEquiv.ofBijective g.toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
      ).toContinuousLinearEquiv
  exact ⟨e, rfl⟩
theorem contDiffOn_inverse_positive_metric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} {n : WithTop ℕ∞}
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContDiffOn ℝ n g U)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ContDiffOn ℝ n (fun x => ContinuousLinearMap.inverse (g x)) U := by
  intro x hx
  exact (positive_metric_duality_isInvertible (g x) (hpos x hx)
    ).contDiffAt_map_inverse.comp_contDiffWithinAt x (hg x hx)
noncomputable def coordinateKoszulForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  by
    letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
    exact D + D.flip -
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        D.flip
theorem coordinateKoszulForm_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w z : E) :
    coordinateKoszulForm D v w z = D v w z + D w v z - D z v w := rfl
theorem exists_smooth_coordinate_koszul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (U : Set E) (hU : IsOpen U)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g U)
    (_hsym : ∀ x ∈ U, ∀ v w : E, g x v w = g x w v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < g x v v) :
    ∃ Γ : E → E →L[ℝ] E →L[ℝ] E,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U ∧
      ∀ x ∈ U, ∀ v w z : E,
        2 * g x (Γ x v w) z =
          (fderiv ℝ g x v) w z + (fderiv ℝ g x w) v z - (fderiv ℝ g x z) v w := by
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
      (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
      (E := E) (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  have hD : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ g) U :=
    hg.fderiv_of_isOpen hU (by simp)
  have hK : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => coordinateKoszulForm (fderiv ℝ g x)) U := by
    apply (contDiffOn_clm_apply (𝕜 := ℝ) (D := E) (E := E)
      (F := E →L[ℝ] E →L[ℝ] ℝ)).mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    apply contDiffOn_clm_apply.mpr
    intro z
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (fderiv ℝ g x) v w z + (fderiv ℝ g x) w v z -
        (fderiv ℝ g x) z v w) U
    exact (((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const
      ).clm_apply contDiffOn_const).add
      (((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
        contDiffOn_const) |>.sub
      (((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
        contDiffOn_const)
  have hinv := contDiffOn_inverse_positive_metric g hg hpos
  let Γ : E → E →L[ℝ] E →L[ℝ] E := fun x =>
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (ContinuousLinearMap.inverse (g x))).comp
        ((2 : ℝ)⁻¹ • coordinateKoszulForm (fderiv ℝ g x))
  refine ⟨Γ, ?_, ?_⟩
  · apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => ContinuousLinearMap.inverse (g x)
        ((2 : ℝ)⁻¹ • coordinateKoszulForm (fderiv ℝ g x) v w)) U
    exact hinv.clm_apply ((contDiffOn_const (c := (2 : ℝ)⁻¹)).smul
      ((hK.clm_apply (g := fun _ : E => v) contDiffOn_const).clm_apply
        (g := fun _ : E => w) contDiffOn_const))
  · intro x hx v w z
    change 2 * (g x (ContinuousLinearMap.inverse (g x)
      ((2 : ℝ)⁻¹ • coordinateKoszulForm (fderiv ℝ g x) v w))) z = _
    rw [(positive_metric_duality_isInvertible (g x) (hpos x hx)).self_apply_inverse]
    change 2 * ((2 : ℝ)⁻¹ *
      ((fderiv ℝ g x v) w z + (fderiv ℝ g x w) v z - (fderiv ℝ g x z) v w)) = _
    ring

def MetricLocallyLinear {M : Type*} [EMetricSpace M]
    (γ : ℝ → M) (c : NNReal) (S : Set ℝ) : Prop :=
  ∀ t₀ ∈ S, ∃ δ > (0 : ℝ), ∀ s t : ℝ,
    s ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
    t ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
    edist (γ s) (γ t) = (c : ENNReal) * ENNReal.ofReal |t - s|
theorem MetricLocallyLinear.mono {M : Type*} [EMetricSpace M]
    {γ : ℝ → M} {c : NNReal} {S T : Set ℝ}
    (h : MetricLocallyLinear γ c S) (hTS : T ⊆ S) : MetricLocallyLinear γ c T := by
  intro x hx
  obtain ⟨δ, hδ, H⟩ := h x (hTS hx)
  exact ⟨δ, hδ, fun s t hs ht => H s t ⟨hTS hs.1, hs.2⟩ ⟨hTS ht.1, ht.2⟩⟩
theorem MetricLocallyLinear.congr {M : Type*} [EMetricSpace M]
    {γ η : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : MetricLocallyLinear γ c S) (heq : Set.EqOn η γ S) :
    MetricLocallyLinear η c S := by
  intro x hx
  obtain ⟨δ, hδ, H⟩ := h x hx
  refine ⟨δ, hδ, fun s t hs ht => ?_⟩
  rw [heq hs.1, heq ht.1]
  exact H s t hs ht
theorem MetricLocallyLinear.continuousOn {M : Type*} [EMetricSpace M]
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : MetricLocallyLinear γ c S) : ContinuousOn γ S := by
  apply LocallyLipschitzOn.continuousOn
  intro x hx
  obtain ⟨δ, hδ, H⟩ := h x hx
  refine ⟨c, S ∩ Set.Ioo (x - δ) (x + δ),
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))), ?_⟩
  intro s hs t ht
  rw [H s t hs ht, edist_dist s t, Real.dist_eq, abs_sub_comm]
theorem MetricLocallyLinear.lipschitzOn {M : Type*} [EMetricSpace M]
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : MetricLocallyLinear γ c S) (hS : S.OrdConnected) :
    LipschitzOnWith c γ S := by
  have hbound : ∀ x ∈ S, ∀ y ∈ S, x ≤ y →
      edist (γ x) (γ y) ≤ (c : ENNReal) * ENNReal.ofReal (y - x) := by
    intro x hx y hy hxy
    let A := {t : ℝ | edist (γ x) (γ t) ≤
      (c : ENNReal) * ENNReal.ofReal (t - x)}
    have hsub : Set.Icc x y ⊆ S := hS.out hx hy
    have hclosed : IsClosed (A ∩ Set.Icc x y) := by
      rw [Set.inter_comm]
      exact isClosed_Icc.isClosed_le
        (continuous_edist.comp_continuousOn
          (continuousOn_const.prodMk (h.continuousOn.mono hsub)))
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          (ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const))).continuousOn
    apply hclosed.mem_of_ge_of_forall_exists_gt (by simp [A]) hxy
    intro t ht
    obtain ⟨δ, hδ, H⟩ := h t (hsub ⟨ht.2.1, ht.2.2.le⟩)
    obtain ⟨u, htu, hu⟩ := exists_between (lt_min ht.2.2 (by linarith : t < t + δ))
    have hut : u ∈ Set.Icc x y := ⟨ht.2.1.trans htu.le, (hu.trans_le (min_le_left _ _)).le⟩
    refine ⟨u, ?_, htu, hut.2⟩
    change edist (γ x) (γ u) ≤ _
    calc
      _ ≤ edist (γ x) (γ t) + edist (γ t) (γ u) := edist_triangle _ _ _
      _ ≤ (c : ENNReal) * ENNReal.ofReal (t - x) +
          (c : ENNReal) * ENNReal.ofReal (u - t) := by
        apply add_le_add ht.1
        rw [H t u ⟨hsub ⟨ht.2.1, ht.2.2.le⟩, by constructor <;> linarith⟩
          ⟨hsub hut, by constructor <;> linarith [min_le_right y (t + δ)]⟩,
          abs_of_pos (sub_pos.mpr htu)]
      _ = _ := by
        rw [← mul_add, ← ENNReal.ofReal_add (sub_nonneg.mpr ht.2.1)
          (sub_nonneg.mpr htu.le)]
        congr 2
        ring
  intro x hx y hy
  rw [edist_dist x y, Real.dist_eq, abs_sub_comm]
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hbound x hx y hy hxy
  · rw [edist_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hbound y hy x hx hyx
theorem MetricLocallyLinear.endpoint_limit {M : Type*} [EMetricSpace M] [CompleteSpace M]
    {γ : ℝ → M} {c : NNReal} {a b : ℝ} (hab : a < b)
    (h : MetricLocallyLinear γ c (Set.Ioo a b)) :
    ∃ p : M, Filter.Tendsto γ (nhdsWithin b (Set.Ioo a b)) (nhds p) := by
  letI := right_nhdsWithin_Ioo_neBot hab
  apply cauchy_map_iff_exists_tendsto.mp
  exact (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le
    (h.lipschitzOn Set.ordConnected_Ioo).uniformContinuousOn inf_le_right
theorem MetricLocallyLinear.reflect {M : Type*} [EMetricSpace M]
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : MetricLocallyLinear γ c S) :
    MetricLocallyLinear (fun t => γ (-t)) c ((fun t : ℝ => -t) ⁻¹' S) := by
  intro x hx
  obtain ⟨δ, hδ, H⟩ := h (-x) hx
  refine ⟨δ, hδ, fun s t hs ht => ?_⟩
  have heq := H (-s) (-t) ⟨hs.1, by constructor <;> linarith [hs.2.1, hs.2.2]⟩
    ⟨ht.1, by constructor <;> linarith [ht.2.1, ht.2.2]⟩
  simpa only [neg_sub_neg, abs_sub_comm] using heq
theorem MetricLocallyLinear.glue {M : Type*} [EMetricSpace M]
    {γ η : ℝ → M} {c : NNReal} {S T : Set ℝ}
    (hS : IsOpen S) (hT : IsOpen T)
    (hγ : MetricLocallyLinear γ c S) (hη : MetricLocallyLinear η c T)
    (heq : Set.EqOn η γ (S ∩ T)) :
    ∃ ζ : ℝ → M, MetricLocallyLinear ζ c (S ∪ T) ∧
      Set.EqOn ζ γ S ∧ Set.EqOn ζ η T := by
  classical
  let ζ : ℝ → M := fun t => if t ∈ S then γ t else η t
  have heqS : Set.EqOn ζ γ S := fun t ht => if_pos ht
  have heqT : Set.EqOn ζ η T := by
    intro t ht
    dsimp [ζ]
    split_ifs with hs
    · exact (heq ⟨hs, ht⟩).symm
    · rfl
  refine ⟨ζ, ?_, heqS, heqT⟩
  have hlocal : ∀ (U : Set ℝ) (f : ℝ → M), IsOpen U →
      MetricLocallyLinear f c U → Set.EqOn ζ f U →
      ∀ x ∈ U, ∃ δ > (0 : ℝ), ∀ s t : ℝ,
        s ∈ (S ∪ T) ∩ Set.Ioo (x - δ) (x + δ) →
        t ∈ (S ∪ T) ∩ Set.Ioo (x - δ) (x + δ) →
        edist (ζ s) (ζ t) = (c : ENNReal) * ENNReal.ofReal |t - s| := by
    intro U f hU hf hζ x hx
    obtain ⟨δ, hδ, H⟩ := hf x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    refine ⟨min δ ε, lt_min hδ hε, fun s t hs ht => ?_⟩
    have hmem : ∀ u ∈ Set.Ioo (x - min δ ε) (x + min δ ε),
        u ∈ U ∩ Set.Ioo (x - δ) (x + δ) := by
      intro u hu
      have huε : u ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2, min_le_right δ ε]
      exact ⟨hεU huε, by constructor <;> linarith [hu.1, hu.2, min_le_left δ ε]⟩
    rw [hζ (hmem s hs.2).1, hζ (hmem t ht.2).1]
    exact H s t (hmem s hs.2) (hmem t ht.2)
  intro x hx
  rcases hx with hx | hx
  · exact hlocal S γ hS hγ heqS x hx
  · exact hlocal T η hT hη heqT x hx
def HasMetricEndpointGerms (M : Type*) [EMetricSpace M] : Prop :=
  ∀ (a b : ℝ) (γ : ℝ → M) (c : NNReal) (p : M), a < b →
    MetricLocallyLinear γ c (Set.Ioo a b) →
    Filter.Tendsto γ (nhdsWithin b (Set.Ioo a b)) (nhds p) →
    ∃ ε > (0 : ℝ), ∃ η : ℝ → M,
      MetricLocallyLinear η c (Set.Ioo (b - ε) (b + ε)) ∧
      ∀ t ∈ Set.Ioo (max a (b - ε)) b, η t = γ t
theorem metricLocallyLinear_extend_bddAbove {M : Type*}
    [EMetricSpace M] [CompleteSpace M] (hG : HasMetricEndpointGerms M)
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (hS : IsOpen S) (hconn : S.OrdConnected) (hne : S.Nonempty)
    (hbdd : BddAbove S) (hγ : MetricLocallyLinear γ c S) :
    ∃ T : Set ℝ, ∃ η : ℝ → M, IsOpen T ∧ T.OrdConnected ∧
      S ⊆ T ∧ MetricLocallyLinear η c T ∧ Set.EqOn η γ S ∧
      ∃ t ∈ T, t ∉ S := by
  let b := sSup S
  have hlt : ∀ x ∈ S, x < b := by
    intro x hx
    obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    have hxδ : x + δ / 2 ∈ S := hδS (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < x + δ / 2 - x)]
      linarith)
    have := le_csSup hbdd hxδ
    dsimp [b]
    linarith
  obtain ⟨a, ha⟩ := hne
  have hab : a < b := hlt a ha
  have hi : Set.Ioo a b ⊆ S := by
    intro t ht
    obtain ⟨u, hu, htu⟩ := exists_lt_of_lt_csSup ⟨a, ha⟩ ht.2
    exact hconn.out ha hu ⟨ht.1.le, htu.le⟩
  obtain ⟨p, hp⟩ := (hγ.mono hi).endpoint_limit hab
  obtain ⟨ε, hε, η, hη, heq⟩ := hG a b γ c p hab (hγ.mono hi) hp
  let δ := min ε ((b - a) / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδa : a < b - δ := by
    have := min_le_right ε ((b - a) / 2)
    dsimp [δ]
    linarith
  let U := Set.Ioo (b - δ) (b + δ)
  have hUsub : U ⊆ Set.Ioo (b - ε) (b + ε) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heqU : Set.EqOn η γ (S ∩ U) := by
    intro t ht
    exact heq t ⟨max_lt (hδa.trans ht.2.1) (by linarith [ht.2.1]), hlt t ht.1⟩
  obtain ⟨ζ, hζ, hζγ, _⟩ := hγ.glue hS isOpen_Ioo (hη.mono hUsub) heqU
  have hinter : (S ∩ U).Nonempty := by
    obtain ⟨t, ht, htb⟩ := exists_between (by linarith : b - δ < b)
    exact ⟨t, hi ⟨hδa.trans ht, htb⟩, ht, by linarith⟩
  refine ⟨S ∪ U, ζ, hS.union isOpen_Ioo,
    (hconn.isPreconnected.union' hinter Set.ordConnected_Ioo.isPreconnected).ordConnected,
    Set.subset_union_left, hζ, hζγ, b, Or.inr ?_, ?_⟩
  · exact ⟨by linarith, by linarith⟩
  · exact fun hb => (hlt b hb).false
theorem metricLocallyLinear_extend_bddBelow {M : Type*}
    [EMetricSpace M] [CompleteSpace M] (hG : HasMetricEndpointGerms M)
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (hS : IsOpen S) (hconn : S.OrdConnected) (hne : S.Nonempty)
    (hbdd : BddBelow S) (hγ : MetricLocallyLinear γ c S) :
    ∃ T : Set ℝ, ∃ η : ℝ → M, IsOpen T ∧ T.OrdConnected ∧
      S ⊆ T ∧ MetricLocallyLinear η c T ∧ Set.EqOn η γ S ∧
      ∃ t ∈ T, t ∉ S := by
  let R := (fun t : ℝ => -t) ⁻¹' S
  have hR : R.Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨-t, by simpa [R] using ht⟩
  have hbR : BddAbove R := by
    obtain ⟨l, hl⟩ := hbdd
    exact ⟨-l, fun t ht => by have := hl ht; dsimp [R] at ht; linarith⟩
  obtain ⟨T, η, hT, hTc, hRT, hη, heq, t, htT, htR⟩ :=
    metricLocallyLinear_extend_bddAbove hG (hS.preimage continuous_neg)
      (hconn.preimage_anti (fun _ _ h => neg_le_neg h)) hR hbR hγ.reflect
  refine ⟨(fun t : ℝ => -t) ⁻¹' T, fun t => η (-t),
    hT.preimage continuous_neg, hTc.preimage_anti (fun _ _ h => neg_le_neg h), ?_, hη.reflect, ?_,
    -t, by simpa using htT, ?_⟩
  · intro t ht
    exact hRT (by simpa [R] using ht)
  · intro t ht
    have hh := heq (show -t ∈ R by simpa [R] using ht)
    simpa only [neg_neg] using hh
  · exact htR
theorem MetricLocallyLinear.on_open {M : Type*} [EMetricSpace M]
    {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : MetricLocallyLinear γ c S) (ho : IsOpen S) {x : ℝ} (hx : x ∈ S) :
    ∃ δ > (0 : ℝ), ∀ s t : ℝ,
      s ∈ Set.Ioo (x - δ) (x + δ) → t ∈ Set.Ioo (x - δ) (x + δ) →
      edist (γ s) (γ t) = (c : ENNReal) * ENNReal.ofReal |t - s| := by
  obtain ⟨δ, hδ, H⟩ := h x hx
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hx)
  have hmem : ∀ u ∈ Set.Ioo (x - min δ ε) (x + min δ ε),
      u ∈ S ∩ Set.Ioo (x - δ) (x + δ) := by
    intro u hu
    have huε : u ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, min_le_right δ ε]
    exact ⟨hεS huε, by constructor <;> linarith [hu.1, hu.2, min_le_left δ ε]⟩
  exact ⟨min δ ε, lt_min hδ hε, fun s t hs ht => H s t (hmem s hs) (hmem t ht)⟩
def MetricLinearExtension {M : Type*} [EMetricSpace M]
    (γ₀ : ℝ → M) (c : NNReal) (S₀ : Set ℝ) :=
  {v : Set ℝ × (ℝ → M) // IsOpen v.1 ∧ v.1.OrdConnected ∧ S₀ ⊆ v.1 ∧
    MetricLocallyLinear v.2 c v.1 ∧ Set.EqOn v.2 γ₀ S₀}
def MetricLinearExtension.domain {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : Set ℝ := u.val.1
def MetricLinearExtension.curve {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : ℝ → M := u.val.2
theorem MetricLinearExtension.isOpen {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : IsOpen u.domain := u.property.1
theorem MetricLinearExtension.ordConnected {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : u.domain.OrdConnected := u.property.2.1
theorem MetricLinearExtension.contains {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : S₀ ⊆ u.domain := u.property.2.2.1
theorem MetricLinearExtension.linear {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : MetricLocallyLinear u.curve c u.domain :=
  u.property.2.2.2.1
theorem MetricLinearExtension.agrees {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u : MetricLinearExtension γ₀ c S₀) : Set.EqOn u.curve γ₀ S₀ := u.property.2.2.2.2
def MetricLinearExtension.Extends {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (u v : MetricLinearExtension γ₀ c S₀) : Prop :=
  u.domain ⊆ v.domain ∧ Set.EqOn v.curve u.curve u.domain
theorem MetricLinearExtension.extends_trans {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    {u v w : MetricLinearExtension γ₀ c S₀}
    (huv : u.Extends v) (hvw : v.Extends w) : u.Extends w := by
  refine ⟨huv.1.trans hvw.1, fun t ht => ?_⟩
  exact (hvw.2 (huv.1 ht)).trans (huv.2 ht)
theorem MetricLinearExtension.chain_bound {M : Type*} [EMetricSpace M]
    {γ₀ : ℝ → M} {c : NNReal} {S₀ : Set ℝ}
    (C : Set (MetricLinearExtension γ₀ c S₀))
    (hC : IsChain MetricLinearExtension.Extends C) (hne : C.Nonempty) :
    ∃ v : MetricLinearExtension γ₀ c S₀, ∀ u ∈ C, u.Extends v := by
  classical
  have htotal : ∀ u ∈ C, ∀ v ∈ C, u.Extends v ∨ v.Extends u := by
    intro u hu v hv
    by_cases heq : u = v
    · subst v
      exact Or.inl ⟨Set.Subset.rfl, fun _ _ => rfl⟩
    · exact hC hu hv heq
  let U := ⋃ u ∈ C, u.domain
  have hex : ∀ t ∈ U, ∃ u ∈ C, t ∈ u.domain := by
    simpa only [U, Set.mem_iUnion, exists_prop] using
      (show ∀ t ∈ U, t ∈ U from fun _ ht => ht)
  let η : ℝ → M := fun t => if ht : t ∈ U then
    (Classical.choose (hex t ht)).curve t else γ₀ t
  have hagree : ∀ u ∈ C, Set.EqOn η u.curve u.domain := by
    intro u hu t ht
    have htU : t ∈ U := Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ht⟩⟩
    dsimp [η]
    rw [dif_pos htU]
    let v := Classical.choose (hex t htU)
    have hv : v ∈ C := (Classical.choose_spec (hex t htU)).1
    have htv : t ∈ v.domain := (Classical.choose_spec (hex t htU)).2
    rcases htotal u hu v hv with huv | hvu
    · exact huv.2 ht
    · exact (hvu.2 htv).symm
  have hUopen : IsOpen U := isOpen_iUnion fun u => isOpen_iUnion fun _ => u.isOpen
  have hUconn : U.OrdConnected := by
    constructor
    intro x hx y hy z hz
    obtain ⟨u, hu, hxu⟩ := hex x hx
    obtain ⟨v, hv, hyv⟩ := hex y hy
    rcases htotal u hu v hv with huv | hvu
    · exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv,
        v.ordConnected.out (huv.1 hxu) hyv hz⟩⟩
    · exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu,
        u.ordConnected.out hxu (hvu.1 hyv) hz⟩⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hcontains : S₀ ⊆ U := fun t ht =>
    Set.mem_iUnion.mpr ⟨u₀, Set.mem_iUnion.mpr ⟨hu₀, u₀.contains ht⟩⟩
  have hη : MetricLocallyLinear η c U := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := hex x hx
    obtain ⟨δ, hδ, H⟩ := (u.linear.congr (hagree u hu)).on_open u.isOpen hxu
    exact ⟨δ, hδ, fun s t hs ht => H s t hs.2 ht.2⟩
  refine ⟨⟨⟨U, η⟩, hUopen, hUconn, hcontains, hη, ?_⟩, ?_⟩
  · intro t ht
    exact (hagree u₀ hu₀ (u₀.contains ht)).trans (u₀.agrees ht)
  · intro u hu
    exact ⟨fun t ht => Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ht⟩⟩,
      hagree u hu⟩
theorem exists_global_locallyLinear_extension_of_endpointGerm
    (M : Type*) [EMetricSpace M] [CompleteSpace M] :
    let L : (ℝ → M) → NNReal → Set ℝ → Prop := fun γ c S =>
      ∀ t₀ ∈ S, ∃ δ > (0 : ℝ), ∀ s t : ℝ,
        s ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
        t ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
        edist (γ s) (γ t) = (c : ENNReal) * ENNReal.ofReal |t - s|
    (∀ (a b : ℝ) (γ : ℝ → M) (c : NNReal) (p : M),
      a < b → L γ c (Set.Ioo a b) →
      Filter.Tendsto γ (nhdsWithin b (Set.Ioo a b)) (nhds p) →
      ∃ ε > (0 : ℝ), ∃ η : ℝ → M,
        L η c (Set.Ioo (b - ε) (b + ε)) ∧
        ∀ t ∈ Set.Ioo (max a (b - ε)) b, η t = γ t) →
    ∀ (a b : ℝ) (γ : ℝ → M) (c : NNReal), a < b → L γ c (Set.Ioo a b) →
      ∃ η : ℝ → M, L η c Set.univ ∧ ∀ t ∈ Set.Ioo a b, η t = γ t := by
  change HasMetricEndpointGerms M →
    ∀ (a b : ℝ) (γ : ℝ → M) (c : NNReal), a < b →
      MetricLocallyLinear γ c (Set.Ioo a b) →
      ∃ η : ℝ → M, MetricLocallyLinear η c Set.univ ∧ Set.EqOn η γ (Set.Ioo a b)
  intro hG a b γ c hab hγ
  let u₀ : MetricLinearExtension γ c (Set.Ioo a b) :=
    ⟨⟨Set.Ioo a b, γ⟩, isOpen_Ioo, Set.ordConnected_Ioo, Set.Subset.rfl,
      hγ, fun _ _ => rfl⟩
  letI : Nonempty (MetricLinearExtension γ c (Set.Ioo a b)) := ⟨u₀⟩
  have hex : ∃ u : MetricLinearExtension γ c (Set.Ioo a b),
      ∀ v, u.Extends v → v.Extends u := by
    apply exists_maximal_of_nonempty_chains_bounded
    · intro C hC hne
      exact MetricLinearExtension.chain_bound C hC hne
    · intro u v w huv hvw
      exact MetricLinearExtension.extends_trans huv hvw
  obtain ⟨u, hmax⟩ := hex
  have hne : u.domain.Nonempty :=
    ⟨(a + b) / 2, u.contains ⟨by linarith, by linarith⟩⟩
  have habove : ¬ BddAbove u.domain := by
    intro hbdd
    obtain ⟨T, η, hT, hTc, hST, hη, heq, t, htT, htS⟩ :=
      metricLocallyLinear_extend_bddAbove hG u.isOpen u.ordConnected hne hbdd u.linear
    let v : MetricLinearExtension γ c (Set.Ioo a b) :=
      ⟨⟨T, η⟩, hT, hTc, u.contains.trans hST, hη,
        fun s hs => (heq (u.contains hs)).trans (u.agrees hs)⟩
    have huv : u.Extends v := ⟨hST, heq⟩
    exact htS ((hmax v huv).1 htT)
  have hbelow : ¬ BddBelow u.domain := by
    intro hbdd
    obtain ⟨T, η, hT, hTc, hST, hη, heq, t, htT, htS⟩ :=
      metricLocallyLinear_extend_bddBelow hG u.isOpen u.ordConnected hne hbdd u.linear
    let v : MetricLinearExtension γ c (Set.Ioo a b) :=
      ⟨⟨T, η⟩, hT, hTc, u.contains.trans hST, hη,
        fun s hs => (heq (u.contains hs)).trans (u.agrees hs)⟩
    have huv : u.Extends v := ⟨hST, heq⟩
    exact htS ((hmax v huv).1 htT)
  have hfull : u.domain = Set.univ :=
    u.ordConnected.isPreconnected.eq_univ_of_unbounded hbelow habove
  refine ⟨u.curve, ?_, u.agrees⟩
  simpa only [← hfull] using u.linear

theorem riemannian_approximate_radial_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [(x : M) → ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    (hmetric : ∀ x y : M, edist x y = Manifold.riemannianEDist I x y)
    (x y : M) (r ε : ℝ) (hr : 0 ≤ r) (hrd : r ≤ dist x y) (hε : 0 < ε) :
    ∃ z : M, dist x z = r ∧ dist z y < dist x y - r + ε := open Bundle in by
  have htotalpos : 0 < dist x y + ε := by positivity
  have hd : Manifold.riemannianEDist I x y < ENNReal.ofReal (dist x y + ε) := by
    rw [← hmetric, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff htotalpos).2 (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hd
  have hf : ContinuousOn (fun t : ℝ => dist x (γ t)) (Set.Icc 0 1) :=
    continuous_dist.continuousOn.comp
      (continuousOn_const.prodMk hγ.continuousOn) (fun _ _ => Set.mem_univ _)
  have hrim : r ∈ Set.Icc (dist x (γ 0)) (dist x (γ 1)) := by
    simpa [hγ0, hγ1] using (show r ∈ Set.Icc 0 (dist x y) from ⟨hr, hrd⟩)
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hrim
  refine ⟨γ t, htr, ?_⟩
  have hpre : ENNReal.ofReal r ≤ Manifold.pathELength I γ 0 t := by
    rw [← htr, ← edist_dist, hmetric]
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
  have hsuf : ENNReal.ofReal (dist (γ t) y) ≤ Manifold.pathELength I γ t 1 := by
    rw [← edist_dist, hmetric]
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Set.Icc_subset_Icc ht.1 le_rfl)) rfl hγ1 ht.2
  have hsum : ENNReal.ofReal r + ENNReal.ofReal (dist (γ t) y) <
      ENNReal.ofReal (dist x y + ε) := by
    calc
      _ ≤ Manifold.pathELength I γ 0 t + Manifold.pathELength I γ t 1 := add_le_add hpre hsuf
      _ = Manifold.pathELength I γ 0 1 := Manifold.pathELength_add ht.1 ht.2
      _ < _ := hlen
  have hrest : 0 ≤ dist x y - r + ε := by linarith
  have heq : ENNReal.ofReal (dist x y + ε) =
      ENNReal.ofReal r + ENNReal.ofReal (dist x y - r + ε) := by
    rw [← ENNReal.ofReal_add hr hrest]
    congr 1
    ring
  rw [heq, ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top] at hsum
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < dist x y - r + ε)).1 hsum

theorem radial_split_inside_compact_ball
    {X : Type*} [MetricSpace X]
    (happrox : ∀ (x y : X) (r ε : ℝ), 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (x y p : X) (R s t : ℝ)
    (hcompact : IsCompact (Metric.closedBall x R))
    (hxy : dist x y = R) (hxp : dist x p = s) (hpy : dist p y = R - s)
    (hst : s ≤ t) (htR : t ≤ R) :
    ∃ z : X, dist p z = t - s ∧ dist z y = R - t ∧ dist x z = t := by
  let K : Set X := Metric.closedBall x R ∩ {z | dist p z = t - s}
  have hK : IsCompact K := hcompact.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have happroxK : ∀ ε > (0 : ℝ), ∃ z ∈ K, dist z y < R - t + ε := by
    intro ε hε
    obtain ⟨z, hpz, hzy⟩ := happrox p y (t-s) ε (by linarith) (by rw [hpy]; linarith) hε
    refine ⟨z, ⟨?_, hpz⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_comm]
      calc
        dist x z ≤ dist x p + dist p z := dist_triangle _ _ _
        _ = t := by rw [hxp, hpz]; ring
        _ ≤ R := htR
    · rw [hpy] at hzy
      linarith
  obtain ⟨z₀, hz₀, _⟩ := happroxK 1 (by norm_num)
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨z₀, hz₀⟩
    (continuous_id.dist continuous_const).continuousOn
  have hle : dist z y ≤ R - t := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨w, hw, hwy⟩ := happroxK ε hε
    exact (hmin hw).trans_lt hwy
  have hge : R-t ≤ dist z y := by
    have := dist_triangle p z y
    rw [hpy, hz.2] at this
    linarith
  have hzy : dist z y = R-t := le_antisymm hle hge
  refine ⟨z, hz.2, hzy, le_antisymm ?_ ?_⟩
  · have := dist_triangle x p z
    rw [hxp, hz.2] at this
    linarith
  · have := dist_triangle x z y
    rw [hxy, hzy] at this
    linarith


theorem metric_segment_of_compact_ball
    {X : Type*} [MetricSpace X]
    (happrox : ∀ (x y : X) (r ε : ℝ), 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (x y : X) (R : ℝ) (hxy : dist x y = R)
    (hcompact : IsCompact (Metric.closedBall x R)) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ R = y ∧
      ∀ s ∈ Set.Icc 0 R, ∀ t ∈ Set.Icc 0 R, dist (γ s) (γ t) = |t-s| := by
  classical
  have hR : 0 ≤ R := hxy ▸ dist_nonneg
  let Good : Set (ℝ × X) → Prop := fun G =>
    G ⊆ Set.Icc 0 R ×ˢ Metric.closedBall x R ∧
    (0,x) ∈ G ∧ (R,y) ∈ G ∧
    ∀ p ∈ G, ∀ q ∈ G, dist p.2 q.2 = |q.1-p.1|
  have hbase : Good {(0,x), (R,y)} := by
    refine ⟨?_, by simp, by simp, ?_⟩
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨⟨le_rfl, hR⟩, by simpa [Metric.mem_closedBall]⟩
      · exact ⟨⟨hR, le_rfl⟩, by simpa [Metric.mem_closedBall, dist_comm] using hxy.le⟩
    · intro p hp q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
        simp [hxy, dist_comm y x, abs_of_nonneg hR]
  obtain ⟨G, hG, hmax⟩ := zorn_subset {G | Good G} (by
    intro C hC hchain
    by_cases hne : C.Nonempty
    · refine ⟨⋃₀ C, ?_, fun G hGC => Set.subset_sUnion_of_mem hGC⟩
      obtain ⟨G₀, hG₀⟩ := hne
      refine ⟨?_, Set.mem_sUnion_of_mem (hC hG₀).2.1 hG₀,
        Set.mem_sUnion_of_mem (hC hG₀).2.2.1 hG₀, ?_⟩
      · exact Set.sUnion_subset fun G hGC => (hC hGC).1
      · intro p hp q hq
        obtain ⟨A, hAC, hpA⟩ := Set.mem_sUnion.1 hp
        obtain ⟨B, hBC, hqB⟩ := Set.mem_sUnion.1 hq
        rcases hchain.total hAC hBC with hAB | hBA
        · exact (hC hBC).2.2.2 p (hAB hpA) q hqB
        · exact (hC hAC).2.2.2 p hpA q (hBA hqB)
    · exact ⟨{(0,x), (R,y)}, hbase, fun G hGC => (hne ⟨G, hGC⟩).elim⟩)
  change Good G at hG
  have hGcl : Good (closure G) := by
    refine ⟨closure_minimal hG.1 (isClosed_Icc.prod Metric.isClosed_closedBall),
      subset_closure hG.2.1, subset_closure hG.2.2.1, ?_⟩
    have hrel : IsClosed {p : (ℝ × X) × (ℝ × X) |
        dist p.1.2 p.2.2 = |p.2.1-p.1.1|} := isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : G ×ˢ G ⊆ {p : (ℝ × X) × (ℝ × X) |
        dist p.1.2 p.2.2 = |p.2.1-p.1.1|} := fun p hp => hG.2.2.2 _ hp.1 _ hp.2
    intro p hp q hq
    exact closure_minimal hsub hrel (by simpa only [closure_prod_eq] using
      (show (p,q) ∈ closure G ×ˢ closure G from ⟨hp,hq⟩))
  have hclosed : IsClosed G := by
    exact closure_eq_iff_isClosed.mp (Set.Subset.antisymm (hmax hGcl subset_closure) subset_closure)
  have hcG : IsCompact G := (isCompact_Icc.prod hcompact).of_isClosed_subset hclosed hG.1
  let D : Set ℝ := Prod.fst '' G
  have hcD : IsCompact D := hcG.image continuous_fst
  have h0 : 0 ∈ D := ⟨(0,x), hG.2.1, rfl⟩
  have hRD : R ∈ D := ⟨(R,y), hG.2.2.1, rfl⟩
  have hD : ∀ t ∈ Set.Icc 0 R, t ∈ D := by
    intro t ht
    by_contra hnot
    obtain ⟨s, ⟨hsD, hst⟩, hsmax⟩ := (hcD.inter_right isClosed_Iic).exists_isGreatest
      ⟨0, h0, ht.1⟩
    obtain ⟨u, ⟨huD, htu⟩, humin⟩ := (hcD.inter_right isClosed_Ici).exists_isLeast
      ⟨R, hRD, ht.2⟩
    change s ≤ t at hst
    change t ≤ u at htu
    have hst' : s < t := lt_of_le_of_ne hst (by intro h; exact hnot (h ▸ hsD))
    have htu' : t < u := lt_of_le_of_ne htu (by intro h; exact hnot (h.symm ▸ huD))
    obtain ⟨⟨s',p⟩, hpG, hsp⟩ := hsD
    obtain ⟨⟨u',q⟩, hqG, huq⟩ := huD
    dsimp at hsp huq
    subst s'
    subst u'
    have hs0 : 0 ≤ s := (hG.1 hpG).1.1
    have huR : u ≤ R := (hG.1 hqG).1.2
    have hxp : dist x p = s := by
      simpa only [sub_zero, abs_of_nonneg hs0] using hG.2.2.2 (0,x) hG.2.1 (s,p) hpG
    have hxq : dist x q = u := by
      simpa only [sub_zero, abs_of_nonneg (hs0.trans (hst.trans htu))] using
        hG.2.2.2 (0,x) hG.2.1 (u,q) hqG
    have hpq : dist p q = u-s := by
      simpa only [abs_of_nonneg (sub_nonneg.2 (hst.trans htu))] using
        hG.2.2.2 (s,p) hpG (u,q) hqG
    have hcu : IsCompact (Metric.closedBall x u) := hcompact.of_isClosed_subset
      Metric.isClosed_closedBall (Metric.closedBall_subset_closedBall huR)
    obtain ⟨z, hpz, hzq, hxz⟩ := radial_split_inside_compact_ball happrox x q p u s t
      hcu hxq hxp hpq hst htu
    have hdist : ∀ v ∈ G, dist v.2 z = |t-v.1| := by
      intro v hv
      have hcase : v.1 ≤ s ∨ u ≤ v.1 := by
        by_cases hvt : v.1 ≤ t
        · exact Or.inl (hsmax ⟨⟨v,hv,rfl⟩,hvt⟩)
        · exact Or.inr (humin ⟨⟨v,hv,rfl⟩,(not_le.1 hvt).le⟩)
      rcases hcase with hvs | huv
      · have hvp : dist v.2 p = s-v.1 := by
          simpa only [abs_of_nonneg (sub_nonneg.2 hvs)] using hG.2.2.2 v hv (s,p) hpG
        have hvq : dist v.2 q = u-v.1 := by
          simpa only [abs_of_nonneg (sub_nonneg.2 (hvs.trans (hst.trans htu)))] using
            hG.2.2.2 v hv (u,q) hqG
        rw [abs_of_nonneg (sub_nonneg.2 (hvs.trans hst))]
        have hupper := dist_triangle v.2 p z
        have hlower := dist_triangle v.2 z q
        rw [hvp, hpz] at hupper
        rw [hvq, hzq] at hlower
        exact le_antisymm (by linarith) (by linarith)
      · have hvq : dist v.2 q = v.1-u := by
          simpa only [abs_of_nonpos (sub_nonpos.2 huv), neg_sub] using
            hG.2.2.2 v hv (u,q) hqG
        have hpv : dist p v.2 = v.1-s := by
          simpa only [abs_of_nonneg (sub_nonneg.2 ((hst.trans htu).trans huv))] using
            hG.2.2.2 (s,p) hpG v hv
        rw [abs_of_nonpos (sub_nonpos.2 (htu.trans huv)), neg_sub]
        have hupper := dist_triangle v.2 q z
        have hlower := dist_triangle p z v.2
        rw [hvq, dist_comm q z, hzq] at hupper
        rw [hpv, hpz, dist_comm z v.2] at hlower
        exact le_antisymm (by linarith) (by linarith)
    have hinsert : Good (insert (t,z) G) := by
      refine ⟨?_, Set.mem_insert_of_mem _ hG.2.1, Set.mem_insert_of_mem _ hG.2.2.1, ?_⟩
      · intro v hv
        rcases Set.mem_insert_iff.1 hv with rfl | hv
        · exact ⟨ht, by simpa [Metric.mem_closedBall, dist_comm, hxz] using ht.2⟩
        · exact hG.1 hv
      · intro v hv w hw
        rcases Set.mem_insert_iff.1 hv with rfl | hv <;>
          rcases Set.mem_insert_iff.1 hw with rfl | hw
        · simp
        · simpa only [dist_comm z w.2, abs_sub_comm] using hdist w hw
        · exact hdist v hv
        · exact hG.2.2.2 v hv w hw
    have : (t,z) ∈ G := hmax hinsert (Set.subset_insert _ _) (Set.mem_insert _ _)
    exact hnot ⟨(t,z), this, rfl⟩
  have hex : ∀ t ∈ Set.Icc 0 R, ∃ p : X, (t,p) ∈ G := by
    intro t ht
    obtain ⟨⟨s,p⟩, hp, hst⟩ := hD t ht
    exact ⟨p, by simpa only [← hst] using hp⟩
  let γ : ℝ → X := fun t => if ht : t ∈ Set.Icc 0 R then (hex t ht).choose else x
  have hγ : ∀ t ∈ Set.Icc 0 R, (t,γ t) ∈ G := by
    intro t ht
    simpa only [γ, dif_pos ht] using (hex t ht).choose_spec
  have hγdist : ∀ s ∈ Set.Icc 0 R, ∀ t ∈ Set.Icc 0 R, dist (γ s) (γ t) = |t-s| :=
    fun s hs t ht => hG.2.2.2 _ (hγ s hs) _ (hγ t ht)
  refine ⟨γ, ?_, ?_, hγdist⟩
  · apply dist_eq_zero.1
    simpa only [sub_self, abs_zero] using hG.2.2.2 _ (hγ 0 ⟨le_rfl,hR⟩) _ hG.2.1
  · apply dist_eq_zero.1
    simpa only [sub_self, abs_zero] using hG.2.2.2 _ (hγ R ⟨hR,le_rfl⟩) _ hG.2.2.1


theorem local_descent_segment
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (happrox : ∀ (x y : X) (r ε : ℝ), 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (f : X → ℝ) (hf : Continuous f)
    (hle : ∀ x y, f x ≤ dist x y + f y)
    (hdesc : ∀ x r ε, 0 ≤ r → r < f x → 0 < ε →
      ∃ y, dist x y = r ∧ f y < f x-r+ε)
    (x : X) (hfx : 0 < f x) :
    ∃ r > (0 : ℝ), r < f x ∧ ∃ γ : ℝ → X, γ 0 = x ∧
      (∀ s ∈ Set.Icc 0 r, ∀ t ∈ Set.Icc 0 r, dist (γ s) (γ t) = |t-s|) ∧
      ∀ t ∈ Set.Icc 0 r, f (γ t) = f x-t := by
  obtain ⟨ρ, hρ, hcρ⟩ := Metric.exists_isCompact_closedBall x
  let r := min ρ (f x / 2)
  have hr : 0 < r := lt_min hρ (by linarith)
  have hrfx : r < f x := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcr : IsCompact (Metric.closedBall x r) := hcρ.of_isClosed_subset
    Metric.isClosed_closedBall (Metric.closedBall_subset_closedBall (min_le_left _ _))
  let K : Set X := Metric.closedBall x r ∩ {y | dist x y = r}
  have hcK : IsCompact K := hcr.inter_right (isClosed_eq (by fun_prop) continuous_const)
  have happK : ∀ ε > (0 : ℝ), ∃ y ∈ K, f y < f x-r+ε := by
    intro ε hε
    obtain ⟨y, hxy, hfy⟩ := hdesc x r ε hr.le hrfx hε
    exact ⟨y, ⟨by simpa [Metric.mem_closedBall, dist_comm, hxy], hxy⟩, hfy⟩
  obtain ⟨y₀, hy₀, _⟩ := happK 1 (by norm_num)
  obtain ⟨y, hy, hmin⟩ := hcK.exists_isMinOn ⟨y₀,hy₀⟩ hf.continuousOn
  have hfy : f y = f x-r := by
    apply le_antisymm
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨z, hz, hfz⟩ := happK ε hε
      exact (hmin hz).trans_lt hfz
    · have := hle x y
      rw [hy.2] at this
      linarith
  obtain ⟨γ, hγ0, hγr, hdist⟩ := metric_segment_of_compact_ball happrox x y r hy.2 hcr
  refine ⟨r, hr, hrfx, γ, hγ0, hdist, ?_⟩
  intro t ht
  have hxt : dist x (γ t) = t := by
    simpa [hγ0, abs_of_nonneg ht.1] using hdist 0 ⟨le_rfl,hr.le⟩ t ht
  have hty : dist (γ t) y = r-t := by
    simpa [hγr, abs_of_nonneg (sub_nonneg.2 ht.2)] using hdist t ht r ⟨hr.le,le_rfl⟩
  have hupper := hle (γ t) y
  have hlower := hle x (γ t)
  rw [hty, hfy] at hupper
  rw [hxt] at hlower
  exact le_antisymm (by linarith) (by linarith)

theorem metric_segment_limit
    {X : Type*} [MetricSpace X]
    (hend : ∀ (b : ℝ) (γ : ℝ → X), 0 < b →
      (∀ s ∈ Set.Ioo 0 b, ∀ t ∈ Set.Ioo 0 b, dist (γ s) (γ t) = |t-s|) →
      ∃ p, Filter.Tendsto γ (nhdsWithin b (Set.Ioo 0 b)) (nhds p))
    (f : X → ℝ) (hf : Continuous f)
    (b R : ℝ) (hb : 0 < b) (γ : ℝ → X)
    (hdist : ∀ s ∈ Set.Ico 0 b, ∀ t ∈ Set.Ico 0 b, dist (γ s) (γ t) = |t-s|)
    (hval : ∀ t ∈ Set.Ioo 0 b, f (γ t) = R-t) :
    ∃ p, f p = R-b ∧ ∀ t ∈ Set.Ico 0 b, dist (γ t) p = b-t := by
  haveI : (nhdsWithin b (Set.Ioo 0 b)).NeBot := right_nhdsWithin_Ioo_neBot hb
  obtain ⟨p, hp⟩ := hend b γ hb (fun s hs t ht => hdist s ⟨hs.1.le,hs.2⟩ t ⟨ht.1.le,ht.2⟩)
  refine ⟨p, ?_, ?_⟩
  · have h₁ := hf.continuousAt.tendsto.comp hp
    have h₂ : Filter.Tendsto (fun t : ℝ => R-t) (nhdsWithin b (Set.Ioo 0 b)) (nhds (R-b)) :=
      (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique h₁
    apply h₂.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hval t ht).symm
  · intro s hs
    have h₁ : Filter.Tendsto (fun t => dist (γ s) (γ t))
        (nhdsWithin b (Set.Ioo 0 b)) (nhds (dist (γ s) p)) :=
      Filter.Tendsto.dist tendsto_const_nhds hp
    have h₂ : Filter.Tendsto (fun t : ℝ => |t-s|) (nhdsWithin b (Set.Ioo 0 b))
        (nhds (b-s)) := by
      simpa only [Pi.sub_apply, id_eq, abs_of_pos (sub_pos.2 hs.2)] using
        ((continuous_id.sub continuous_const).abs.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds : Filter.Tendsto (fun t : ℝ => |t-s|)
            (nhdsWithin b (Set.Ioo 0 b)) (nhds |b-s|))
    apply tendsto_nhds_unique h₁
    apply h₂.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hdist s hs t ⟨ht.1.le,ht.2⟩).symm


theorem false_of_positive_descent
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (happrox : ∀ (x y : X) (r ε : ℝ), 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (hend : ∀ (b : ℝ) (γ : ℝ → X), 0 < b →
      (∀ s ∈ Set.Ioo 0 b, ∀ t ∈ Set.Ioo 0 b, dist (γ s) (γ t) = |t-s|) →
      ∃ p, Filter.Tendsto γ (nhdsWithin b (Set.Ioo 0 b)) (nhds p))
    (f : X → ℝ) (hf : Continuous f)
    (hle : ∀ x y, f x ≤ dist x y + f y)
    (hpos : ∀ x, 0 < f x)
    (hdesc : ∀ x r ε, 0 ≤ r → r < f x → 0 < ε →
      ∃ y, dist x y = r ∧ f y < f x-r+ε)
    (x₀ : X) : False := by
  classical
  let R := f x₀
  have hR : 0 < R := hpos x₀
  let Good : Set (ℝ × X) → Prop := fun G =>
    ∃ r ∈ Set.Icc 0 R,
      (∀ t, (∃ p, (t,p) ∈ G) ↔ t ∈ Set.Icc 0 r) ∧
      (0,x₀) ∈ G ∧
      (∀ p ∈ G, f p.2 = R-p.1) ∧
      ∀ p ∈ G, ∀ q ∈ G, dist p.2 q.2 = |q.1-p.1|
  have hbase : Good {(0,x₀)} := by
    refine ⟨0, ⟨le_rfl,hR.le⟩, ?_, by simp, ?_, ?_⟩
    · intro t
      simp
    · intro p hp
      rcases Set.mem_singleton_iff.1 hp with rfl
      simp [R]
    · intro p hp q hq
      rcases Set.mem_singleton_iff.1 hp with rfl
      rcases Set.mem_singleton_iff.1 hq with rfl
      simp
  obtain ⟨G,hG,hmax⟩ := zorn_subset {G | Good G} (by
    intro C hC hchain
    by_cases hne : C.Nonempty
    · let U : Set (ℝ × X) := ⋃₀ C
      let D : Set ℝ := Prod.fst '' U
      obtain ⟨A,hAC⟩ := hne
      have h0U : (0,x₀) ∈ U := Set.mem_sUnion_of_mem (hC hAC).choose_spec.2.2.1 hAC
      have h0D : 0 ∈ D := ⟨(0,x₀),h0U,rfl⟩
      have htime : ∀ p ∈ U, p.1 ∈ Set.Icc 0 R := by
        intro p hp
        obtain ⟨A,hAC,hpA⟩ := Set.mem_sUnion.1 hp
        obtain ⟨r,hr,hdom,-⟩ := hC hAC
        exact ⟨(hdom p.1).1 ⟨p.2,hpA⟩ |>.1,
          le_trans ((hdom p.1).1 ⟨p.2,hpA⟩ |>.2) hr.2⟩
      have hdown : ∀ u ∈ D, ∀ t ∈ Set.Icc 0 u, t ∈ D := by
        intro u hu t ht
        obtain ⟨⟨u',p⟩,hp,hu'⟩ := hu
        dsimp at hu'
        subst u'
        obtain ⟨A,hAC,hpA⟩ := Set.mem_sUnion.1 hp
        obtain ⟨r,hr,hdom,-⟩ := hC hAC
        obtain ⟨q,hq⟩ := (hdom t).2 ⟨ht.1,ht.2.trans ((hdom u).1 ⟨p,hpA⟩).2⟩
        exact ⟨(t,q),Set.mem_sUnion_of_mem hq hAC,rfl⟩
      have hval : ∀ p ∈ U, f p.2 = R-p.1 := by
        intro p hp
        obtain ⟨A,hAC,hpA⟩ := Set.mem_sUnion.1 hp
        exact (hC hAC).choose_spec.2.2.2.1 p hpA
      have hdist : ∀ p ∈ U, ∀ q ∈ U, dist p.2 q.2 = |q.1-p.1| := by
        intro p hp q hq
        obtain ⟨A,hAC,hpA⟩ := Set.mem_sUnion.1 hp
        obtain ⟨B,hBC,hqB⟩ := Set.mem_sUnion.1 hq
        rcases hchain.total hAC hBC with hAB | hBA
        · exact (hC hBC).choose_spec.2.2.2.2 p (hAB hpA) q hqB
        · exact (hC hAC).choose_spec.2.2.2.2 p hpA q (hBA hqB)
      have hbdd : BddAbove D := ⟨R, fun t ⟨p,hp,hpt⟩ => hpt ▸ (htime p hp).2⟩
      let b := sSup D
      have htb : ∀ t ∈ D, t ≤ b := fun t ht => le_csSup hbdd ht
      have hb0 : 0 ≤ b := htb 0 h0D
      have hbR : b ≤ R := csSup_le ⟨0,h0D⟩ (fun t ⟨p,hp,hpt⟩ => hpt ▸ (htime p hp).2)
      have hbelow : ∀ t ∈ Set.Ico 0 b, t ∈ D := by
        intro t ht
        obtain ⟨u,hu,htu⟩ := exists_lt_of_lt_csSup ⟨0,h0D⟩ ht.2
        exact hdown u hu t ⟨ht.1,htu.le⟩
      by_cases hbD : b ∈ D
      · refine ⟨U, ⟨b,⟨hb0,hbR⟩,?_,h0U,hval,hdist⟩,
          fun A hAC => Set.subset_sUnion_of_mem hAC⟩
        intro t
        constructor
        · intro ⟨p,hp⟩
          exact ⟨(htime (t,p) hp).1,htb t ⟨(t,p),hp,rfl⟩⟩
        · intro ht
          obtain ⟨⟨s,p⟩,hp,hst⟩ := hdown b hbD t ht
          exact ⟨p,by simpa only [← hst] using hp⟩
      · have hbpos : 0 < b := lt_of_le_of_ne hb0 (by intro hb; exact hbD (hb ▸ h0D))
        have hstrict : ∀ p ∈ U, p.1 < b := by
          intro p hp
          exact lt_of_le_of_ne (htb p.1 ⟨p,hp,rfl⟩)
            (by intro he; exact hbD (he ▸ (show p.1 ∈ D from ⟨p,hp,rfl⟩)))
        have hex : ∀ t ∈ Set.Ico 0 b, ∃ p : X, (t,p) ∈ U := by
          intro t ht
          obtain ⟨⟨s,p⟩,hp,hst⟩ := hbelow t ht
          exact ⟨p,by simpa only [← hst] using hp⟩
        let γ : ℝ → X := fun t => if ht : t ∈ Set.Ico 0 b then (hex t ht).choose else x₀
        have hγ : ∀ t ∈ Set.Ico 0 b, (t,γ t) ∈ U := by
          intro t ht
          simpa only [γ,dite_eq_left ht] using (hex t ht).choose_spec
        obtain ⟨p,hfp,hdp⟩ := metric_segment_limit hend f hf b R hbpos γ
          (fun s hs t ht => hdist _ (hγ s hs) _ (hγ t ht))
          (fun t ht => hval _ (hγ t ⟨ht.1.le,ht.2⟩))
        have hUeq : ∀ z ∈ U, z.2 = γ z.1 := by
          intro z hz
          apply dist_eq_zero.1
          simpa only [sub_self,abs_zero] using
            hdist z hz _ (hγ z.1 ⟨(htime z hz).1,hstrict z hz⟩)
        have hzp : ∀ z ∈ U, dist z.2 p = b-z.1 := by
          intro z hz
          rw [hUeq z hz]
          exact hdp z.1 ⟨(htime z hz).1,hstrict z hz⟩
        refine ⟨insert (b,p) U, ?_, fun A hAC =>
          (Set.subset_sUnion_of_mem hAC).trans (Set.subset_insert _ _)⟩
        refine ⟨b,⟨hb0,hbR⟩,?_,Set.mem_insert_of_mem _ h0U,?_,?_⟩
        · intro t
          constructor
          · rintro ⟨z,hz⟩
            rcases Set.mem_insert_iff.1 hz with heq | hz
            · have : t = b := congrArg Prod.fst heq
              rw [this]
              exact ⟨hb0,le_rfl⟩
            · exact ⟨(htime (t,z) hz).1,(hstrict (t,z) hz).le⟩
          · intro ht
            rcases lt_or_eq_of_le ht.2 with hlt | rfl
            · obtain ⟨z,hz⟩ := hex t ⟨ht.1,hlt⟩
              exact ⟨z,Set.mem_insert_of_mem _ hz⟩
            · exact ⟨p,Set.mem_insert _ _⟩
        · intro z hz
          rcases Set.mem_insert_iff.1 hz with rfl | hz
          · exact hfp
          · exact hval z hz
        · intro z hz w hw
          rcases Set.mem_insert_iff.1 hz with rfl | hz <;>
            rcases Set.mem_insert_iff.1 hw with rfl | hw
          · simp
          · rw [dist_comm, hzp w hw, abs_of_nonpos (sub_nonpos.2 (hstrict w hw).le),neg_sub]
          · rw [hzp z hz, abs_of_nonneg (sub_nonneg.2 (hstrict z hz).le)]
          · exact hdist z hz w hw
    · exact ⟨{(0,x₀)},hbase,fun A hAC => (hne ⟨A,hAC⟩).elim⟩)
  obtain ⟨r,hr,hdom,h0,hval,hdist⟩ := hG
  obtain ⟨p,hp⟩ := (hdom r).2 ⟨hr.1,le_rfl⟩
  have hfp : f p = R-r := hval (r,p) hp
  obtain ⟨ℓ,hℓ,hℓf,γ,hγ0,hγdist,hγval⟩ :=
    local_descent_segment happrox f hf hle hdesc p (hpos p)
  have hrℓ : r+ℓ ≤ R := by rw [hfp] at hℓf; linarith
  let V : Set (ℝ × X) := (fun t : ℝ => (r+t,γ t)) '' Set.Icc 0 ℓ
  have hcross : ∀ z ∈ G, ∀ t ∈ Set.Icc 0 ℓ, dist z.2 (γ t) = r+t-z.1 := by
    intro z hz t ht
    have hzr : z.1 ≤ r := ((hdom z.1).1 ⟨z.2,hz⟩).2
    have hzp : dist z.2 p = r-z.1 := by
      simpa only [abs_of_nonneg (sub_nonneg.2 hzr)] using hdist z hz (r,p) hp
    have hpt : dist p (γ t) = t := by
      simpa [hγ0,abs_of_nonneg ht.1] using hγdist 0 ⟨le_rfl,hℓ.le⟩ t ht
    have hupper := dist_triangle z.2 p (γ t)
    rw [hzp,hpt] at hupper
    have hlower := hle z.2 (γ t)
    rw [hval z hz,hγval t ht,hfp] at hlower
    exact le_antisymm (by linarith) (by linarith)
  have hnew : Good (G ∪ V) := by
    refine ⟨r+ℓ,⟨by linarith [hr.1],hrℓ⟩,?_,Or.inl h0,?_,?_⟩
    · intro t
      constructor
      · rintro ⟨z,hz | hz⟩
        · have := (hdom t).1 ⟨z,hz⟩
          exact ⟨this.1,by linarith [this.2]⟩
        · obtain ⟨s,hs,he⟩ := hz
          have he' : r+s = t := congrArg Prod.fst he
          exact ⟨by linarith [hs.1,hr.1],by linarith [hs.2]⟩
      · intro ht
        by_cases htr : t ≤ r
        · obtain ⟨z,hz⟩ := (hdom t).2 ⟨ht.1,htr⟩
          exact ⟨z,Or.inl hz⟩
        · exact ⟨γ (t-r),Or.inr ⟨t-r,⟨by linarith,by linarith [ht.2]⟩,
            by simp⟩⟩
    · intro z hz
      rcases hz with hz | ⟨t,ht,rfl⟩
      · exact hval z hz
      · dsimp
        rw [hγval t ht,hfp]
        ring
    · intro z hz w hw
      rcases hz with hz | ⟨s,hs,rfl⟩ <;> rcases hw with hw | ⟨t,ht,rfl⟩
      · exact hdist z hz w hw
      · have hzr := ((hdom z.1).1 ⟨z.2,hz⟩).2
        simpa only [abs_of_nonneg (by linarith [ht.1] : 0 ≤ r+t-z.1)] using hcross z hz t ht
      · have hwr := ((hdom w.1).1 ⟨w.2,hw⟩).2
        rw [dist_comm, hcross w hw s hs]
        dsimp
        rw [abs_of_nonpos (by linarith [hs.1] : w.1-(r+s) ≤ 0)]
        ring
      · dsimp
        rw [hγdist s hs t ht]
        congr 1
        ring
  have hsub : G ∪ V ⊆ G := hmax hnew Set.subset_union_left
  have hendG : (r+ℓ,γ ℓ) ∈ G := hsub (Or.inr ⟨ℓ,⟨hℓ.le,le_rfl⟩,rfl⟩)
  have := ((hdom (r+ℓ)).1 ⟨γ ℓ,hendG⟩).2
  linarith


theorem completeSpace_of_metric_segment_limits
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (happrox : ∀ (x y : X) (r ε : ℝ), 0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : X, dist x z = r ∧ dist z y < dist x y - r + ε)
    (hend : ∀ (b : ℝ) (γ : ℝ → X), 0 < b →
      (∀ s ∈ Set.Ioo 0 b, ∀ t ∈ Set.Ioo 0 b, dist (γ s) (γ t) = |t-s|) →
      ∃ p, Filter.Tendsto γ (nhdsWithin b (Set.Ioo 0 b)) (nhds p)) :
    CompleteSpace X := by
  classical
  have hsurj : Function.Surjective ((↑) : X → UniformSpace.Completion X) := by
    intro q
    by_contra hq
    let f : X → ℝ := fun x => dist (x : UniformSpace.Completion X) q
    have hf : Continuous f := (UniformSpace.Completion.continuous_coe X).dist continuous_const
    have hpos : ∀ x, 0 < f x := fun x => dist_pos.2 (by
      intro h
      exact hq ⟨x,h⟩)
    have hle : ∀ x y, f x ≤ dist x y + f y := by
      intro x y
      simpa only [f,UniformSpace.Completion.dist_eq] using
        dist_triangle (x : UniformSpace.Completion X) (y : UniformSpace.Completion X) q
    have hdesc : ∀ x r ε, 0 ≤ r → r < f x → 0 < ε →
        ∃ y, dist x y = r ∧ f y < f x-r+ε := by
      intro x r ε hr hrfx hε
      let δ := min ((f x-r)/2) (ε/4)
      have hδ : 0 < δ := lt_min (by linarith) (by linarith)
      obtain ⟨y,hy⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt q hδ
      have hfy : f y < δ := by simpa only [f,dist_comm q] using hy
      have hfy₁ : f y < (f x-r)/2 := lt_of_lt_of_le hfy (min_le_left _ _)
      have hfy₂ : f y < ε/4 := lt_of_lt_of_le hfy (min_le_right _ _)
      have hrxy : r ≤ dist x y := by have := hle x y; linarith
      obtain ⟨z,hxz,hzy⟩ := happrox x y r (ε/2) hr hrxy (by linarith)
      have hxy : dist x y ≤ f x+f y := by
        simpa only [f,UniformSpace.Completion.dist_eq,dist_comm q] using
          dist_triangle (x : UniformSpace.Completion X) q (y : UniformSpace.Completion X)
      have hfz := hle z y
      exact ⟨z,hxz,by linarith⟩
    obtain ⟨x₀,-⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt q zero_lt_one
    exact false_of_positive_descent happrox hend f hf hle hpos hdesc x₀
  exact (UniformSpace.Completion.isUniformInducing_coe X).completeSpace_congr hsurj |>.2 inferInstance

theorem edist_ne_top_of_preconnected
    {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X] (x y : X) :
    edist x y ≠ ⊤ := by
  have huniv : Metric.eball x ⊤ = Set.univ :=
    IsClopen.eq_univ ⟨Metric.isClosed_eball_top,Metric.isOpen_eball⟩
      ⟨x,by simp [Metric.mem_eball]⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [huniv]; trivial
  exact (Metric.mem_eball'.1 hy).ne

theorem contDiffAt_fixedPoint_of_invertible
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {n : WithTop ℕ∞} {T : P × X → X} {u : P → X} {p : P}
    (hT : ContDiffAt ℝ n T (p, u p)) (hn : n ≠ 0)
    (hInv : (fderiv ℝ (fun z : P × X => z.2 - T z) (p, u p) ∘L
      ContinuousLinearMap.inr ℝ P X).IsInvertible)
    (hu : ContinuousAt u p)
    (hfix : ∀ᶠ q in nhds p, T (q, u q) = u q) :
    ContDiffAt ℝ n u p := by
  let R : P × X → X := fun z => z.2 - T z
  have hR : ContDiffAt ℝ n R (p, u p) := contDiffAt_snd.sub hT
  let v : P → X := hR.implicitFunction hn hInv
  have hv : ContDiffAt ℝ n v p := hR.contDiffAt_implicitFunction hn hInv
  have hzero : R (p, u p) = 0 := by simp [R, hfix.self_of_nhds]
  have hpair : Filter.Tendsto (fun q => (q, u q)) (nhds p) (nhds (p, u p)) :=
    continuousAt_id.prodMk hu
  have heq : ∀ᶠ q in nhds p, u q = v q := by
    filter_upwards [hpair.eventually (hR.eventually_apply_eq_iff_implicitFunction hn hInv),
      hfix] with q hq hqfix
    exact (hq.mp (by simp [R, hqfix, hzero])).symm
  exact hv.congr_of_eventuallyEq heq

theorem exists_smooth_fixedPoint_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {U : Set (P × X)} (hU : IsOpen U) {T : P × X → X}
    (hT : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) T U)
    {p : P} {x : X} (hz : (p, x) ∈ U) (hfix : T (p, x) = x)
    (hInv : (fderiv ℝ (fun z : P × X => z.2 - T z) (p, x) ∘L
      ContinuousLinearMap.inr ℝ P X).IsInvertible) :
    ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ ∃ u : P → X, u p = x ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u V ∧
      ∀ q ∈ V, (q, u q) ∈ U ∧ T (q, u q) = u q := by
  let R : P × X → X := fun z => z.2 - T z
  have hRW : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) R U := contDiffOn_snd.sub hT
  have hR := hRW.contDiffAt (hU.mem_nhds hz)
  have hR1 : ContDiffAt ℝ 1 R (p, x) := hR.of_le (by simp)
  let u : P → X := hR1.implicitFunction one_ne_zero hInv
  have hu : ContDiffAt ℝ 1 u p := hR1.contDiffAt_implicitFunction one_ne_zero hInv
  have hup : u p = x := hR1.implicitFunction_apply_self one_ne_zero hInv
  have hpair : Filter.Tendsto (fun q => (q, u q)) (nhds p) (nhds (p, x)) := by
    simpa only [hup, id_eq] using (continuousAt_id.prodMk hu.continuousAt).tendsto
  have hD : ContinuousAt
      (fun z : P × X => fderiv ℝ R z ∘L ContinuousLinearMap.inr ℝ P X) (p, x) :=
    ((hRW.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt
      (hU.mem_nhds hz)).clm_comp continuousAt_const
  have hnear : ∀ᶠ q in nhds p,
      (q, u q) ∈ U ∧ T (q, u q) = u q ∧
      (fderiv ℝ R (q, u q) ∘L ContinuousLinearMap.inr ℝ P X).IsInvertible ∧
      ContinuousAt u q := by
    filter_upwards [hpair.eventually (hU.mem_nhds hz),
      hR1.eventually_apply_implicitFunction one_ne_zero hInv,
      (hD.tendsto.comp hpair).eventually hInv.eventually_nhds,
      hu.eventually (by norm_num)] with q hq hqfix hqInv hqu
    refine ⟨hq, ?_, hqInv, hqu.continuousAt⟩
    have hzero : R (p, x) = 0 := by simp [R, hfix]
    exact (sub_eq_zero.mp (hqfix.trans hzero)).symm
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnear
  refine ⟨V, hV, hpV, u, hup, ?_, fun q hq => ⟨(hVsub hq).1,
    (hVsub hq).2.1⟩⟩
  intro q hq
  have hqu := hVsub hq
  apply (contDiffAt_fixedPoint_of_invertible
    (hT.contDiffAt (hU.mem_nhds hqu.1)) (by simp) hqu.2.2.1 hqu.2.2.2 ?_).contDiffWithinAt
  filter_upwards [hV.mem_nhds hq] with r hr
  exact (hVsub hr).2.1

noncomputable def picardPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ContinuousMap (Set.Icc (0 : ℝ) 1) E) :
    ContinuousMap (Set.Icc (0 : ℝ) 1) E :=
  let F : ℝ → E := fun s => f (Set.projIcc 0 1 zero_le_one s)
  have hF : Continuous F := f.continuous.comp continuous_projIcc
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), F s,
    (intervalIntegral.differentiable_integral_of_continuous hF).continuous.comp
      continuous_subtype_val⟩

noncomputable def picardPrimitiveCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    ContinuousMap (Set.Icc (0 : ℝ) 1) E →L[ℝ]
      ContinuousMap (Set.Icc (0 : ℝ) 1) E := by
  let L : ContinuousMap (Set.Icc (0 : ℝ) 1) E →ₗ[ℝ]
      ContinuousMap (Set.Icc (0 : ℝ) 1) E := {
    toFun := picardPrimitive
    map_add' := by
      intro f g
      ext t
      exact intervalIntegral.integral_add
        ((f.continuous.comp continuous_projIcc).intervalIntegrable _ _)
        ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
    map_smul' := by
      intro c f
      ext t
      exact intervalIntegral.integral_smul c _ }
  apply L.mkContinuous 1
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le (L f) (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in (0 : ℝ)..(t : ℝ), f (Set.projIcc 0 1 zero_le_one s)‖ ≤ ‖f‖
  calc
    _ ≤ ‖f‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => f.norm_coe_le_norm _)
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact mul_le_of_le_one_right (norm_nonneg f) t.2.2

theorem exists_smooth_rescaled_picard_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (W : Set (ContinuousMap (Set.Icc (0 : ℝ) 1) E)) (hW : IsOpen W)
    (N : ContinuousMap (Set.Icc (0 : ℝ) 1) E → ContinuousMap (Set.Icc (0 : ℝ) 1) E)
    (hN : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) N W)
    (x : E) (hx : ContinuousMap.const (Set.Icc (0 : ℝ) 1) x ∈ W) :
    ∃ V : Set (ℝ × E), IsOpen V ∧ (0, x) ∈ V ∧
      ∃ A : ℝ × E → ContinuousMap (Set.Icc (0 : ℝ) 1) E,
        A (0, x) = ContinuousMap.const _ x ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A V ∧
        ∀ z ∈ V, A z ∈ W ∧
          A z = ContinuousMap.const _ z.2 + z.1 • picardPrimitiveCLM (N (A z)) := by
  let C := ContinuousMap (Set.Icc (0 : ℝ) 1) E
  let c : E →L[ℝ] C := ContinuousLinearMap.const ℝ _
  let J : C →L[ℝ] C := picardPrimitiveCLM
  let T : ((ℝ × E) × C) → C := fun z => c z.1.2 + z.1.1 • J (N z.2)
  let D : Set ((ℝ × E) × C) := Set.univ ×ˢ W
  have hD : IsOpen D := isOpen_univ.prod hW
  have hT : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) T D := by
    have hNc : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (ℝ × E) × C => N z.2) D :=
      hN.comp contDiffOn_snd (fun _ hz => hz.2)
    exact (c.contDiff.comp_contDiffOn contDiffOn_fst.snd).add
      (contDiffOn_fst.fst.smul (J.contDiff.comp_contDiffOn hNc))
  let α₀ : C := ContinuousMap.const _ x
  have hz : (((0 : ℝ), x), α₀) ∈ D := ⟨Set.mem_univ _, hx⟩
  have hfix : T ((0, x), α₀) = α₀ := by
    change c x + (0 : ℝ) • _ = α₀
    simp only [zero_smul, add_zero]
    rfl
  let R : ((ℝ × E) × C) → C := fun z => z.2 - T z
  have hR : DifferentiableAt ℝ R ((0, x), α₀) :=
    ((contDiffOn_snd.sub hT).contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have hi : HasFDerivAt (fun α : C => (((0 : ℝ), x), α))
      (ContinuousLinearMap.inr ℝ (ℝ × E) C) α₀ :=
    (hasFDerivAt_const ((0 : ℝ), x) α₀).prodMk (hasFDerivAt_id α₀)
  have hc : HasFDerivAt (fun α : C => R ((0, x), α))
      (ContinuousLinearMap.id ℝ C) α₀ := by
    simpa [R, T] using (hasFDerivAt_id α₀).sub_const (c x)
  have hpartial : fderiv ℝ R ((0, x), α₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) C = ContinuousLinearMap.id ℝ C :=
    (hR.hasFDerivAt.comp α₀ hi).unique hc
  have hInv : (fderiv ℝ R ((0, x), α₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) C).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.refl ℝ C, rfl⟩
  obtain ⟨V, hV, hpV, A, hA₀, hA, hAT⟩ :=
    exists_smooth_fixedPoint_family hD hT hz hfix hInv
  refine ⟨V, hV, hpV, A, hA₀, hA, ?_⟩
  intro z hz
  exact ⟨(hAT z hz).1.2, (hAT z hz).2.symm⟩

theorem isOpen_superposition_domain
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsOpen U) :
    IsOpen {g : ContinuousMap K E | Set.range (fun k => g k) ⊆ U} :=
  ContinuousMap.isOpen_setOfPred_range_subset hU

theorem continuousOn_superposition_compact
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {E : Type*} [TopologicalSpace E] {F : Type*} [TopologicalSpace F]
    (U : Set E) (f : E → F) (N : ContinuousMap K E → ContinuousMap K F)
    (hf : ContinuousOn f U)
    (hN : ∀ g : ContinuousMap K E, Set.range (fun k => g k) ⊆ U →
      ∀ k, N g k = f (g k)) :
    ContinuousOn N {g : ContinuousMap K E | Set.range (fun k => g k) ⊆ U} := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have h := hf.comp continuous_eval.continuousOn
    (show Set.MapsTo (fun p : ContinuousMap K E × K => p.1 p.2)
      ({g : ContinuousMap K E | Set.range (fun k => g k) ⊆ U} ×ˢ Set.univ) U from
      fun p hp => hp.1 ⟨p.2, rfl⟩)
  exact h.congr (fun p hp => hN p.1 hp.1 p.2)

noncomputable def superposition_compact
    {K : Type*} [TopologicalSpace K]
    {E : Type*} [TopologicalSpace E]
    {F : Type*} [TopologicalSpace F] [Zero F]
    (f : E → F) (g : ContinuousMap K E) : ContinuousMap K F :=
  ContinuousMap.mkD (fun k => f (g k)) 0

theorem superposition_compact_apply
    {K : Type*} [TopologicalSpace K]
    {E : Type*} [TopologicalSpace E]
    {F : Type*} [TopologicalSpace F] [Zero F]
    {U : Set E} {f : E → F} (hf : ContinuousOn f U)
    {g : ContinuousMap K E} (hg : Set.range (fun k => g k) ⊆ U) (k : K) :
    superposition_compact f g k = f (g k) :=
  ContinuousMap.mkD_apply_of_continuous
    (hf.comp_continuous g.continuous (fun k => hg ⟨k, rfl⟩))

noncomputable def continuousMap_applyLinear
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ContinuousMap K (E →L[ℝ] F) →L[ℝ]
      ContinuousMap K E →L[ℝ] ContinuousMap K F := by
  letI : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  let B : ContinuousMap K (E →L[ℝ] F) →ₗ[ℝ]
      ContinuousMap K E →ₗ[ℝ] ContinuousMap K F :=
    LinearMap.mk₂ ℝ
      (fun A h => ⟨fun k => A k (h k), A.continuous.clm_apply h.continuous⟩)
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
  refine B.mkContinuous₂ 1 ?_
  intro A h
  apply (ContinuousMap.norm_le (B A h) (by positivity : 0 ≤ 1 * ‖A‖ * ‖h‖)).mpr
  intro k
  change ‖A k (h k)‖ ≤ 1 * ‖A‖ * ‖h‖
  simpa only [one_mul] using (A k).le_opNorm (h k) |>.trans
    (mul_le_mul (A.norm_coe_le_norm k) (h.norm_coe_le_norm k)
      (norm_nonneg _) (norm_nonneg _))

theorem continuousMap_applyLinear_apply
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ContinuousMap K (E →L[ℝ] F)) (h : ContinuousMap K E) (k : K) :
    continuousMap_applyLinear A h k = A k (h k) := rfl

theorem hasFDerivAt_continuousMap_of_pointwise
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} (hS : IsOpen S)
    (N : P → ContinuousMap K F) (A : P → P →L[ℝ] ContinuousMap K F)
    (hA : ContinuousOn A S)
    (hN : ∀ x ∈ S, ∀ k : K,
      HasFDerivAt (fun y => N y k) ((ContinuousMap.evalCLM ℝ k).comp (A x)) x)
    {g : P} (hg : g ∈ S) : HasFDerivAt N (A g) g := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.mp
    ((hA g hg).continuousAt (hS.mem_nhds hg)) ε hε
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hg)
  have hrδ : 0 < min r δ := lt_min hr hδ
  filter_upwards [Metric.ball_mem_nhds g hrδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  have hsub : Metric.ball g (min r δ) ⊆ S :=
    fun z hz => hrS (Metric.mem_ball.mpr (lt_of_lt_of_le hz (min_le_left _ _)))
  have hd (z) (hz : z ∈ Metric.ball g (min r δ)) :
      HasFDerivWithinAt (fun h => N h k - A g h k)
        ((ContinuousMap.evalCLM ℝ k).comp (A z) -
          (ContinuousMap.evalCLM ℝ k).comp (A g)) (Metric.ball g (min r δ)) z :=
    ((hN z (hsub hz) k).sub
      (((ContinuousMap.evalCLM ℝ k).comp (A g)).hasFDerivAt)).hasFDerivWithinAt
  have hb (z) (hz : z ∈ Metric.ball g (min r δ)) :
      ‖(ContinuousMap.evalCLM ℝ k).comp (A z) -
        (ContinuousMap.evalCLM ℝ k).comp (A g)‖ ≤ ε := by
    apply ContinuousLinearMap.opNorm_le_bound _ hε.le
    intro v
    change ‖((A z - A g) v) k‖ ≤ ε * ‖v‖
    refine (((A z - A g) v).norm_coe_le_norm k).trans
      (((A z - A g).le_opNorm v).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (le_of_lt (by
        simpa only [dist_eq_norm] using hAδ
          (lt_of_lt_of_le hz (min_le_right _ _)))) (norm_nonneg _)
  have hm := (convex_ball g (min r δ)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb (Metric.mem_ball_self hrδ) hy
  have he : (N y k - A g y k) - (N g k - A g g k) =
      (N y - N g - A g (y - g)) k := by
    simp only [ContinuousMap.sub_apply, map_sub]
    abel
  rw [he] at hm
  exact hm

theorem hasFDerivAt_superposition_compact
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set E) (f : E → F) (N : ContinuousMap K E → ContinuousMap K F)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hN : ∀ g : ContinuousMap K E, Set.range (fun k => g k) ⊆ U →
      ∀ k, N g k = f (g k))
    {g : ContinuousMap K E} (hg : Set.range (fun k => g k) ⊆ U) :
    HasFDerivAt N
      (continuousMap_applyLinear (superposition_compact (fderiv ℝ f) g)) g := by
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hS := isOpen_superposition_domain (K := K) hU
  have hdf := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hD := continuousOn_superposition_compact (K := K) U (fderiv ℝ f)
    (superposition_compact (K := K) (fderiv ℝ f)) hdf
    (fun g hg k => superposition_compact_apply hdf hg k)
  apply hasFDerivAt_continuousMap_of_pointwise hS N
    (fun g => continuousMap_applyLinear (superposition_compact (fderiv ℝ f) g))
    (continuousMap_applyLinear.continuous.comp_continuousOn hD) ?_ hg
  intro x hx k
  have hf' := ((hf.differentiableOn one_ne_zero (x k) (hx ⟨k, rfl⟩)
    ).differentiableAt (hU.mem_nhds (hx ⟨k, rfl⟩))).hasFDerivAt
  have hcomp := hf'.comp x ((ContinuousMap.evalCLM ℝ k).hasFDerivAt)
  have he : (fderiv ℝ f (x k)).comp (ContinuousMap.evalCLM ℝ k) =
      (ContinuousMap.evalCLM ℝ k).comp
        (continuousMap_applyLinear (superposition_compact (fderiv ℝ f) x)) := by
    ext v
    change (fderiv ℝ f (x k)) (v k) =
      superposition_compact (fderiv ℝ f) x k (v k)
    rw [superposition_compact_apply hdf hx]
  rw [he] at hcomp
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hx] with y hy
  exact hN y hy k

theorem contDiffOn_superposition_compact_nat.{uK, uE, uF}
    {K : Type uK} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) :
    ∀ {F : Type (max uE uF)} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (U : Set E) (f : E → F) (N : ContinuousMap K E → ContinuousMap K F),
      IsOpen U → ContDiffOn ℝ n f U →
      (∀ g : ContinuousMap K E, Set.range (fun k => g k) ⊆ U →
        ∀ k, N g k = f (g k)) →
      ContDiffOn ℝ n N {g : ContinuousMap K E | Set.range (fun k => g k) ⊆ U} := by
  induction n with
  | zero =>
    intro F _ _ U f N hU hf hN
    exact contDiffOn_zero.mpr
      (continuousOn_superposition_compact U f N hf.continuousOn hN)
  | succ n ih =>
    intro F _ _ U f N hU hf hN
    let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
    let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
    have hS := isOpen_superposition_domain (K := K) hU
    have hdf : ContDiffOn ℝ n (fderiv ℝ f) U :=
      hf.fderiv_of_isOpen hU (by simp)
    have hD := ih U (fderiv ℝ f) (superposition_compact (K := K) (fderiv ℝ f)) hU hdf
      (fun g hg k => superposition_compact_apply hdf.continuousOn hg k)
    have hder (g : ContinuousMap K E) (hg : Set.range (fun k => g k) ⊆ U) :=
      hasFDerivAt_superposition_compact U f N hU
        (hf.of_le (by exact_mod_cast Nat.succ_pos n)) hN hg
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hS).mpr
    refine ⟨fun g hg => (hder g hg).differentiableAt.differentiableWithinAt,
      ?_, ?_⟩
    · intro h
      simp at h
    · apply (continuousMap_applyLinear.contDiff.comp_contDiffOn hD).congr
      intro g hg
      exact (hder g hg).fderiv

theorem contDiffOn_superposition_compact.{uK, uE, uF}
    {K : Type uK} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (U : Set E) (f : E → F) (N : ContinuousMap K E → ContinuousMap K F)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hN : ∀ g : ContinuousMap K E, Set.range (fun k => g k) ⊆ U →
      ∀ k : K, N g k = f (g k)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) N
      {g : ContinuousMap K E | Set.range (fun k => g k) ⊆ U} := by
  let e : ULift.{uE} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  apply contDiffOn_infty.mpr
  intro n
  let Nu := fun g => (e.symm.toContinuousLinearMap.compLeftContinuous ℝ K) (N g)
  have hf' : ContDiffOn ℝ n (fun x => e.symm (f x)) U :=
    e.symm.contDiff.comp_contDiffOn (hf.of_le (by simp))
  have hNu := contDiffOn_superposition_compact_nat n U (fun x => e.symm (f x)) Nu
    hU hf' (by
      intro g hg k
      change e.symm (N g k) = e.symm (f (g k))
      rw [hN g hg k])
  have hdown := (e.toContinuousLinearMap.compLeftContinuous ℝ K).contDiff.comp_contDiffOn hNu
  convert hdown using 1
  ext g k
  rfl

theorem exists_smooth_rescaled_solution_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : Set E) (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (x : E) (hx : x ∈ U) :
    ∃ V : Set (ℝ × E), IsOpen V ∧ (0, x) ∈ V ∧
      ∃ A : ℝ × E → ContinuousMap (Set.Icc (0 : ℝ) 1) E,
        A (0, x) = ContinuousMap.const _ x ∧
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A V ∧
        ∀ z ∈ V, (∀ s, A z s ∈ U) ∧ ∀ s : Set.Icc (0 : ℝ) 1,
          A z s = z.2 + z.1 • ∫ τ in (0 : ℝ)..(s : ℝ),
            f (A z (Set.projIcc 0 1 zero_le_one τ)) := by
  let W := {g : ContinuousMap (Set.Icc (0 : ℝ) 1) E |
    Set.range (fun s => g s) ⊆ U}
  let N := superposition_compact (K := Set.Icc (0 : ℝ) 1) f
  have hN : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) N W :=
    contDiffOn_superposition_compact U f N hU hf
      (fun g hg s => superposition_compact_apply hf.continuousOn hg s)
  have hx' : ContinuousMap.const (Set.Icc (0 : ℝ) 1) x ∈ W := by
    rintro _ ⟨s, rfl⟩
    exact hx
  obtain ⟨V, hV, hpV, A, hA₀, hA, hAT⟩ :=
    exists_smooth_rescaled_picard_family W (isOpen_superposition_domain hU) N hN x hx'
  refine ⟨V, hV, hpV, A, hA₀, hA, ?_⟩
  intro z hz
  have hAW := (hAT z hz).1
  refine ⟨fun s => hAW ⟨s, rfl⟩, ?_⟩
  intro s
  have heq := congrArg (fun g : ContinuousMap (Set.Icc (0 : ℝ) 1) E => g s)
    (hAT z hz).2
  change A z s = z.2 + z.1 • ∫ τ in (0 : ℝ)..(s : ℝ),
    N (A z) (Set.projIcc 0 1 zero_le_one τ) at heq
  simpa only [N, superposition_compact_apply hf.continuousOn hAW] using heq

theorem contDiffOn_coordinate_spray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {n : WithTop ℕ∞} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ n Γ U) :
    ContDiffOn ℝ n (fun z : E × E => (z.2, -(Γ z.1 z.2 z.2))) (U ×ˢ Set.univ) := by
  exact contDiffOn_snd.prodMk
    ((((hΓ.comp contDiffOn_fst (fun _ hz => hz.1)).clm_apply
      contDiffOn_snd).clm_apply contDiffOn_snd).neg)


theorem rescaled_picard_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set E} {f : E → E} {K : NNReal} (hf : LipschitzOnWith K f S)
    {h : ℝ} (hh : ‖h‖ * K < 1) {y : E}
    {A B : ContinuousMap (Set.Icc (0 : ℝ) 1) E}
    (hAS : ∀ s, A s ∈ S) (hBS : ∀ s, B s ∈ S)
    (hA : ∀ s : Set.Icc (0 : ℝ) 1,
      A s = y + h • ∫ τ in (0 : ℝ)..(s : ℝ),
        f (A (Set.projIcc 0 1 zero_le_one τ)))
    (hB : ∀ s : Set.Icc (0 : ℝ) 1,
      B s = y + h • ∫ τ in (0 : ℝ)..(s : ℝ),
        f (B (Set.projIcc 0 1 zero_le_one τ))) : A = B := by
  have hAc : Continuous (fun τ : ℝ => f (A (Set.projIcc 0 1 zero_le_one τ))) :=
    hf.continuousOn.comp_continuous (A.continuous.comp continuous_projIcc)
      (fun τ => hAS _)
  have hBc : Continuous (fun τ : ℝ => f (B (Set.projIcc 0 1 zero_le_one τ))) :=
    hf.continuousOn.comp_continuous (B.continuous.comp continuous_projIcc)
      (fun τ => hBS _)
  have hn : ‖A - B‖ ≤ (‖h‖ * K) * ‖A - B‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro s
    change ‖A s - B s‖ ≤ _
    rw [hA s, hB s, add_sub_add_left_eq_sub, ← smul_sub,
      ← intervalIntegral.integral_sub (hAc.intervalIntegrable _ _)
        (hBc.intervalIntegrable _ _), norm_smul]
    have hi : ‖∫ τ in (0 : ℝ)..(s : ℝ),
        (f (A (Set.projIcc 0 1 zero_le_one τ)) -
          f (B (Set.projIcc 0 1 zero_le_one τ)))‖ ≤ K * ‖A - B‖ := by
      calc
        _ ≤ (K * ‖A - B‖) * |(s : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun τ _ =>
            (hf.norm_sub_le (hAS _) (hBS _)).trans
              (mul_le_mul_of_nonneg_left ((A - B).norm_coe_le_norm _) K.2))
        _ ≤ K * ‖A - B‖ := by
          rw [sub_zero, abs_of_nonneg s.2.1]
          exact mul_le_of_le_one_right (by positivity) s.2.2
    calc
      _ ≤ ‖h‖ * (K * ‖A - B‖) := mul_le_mul_of_nonneg_left hi (norm_nonneg h)
      _ = _ := by ring
  have hz : ‖A - B‖ = 0 := by nlinarith [norm_nonneg (A - B)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem mul_mem_time_interval {h δ s : ℝ} (hh : |h| < δ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : h * s ∈ Set.Ioo (-δ) δ := by
  apply abs_lt.mp
  calc
    |h * s| = |h| * s := by rw [abs_mul, abs_of_nonneg hs.1]
    _ ≤ |h| := mul_le_of_le_one_right (abs_nonneg h) hs.2
    _ < δ := hh

theorem rescaled_solution_picard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {δ h : ℝ} (hh : |h| < δ) {β : ℝ → E}
    (hβ : ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt β (f (β t)) t)
    (B : ContinuousMap (Set.Icc (0 : ℝ) 1) E)
    (hB : ∀ s, B s = β (h * s))
    (hfc : Continuous (fun τ : ℝ => f (B (Set.projIcc 0 1 zero_le_one τ)))) :
    ∀ s : Set.Icc (0 : ℝ) 1,
      B s = β 0 + h • ∫ τ in (0 : ℝ)..(s : ℝ),
        f (B (Set.projIcc 0 1 zero_le_one τ)) := by
  intro s
  have hd (τ : ℝ) (hτ : τ ∈ Set.uIcc (0 : ℝ) (s : ℝ)) :
      HasDerivAt (fun τ => β (h * τ))
        (h • f (B (Set.projIcc 0 1 zero_le_one τ))) τ := by
    have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le s.2.1] at hτ
      exact ⟨hτ.1, hτ.2.trans s.2.2⟩
    have he : B (Set.projIcc 0 1 zero_le_one τ) = β (h * τ) := by
      rw [hB, Set.projIcc_of_mem zero_le_one hτ']
    rw [he]
    simpa only [Function.comp_def, mul_one] using
      (hβ (h * τ) (mul_mem_time_interval hh hτ')).scomp τ
      ((hasDerivAt_id τ).const_mul h)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hfc.const_smul h).intervalIntegrable 0 (s : ℝ))
  rw [intervalIntegral.integral_smul, mul_zero] at hi
  rw [hB, hi]
  abel

theorem exists_smooth_local_ode_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : Set E) (hU : IsOpen U) (f : E → E)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (x : E) (hx : x ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × E → E,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
        (Set.Ioo (-ε) ε ×ˢ Metric.ball x r) ∧
      (∀ y ∈ Metric.ball x r, Φ (0, y) = y) ∧
      ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball x r,
        Φ z ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2)) (f (Φ z)) z.1 := by
  obtain ⟨V, hV, h0V, A, hA0, hA, hApic⟩ :=
    exists_smooth_rescaled_solution_family U hU f hf x hx
  have hf1 : ContDiffAt ℝ 1 f x :=
    (hf.contDiffAt (hU.mem_nhds hx)).of_le (by simp)
  obtain ⟨K, S, hS, hLf⟩ := hf1.exists_lipschitzOnWith
  obtain ⟨T, hTS, hT, hxT⟩ := mem_nhds_iff.mp hS
  have hLT : LipschitzOnWith K f T := hLf.mono hTS
  obtain ⟨δ, hδ, a, ρ, L, Kβ, hρ, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf1
  obtain ⟨β, hβ, hβcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hβ hβcont
  have hβ0 : β (x, 0) = x := (hβ x (Metric.mem_closedBall_self (by positivity))).1
  have hβc : ContinuousAt β (x, (0 : ℝ)) :=
    hβcont.continuousAt (by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds x
        (show 0 < (ρ : ℝ) from hρ)) (Icc_mem_nhds (by linarith) hδ))
  have hβswap : ContinuousAt (fun z : ℝ × E => β (z.2, z.1)) (0, x) :=
    hβc.comp (f := fun z : ℝ × E => (z.2, z.1))
      (continuousAt_snd.prodMk continuousAt_fst)
  have hβnear : ∀ᶠ z : ℝ × E in nhds (0, x), β (z.2, z.1) ∈ T := by
    apply hβswap.tendsto.eventually
    change T ∈ nhds (β (x, 0))
    rw [hβ0]
    exact hT.mem_nhds hxT
  have hAnear : ∀ᶠ z : ℝ × E in nhds (0, x), ∀ s, A z s ∈ T := by
    have hW := isOpen_superposition_domain (K := Set.Icc (0 : ℝ) 1) hT
    have hAx : Set.range (fun s => A (0, x) s) ⊆ T := by
      rw [hA0]
      rintro _ ⟨s, rfl⟩
      exact hxT
    filter_upwards [(hA.contDiffAt (hV.mem_nhds h0V)).continuousAt.tendsto.eventually
      (hW.mem_nhds hAx)] with z hz s
    exact hz ⟨s, rfl⟩
  have hsmall : ∀ᶠ z : ℝ × E in nhds (0, x), ‖z.1‖ * K < 1 := by
    have hc : ContinuousAt (fun z : ℝ × E => ‖z.1‖ * (K : ℝ)) (0, x) :=
      continuousAt_fst.norm.mul continuousAt_const
    exact hc.eventually (gt_mem_nhds (by simp))
  have hdom : (Metric.closedBall x (ρ : ℝ) ×ˢ Set.Ioo (-δ) δ) ∈ nhds (x, (0 : ℝ)) :=
    by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds x
        (show 0 < (ρ : ℝ) from hρ)) (Ioo_mem_nhds (by linarith) hδ)
  have hdom' : ∀ᶠ z : ℝ × E in nhds (0, x),
      z.2 ∈ Metric.closedBall x (ρ : ℝ) ∧ z.1 ∈ Set.Ioo (-δ) δ := by
    have hc : ContinuousAt (fun z : ℝ × E => (z.2, z.1)) (0, x) :=
      continuousAt_snd.prodMk continuousAt_fst
    exact hc.tendsto.eventually hdom
  have hnear : ∀ᶠ z : ℝ × E in nhds (0, x),
      z ∈ V ∧ (∀ s, A z s ∈ T) ∧ β (z.2, z.1) ∈ T ∧
      ‖z.1‖ * K < 1 ∧ z.2 ∈ Metric.closedBall x (ρ : ℝ) ∧
      z.1 ∈ Set.Ioo (-δ) δ := by
    filter_upwards [hV.mem_nhds h0V, hAnear, hβnear, hsmall, hdom']
      with z hz hAz hβz hsz hdz
    exact ⟨hz, hAz, hβz, hsz, hdz⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hrect (z : ℝ × E) (hz : z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball x ε) :
      z ∈ V ∧ (∀ s, A z s ∈ T) ∧ β (z.2, z.1) ∈ T ∧
      ‖z.1‖ * K < 1 ∧ z.2 ∈ Metric.closedBall x (ρ : ℝ) ∧
      z.1 ∈ Set.Ioo (-δ) δ := by
    apply hεsub
    rw [← ball_prod_same]
    exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr hz.1,
      hz.2⟩
  let e : Set.Icc (0 : ℝ) 1 := ⟨1, by simp⟩
  let Φ : ℝ × E → E := fun z => A z e
  have heq (z : ℝ × E) (hz : z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball x ε) :
      Φ z = β (z.2, z.1) := by
    have hz' := hrect z hz
    have hh : |z.1| < δ := abs_lt.mpr hz'.2.2.2.2.2
    have hβd : ∀ t ∈ Set.Ioo (-δ) δ,
        HasDerivAt (fun t => β (z.2, t)) (f (β (z.2, t))) t := by
      intro t ht
      exact ((hβ z.2 hz'.2.2.2.2.1).2 t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    let B : ContinuousMap (Set.Icc (0 : ℝ) 1) E :=
      ⟨fun s => β (z.2, z.1 * s),
        (HasDerivAt.continuousOn hβd).comp_continuous
          (continuous_const.mul continuous_subtype_val)
          (fun s => mul_mem_time_interval hh s.2)⟩
    have hBS : ∀ s, B s ∈ T := by
      intro s
      exact (hrect (z.1 * s, z.2) ⟨mul_mem_time_interval (abs_lt.mpr hz.1) s.2,
        hz.2⟩).2.2.1
    have hfc : Continuous (fun τ : ℝ => f (B (Set.projIcc 0 1 zero_le_one τ))) :=
      hLT.continuousOn.comp_continuous (B.continuous.comp continuous_projIcc)
        (fun τ => hBS _)
    have hBpic := rescaled_solution_picard hh hβd B (fun _ => rfl) hfc
    have hAB : A z = B := rescaled_picard_unique hLT hz'.2.2.2.1
      hz'.2.1 hBS (hApic z hz'.1).2 (by
        simpa only [(hβ z.2 hz'.2.2.2.2.1).1] using hBpic)
    change A z e = _
    rw [hAB]
    change β (z.2, z.1 * 1) = _
    rw [mul_one]
  refine ⟨ε, hε, ε, hε, Φ, ?_, ?_, ?_⟩
  · exact ((ContinuousMap.evalCLM ℝ e).contDiff.comp_contDiffOn hA).mono
      (fun z hz => (hrect z hz).1)
  · intro y hy
    have hyV := (hrect (0, y) ⟨by simpa using hε, hy⟩).1
    simpa only [Φ, zero_smul, add_zero] using (hApic (0, y) hyV).2 e
  · intro z hz
    refine ⟨(hApic z (hrect z hz).1).1 e, ?_⟩
    have hz' := hrect z hz
    have hd := ((hβ z.2 hz'.2.2.2.2.1).2 z.1
      (Set.Ioo_subset_Icc_self hz'.2.2.2.2.2)).hasDerivAt
        (Icc_mem_nhds hz'.2.2.2.2.2.1 hz'.2.2.2.2.2.2)
    rw [← heq z hz] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hz.1.1 hz.1.2] with t ht
    exact heq (t, z.2) ⟨ht, hz.2⟩


theorem exists_smooth_local_ode_flow_at_equilibrium
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : Set E) (hU : IsOpen U) (F : E → E)
    (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F U)
    (p : E) (hp : p ∈ U) (hFp : F p = 0) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × E → E,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
        (Set.Ioo (-ε) ε ×ˢ Metric.ball p r) ∧
      (∀ y ∈ Metric.ball p r, Φ (0, y) = y) ∧
      (∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball p r,
        Φ z ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2)) (F (Φ z)) z.1) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, Φ (t, p) = p := by
  have hF1 : ContDiffAt ℝ 1 F p :=
    (hF.contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  obtain ⟨K, W, hW, hKF⟩ := hF1.exists_lipschitzOnWith
  obtain ⟨T, hTW, hT, hpT⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hp) hW)
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, hΦF⟩ :=
    Helpers.exists_smooth_local_ode_flow T hT F
      (hF.mono (fun y hy => (hTW hy).1)) p hpT
  refine ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, ?_, ?_⟩
  · intro z hz
    exact ⟨(hTW (hΦF z hz).1).1, (hΦF z hz).2⟩
  · apply Helpers.eq_const_of_lipschitz_ode (hKF.mono (fun y hy => (hTW hy).2)) hpT hFp
      (show (0 : ℝ) ∈ Set.Ioo (-ε) ε from ⟨by linarith, hε⟩)
    · intro t ht
      exact ⟨(hΦF (t,p) ⟨ht, Metric.mem_ball_self hr⟩).2,
        (hΦF (t,p) ⟨ht, Metric.mem_ball_self hr⟩).1⟩
    · exact hΦ0 p (Metric.mem_ball_self hr)

theorem fderiv_flow_initial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × E → E} {p : E}
    (hΦ : DifferentiableAt ℝ Φ (0, p))
    (hΦ0 : ∀ᶠ y in nhds p, Φ (0, y) = y) (v : E) :
    fderiv ℝ Φ (0, p) (0, v) = v := by
  have hi : HasFDerivAt (fun y : E => ((0 : ℝ), y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p :=
    (hasFDerivAt_const (0 : ℝ) p).prodMk (hasFDerivAt_id p)
  have hc := HasFDerivAt.comp (g := Φ) (f := fun y : E => ((0 : ℝ), y))
    p hΦ.hasFDerivAt hi
  have heq := (hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm hΦ0)).unique
    (hasFDerivAt_id p)
  have heqv := congrArg (fun L : E →L[ℝ] E => L v) heq
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using heqv

theorem fderiv_flow_eq_affine_of_sq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {Φ : ℝ × E → E} {A : E →L[ℝ] E} {p : E}
    {S : Set ℝ} {U : Set E}
    (hS : IsOpen S) (hconn : IsPreconnected S) (h0 : (0 : ℝ) ∈ S)
    (hU : IsOpen U) (hp : p ∈ U)
    (hΦ : ContDiffOn ℝ 2 Φ (S ×ˢ U))
    (hΦ0 : ∀ y ∈ U, Φ (0, y) = y)
    (hstationary : ∀ t ∈ S, Φ (t, p) = p)
    (htime : ∀ z ∈ S ×ˢ U,
      HasDerivAt (fun t : ℝ => Φ (t, z.2)) (F (Φ z)) z.1)
    (hF : HasFDerivAt F A p) (hA : A.comp A = 0) :
    ∀ t ∈ S, ∀ v : E, fderiv ℝ Φ (t, p) (0, v) = v + t • A v := by
  intro t ht v
  let D : ℝ → E := fun t => fderiv ℝ Φ (t, p) (0, v)
  have hD (s : ℝ) (hs : s ∈ S) : HasDerivAt D (A (D s)) s := by
    have hΦs : ContDiffAt ℝ 2 Φ (s,p) :=
      hΦ.contDiffAt ((hS.prod hU).mem_nhds ⟨hs,hp⟩)
    have hFs : DifferentiableAt ℝ F (Φ (s,p)) := by
      rw [hstationary s hs]
      exact hF.differentiableAt
    have hnear : ∀ᶠ z in nhds (s,p),
        HasDerivAt (fun t : ℝ => Φ (t,z.2)) (F (Φ z)) z.1 := by
      filter_upwards [(hS.prod hU).mem_nhds ⟨hs,hp⟩] with z hz
      exact htime z hz
    have hd := Helpers.hasDerivAt_flow_variation v hΦs hFs hnear
    simpa only [hstationary s hs, hF.fderiv] using hd
  have hD0 : D 0 = v := by
    apply Helpers.fderiv_flow_initial
      ((hΦ.contDiffAt ((hS.prod hU).mem_nhds ⟨h0,hp⟩)).differentiableAt (by norm_num))
    filter_upwards [hU.mem_nhds hp] with y hy using hΦ0 y hy
  simpa only [hD0] using Helpers.eq_affine_of_hasDerivAt_sq_zero A hA S hS hconn h0 D hD t ht

theorem exists_coordinate_spray_flow_with_linearization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {p : E} (hp : p ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × (E × E) → E × E,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
        (Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r) ∧
      (∀ y ∈ Metric.ball (p, 0) r, Φ (0, y) = y) ∧
      (∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
        (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2))
          ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, Φ (t, (p, 0)) = (p, 0)) ∧
      ∀ t ∈ Set.Ioo (-ε) ε, ∀ v : E,
        fderiv ℝ Φ (t, (p, 0)) (0, (0, v)) = (t • v, v) := by
  let F : E × E → E × E := fun z => (z.2, -(Γ z.1 z.2 z.2))
  have hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F (U ×ˢ Set.univ) :=
    Helpers.contDiffOn_coordinate_spray hΓ
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, hΦF, hΦp⟩ :=
    Helpers.exists_smooth_local_ode_flow_at_equilibrium (U ×ˢ Set.univ)
      (hU.prod isOpen_univ) F hF (p, 0) ⟨hp, Set.mem_univ _⟩ (by simp [F])
  refine ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, ?_, hΦp, ?_⟩
  · intro z hz
    exact ⟨(hΦF z hz).1.1, (hΦF z hz).2⟩
  · have hlinear := Helpers.fderiv_flow_eq_affine_of_sq_zero
      isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected
      (show (0 : ℝ) ∈ Set.Ioo (-ε) ε from ⟨by linarith, hε⟩)
      Metric.isOpen_ball (Metric.mem_ball_self hr)
      (hΦ.of_le (by simp)) hΦ0 hΦp (fun z hz => (hΦF z hz).2)
      (Helpers.hasFDerivAt_coordinate_spray_zero
        ((hΓ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)))
      (Helpers.coordinateSprayLinearization_sq E)
    intro t ht v
    simpa [Helpers.coordinateSprayLinearization] using hlinear t ht (0, v)

theorem exists_local_inverse_of_spray_flow_linearization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Φ : ℝ × (E × E) → E × E} {τ : ℝ} {p : E} (hτ : τ ≠ 0)
    (hΦ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ (τ, (p, 0)))
    (hΦp : Φ (τ, (p, 0)) = (p, 0))
    (hlin : ∀ v : E, fderiv ℝ Φ (τ, (p, 0)) (0, (0, v)) = (τ • v, v)) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ p ∈ e.target ∧
      (∀ v : E, e v = (Φ (τ, (p, v))).1) ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e 0 ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm p := by
  let f : E → E := fun v => (Φ (τ, (p, v))).1
  let J : E →L[ℝ] (ℝ × (E × E)) :=
    (0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))
  have hι : HasFDerivAt (fun v : E => (τ, (p, v))) J 0 :=
    (hasFDerivAt_const τ 0).prodMk
      ((hasFDerivAt_const p 0).prodMk (hasFDerivAt_id 0))
  have hcomp : HasFDerivAt (fun v : E => Φ (τ, (p, v)))
      ((fderiv ℝ Φ (τ,(p,0))).comp J) 0 :=
    HasFDerivAt.comp (g := Φ) (f := fun v : E => (τ, (p, v))) 0
      (hΦ.differentiableAt (by simp)).hasFDerivAt hι
  let L : E ≃L[ℝ] E := (Units.mk0 τ hτ) • ContinuousLinearEquiv.refl ℝ E
  have hf' : HasFDerivAt f (L : E →L[ℝ] E) 0 := by
    have hd := HasFDerivAt.comp (g := fun z : E × E => z.1)
      (f := fun v : E => Φ (τ, (p, v))) 0 hasFDerivAt_fst hcomp
    convert hd using 1
    · rfl
    · ext v
      simp [J, L, ContinuousLinearMap.comp_apply, hlin]
  have hf : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f 0 := by
    apply contDiffAt_fst.comp 0
    apply hΦ.comp 0
    exact contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
  let e : OpenPartialHomeomorph E E := hf.toOpenPartialHomeomorph f hf' (by simp)
  have hfp : f 0 = p := congrArg Prod.fst hΦp
  refine ⟨e, hf.mem_toOpenPartialHomeomorph_source hf' (by simp), ?_,
    fun _ => rfl, hf, ?_⟩
  · rw [← hfp]
    exact hf.image_mem_toOpenPartialHomeomorph_target hf' (by simp)
  · rw [← hfp]
    exact hf.to_localInverse hf' (by simp)

theorem bilinear_radius_sub_le_integral_of_bound : open MeasureTheory in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (B₀ : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ u v : E, B₀ u v = B₀ v u) → (∀ u : E, 0 ≤ B₀ u u) →
      ∀ (a b : ℝ), a ≤ b → ∀ (γ v : ℝ → E) (h : ℝ → ℝ),
      ContinuousOn v (Set.Icc a b) → ContinuousOn h (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, HasDerivAt γ (v t) t) →
      (∀ t ∈ Set.Icc a b, 0 ≤ h t) →
      (∀ t ∈ Set.Icc a b,
        |B₀ (γ t) (v t)| ≤ Real.sqrt (B₀ (γ t) (γ t)) * h t) →
      |Real.sqrt (B₀ (γ b) (γ b)) - Real.sqrt (B₀ (γ a) (γ a))| ≤
        ∫ t in a..b, h t := by
  intro E _ _ B₀ hsymm hnonneg a b hab γ v h hv hh hγ hhpos hbound
  have hγc : ContinuousOn γ (Set.Icc a b) :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hBc : ContinuousOn (fun t => B₀ (γ t)) (Set.Icc a b) :=
    B₀.continuous.comp_continuousOn hγc
  have hqc : ContinuousOn (fun t => B₀ (γ t) (γ t)) (Set.Icc a b) :=
    hBc.clm_apply hγc
  have hregular (δ : ℝ) (hδ : 0 < δ) :
      |Real.sqrt (B₀ (γ b) (γ b) + δ) - Real.sqrt (B₀ (γ a) (γ a) + δ)| ≤
        ∫ t in a..b, h t := by
    let f : ℝ → ℝ := fun t => Real.sqrt (B₀ (γ t) (γ t) + δ)
    let D : ℝ → ℝ := fun t => B₀ (γ t) (v t) / Real.sqrt (B₀ (γ t) (γ t) + δ)
    have hsqrtpos (t : ℝ) : 0 < Real.sqrt (B₀ (γ t) (γ t) + δ) :=
      Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (hnonneg _) hδ)
    have hD (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt f (D t) t := by
      have hq := (B₀.hasFDerivAt.comp_hasDerivAt t (hγ t ht)).clm_apply (hγ t ht)
      have hq' : HasDerivAt (fun s => B₀ (γ s) (γ s)) (2 * B₀ (γ t) (v t)) t := by
        convert hq using 1 <;> simp only [Function.comp_apply, hsymm (v t) (γ t)] <;> ring
      dsimp only [f, D]
      convert (hq'.add_const δ).sqrt
        (ne_of_gt (add_pos_of_nonneg_of_pos (hnonneg _) hδ)) using 1 <;> field_simp
    have hDc : ContinuousOn D (Set.Icc a b) :=
      (hBc.clm_apply hv).div (hqc.add continuousOn_const).sqrt
        (fun t _ => ne_of_gt (hsqrtpos t))
    have hDbound (t : ℝ) (ht : t ∈ Set.Icc a b) : |D t| ≤ h t := by
      dsimp only [D]
      rw [abs_div, abs_of_pos (hsqrtpos t), div_le_iff₀ (hsqrtpos t)]
      calc
        |B₀ (γ t) (v t)| ≤ Real.sqrt (B₀ (γ t) (γ t)) * h t := hbound t ht
        _ ≤ Real.sqrt (B₀ (γ t) (γ t) + δ) * h t :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (hhpos t ht)
        _ = h t * Real.sqrt (B₀ (γ t) (γ t) + δ) := mul_comm _ _
    have hFTC : (∫ t in a..b, D t) = f b - f a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hD t (by simpa only [Set.uIcc_of_le hab] using ht))
        (ContinuousOn.intervalIntegrable_of_Icc hab hDc)
    change |f b - f a| ≤ ∫ t in a..b, h t
    rw [← hFTC]
    apply (show ‖∫ t in a..b, D t‖ ≤ ∫ t in a..b, h t from ?_)
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun t ht => ?_))
      (ContinuousOn.intervalIntegrable_of_Icc hab hh)
    simpa only [Real.norm_eq_abs] using hDbound t ⟨ht.1.le, ht.2⟩
  have hc : Continuous (fun δ : ℝ =>
      |Real.sqrt (B₀ (γ b) (γ b) + δ) - Real.sqrt (B₀ (γ a) (γ a) + δ)|) := by
    fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ =>
      |Real.sqrt (B₀ (γ b) (γ b) + δ) - Real.sqrt (B₀ (γ a) (γ a) + δ)|)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds |Real.sqrt (B₀ (γ b) (γ b)) - Real.sqrt (B₀ (γ a) (γ a))|) := by
    simpa only [add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hregular δ hδ


theorem coordinate_spray_flow_linearization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {p : E} (hp : p ∈ U) (hΓ : DifferentiableAt ℝ Γ p)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r))
    (hΦ0 : ∀ y ∈ Metric.ball (p, 0) r, Φ (0, y) = y)
    (hΦp : ∀ t ∈ Set.Ioo (-ε) ε, Φ (t, (p, 0)) = (p, 0))
    (hODE : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
      HasDerivAt (fun t : ℝ => Φ (t, z.2))
        ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1) :
    ∀ t ∈ Set.Ioo (-ε) ε, ∀ u v : E,
      fderiv ℝ Φ (t, (p, 0)) (0, (u, v)) = (u + t • v, v) := by
  have hlinear := Helpers.fderiv_flow_eq_affine_of_sq_zero
    isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected
    (show (0 : ℝ) ∈ Set.Ioo (-ε) ε from ⟨by linarith, hε⟩)
    Metric.isOpen_ball (Metric.mem_ball_self hr) hΦ hΦ0 hΦp hODE
    (Helpers.hasFDerivAt_coordinate_spray_zero hΓ)
    (Helpers.coordinateSprayLinearization_sq E)
  intro t ht u v
  simpa [Helpers.coordinateSprayLinearization] using hlinear t ht (u,v)

noncomputable def coordinateEndpointLinearEquiv
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : ℝ) (hτ : τ ≠ 0) : (E × E) ≃L[ℝ] (E × E) where
  toFun z := (z.1, z.1 + τ • z.2)
  invFun z := (z.1, τ⁻¹ • (z.2 - z.1))
  left_inv z := by ext <;> simp [smul_smul, hτ]
  right_inv z := by ext <;> simp [smul_smul, hτ]
  map_add' x y := by ext <;> simp [smul_add] <;> abel
  map_smul' c z := by ext <;> simp [smul_add, smul_smul, mul_comm]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_local_inverse_of_two_point_spray_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Φ : ℝ × (E × E) → E × E} {τ : ℝ} {p : E} (hτ : τ ≠ 0)
    (hΦ : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ (τ, (p, 0)))
    (hΦp : Φ (τ, (p, 0)) = (p, 0))
    (hlin : ∀ u v : E,
      fderiv ℝ Φ (τ, (p, 0)) (0, (u, v)) = (u + τ • v, v)) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      (p, 0) ∈ e.source ∧ (p, p) ∈ e.target ∧
      (∀ z : E × E, e z = (z.1, (Φ (τ, z)).1)) ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e (p, 0) ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm (p, p) := by
  let f : (E × E) → E × E := fun z => (z.1, (Φ (τ, z)).1)
  let J : (E × E) →L[ℝ] (ℝ × (E × E)) :=
    (0 : (E × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))
  have hι : HasFDerivAt (fun z : E × E => (τ, z)) J (p,0) :=
    (hasFDerivAt_const τ (p,0)).prodMk (hasFDerivAt_id (p,0))
  have hcomp : HasFDerivAt (fun z : E × E => Φ (τ, z))
      ((fderiv ℝ Φ (τ,(p,0))).comp J) (p,0) :=
    HasFDerivAt.comp (g := Φ) (f := fun z : E × E => (τ,z)) (p,0)
      (hΦ.differentiableAt (by simp)).hasFDerivAt hι
  let L : (E × E) ≃L[ℝ] (E × E) := Helpers.coordinateEndpointLinearEquiv E τ hτ
  have hf' : HasFDerivAt f (L : (E × E) →L[ℝ] (E × E)) (p,0) := by
    have hd := HasFDerivAt.comp (g := fun z : E × E => z.1)
      (f := fun z : E × E => Φ (τ,z)) (p,0) hasFDerivAt_fst hcomp
    have hp := hasFDerivAt_fst (𝕜 := ℝ) (p := (p, (0 : E)))
    convert hp.prodMk hd using 1
    · rfl
    · ext z <;> simp [J, L, Helpers.coordinateEndpointLinearEquiv, hlin]
  have hf : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (p,0) :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp (p,0)
      (hΦ.comp (p,0) (contDiffAt_const.prodMk contDiffAt_id)))
  let e : OpenPartialHomeomorph (E × E) (E × E) :=
    hf.toOpenPartialHomeomorph f hf' (by simp)
  have hfp : f (p,0) = (p,p) := by simp [f, hΦp]
  refine ⟨e, hf.mem_toOpenPartialHomeomorph_source hf' (by simp), ?_,
    fun _ => rfl, hf, ?_⟩
  · rw [← hfp]
    exact hf.image_mem_toOpenPartialHomeomorph_target hf' (by simp)
  · rw [← hfp]
    exact hf.to_localInverse hf' (by simp)

theorem exists_coordinate_endpoint_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {p : E} (hp : p ∈ U) :
    ∃ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∃ Φ : ℝ × (E × E) → E × E,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
        (Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r) ∧
      (∀ y ∈ Metric.ball (p, 0) r, Φ (0, y) = y) ∧
      (∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
        (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2))
          ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1) ∧
      ∃ τ ∈ Set.Ioo (0 : ℝ) ε, ∃ e : OpenPartialHomeomorph (E × E) (E × E),
        (p, 0) ∈ e.source ∧ (p, p) ∈ e.target ∧
        (∀ z : E × E, e z = (z.1, (Φ (τ, z)).1)) ∧
        ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e (p, 0) ∧
        ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm (p, p) := by
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, hΦF, hΦp, _⟩ :=
    Helpers.exists_coordinate_spray_flow_with_linearization hU hΓ hp
  have hlin := Helpers.coordinate_spray_flow_linearization hU hp
    ((hΓ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hr hε
    (hΦ.of_le (by simp)) hΦ0 hΦp (fun z hz => (hΦF z hz).2)
  have hτ : (ε / 2 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  obtain ⟨e, he0, hep, hef, he, hei⟩ :=
    Helpers.exists_local_inverse_of_two_point_spray_flow
      (show ε / 2 ≠ 0 from ne_of_gt (by linarith))
      (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
        ⟨hτ, Metric.mem_ball_self hr⟩)) (hΦp (ε/2) hτ) (hlin (ε/2) hτ)
  exact ⟨ε, hε, r, hr, Φ, hΦ, hΦ0, hΦF, ε/2, ⟨by linarith, by linarith⟩,
    e, he0, hep, hef, he, hei⟩

theorem hasDerivAt_rescale_coordinate_geodesic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E} {κ t : ℝ}
    (hγ : HasDerivAt γ ((γ (κ*t)).2,
      -(Γ (γ (κ*t)).1 (γ (κ*t)).2 (γ (κ*t)).2)) (κ*t)) :
    HasDerivAt (fun s : ℝ => ((γ (κ*s)).1, κ • (γ (κ*s)).2))
      (κ • (γ (κ*t)).2,
        -(Γ (γ (κ*t)).1 (κ • (γ (κ*t)).2) (κ • (γ (κ*t)).2))) t := by
  have hd : HasDerivAt (fun s => γ (κ*s))
      (κ • ((γ (κ*t)).2, -(Γ (γ (κ*t)).1 (γ (κ*t)).2 (γ (κ*t)).2))) t := by
    simpa only [Function.comp_def, mul_one] using
      hγ.scomp t ((hasDerivAt_id t).const_mul κ)
  have hx : HasDerivAt (fun s => (γ (κ*s)).1) (κ • (γ (κ*t)).2) t := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.1) t hasFDerivAt_fst hd
  have hv : HasDerivAt (fun s => (γ (κ*s)).2)
      (κ • (-(Γ (γ (κ*t)).1 (γ (κ*t)).2 (γ (κ*t)).2))) t := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.2) t hasFDerivAt_snd hd
  have hv' := hv.const_smul κ
  simpa [smul_smul, map_smul, smul_apply, smul_neg] using hx.prodMk hv'

theorem coordinate_spray_flow_gauss_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} {r ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r))
    (hΦ0 : ∀ z ∈ Metric.ball (p,0) r, Φ (0,z) = z)
    (hODE : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r,
      (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t,z.2))
        ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1)
    (v w : E) (hv : (p,v) ∈ Metric.ball (p,0) r) :
    ∀ t ∈ Set.Ioo (-ε) ε,
      g (Φ (t,(p,v))).1 (Φ (t,(p,v))).2
          ((fderiv ℝ Φ (t,(p,v)) (0,(0,w))).1) = t * g p v w := by
  let R : Set ℝ := {s | (p,v+s•w) ∈ Metric.ball (p,0) r}
  let S : Set ℝ := Set.Ioo (-ε) ε
  let A : ℝ × ℝ → ℝ × (E × E) := fun z => (z.2,(p,v+z.1•w))
  let X : ℝ × ℝ → E := fun z => (Φ (A z)).1
  let V : ℝ × ℝ → E := fun z => (Φ (A z)).2
  have hR : IsOpen R := Metric.isOpen_ball.preimage (by fun_prop)
  have h0R : (0 : ℝ) ∈ R := by simpa [R] using hv
  have hZ : ContDiffOn ℝ 2 (fun z => Φ (A z)) (R ×ˢ S) :=
    hΦ.comp (by fun_prop) (fun z hz => ⟨hz.2,hz.1⟩)
  have hX : ContDiffOn ℝ 2 X (R ×ˢ S) := contDiff_fst.comp_contDiffOn hZ
  have hV : ContDiffOn ℝ 1 V (R ×ˢ S) :=
    (contDiff_snd.comp_contDiffOn hZ).of_le (by norm_num)
  have hXt (s : ℝ) (hs : s ∈ R) (t : ℝ) (ht : t ∈ S) :
      HasDerivAt (fun τ => X (s,τ)) (V (s,t)) t := by
    simpa [X,V,A,Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.1) t
        hasFDerivAt_fst (hODE (t,(p,v+s•w)) ⟨ht,hs⟩).2
  have hVt (s : ℝ) (hs : s ∈ R) (t : ℝ) (ht : t ∈ S) :
      HasDerivAt (fun τ => V (s,τ)) (-(Γ (X (s,t)) (V (s,t)) (V (s,t)))) t := by
    simpa [X,V,A,Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.2) t
        hasFDerivAt_snd (hODE (t,(p,v+s•w)) ⟨ht,hs⟩).2
  have hX0 (s : ℝ) (hs : s ∈ R) : X (s,0) = p := by
    simp [X,A,hΦ0 (p,v+s•w) hs]
  have hV0 (s : ℝ) (hs : s ∈ R) : V (s,0) = v+s•w := by
    simp [V,A,hΦ0 (p,v+s•w) hs]
  have hGauss := Helpers.coordinate_gauss_radial_pairing_of_contDiffOn
    (g := g) (Γ := fun x u v => Γ x u v) (X := X) (V := V)
    hR isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected
    (show (0 : ℝ) ∈ S from ⟨by linarith,hε⟩) hX hV
    (fun s hs t ht => (hg.contDiffAt (hU.mem_nhds
      (hODE (t,(p,v+s•w)) ⟨ht,hs⟩).1)).differentiableAt one_ne_zero)
    hsym (fun s hs t ht => hKoszul _ (hODE (t,(p,v+s•w)) ⟨ht,hs⟩).1)
    hXt hVt hX0 hV0 h0R
  intro t ht
  have hline : HasDerivAt (fun s : ℝ => (t,(p,v+s•w))) (0,(0,w)) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) t).prodMk
      ((hasDerivAt_const (0 : ℝ) p).prodMk
        (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v))
  have hΦat : DifferentiableAt ℝ Φ (t,(p,v)) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨ht,hv⟩)).differentiableAt (by norm_num)
  have hcomp : HasDerivAt (fun s : ℝ => Φ (t,(p,v+s•w)))
      (fderiv ℝ Φ (t,(p,v)) (0,(0,w))) 0 := by
    have hΦat' : HasFDerivAt Φ (fderiv ℝ Φ (t,(p,v))) (t,(p,v+(0:ℝ)•w)) := by
      simpa only [zero_smul,add_zero] using hΦat.hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun s : ℝ => (t,(p,v+s•w)))
      (0 : ℝ) hΦat' hline
  have hfirst : HasDerivAt (fun s => X (s,t))
      ((fderiv ℝ Φ (t,(p,v)) (0,(0,w))).1) 0 := by
    simpa [X,A,Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.1) (0 : ℝ)
        hasFDerivAt_fst hcomp
  have hJ := Helpers.hasDerivAt_coordinate_first_slice
    ((hX.contDiffAt ((hR.prod isOpen_Ioo).mem_nhds ⟨h0R,ht⟩)).differentiableAt
      (by norm_num))
  have hJeq := hJ.unique hfirst
  have h := hGauss t ht
  rw [hJeq] at h
  simpa [X,V,A] using h


theorem hasDerivAt_rescale_bilinear_spray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (γ : ℝ → E × E) (κ t : ℝ)
    (hγ : HasDerivAt γ
      ((γ (κ * t)).2, -Γ (γ (κ * t)).1 (γ (κ * t)).2 (γ (κ * t)).2) (κ * t)) :
    HasDerivAt (fun s => ((γ (κ * s)).1, κ • (γ (κ * s)).2))
      (κ • (γ (κ * t)).2,
        -Γ (γ (κ * t)).1 (κ • (γ (κ * t)).2) (κ • (γ (κ * t)).2)) t := by
  have htime : HasDerivAt (fun s : ℝ => κ * s) κ t := by
    simpa using (hasDerivAt_id t).const_mul κ
  have h : HasDerivAt (fun s => γ (κ * s))
      (κ • ((γ (κ * t)).2,
        -Γ (γ (κ * t)).1 (γ (κ * t)).2 (γ (κ * t)).2)) t :=
    hγ.scomp t htime
  have hf : HasDerivAt (fun s => (γ (κ * s)).1) (κ • (γ (κ * t)).2) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', Prod.smul_fst] using
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h
  have hs : HasDerivAt (fun s => (γ (κ * s)).2)
      (κ • (-Γ (γ (κ * t)).1 (γ (κ * t)).2 (γ (κ * t)).2)) t := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', Prod.smul_snd] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h
  convert hf.prodMk (hs.const_smul κ) using 1
  simp only [map_smul, smul_apply, smul_neg]

theorem rescale_velocity_mem_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E} {z : E × E} {R κ : ℝ} (hκ : |κ| ≤ 1)
    (hz : z ∈ Metric.ball (p, 0) R) :
    (z.1, κ • z.2) ∈ Metric.ball (p, 0) R := by
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hz ⊢
  refine ⟨hz.1, ?_⟩
  simp only [dist_zero_right, norm_smul, Real.norm_eq_abs] at hz ⊢
  exact lt_of_le_of_lt (by nlinarith [norm_nonneg z.2]) hz.2

theorem coordinate_spray_flow_rescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (Φ : ℝ → E × E → E × E)
    (p : E) {ε r R : ℝ} {K : NNReal} (hε : 0 < ε)
    (hLip : LipschitzOnWith K (fun z : E × E => (z.2, -Γ z.1 z.2 z.2))
      (Metric.ball (p, 0) R))
    (hΦ0 : ∀ v : E, ‖v‖ < r → Φ 0 (p, v) = (p, v))
    (hΦ : ∀ v : E, ‖v‖ < r → ∀ t : ℝ, |t| < ε →
      HasDerivAt (fun s => Φ s (p, v))
        ((Φ t (p, v)).2, -Γ (Φ t (p, v)).1 (Φ t (p, v)).2 (Φ t (p, v)).2) t ∧
      Φ t (p, v) ∈ Metric.ball (p, 0) R)
    (κ t : ℝ) (v : E) (hκ : |κ| ≤ 1) (ht : |t| < ε) (hv : ‖v‖ < r) :
    Φ t (p, κ • v) = ((Φ (κ * t) (p, v)).1, κ • (Φ (κ * t) (p, v)).2) := by
  have hκv : ‖κ • v‖ < r := by
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt (by nlinarith [norm_nonneg v]) hv
  have htime (s : ℝ) (hs : |s| < ε) : |κ * s| < ε := by
    rw [abs_mul]
    exact lt_of_le_of_lt (by nlinarith [abs_nonneg s]) hs
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun _ (z : E × E) => (z.2, -Γ z.1 z.2 z.2))
    (s := fun _ => Metric.ball (p, 0) R)
    (f := fun s => Φ s (p, κ • v))
    (g := fun s => ((Φ (κ * s) (p, v)).1, κ • (Φ (κ * s) (p, v)).2))
    (fun _ _ => hLip) hzero
    (fun s hs => hΦ (κ • v) hκv s (abs_lt.mpr hs))
    (fun s hs => ⟨hasDerivAt_rescale_bilinear_spray Γ (fun τ => Φ τ (p, v)) κ s
      (hΦ v hv (κ * s) (htime s (abs_lt.mpr hs))).1,
      rescale_velocity_mem_ball hκ
        (hΦ v hv (κ * s) (htime s (abs_lt.mpr hs))).2⟩)
    (by simp only [mul_zero, hΦ0 v hv, hΦ0 (κ • v) hκv])
  exact heq (abs_lt.mp ht)


theorem radial_fderiv_fst_of_scaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : ℝ × (E × E) → E × E) (t : ℝ) (p v V : E)
    (hΦ : DifferentiableAt ℝ Φ (t, (p, v)))
    (htime : HasDerivAt (fun s => (Φ (s, (p, v))).1) V t)
    (hscale : ∀ κ ∈ Set.Icc (0 : ℝ) 1,
      (Φ (t, (p, κ • v))).1 = (Φ (κ * t, (p, v))).1) :
    (fderiv ℝ Φ (t, (p, v)) (0, (0, v))).1 = t • V := by
  have hin : HasDerivAt (fun κ : ℝ => (t, (p, κ • v))) (0, (0, v)) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) t).prodMk
      ((hasDerivAt_const (1 : ℝ) p).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const v))
  have hleft : HasDerivAt (fun κ : ℝ => (Φ (t, (p, κ • v))).1)
      (fderiv ℝ Φ (t, (p, v)) (0, (0, v))).1 1 := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst'] using
      hΦ.hasFDerivAt.fst.comp_hasDerivAt_of_eq 1 hin (by simp)
  have hright : HasDerivAt (fun κ : ℝ => (Φ (κ * t, (p, v))).1) (t • V) 1 := by
    simpa only [Function.comp_def, one_mul, id_eq] using
      htime.scomp_of_eq 1 ((hasDerivAt_id (1 : ℝ)).mul_const t) (by simp)
  have hu : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) 1 :=
    uniqueDiffOn_Icc_zero_one 1 (by norm_num)
  have heq : HasDerivWithinAt (fun κ : ℝ => (Φ (t, (p, κ • v))).1)
      (t • V) (Set.Icc (0 : ℝ) 1) 1 :=
    hright.hasDerivWithinAt.congr_of_mem hscale (by norm_num)
  exact (hleft.hasDerivWithinAt.derivWithin hu).symm.trans (heq.derivWithin hu)


theorem enorm_sub_le_pathELength_of_scalar_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    (U : Set M) (hU : IsOpen U) (ρ : M → ℝ)
    (hρ : ContMDiffOn I (modelWithCornersSelf ℝ ℝ) 1 ρ U)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace I x,
      @enorm ℝ _ (mfderiv I (modelWithCornersSelf ℝ ℝ) ρ x v) ≤ enorm v)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hγU : Set.MapsTo γ (Set.Icc a b) U) :
    enorm (ρ (γ b) - ρ (γ a)) ≤ Manifold.pathELength I γ a b := by
  exact (open scoped ENNReal in by
    rcases hab.eq_or_lt with rfl | hab
    · simp
    have hcomp : ContDiffOn ℝ 1 (ρ ∘ γ) (Set.Icc a b) :=
      contMDiffOn_iff_contDiffOn.mp (hρ.comp hγ hγU)
    calc
      ‖ρ (γ b) - ρ (γ a)‖ₑ ≤
          ∫⁻ t in Set.Icc a b, ‖derivWithin (ρ ∘ γ) (Set.Icc a b) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hcomp hab.le
      _ = ∫⁻ t in Set.Icc a b,
          @enorm ℝ _ (mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
            (ρ ∘ γ) (Set.Icc a b) t 1) := by
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      _ ≤ ∫⁻ t in Set.Icc a b,
          ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I γ (Set.Icc a b) t 1‖ₑ := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hdρ : MDifferentiableAt I (modelWithCornersSelf ℝ ℝ) ρ (γ t) :=
          ((hρ (γ t) (hγU ht)).mdifferentiableWithinAt one_ne_zero).mdifferentiableAt
            (hU.mem_nhds (hγU ht))
        have heq := mfderiv_comp_mfderivWithin t
          hdρ ((hγ t ht).mdifferentiableWithinAt one_ne_zero)
          (show UniqueMDiffWithinAt (modelWithCornersSelf ℝ ℝ) (Set.Icc a b) t from
            uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_Icc hab t ht))
        rw [heq, ContinuousLinearMap.comp_apply]
        exact hbound (γ t) (hγU ht) _
      _ = Manifold.pathELength I γ a b :=
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc.symm)

theorem enorm_sub_le_pathELength_of_coordinate_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set M) (hU : IsOpen U) (V : Set F) (hV : IsOpen V)
    (c : M → F) (hc : ContMDiffOn I (modelWithCornersSelf ℝ F) 1 c U)
    (hcV : Set.MapsTo c U V) (f : F → ℝ) (hf : ContDiffOn ℝ 1 f V)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace I x,
      enorm (fderiv ℝ f (c x) (mfderiv I (modelWithCornersSelf ℝ F) c x v)) ≤ enorm v)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hγU : Set.MapsTo γ (Set.Icc a b) U) :
    enorm (f (c (γ b)) - f (c (γ a))) ≤ Manifold.pathELength I γ a b := by
  have hfM : ContMDiffOn (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ ℝ) 1 f V :=
    contMDiffOn_iff_contDiffOn.mpr hf
  apply enorm_sub_le_pathELength_of_scalar_bound I U hU (f ∘ c)
    (hfM.comp hc hcV) ?_ γ a b hab hγ hγU
  intro x hx v
  have hc' := ((hc x hx).mdifferentiableWithinAt one_ne_zero).mdifferentiableAt
    (hU.mem_nhds hx)
  have hf' := ((hfM (c x) (hcV hx)).mdifferentiableWithinAt one_ne_zero).mdifferentiableAt
    (hV.mem_nhds (hcV hx))
  rw [mfderiv_comp x hf' hc', ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
  exact hbound x hx v

theorem enorm_sub_le_pathELength_of_scalar_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    (U : Set M) (hU : IsOpen U) (ρ : M → ℝ) (ρδ : ℝ → M → ℝ)
    (hsmooth : ∀ δ > 0, ContMDiffOn I (modelWithCornersSelf ℝ ℝ) 1 (ρδ δ) U)
    (hbound : ∀ δ > 0, ∀ x ∈ U, ∀ v : TangentSpace I x,
      @enorm ℝ _ (mfderiv I (modelWithCornersSelf ℝ ℝ) (ρδ δ) x v) ≤ enorm v)
    (hlim : ∀ x ∈ U, Filter.Tendsto (fun δ => ρδ δ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ρ x)))
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hγU : Set.MapsTo γ (Set.Icc a b) U) :
    enorm (ρ (γ b) - ρ (γ a)) ≤ Manifold.pathELength I γ a b := by
  have hlim' := continuous_enorm.continuousAt.tendsto.comp
    ((hlim (γ b) (hγU (Set.right_mem_Icc.mpr hab))).sub
      (hlim (γ a) (hγU (Set.left_mem_Icc.mpr hab))))
  apply le_of_tendsto hlim'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact enorm_sub_le_pathELength_of_scalar_bound I U hU (ρδ δ)
    (hsmooth δ hδ) (hbound δ hδ) γ a b hab hγ hγU

theorem enorm_sqrt_sub_le_pathELength_of_regularized_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    (U : Set M) (hU : IsOpen U) (q : M → ℝ)
    (hsmooth : ∀ δ > 0, ContMDiffOn I (modelWithCornersSelf ℝ ℝ) 1
      (fun x => Real.sqrt (q x + δ)) U)
    (hbound : ∀ δ > 0, ∀ x ∈ U, ∀ v : TangentSpace I x,
      @enorm ℝ _ (mfderiv I (modelWithCornersSelf ℝ ℝ)
        (fun y => Real.sqrt (q y + δ)) x v) ≤ enorm v)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hγU : Set.MapsTo γ (Set.Icc a b) U) :
    enorm (Real.sqrt (q (γ b)) - Real.sqrt (q (γ a))) ≤
      Manifold.pathELength I γ a b := by
  apply enorm_sub_le_pathELength_of_scalar_limit I U hU (fun x => Real.sqrt (q x))
    (fun δ x => Real.sqrt (q x + δ)) hsmooth hbound ?_ γ a b hab hγ hγU
  intro x hx
  have hc : Continuous (fun δ : ℝ => Real.sqrt (q x + δ)) := by fun_prop
  simpa only [add_zero] using
    (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

theorem enorm_sub_le_pathELength_of_finite_piece_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    (ρ : M → ℝ) (γ : ℝ → M) (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) :
    (∀ i < n, enorm (ρ (γ (τ (i + 1))) - ρ (γ (τ i))) ≤
      Manifold.pathELength I γ (τ i) (τ (i + 1))) →
    enorm (ρ (γ (τ n)) - ρ (γ (τ 0))) ≤
      Manifold.pathELength I γ (τ 0) (τ n) := by
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    have hprev := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    have hlast := h n (Nat.lt_succ_self n)
    calc
      enorm (ρ (γ (τ (n + 1))) - ρ (γ (τ 0))) =
          enorm ((ρ (γ (τ n)) - ρ (γ (τ 0))) +
            (ρ (γ (τ (n + 1))) - ρ (γ (τ n)))) := by congr 1; ring
      _ ≤ enorm (ρ (γ (τ n)) - ρ (γ (τ 0))) +
          enorm (ρ (γ (τ (n + 1))) - ρ (γ (τ n))) := enorm_add_le _ _
      _ ≤ Manifold.pathELength I γ (τ 0) (τ n) +
          Manifold.pathELength I γ (τ n) (τ (n + 1)) := add_le_add hprev hlast
      _ = Manifold.pathELength I γ (τ 0) (τ (n + 1)) :=
        Manifold.pathELength_add (hτ (Nat.zero_le n)) (hτ (Nat.le_succ n))

theorem exists_first_exit_of_continuousOn
    {M : Type*} [TopologicalSpace M] (U : Set M) (hU : IsOpen U)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (ha : γ a ∈ U) (hb : γ b ∉ U) :
    ∃ t ∈ Set.Ioc a b, γ t ∈ frontier U ∧ Set.MapsTo γ (Set.Ico a t) U := by
  let K : Set ℝ := Set.Icc a b ∩ γ ⁻¹' Uᶜ
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl)
    Set.inter_subset_left
  have hbK : b ∈ K := ⟨⟨hab, le_rfl⟩, hb⟩
  obtain ⟨t, ht, hmin⟩ := hK.exists_isLeast ⟨b, hbK⟩
  have hat : a < t := lt_of_le_of_ne ht.1.1 (by
    intro heq
    exact ht.2 (heq ▸ ha))
  have hpre : Set.MapsTo γ (Set.Ico a t) U := by
    intro s hs
    by_contra hsu
    have hsK : s ∈ K := ⟨⟨hs.1, hs.2.le.trans ht.1.2⟩, hsu⟩
    exact (not_le_of_gt hs.2) (hmin hsK)
  have hclosure : γ t ∈ closure U := by
    apply ((hγ t ht.1).mono (show Set.Ico a t ⊆ Set.Icc a b from
      fun s hs => ⟨hs.1, hs.2.le.trans ht.1.2⟩)).mem_closure ?_ hpre
    rw [closure_Ico hat.ne]
    exact ⟨hat.le, le_rfl⟩
  refine ⟨t, ⟨hat, ht.1.2⟩, ?_, hpre⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hclosure, ht.2⟩

theorem exists_coordinate_spray_flow_in_lipschitz_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {p : E} (hp : p ∈ U) :
    ∃ R > (0 : ℝ), ∃ K : NNReal,
      LipschitzOnWith K (fun z : E × E => (z.2, -(Γ z.1 z.2 z.2)))
        (Metric.ball (p,0) R) ∧
      (∀ z : E × E, z ∈ Metric.ball (p,0) R → z.1 ∈ U) ∧
      ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × (E × E) → E × E,
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
          (Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r) ∧
        (∀ z ∈ Metric.ball (p,0) r, Φ (0,z) = z) ∧
        (∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r,
          Φ z ∈ Metric.ball (p,0) R ∧
          HasDerivAt (fun t : ℝ => Φ (t,z.2))
            ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1) ∧
        ∀ t ∈ Set.Ioo (-ε) ε, Φ (t,(p,0)) = (p,0) := by
  let F : E × E → E × E := fun z => (z.2, -(Γ z.1 z.2 z.2))
  have hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F (U ×ˢ Set.univ) :=
    Helpers.contDiffOn_coordinate_spray hΓ
  have hF1 : ContDiffAt ℝ 1 F (p,0) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp,Set.mem_univ _⟩)).of_le
      (by simp)
  obtain ⟨K,W,hW,hKF⟩ := hF1.exists_lipschitzOnWith
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hW ((hU.prod isOpen_univ).mem_nhds ⟨hp,Set.mem_univ _⟩))
  have hLip : LipschitzOnWith K F (Metric.ball (p,0) R) :=
    hKF.mono (fun z hz => (hsub hz).1)
  have hdom : Metric.ball (p,(0:E)) R ⊆ U ×ˢ (Set.univ : Set E) :=
    fun z hz => (hsub hz).2
  obtain ⟨r,hr,ε,hε,Φ,hΦ,hΦ0,hΦF⟩ :=
    Helpers.exists_smooth_local_ode_flow (Metric.ball (p,0) R) Metric.isOpen_ball F
      (hF.mono hdom) (p,0) (Metric.mem_ball_self hR)
  refine ⟨R,hR,K,hLip,(fun z hz => (hdom hz).1),r,hr,ε,hε,Φ,hΦ,hΦ0,hΦF,?_⟩
  apply Helpers.eq_const_of_lipschitz_ode hLip (Metric.mem_ball_self hR)
    (show F (p,0) = 0 by simp [F])
    (show (0:ℝ) ∈ Set.Ioo (-ε) ε from ⟨by linarith,hε⟩)
  · intro t ht
    exact ⟨(hΦF (t,(p,0)) ⟨ht,Metric.mem_ball_self hr⟩).2,
      (hΦF (t,(p,0)) ⟨ht,Metric.mem_ball_self hr⟩).1⟩
  · exact hΦ0 (p,0) (Metric.mem_ball_self hr)

theorem fderiv_coordinate_spray_endpoint_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : ℝ × (E × E) → E × E} {t : ℝ} {p v : E}
    (hΦ : DifferentiableAt ℝ Φ (t,(p,v))) (w : E) :
    fderiv ℝ (fun u : E => (Φ (t,(p,u))).1) v w =
      (fderiv ℝ Φ (t,(p,v)) (0,(0,w))).1 := by
  let J : E →L[ℝ] (ℝ × (E × E)) :=
    (0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))
  have hi : HasFDerivAt (fun u : E => (t,(p,u))) J v :=
    (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const p v).prodMk (hasFDerivAt_id v))
  have hc := HasFDerivAt.comp (g := Φ) (f := fun u : E => (t,(p,u)))
    v hΦ.hasFDerivAt hi
  have hd := HasFDerivAt.comp (g := fun z : E × E => z.1)
    (f := fun u : E => Φ (t,(p,u))) v hasFDerivAt_fst hc
  simpa [Function.comp_def,J] using
    congrArg (fun L : E →L[ℝ] E => L w) hd.fderiv

theorem coordinate_spray_endpoint_gauss
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} {r ε : ℝ} (hε : 0 < ε) {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r))
    (hΦ0 : ∀ z ∈ Metric.ball (p,0) r, Φ (0,z) = z)
    (hODE : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r,
      (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t,z.2))
        ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1)
    {v : E} (hv : (p,v) ∈ Metric.ball (p,0) r)
    {t : ℝ} (ht : t ∈ Set.Ioo (-ε) ε)
    (hscale : ∀ κ ∈ Set.Icc (0:ℝ) 1,
      (Φ (t,(p,κ•v))).1 = (Φ (κ*t,(p,v))).1) :
    ∀ w : E,
      g (Φ (t,(p,v))).1
        (fderiv ℝ (fun u : E => (Φ (t,(p,u))).1) v v)
        (fderiv ℝ (fun u : E => (Φ (t,(p,u))).1) v w) =
      t^2 * g p v w := by
  have hΦat : DifferentiableAt ℝ Φ (t,(p,v)) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨ht,hv⟩)).differentiableAt (by norm_num)
  have htime : HasDerivAt (fun s => (Φ (s,(p,v))).1) (Φ (t,(p,v))).2 t := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt (l := fun z : E × E => z.1) t
        hasFDerivAt_fst (hODE (t,(p,v)) ⟨ht,hv⟩).2
  have hradial := Helpers.radial_fderiv_fst_of_scaling Φ t p v _ hΦat htime hscale
  intro w
  rw [Helpers.fderiv_coordinate_spray_endpoint_apply hΦat,
    Helpers.fderiv_coordinate_spray_endpoint_apply hΦat,hradial]
  simp only [map_smul,smul_apply,smul_eq_mul]
  rw [Helpers.coordinate_spray_flow_gauss_pairing hU hg hsym hKoszul hε
    hΦ hΦ0 hODE v w hv t ht]
  ring

theorem exists_coordinate_normal_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : ContDiffOn ℝ 1 g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} (hp : p ∈ U) :
    ∃ τ > (0:ℝ), ∃ r > (0:ℝ), ∃ e : OpenPartialHomeomorph E E,
      (0:E) ∈ e.source ∧ p ∈ e.target ∧ e 0 = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e (Metric.ball 0 r) ∧
      ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm p ∧
      ∀ v ∈ Metric.ball 0 r, e v ∈ U ∧ ∀ w : E,
        g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = τ^2 * g p v w := by
  obtain ⟨R,hR,K,hLip,hdom,r,hr,ε,hε,Φ,hΦ,hΦ0,hΦF,hΦp⟩ :=
    Helpers.exists_coordinate_spray_flow_in_lipschitz_ball hU hΓ hp
  have hODE : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p,0) r,
      (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t,z.2))
        ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1 := by
    intro z hz
    exact ⟨hdom _ (hΦF z hz).1,(hΦF z hz).2⟩
  have hvball (v : E) (hv : ‖v‖ < r) : (p,v) ∈ Metric.ball (p,0) r := by
    simpa [Metric.mem_ball,Prod.dist_eq] using hv
  have hscale (κ t : ℝ) (v : E) (hκ : |κ| ≤ 1) (ht : |t| < ε) (hv : ‖v‖ < r) :
      Φ (t,(p,κ•v)) = ((Φ (κ*t,(p,v))).1,κ•(Φ (κ*t,(p,v))).2) := by
    apply Helpers.coordinate_spray_flow_rescale Γ (fun s z => Φ (s,z)) p hε hLip
    · intro u hu
      exact hΦ0 (p,u) (hvball u hu)
    · intro u hu s hs
      exact ⟨(hΦF (s,(p,u)) ⟨abs_lt.mp hs,hvball u hu⟩).2,
        (hΦF (s,(p,u)) ⟨abs_lt.mp hs,hvball u hu⟩).1⟩
    · exact hκ
    · exact ht
    · exact hv
  let τ : ℝ := ε/2
  have hτ : τ ∈ Set.Ioo (-ε) ε := ⟨by dsimp [τ]; linarith,by dsimp [τ]; linarith⟩
  have hτpos : 0 < τ := by dsimp [τ]; positivity
  have hΦat : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ (τ,(p,0)) :=
    hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨hτ,Metric.mem_ball_self hr⟩)
  have hlin := Helpers.coordinate_spray_flow_linearization hU hp
    ((hΓ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hr hε
    (hΦ.of_le (by simp)) hΦ0 hΦp (fun z hz => (hODE z hz).2)
  obtain ⟨e,he0,hep,hef,he,hei⟩ :=
    Helpers.exists_local_inverse_of_spray_flow_linearization hτpos.ne' hΦat
      (hΦp τ hτ) (fun v => by simpa only [zero_add] using hlin τ hτ 0 v)
  refine ⟨τ,hτpos,r,hr,e,he0,hep,?_,?_,hei,?_⟩
  · rw [hef]
    exact congrArg Prod.fst (hΦp τ hτ)
  · have hi : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : E => (τ,(p,v))) (Metric.ball 0 r) := by fun_prop
    have hc := hΦ.comp hi (fun v hv => ⟨hτ,hvball v (by simpa using hv)⟩)
    simpa only [Function.comp_def,← funext hef] using contDiff_fst.comp_contDiffOn hc
  · intro v hv
    have hvr : ‖v‖ < r := by simpa using hv
    have hv' := hvball v hvr
    refine ⟨by rw [hef]; exact (hODE (τ,(p,v)) ⟨hτ,hv'⟩).1,?_⟩
    intro w
    have h := Helpers.coordinate_spray_endpoint_gauss hU hg hsym hKoszul hε
      (hΦ.of_le (by simp)) hΦ0 hODE hv' hτ (fun κ hκ => by
        simpa only using congrArg (fun z : E × E => z.1)
          (hscale κ τ v (by simpa [abs_of_nonneg hκ.1] using hκ.2)
            (abs_lt.mpr hτ) hvr)) w
    simpa only [funext hef] using h

theorem hasFDerivAt_regularized_bilinear_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w : E, B₀ v w = B₀ w v)
    {ξ : E → E} {A : E →L[ℝ] E} {x : E} (hξ : HasFDerivAt ξ A x)
    (δ : ℝ) (hpos : 0 < B₀ (ξ x) (ξ x) + δ) :
    HasFDerivAt (fun y => Real.sqrt (B₀ (ξ y) (ξ y) + δ))
      ((1 / Real.sqrt (B₀ (ξ x) (ξ x) + δ)) • ((B₀ (ξ x)).comp A)) x := by
  have hq : HasFDerivAt (fun y => B₀ (ξ y) (ξ y))
      ((2 : ℝ) • ((B₀ (ξ x)).comp A)) x := by
    convert (B₀.hasFDerivAt.comp x hξ).clm_apply hξ using 1 <;> ext w <;>
      simp [hsymm (A w) (ξ x), two_mul]
  convert (hq.add_const δ).sqrt (ne_of_gt hpos) using 1
  ext w
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  field_simp

theorem radial_gauss_regularized_radius_fderiv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B B₀ : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ v w : E, B v w = B w v)
    (hnonneg : ∀ v : E, 0 ≤ B v v)
    (hsymm₀ : ∀ v w : E, B₀ v w = B₀ w v)
    (L A : E →L[ℝ] E) {ξ : E → E} {x : E}
    (hξ : HasFDerivAt ξ A x) (hinv : ∀ w : E, L (A w) = w)
    (hGauss : ∀ z : E, B (L (ξ x)) (L z) = B₀ (ξ x) z)
    (δ : ℝ) (hδ : 0 < δ) :
    DifferentiableAt ℝ (fun y => Real.sqrt (B₀ (ξ y) (ξ y) + δ)) x ∧
      ∀ w : E,
        |fderiv ℝ (fun y => Real.sqrt (B₀ (ξ y) (ξ y) + δ)) x w| ≤
          Real.sqrt (B w w) := by
  have hqnonneg : 0 ≤ B₀ (ξ x) (ξ x) := by
    rw [← hGauss (ξ x)]
    exact hnonneg _
  have hqpos : 0 < B₀ (ξ x) (ξ x) + δ :=
    add_pos_of_nonneg_of_pos hqnonneg hδ
  have hsqrtpos : 0 < Real.sqrt (B₀ (ξ x) (ξ x) + δ) :=
    Real.sqrt_pos.mpr hqpos
  have hρ := hasFDerivAt_regularized_bilinear_radius B₀ hsymm₀ hξ δ hqpos
  refine ⟨hρ.differentiableAt, fun w => ?_⟩
  rw [hρ.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, one_div_mul_eq_div]
  rw [abs_div, abs_of_pos hsqrtpos, div_le_iff₀ hsqrtpos]
  have hcs := radial_gauss_cauchy_schwarz B B₀ hsymm hnonneg L (ξ x) hGauss (A w)
  rw [hinv w] at hcs
  calc
    |B₀ (ξ x) (A w)| ≤ Real.sqrt (B₀ (ξ x) (ξ x)) * Real.sqrt (B w w) := hcs
    _ ≤ Real.sqrt (B₀ (ξ x) (ξ x) + δ) * Real.sqrt (B w w) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    _ = Real.sqrt (B w w) * Real.sqrt (B₀ (ξ x) (ξ x) + δ) := mul_comm _ _

theorem exists_pos_mul_norm_sq_le_bilinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : E, m * ‖v‖ ^ 2 ≤ B v v := by
  have hq : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  obtain ⟨m, hm, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hq.continuousOn (a := 0) (by
      intro v hv
      apply hpos v
      intro hv₀
      simp [hv₀] at hv)
  refine ⟨m, hm, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  calc
    m * ‖v‖ ^ 2 = ‖v‖ ^ 2 * m := mul_comm _ _
    _ ≤ ‖v‖ ^ 2 * B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) :=
      mul_le_mul_of_nonneg_left (hmin _ hunit) (sq_nonneg _)
    _ = B v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      field_simp

theorem isCompact_bilinear_radius_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (c : ℝ) : IsCompact {v : E | Real.sqrt (B v v) ≤ c} := by
  have hq : Continuous (fun v : E => B v v) := B.continuous.clm_apply continuous_id
  have hclosed : IsClosed {v : E | Real.sqrt (B v v) ≤ c} :=
    isClosed_le hq.sqrt continuous_const
  obtain ⟨m, hm, hbound⟩ := exists_pos_mul_norm_sq_le_bilinear B hpos
  apply (isCompact_closedBall (0 : E) (1 + c ^ 2 / m)).of_isClosed_subset hclosed
  intro v hv
  change Real.sqrt (B v v) ≤ c at hv
  have hqnonneg : 0 ≤ B v v := by
    by_cases hv₀ : v = 0
    · simp [hv₀]
    · exact (hpos v hv₀).le
  have hsqrt : 0 ≤ Real.sqrt (B v v) := Real.sqrt_nonneg _
  have hsq : B v v ≤ c ^ 2 := by
    nlinarith [Real.sq_sqrt hqnonneg, mul_self_le_mul_self hsqrt hv]
  have hnorm : ‖v‖ ^ 2 ≤ c ^ 2 / m := by
    apply (le_div_iff₀ hm).mpr
    nlinarith [hbound v]
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [sq_nonneg (‖v‖ - 1 / 2)]

theorem exists_inner_radius_neighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (x₀ : X) (hx₀ : x₀ ∈ e.source)
    (r : X → ℝ) (hr : Continuous r) (hr₀ : r x₀ = 0)
    (hrpos : ∀ x, x ≠ x₀ → 0 < r x)
    (hrcompact : IsCompact {x | r x ≤ 1})
    (W : Set Y) (hW : IsOpen W) (hxW : e x₀ ∈ W) :
    ∃ c : ℝ, 0 < c ∧ ∃ V : Set Y, IsOpen V ∧ e x₀ ∈ V ∧
      closure V ⊆ W ∧ closure V ⊆ e.target ∧
      (∀ y ∈ frontier V, r (e.symm y) = c) ∧
      (∀ y ∈ V, r (e.symm y) < c) := by
  let U : Set X := e.source ∩ e ⁻¹' W
  have hU : IsOpen U := e.isOpen_inter_preimage hW
  have hxU : x₀ ∈ U := ⟨hx₀, hxW⟩
  have hK : IsCompact ({x | r x ≤ 1} ∩ Uᶜ) :=
    hrcompact.inter_right hU.isClosed_compl
  obtain ⟨d, hd, hdle⟩ := hK.exists_forall_le' hr.continuousOn
    (a := 0) (fun x hx => hrpos x (fun heq => hx.2 (heq ▸ hxU)))
  let c : ℝ := min 1 d / 2
  have hc : 0 < c := half_pos (lt_min zero_lt_one hd)
  have hc₁ : c < 1 := by dsimp [c]; linarith [min_le_left (1 : ℝ) d]
  have hcd : c < d := by dsimp [c]; linarith [min_le_right (1 : ℝ) d]
  have hsub : {x | r x ≤ c} ⊆ U := by
    intro x hx
    by_contra hxu
    have := hdle x ⟨hx.trans hc₁.le, hxu⟩
    exact (not_le_of_gt hcd) (this.trans hx)
  have hsource : {x | r x ≤ c} ⊆ e.source := fun x hx => (hsub hx).1
  have hcompact : IsCompact {x | r x ≤ c} :=
    hrcompact.of_isClosed_subset (isClosed_le hr continuous_const)
      (fun x hx => hx.trans hc₁.le)
  have himage : IsCompact (e '' {x | r x ≤ c}) :=
    hcompact.image_of_continuousOn (e.continuousOn.mono hsource)
  let V : Set Y := e '' {x | r x < c}
  have hV : IsOpen V := e.isOpen_image_of_subset_source
    (isOpen_lt hr continuous_const) (fun x (hx : r x < c) => hsource hx.le)
  have hclosure : closure V ⊆ e '' {x | r x ≤ c} :=
    closure_minimal (Set.image_mono (fun x (hx : r x < c) => hx.le)) himage.isClosed
  have hrad (y : Y) (hy : y ∈ V) : r (e.symm y) < c := by
    obtain ⟨x, hx, rfl⟩ := hy
    change r x < c at hx
    simpa only [e.left_inv (hsource hx.le)] using hx
  refine ⟨c, hc, V, hV, ⟨x₀, ?_, rfl⟩, ?_, ?_, ?_, hrad⟩
  · change r x₀ < c
    simpa only [hr₀] using hc
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hclosure hy
    exact (hsub hx).2
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hclosure hy
    exact e.map_source (hsource hx)
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hclosure hy.1
    have hle : r (e.symm y) ≤ c := by
      rw [← hxy, e.left_inv (hsource hx)]
      exact hx
    apply le_antisymm hle
    by_contra hge
    have hlt : r (e.symm y) < c := lt_of_not_ge hge
    have hyV : y ∈ V := ⟨e.symm y, hlt,
      e.right_inv (hxy ▸ e.map_source (hsource hx))⟩
    exact hy.2 (by simpa only [hV.interior_eq] using hyV)

theorem exists_inner_bilinear_radius_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (e : OpenPartialHomeomorph E Y) (h₀ : (0 : E) ∈ e.source)
    (W : Set Y) (hW : IsOpen W) (hW₀ : e 0 ∈ W) :
    ∃ c : ℝ, 0 < c ∧ ∃ V : Set Y, IsOpen V ∧ e 0 ∈ V ∧
      closure V ⊆ W ∧ closure V ⊆ e.target ∧
      (∀ y ∈ frontier V, Real.sqrt (B (e.symm y) (e.symm y)) = c) ∧
      (∀ y ∈ V, Real.sqrt (B (e.symm y) (e.symm y)) < c) := by
  exact exists_inner_radius_neighborhood e 0 h₀ (fun v => Real.sqrt (B v v))
    (B.continuous.clm_apply continuous_id).sqrt (by simp)
    (fun v hv => Real.sqrt_pos.mpr (hpos v hv))
    (isCompact_bilinear_radius_sublevel B hpos 1) W hW hW₀

theorem ofReal_radius_le_riemannianEDist_of_first_exit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    (W V : Set M) (hV : IsOpen V) (hVW : closure V ⊆ W)
    (ρ : M → ℝ) (p q : M) (c : ℝ)
    (hp : p ∈ V) (hρp : ρ p = 0) (hρq : 0 ≤ ρ q) (hqc : ρ q ≤ c)
    (hfront : ∀ x ∈ frontier V, ρ x = c)
    (hbound : ∀ (γ : ℝ → M) (a b : ℝ), a ≤ b →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b) →
      Set.MapsTo γ (Set.Icc a b) W →
      enorm (ρ (γ b) - ρ (γ a)) ≤ Manifold.pathELength I γ a b) :
    ENNReal.ofReal (ρ q) ≤ Manifold.riemannianEDist I p q := by
  by_contra h
  obtain ⟨γ,hγ0,hγ1,hγ,hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (lt_of_not_ge h)
  have hpath : ENNReal.ofReal (ρ q) ≤ Manifold.pathELength I γ 0 1 := by
    by_cases hstay : Set.MapsTo γ (Set.Icc (0:ℝ) 1) V
    · have hb := hbound γ 0 1 zero_le_one hγ
        (fun t ht => hVW (subset_closure (hstay ht)))
      simpa only [hγ0,hγ1,hρp,sub_zero,Real.enorm_eq_ofReal hρq] using hb
    · obtain ⟨t,ht,htV⟩ : ∃ t ∈ Set.Icc (0:ℝ) 1, γ t ∉ V := by
        simpa only [Set.MapsTo,not_forall,exists_prop] using hstay
      obtain ⟨s,hs,hsV,hpre⟩ := exists_first_exit_of_continuousOn V hV γ 0 t ht.1
        (hγ.continuousOn.mono (Set.Icc_subset_Icc le_rfl ht.2))
        (hγ0.symm ▸ hp) htV
      have hs1 : s ≤ 1 := hs.2.trans ht.2
      have hmap : Set.MapsTo γ (Set.Icc 0 s) W := by
        intro u hu
        apply hVW
        rcases hu.2.eq_or_lt with hus | hus
        · simpa only [hus] using frontier_subset_closure hsV
        · exact subset_closure (hpre ⟨hu.1,hus⟩)
      have hb := hbound γ 0 s hs.1.le
        (hγ.mono (Set.Icc_subset_Icc le_rfl hs1)) hmap
      have hc : 0 ≤ c := hρq.trans hqc
      have hb' : ENNReal.ofReal c ≤ Manifold.pathELength I γ 0 s := by
        simpa only [hfront _ hsV,hγ0,hρp,sub_zero,Real.enorm_eq_ofReal hc] using hb
      exact (ENNReal.ofReal_le_ofReal hqc).trans
        (hb'.trans (Manifold.pathELength_mono le_rfl hs1))
  exact (not_lt_of_ge hpath) hlen

end Submission.Helpers
