import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Order.Zorn
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
namespace Submission.Helpers

theorem norm_mfderivWithin_inverse_chart_curve : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2) →
      ∀ (x : ℝ → E) (S : Set ℝ) (t : ℝ) (v : E),
      Set.MapsTo x S (extChartAt I p).target → t ∈ S → UniqueDiffWithinAt ℝ S t →
      HasDerivWithinAt x v S t →
      ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I
        ((extChartAt I p).symm ∘ x) S t 1‖ = Real.sqrt (g (x t) v v) := by
  intro E _ _ H _ I M _ _ _ _ p g hg x S t v hx ht hS hderiv
  have hcomp : mfderivWithin (modelWithCornersSelf ℝ ℝ) I
      ((extChartAt I p).symm ∘ x) S t =
      (mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) (x t)).comp
      (mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E) x S t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hx ht)
    · exact hderiv.differentiableWithinAt.mdifferentiableWithinAt
    · exact fun s hs => extChartAt_target_subset_range p (hx hs)
    · rwa [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
  have hxv : mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
      x S t 1 = v := by
    rw [mfderivWithin_eq_fderivWithin]
    change fderivWithin ℝ x S t 1 = v
    rw [hderiv.hasFDerivWithinAt.fderivWithin hS]
    simp
  rw [hcomp, ContinuousLinearMap.comp_apply, hxv, hg (x t) (hx ht) v]
  exact (open scoped Bundle in
    (Real.sqrt_sq (norm_nonneg (mfderivWithin (modelWithCornersSelf ℝ E) I
      (extChartAt I p).symm (Set.range I) (x t) v))).symm)

theorem pathELength_inverse_chart_eq_of_constant_energy : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2) →
      ∀ (x v : ℝ → E) (a b k : ℝ), a ≤ b → 0 ≤ k →
      Set.MapsTo x (Set.Icc a b) (extChartAt I p).target →
      (∀ t ∈ Set.Icc a b, HasDerivWithinAt x (v t) (Set.Icc a b) t) →
      (∀ t ∈ Set.Icc a b, g (x t) (v t) (v t) = k ^ 2) →
      Manifold.pathELength I ((extChartAt I p).symm ∘ x) a b =
        ENNReal.ofReal ((b - a) * k) := by
  intro E _ _ H _ I M _ _ _ _ p g hg x v a b k hab hk hx hderiv henergy
  letI (z : M) : NormedAddCommGroup (TangentSpace I z) :=
    (open scoped Bundle in inferInstance)
  exact (open scoped Bundle in by
    rcases eq_or_lt_of_le hab with rfl | hab'
    · simp
    have hspeed (t : ℝ) (ht : t ∈ Set.Icc a b) :
        ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I
          ((extChartAt I p).symm ∘ x) (Set.Icc a b) t 1‖ = k := by
      rw [norm_mfderivWithin_inverse_chart_curve I p g hg x (Set.Icc a b) t (v t)
        hx ht (uniqueDiffOn_Icc hab' t ht) (hderiv t ht), henergy t ht,
        Real.sqrt_sq hk]
    rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      (∫⁻ t in Set.Icc a b, ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I
          ((extChartAt I p).symm ∘ x) (Set.Icc a b) t 1‖ₑ) =
          ∫⁻ _t in Set.Icc a b, ENNReal.ofReal k := by
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
        intro t ht
        exact (ofReal_norm (mfderivWithin (modelWithCornersSelf ℝ ℝ) I
          ((extChartAt I p).symm ∘ x) (Set.Icc a b) t 1)).symm.trans
          (congrArg ENNReal.ofReal (hspeed t ht))
      _ = ENNReal.ofReal ((b - a) * k) := by
        simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, ← ENNReal.ofReal_mul hk, mul_comm k])

theorem riemannianEDist_inverse_chart_le_of_constant_energy : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2) →
      ∀ (x v : ℝ → E) (a b k : ℝ), a ≤ b → 0 ≤ k →
      Set.MapsTo x (Set.Icc a b) (extChartAt I p).target →
      ContDiffOn ℝ 1 x (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, HasDerivWithinAt x (v t) (Set.Icc a b) t) →
      (∀ t ∈ Set.Icc a b, g (x t) (v t) (v t) = k ^ 2) →
      Manifold.riemannianEDist I ((extChartAt I p).symm (x a))
        ((extChartAt I p).symm (x b)) ≤ ENNReal.ofReal ((b - a) * k) := by
  intro E _ _ H _ I M _ _ _ _ p g hg x v a b k hab hk hx hCx hderiv henergy
  letI (z : M) : NormedAddCommGroup (TangentSpace I z) :=
    (open scoped Bundle in inferInstance)
  have hpath : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      ((extChartAt I p).symm ∘ x) (Set.Icc a b) :=
    (contMDiffOn_extChartAt_symm p).comp (contMDiffOn_iff_contDiffOn.mpr hCx) hx
  letI (z : M) : InnerProductSpace ℝ (TangentSpace I z) :=
    (open scoped Bundle in inferInstance)
  exact (Manifold.riemannianEDist_le_pathELength hpath rfl rfl hab).trans_eq
    (pathELength_inverse_chart_eq_of_constant_energy I p g hg x v a b k hab hk hx
      hderiv henergy)

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
end Submission.Helpers
