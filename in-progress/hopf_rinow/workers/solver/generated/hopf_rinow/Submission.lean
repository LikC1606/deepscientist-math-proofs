import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry
open scoped Manifold ENNReal ContDiff
open Bundle

namespace Submission

theorem Helpers.metric_segment_endpoint_of_isGeodesicallyComplete
    {M : Type*} [MetricSpace M] (hgc : IsGeodesicallyComplete M)
    (b : ℝ) (γ : ℝ → M) (hb : 0 < b)
    (hdist : ∀ s ∈ Set.Ioo 0 b, ∀ t ∈ Set.Ioo 0 b, dist (γ s) (γ t) = |t-s|) :
    ∃ p, Filter.Tendsto γ (nhdsWithin b (Set.Ioo 0 b)) (nhds p) := by
  obtain ⟨η,⟨c,hη⟩,heq⟩ := hgc 0 b γ hb (by
    refine ⟨1,?_⟩
    intro t₀ ht₀
    refine ⟨1,zero_lt_one,?_⟩
    intro s t hs ht
    have hs' : s ∈ Set.Ioo 0 b := ⟨lt_of_le_of_lt (le_max_left _ _) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have ht' : t ∈ Set.Ioo 0 b := ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    simpa only [ENNReal.coe_one,one_mul,edist_dist] using
      congrArg ENNReal.ofReal (hdist s hs' t ht'))
  refine ⟨η b,Metric.tendsto_nhdsWithin_nhds.2 ?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hηδ⟩ := hη b
  refine ⟨min δ (ε/((c:ℝ)+1)),lt_min hδ (div_pos hε (by positivity)),?_⟩
  intro t ht htd
  have htδ : |t-b| < δ := by
    exact lt_of_lt_of_le (by simpa only [Real.dist_eq] using htd) (min_le_left _ _)
  have htd' : |b-t| < ε/((c:ℝ)+1) := by
    exact lt_of_lt_of_le (by simpa only [Real.dist_eq,abs_sub_comm] using htd) (min_le_right _ _)
  have he := hηδ t b htδ (by simpa using hδ)
  have hde : dist (η t) (η b) = (c:ℝ)*|b-t| := by
    simpa [dist_edist,ENNReal.toReal_mul] using congrArg ENNReal.toReal he
  rw [heq t ht] at hde
  rw [hde]
  have hmul := (lt_div_iff₀ (by positivity : 0 < (c:ℝ)+1)).1 htd'
  nlinarith [abs_nonneg (b-t)]

theorem Helpers.completeSpace_of_isGeodesicallyComplete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M]
    [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (↑(⊤ : ℕ∞) : WithTop ℕ∞) E
      (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [LocallyCompactSpace M] [ConnectedSpace M] :
    IsGeodesicallyComplete M → CompleteSpace M := by
  intro hgc
  letI : MetricSpace M := EMetricSpace.toMetricSpace (Helpers.edist_ne_top_of_preconnected)
  apply Helpers.completeSpace_of_metric_segment_limits
  · exact (open scoped Bundle in by
      intro x y r ε hr hrd hε
      exact Helpers.riemannian_approximate_radial_split I
        (fun x y => IsRiemannianManifold.out (I := I) x y) x y r ε hr hrd hε)
  · exact Helpers.metric_segment_endpoint_of_isGeodesicallyComplete hgc

theorem Helpers.isGeodesicallyComplete_of_endpointGerm : open Bundle in
    ∀ (M : Type*) [EMetricSpace M] [CompleteSpace M],
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
    LeanEval.Geometry.IsGeodesicallyComplete M := by
  intro M _ _
  dsimp only
  intro hG a b γ hab hγ
  obtain ⟨c, hc⟩ := hγ
  have hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo a b) := by
    intro t₀ ht₀
    obtain ⟨δ, hδ, H⟩ := hc t₀ ht₀
    refine ⟨δ, hδ, fun s t hs ht => H s t ?_ ?_⟩
    · exact ⟨max_lt hs.1.1 hs.2.1, lt_min hs.1.2 hs.2.2⟩
    · exact ⟨max_lt ht.1.1 ht.2.1, lt_min ht.1.2 ht.2.2⟩
  obtain ⟨η, hη, heq⟩ :=
    Helpers.exists_global_locallyLinear_extension_of_endpointGerm M hG a b γ c hab hlin
  refine ⟨η, ⟨c, ?_⟩, heq⟩
  intro t₀
  obtain ⟨δ, hδ, H⟩ := hη t₀ (Set.mem_univ _)
  refine ⟨δ, hδ, fun s t hs ht => H s t ⟨Set.mem_univ _, ?_⟩
    ⟨Set.mem_univ _, ?_⟩⟩
  · obtain ⟨hs₁, hs₂⟩ := abs_lt.mp hs
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨ht₁, ht₂⟩ := abs_lt.mp ht
    exact ⟨by linarith, by linarith⟩

theorem Helpers.exists_smooth_inverse_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {r : ℝ} (hr : 0 < r)
    (he0 : (0:E) ∈ e.source) (he : ContDiffOn ℝ 1 e (Metric.ball 0 r))
    (hei : ContDiffAt ℝ 1 e.symm (e 0)) :
    ∃ W : Set E, IsOpen W ∧ e 0 ∈ W ∧ W ⊆ e.target ∧
      Set.MapsTo e.symm W (Metric.ball 0 r) ∧ ContDiffOn ℝ 1 e.symm W ∧
      ∀ y ∈ W, ∀ w : E,
        fderiv ℝ e (e.symm y) (fderiv ℝ e.symm y w) = w := by
  have hsymm0 : e.symm (e 0) = 0 := e.left_inv he0
  obtain ⟨T,hT,hTi⟩ := hei.contDiffOn le_rfl (by norm_num)
  have hball : e.symm ⁻¹' Metric.ball 0 r ∈ nhds (e 0) := by
    apply hei.continuousAt.tendsto.eventually
    rw [hsymm0]
    exact Metric.ball_mem_nhds 0 hr
  obtain ⟨W,hsub,hW,h0W⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hT (Filter.inter_mem
      (e.open_target.mem_nhds (e.map_source he0)) hball))
  have hWtarget : W ⊆ e.target := fun y hy => (hsub hy).2.1
  have hWball : Set.MapsTo e.symm W (Metric.ball 0 r) := fun y hy => (hsub hy).2.2
  have hi : ContDiffOn ℝ 1 e.symm W := hTi.mono (fun y hy => (hsub hy).1)
  refine ⟨W,hW,h0W,hWtarget,hWball,hi,?_⟩
  intro y hy w
  have hEi : DifferentiableAt ℝ e.symm y :=
    (hi.contDiffAt (hW.mem_nhds hy)).differentiableAt one_ne_zero
  have hE : DifferentiableAt ℝ e (e.symm y) :=
    (he.contDiffAt (Metric.isOpen_ball.mem_nhds (hWball hy))).differentiableAt one_ne_zero
  have hcomp := HasFDerivAt.comp (g := (e : E → E)) (f := (e.symm : E → E))
    y hE.hasFDerivAt hEi.hasFDerivAt
  have hEq : (fun y : E => e (e.symm y)) =ᶠ[nhds y] id := by
    filter_upwards [e.open_target.mem_nhds (hWtarget hy)] with z hz
    exact e.right_inv hz
  have hd := (hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.symm hEq)).unique
    (hasFDerivAt_id y)
  simpa using congrArg (fun L : E →L[ℝ] E => L w) hd

theorem Helpers.exists_coordinate_radial_length_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : ContDiffOn ℝ 1 g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < g x v v)
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} (hp : p ∈ U) :
    ∃ τ > (0:ℝ), ∃ e : OpenPartialHomeomorph E E, ∃ W : Set E,
      IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ W ⊆ e.target ∧ e 0 = p ∧
      ContDiffOn ℝ 1 e.symm W ∧
      ∀ δ > (0:ℝ),
        ContDiffOn ℝ 1 (fun y =>
          Real.sqrt (((τ^2:ℝ) • g p) (e.symm y) (e.symm y) + δ)) W ∧
        ∀ y ∈ W, ∀ w : E,
          |fderiv ℝ (fun y =>
            Real.sqrt (((τ^2:ℝ) • g p) (e.symm y) (e.symm y) + δ)) y w| ≤
            Real.sqrt (g y w w) := by
  obtain ⟨τ,hτ,r,hr,e,he0,hep,he0p,he,hei,hGauss⟩ :=
    Helpers.exists_coordinate_normal_chart hU hg hsym hΓ hKoszul hp
  obtain ⟨W,hW,hpW,hWt,hWb,hi,hDinv⟩ :=
    Helpers.exists_smooth_inverse_domain e hr he0 (he.of_le (by simp))
      (by rw [he0p]; exact hei.of_le (by simp))
  have hW0 : p ∈ W := by simpa only [he0p] using hpW
  have hWU : W ⊆ U := by
    intro y hy
    have h := (hGauss (e.symm y) (hWb hy)).1
    simpa only [e.right_inv (hWt hy)] using h
  let B₀ : E →L[ℝ] E →L[ℝ] ℝ := (τ^2:ℝ) • g p
  have hsym₀ : ∀ u v : E, B₀ u v = B₀ v u := by
    intro u v
    simp only [B₀,smul_apply,smul_eq_mul,hsym p u v]
  have hnonneg (x : E) (hx : x ∈ U) (v : E) : 0 ≤ g x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos x hx v hv).le
  have hBnonneg (v : E) : 0 ≤ B₀ v v := by
    exact mul_nonneg (sq_nonneg τ) (hnonneg p hp v)
  refine ⟨τ,hτ,e,W,hW,hW0,hWU,hWt,he0p,hi,?_⟩
  intro δ hδ
  have hq : ContDiffOn ℝ 1 (fun y => B₀ (e.symm y) (e.symm y)) W :=
    ((contDiffOn_const.clm_apply hi).clm_apply hi)
  refine ⟨(hq.add contDiffOn_const).sqrt
    (fun y hy => ne_of_gt (add_pos_of_nonneg_of_pos (hBnonneg _) hδ)),?_⟩
  intro y hy w
  have hG : ∀ z : E,
      g y (fderiv ℝ e (e.symm y) (e.symm y)) (fderiv ℝ e (e.symm y) z) =
        B₀ (e.symm y) z := by
    intro z
    simpa only [e.right_inv (hWt hy), B₀, smul_apply, smul_eq_mul] using
      (hGauss (e.symm y) (hWb hy)).2 z
  exact (Helpers.radial_gauss_regularized_radius_fderiv_bound (g y) B₀
    (hsym y) (hnonneg y (hWU hy)) hsym₀
    (fderiv ℝ e (e.symm y)) (fderiv ℝ e.symm y)
    ((hi.contDiffAt (hW.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
    (hDinv y hy) hG δ hδ).2 w

theorem Helpers.enorm_sqrt_sub_le_pathELength_of_chart_regularized_bound : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
      (hg : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
      (W : Set E) (hW : IsOpen W) (q : E → ℝ)
      (hsmooth : ∀ δ > (0 : ℝ),
        ContDiffOn ℝ 1 (fun z => Real.sqrt (q z + δ)) W)
      (hbound : ∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w : E,
        |fderiv ℝ (fun y => Real.sqrt (q y + δ)) z w| ≤ Real.sqrt (g z w w))
      (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
      (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
      (hγW : Set.MapsTo γ (Set.Icc a b)
        ((extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W)),
      enorm (Real.sqrt (q (extChartAt I p (γ b))) -
        Real.sqrt (q (extChartAt I p (γ a)))) ≤ Manifold.pathELength I γ a b := by
  intro E _ _ H _ I M _ _ _ _ p g hg W hW q hsmooth hbound γ a b hab hγ hγW
  exact (open scoped Bundle in by
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    have hlim (x : M) : Filter.Tendsto
        (fun δ : ℝ => Real.sqrt (q (extChartAt I p x) + δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt (q (extChartAt I p x)))) := by
      have hc : Continuous (fun δ : ℝ => Real.sqrt (q (extChartAt I p x) + δ)) := by
        fun_prop
      simpa only [add_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto (continuous_enorm.continuousAt.tendsto.comp
      ((hlim (γ b)).sub (hlim (γ a))))
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply Helpers.enorm_sub_le_pathELength_of_coordinate_bound I
      ((extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W)
      (isOpen_extChartAt_preimage' p hW) W hW (extChartAt I p)
      (contMDiffOn_extChartAt.mono (fun _ hx => by
        simpa only [extChartAt_source] using hx.1)) (fun _ hx => hx.2)
      (fun z => Real.sqrt (q z + δ)) (hsmooth δ hδ) ?_ γ a b hab hγ hγW
    intro x hx v
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (hbound δ hδ _ hx.2 _).trans_eq
      (Helpers.sqrt_coordinate_metric_chart_derivative_eq_norm p g hg x hx.1 v))

theorem Helpers.exists_normal_radius_lower_bound : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
      {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
      (hg : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
      (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
      (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
      (hep : e 0 = extChartAt I p p) (W : Set E) (hW : IsOpen W)
      (hpW : extChartAt I p p ∈ W)
      (hsmooth : ∀ δ > (0 : ℝ), ContDiffOn ℝ 1
        (fun z => Real.sqrt (B (e.symm z) (e.symm z) + δ)) W)
      (hbound : ∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w : E,
        |fderiv ℝ (fun y => Real.sqrt (B (e.symm y) (e.symm y) + δ)) z w| ≤
          Real.sqrt (g z w w)),
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
        V ⊆ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W ∧
        V ⊆ (extChartAt I p) ⁻¹' e.target ∧
        ∀ q ∈ V, ENNReal.ofReal
          (Real.sqrt (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) ≤
            Manifold.riemannianEDist I p q := by
  intro E _ _ _ H _ I _ M _ _ _ _ _ p g hg B hpos e he0 hep W hW hpW hsmooth hbound
  let c : OpenPartialHomeomorph M E := {
    toPartialEquiv := extChartAt I p
    open_source := isOpen_extChartAt_source p
    open_target := isOpen_extChartAt_target p
    continuousOn_toFun := continuousOn_extChartAt p
    continuousOn_invFun := continuousOn_extChartAt_symm p }
  let f : OpenPartialHomeomorph E M := e.trans c.symm
  have hf0 : (0 : E) ∈ f.source :=
    ⟨he0, by change e 0 ∈ (extChartAt I p).target; rw [hep]; exact mem_extChartAt_target p⟩
  have hfp : f 0 = p := by
    change (extChartAt I p).symm (e 0) = p
    rw [hep]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  let A := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W
  have hA : IsOpen A := isOpen_extChartAt_preimage' p hW
  obtain ⟨k,hk,V,hV,hV0,hVA,hVf,hfront,hinside⟩ :=
    Helpers.exists_inner_bilinear_radius_neighborhood B hpos f hf0 A hA
      (by rw [hfp]; exact ⟨mem_extChartAt_source p,hpW⟩)
  have hpV : p ∈ V := hfp ▸ hV0
  have hsub (q : M) (hq : q ∈ V) : q ∈ f.target := hVf (subset_closure hq)
  refine ⟨V,hV,hpV,(fun q hq => hVA (subset_closure hq)),
    (fun q hq => (hsub q hq).2),?_⟩
  intro q hq
  letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun x : M => TangentSpace I x) x
  apply Helpers.ofReal_radius_le_riemannianEDist_of_first_exit I A V hV hVA
    (fun y => Real.sqrt (B (f.symm y) (f.symm y))) p q k hpV
  · have hzero : f.symm p = 0 := by rw [← hfp]; exact f.left_inv hf0
    simp only [hzero,map_zero,ContinuousLinearMap.zero_apply,Real.sqrt_zero]
  · exact Real.sqrt_nonneg _
  · exact (hinside q hq).le
  · exact hfront
  · intro γ a b hab hγ hγA
    exact Helpers.enorm_sqrt_sub_le_pathELength_of_chart_regularized_bound I p g hg W hW
      (fun z => B (e.symm z) (e.symm z)) hsmooth hbound γ a b hab hγ hγA

theorem hopf_rinow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [LocallyCompactSpace M] [ConnectedSpace M] :
    IsGeodesicallyComplete M ↔ CompleteSpace M := by
  sorry

end Submission
