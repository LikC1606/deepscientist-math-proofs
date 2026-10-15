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
