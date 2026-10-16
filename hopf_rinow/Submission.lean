import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry
open scoped Manifold ENNReal ContDiff
open Bundle

namespace Submission

theorem Helpers.hasDerivWithinAt_update_of_ode_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {X : ℝ → E} {p : E} {a b : ℝ}
    (hab : a < b) (hF : ContinuousAt F p)
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (F (X t)) t)
    (hlim : Filter.Tendsto X (nhdsWithin b (Set.Ioo a b)) (nhds p)) :
    HasDerivWithinAt (Function.update X b p) (F p) (Set.Iic b) b := by
  classical
  let Y : ℝ → E := Function.update X b p
  have heq (t : ℝ) (ht : t < b) : Y =ᶠ[nhds t] X := by
    filter_upwards [isOpen_ne.mem_nhds ht.ne] with s hs
    exact Function.update_of_ne hs _ _
  have hd (t : ℝ) (ht : t ∈ Set.Ioo a b) : HasDerivAt Y (F (X t)) t :=
    (hX t ht).congr_of_eventuallyEq (heq t ht.2)
  have hc : ContinuousWithinAt Y (Set.Ioo a b) b := by
    apply continuousWithinAt_update_same.mpr
    simpa only [Set.sdiff_singleton_eq_self (show b ∉ Set.Ioo a b by simp)] using hlim
  have hlim' : Filter.Tendsto X (nhdsWithin b (Set.Iio b)) (nhds p) := by
    rwa [nhdsWithin_Ioo_eq_nhdsLT hab] at hlim
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) hc
    (Ioo_mem_nhdsLT hab)
  apply (hF.tendsto.comp hlim').congr'
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact (hd t ht).deriv.symm
theorem Helpers.exists_ode_continuation_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {F : E → E}
    (hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F U)
    {X : ℝ → E} {p : E} {a b : ℝ} (hab : a < b) (hp : p ∈ U)
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (F (X t)) t)
    (hlim : Filter.Tendsto X (nhdsWithin b (Set.Ioo a b)) (nhds p)) :
    ∃ δ > (0 : ℝ), ∃ Y : ℝ → E,
      Y b = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Y (Set.Ioo (b - δ) (b + δ)) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), Y t ∈ U ∧ HasDerivAt Y (F (Y t)) t) ∧
      ∀ t ∈ Set.Ioo (b - δ) b, Y t = X t := by
  classical
  have hFat := hF.contDiffAt (hU.mem_nhds hp)
  obtain ⟨K, W, hW, hLip⟩ := (hFat.of_le (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)).exists_lipschitzOnWith
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hU.mem_nhds hp))
  have hRU : Metric.ball p R ⊆ U := fun z hz => (hRsub hz).2
  have hLK : LipschitzOnWith K F (Metric.ball p R) :=
    hLip.mono (fun z hz => (hRsub hz).1)
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hΦ0, hΦode⟩ :=
    Helpers.exists_smooth_local_ode_flow (Metric.ball p R) Metric.isOpen_ball F
      (hF.mono hRU) p (Metric.mem_ball_self hR)
  let Y : ℝ → E := fun t => Φ (t - b, p)
  have hYb : Y b = p := by
    simpa only [Y, sub_self] using hΦ0 p (Metric.mem_ball_self hr)
  have hYode (t : ℝ) (ht : t ∈ Set.Ioo (b - ε) (b + ε)) :
      Y t ∈ Metric.ball p R ∧ HasDerivAt Y (F (Y t)) t := by
    have ht' : t - b ∈ Set.Ioo (-ε) ε := by constructor <;> linarith [ht.1, ht.2]
    have h := hΦode (t - b, p) ⟨ht', Metric.mem_ball_self hr⟩
    refine ⟨h.1, ?_⟩
    simpa only [Y, Function.comp_def, id_eq, one_smul] using
      h.2.scomp t ((hasDerivAt_id t).sub_const b)
  have hnear : ∀ᶠ t in nhdsWithin b (Set.Iio b), X t ∈ Metric.ball p R := by
    have h := hlim.eventually (Metric.ball_mem_nhds p hR)
    rwa [nhdsWithin_Ioo_eq_nhdsLT hab] at h
  obtain ⟨d, hdb, hd⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hnear
  let δ : ℝ := min ε (b - max a d) / 2
  have hgap : 0 < b - max a d := sub_pos.mpr (max_lt hab hdb)
  have hδ : 0 < δ := half_pos (lt_min hε hgap)
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (b - max a d)]
  have hδgap : δ < b - max a d := by
    dsimp [δ]
    linarith [min_le_right ε (b - max a d)]
  have haδ : a < b - δ := by linarith [le_max_left a d]
  have hdδ : d < b - δ := by linarith [le_max_right a d]
  have hsub (t : ℝ) (ht : t ∈ Set.Icc (b - δ) b) (htb : t ≠ b) :
      t ∈ Set.Ioo a b := ⟨haδ.trans_le ht.1, lt_of_le_of_ne ht.2 htb⟩
  let Z : ℝ → E := Function.update X b p
  have hZb : Z b = p := by simp [Z]
  have hZd (t : ℝ) (ht : t ∈ Set.Ioo a b) : HasDerivAt Z (F (Z t)) t := by
    have heq : Z =ᶠ[nhds t] X := by
      filter_upwards [isOpen_ne.mem_nhds ht.2.ne] with s hs
      exact Function.update_of_ne hs _ _
    have hz : Z t = X t := Function.update_of_ne ht.2.ne _ _
    rw [hz]
    exact (hX t ht).congr_of_eventuallyEq heq
  have hZdb : HasDerivWithinAt Z (F p) (Set.Iic b) b :=
    Helpers.hasDerivWithinAt_update_of_ode_limit hab hFat.continuousAt hX hlim
  have hZcont : ContinuousOn Z (Set.Icc (b - δ) b) := by
    intro t ht
    by_cases htb : t = b
    · subst t
      exact hZdb.continuousWithinAt.mono (fun _ hz => hz.2)
    · exact (hZd t (hsub t ht htb)).continuousAt.continuousWithinAt
  have hZmem (t : ℝ) (ht : t ∈ Set.Icc (b - δ) b) : Z t ∈ Metric.ball p R := by
    by_cases htb : t = b
    · simpa only [htb, hZb] using Metric.mem_ball_self hR
    · rw [show Z t = X t from Function.update_of_ne htb _ _]
      exact hd ⟨hdδ.trans_le ht.1, lt_of_le_of_ne ht.2 htb⟩
  have hYtime (t : ℝ) (ht : t ∈ Set.Icc (b - δ) b) :
      t ∈ Set.Ioo (b - ε) (b + ε) := by constructor <;> linarith [ht.1, ht.2]
  have hEq : Set.EqOn Z Y (Set.Icc (b - δ) b) := by
    apply ODE_solution_unique_of_mem_Icc_left (v := fun _ => F)
      (s := fun _ => Metric.ball p R) (fun _ _ => hLK)
      hZcont ?_ (fun t ht => hZmem t ⟨ht.1.le, ht.2⟩)
      (fun t ht => (hYode t (hYtime t ht)).2.continuousAt.continuousWithinAt)
      (fun t ht => (hYode t (hYtime t ⟨ht.1.le, ht.2⟩)).2.hasDerivWithinAt)
      (fun t ht => (hYode t (hYtime t ⟨ht.1.le, ht.2⟩)).1)
      (hZb.trans hYb.symm)
    intro t ht
    by_cases htb : t = b
    · subst t
      simpa only [hZb] using hZdb
    · exact (hZd t (hsub t ⟨ht.1.le, ht.2⟩ htb)).hasDerivWithinAt
  refine ⟨δ, hδ, Y, hYb, ?_, ?_, ?_⟩
  · apply hΦ.comp (contDiffOn_id.sub contDiffOn_const |>.prodMk contDiffOn_const)
    intro t ht
    change (t - b, p) ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball p r
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, Metric.mem_ball_self hr⟩
  · intro t ht
    have h := hYode t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨hRU h.1, h.2⟩
  · intro t ht
    exact (hEq ⟨ht.1.le, ht.2.le⟩).symm.trans (Function.update_of_ne ht.2.ne _ _)
theorem Helpers.exists_spray_continuation_of_phase_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {x v : ℝ → E} {p w : E} {a b : ℝ} (hab : a < b) (hp : p ∈ U)
    (hphase : ∀ t ∈ Set.Ioo a b,
      HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hx : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p))
    (hv : Filter.Tendsto v (nhdsWithin b (Set.Ioo a b)) (nhds w)) :
    ∃ δ > (0 : ℝ), ∃ X V : ℝ → E,
      X b = p ∧ V b = w ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => (X t, V t)) (Set.Ioo (b - δ) (b + δ)) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), X t ∈ U ∧
        HasDerivAt X (V t) t ∧ HasDerivAt V (-(Γ (X t) (V t) (V t))) t) ∧
      ∀ t ∈ Set.Ioo (b - δ) b, X t = x t ∧ V t = v t := by
  let F : E × E → E × E := fun z => (z.2, -(Γ z.1 z.2 z.2))
  have hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F (U ×ˢ Set.univ) :=
    Helpers.contDiffOn_coordinate_spray hΓ
  have hd (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (fun s => (x s, v s)) (F (x t, v t)) t :=
    (hphase t ht).1.prodMk (hphase t ht).2
  obtain ⟨δ, hδ, Y, hYb, hYs, hYode, hYeq⟩ :=
    Helpers.exists_ode_continuation_of_tendsto (hU.prod isOpen_univ) hF hab
      ⟨hp, Set.mem_univ w⟩ hd (hx.prodMk_nhds hv)
  refine ⟨δ, hδ, (fun t => (Y t).1), (fun t => (Y t).2),
    congrArg Prod.fst hYb, congrArg Prod.snd hYb, ?_, ?_, ?_⟩
  · simpa only [Prod.eta] using hYs
  · intro t ht
    have h := hYode t ht
    exact ⟨h.1.1, h.2.fst, h.2.snd⟩
  · intro t ht
    exact ⟨congrArg Prod.fst (hYeq t ht), congrArg Prod.snd (hYeq t ht)⟩
theorem Helpers.exists_spray_continuation_of_bounded_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {x v : ℝ → E} {p : E} {a b : ℝ} (hab : a < b) (hp : p ∈ U)
    (hphase : ∀ t ∈ Set.Ioo a b,
      HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hx : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p))
    (hv : ∃ K : ℝ, ∀ t ∈ Set.Ioo a b, ‖v t‖ ≤ K) :
    ∃ δ > (0 : ℝ), ∃ X V : ℝ → E,
      X b = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => (X t, V t)) (Set.Ioo (b - δ) (b + δ)) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), X t ∈ U ∧
        HasDerivAt X (V t) t ∧ HasDerivAt V (-(Γ (X t) (V t) (V t))) t) ∧
      ∀ t ∈ Set.Ioo (b - δ) b, X t = x t ∧ V t = v t := by
  obtain ⟨w, hw⟩ := Helpers.exists_velocity_limit_of_bounded_spray_curve hab
    (hΓ.contDiffAt (hU.mem_nhds hp)).continuousAt hx hv (fun t ht => (hphase t ht).2)
  obtain ⟨δ, hδ, X, V, hXb, hVb, hC, hODE, heq⟩ :=
    Helpers.exists_spray_continuation_of_phase_limit hU hΓ hab hp hphase hx hw
  exact ⟨δ, hδ, X, V, hXb, hC, hODE, heq⟩
theorem Helpers.exists_spray_continuation_of_energy_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hg : ContinuousOn g U)
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {x v : ℝ → E} {p : E} {a b C : ℝ} (hab : a < b) (hp : p ∈ U)
    (hpos : ∀ w : E, w ≠ 0 → 0 < g p w w)
    (hphase : ∀ t ∈ Set.Ioo a b,
      HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hx : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p))
    (henergy : ∀ t ∈ Set.Ioo a b, g (x t) (v t) (v t) ≤ C ^ 2) :
    ∃ δ > (0 : ℝ), ∃ X V : ℝ → E,
      X b = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => (X t, V t)) (Set.Ioo (b - δ) (b + δ)) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), X t ∈ U ∧
        HasDerivAt X (V t) t ∧ HasDerivAt V (-(Γ (X t) (V t) (V t))) t) ∧
      ∀ t ∈ Set.Ioo (b - δ) b, X t = x t ∧ V t = v t := by
  obtain ⟨w, hw⟩ := Helpers.velocity_limit_of_positive_metric_spray hab
    (hg.continuousAt (hU.mem_nhds hp)) (hΓ.contDiffAt (hU.mem_nhds hp)).continuousAt
    hpos hx (fun t ht => (hphase t ht).2) henergy
  obtain ⟨δ, hδ, X, V, hXb, hVb, hC, hODE, heq⟩ :=
    Helpers.exists_spray_continuation_of_phase_limit hU hΓ hab hp hphase hx hw
  exact ⟨δ, hδ, X, V, hXb, hC, hODE, heq⟩
theorem Helpers.exists_energy_preserving_spray_continuation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hg : ContDiffOn ℝ 1 g U)
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    (hsym : ∀ z u w, g z u w = g z w u)
    (hKoszul : ∀ z ∈ U, ∀ u v w,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    {x v : ℝ → E} {p : E} {a b C : ℝ} (hab : a < b) (hp : p ∈ U)
    (hpos : ∀ w : E, w ≠ 0 → 0 < g p w w)
    (hphase : ∀ t ∈ Set.Ioo a b,
      HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hx : Filter.Tendsto x (nhdsWithin b (Set.Ioo a b)) (nhds p))
    (henergy : ∀ t ∈ Set.Ioo a b, g (x t) (v t) (v t) = C ^ 2) :
    ∃ δ > (0 : ℝ), ∃ X V : ℝ → E,
      X b = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => (X t, V t)) (Set.Ioo (b - δ) (b + δ)) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), X t ∈ U ∧
        HasDerivAt X (V t) t ∧ HasDerivAt V (-(Γ (X t) (V t) (V t))) t) ∧
      (∀ t ∈ Set.Ioo (b - δ) (b + δ), g (X t) (V t) (V t) = C ^ 2) ∧
      ∀ t ∈ Set.Ioo (b - δ) b, X t = x t ∧ V t = v t := by
  obtain ⟨δ, hδ, X, V, hXb, hC, hODE, heq⟩ :=
    Helpers.exists_spray_continuation_of_energy_bound hU hg.continuousOn hΓ hab hp
      hpos hphase hx (fun t ht => (henergy t ht).le)
  let θ : ℝ := min δ (b - a) / 2
  have hθ : 0 < θ := half_pos (lt_min hδ (sub_pos.mpr hab))
  have hθδ : θ < δ := by dsimp [θ]; linarith [min_le_left δ (b - a)]
  have hθab : θ < b - a := by dsimp [θ]; linarith [min_le_right δ (b - a)]
  have hleft : b - θ ∈ Set.Ioo (b - δ) b := ⟨by linarith, by linarith⟩
  have href : b - θ ∈ Set.Ioo (b - δ) (b + δ) :=
    ⟨hleft.1, by linarith⟩
  have hEref : g (X (b - θ)) (V (b - θ)) (V (b - θ)) = C ^ 2 := by
    rw [(heq _ hleft).1, (heq _ hleft).2]
    exact henergy _ ⟨by linarith, hleft.2⟩
  refine ⟨δ, hδ, X, V, hXb, hC, hODE, ?_, heq⟩
  intro t ht
  have hconst := Helpers.coordinate_geodesic_energy_eq
    (Γ := fun z u v => Γ z u v) (g := g) (x := X) (v := V) isOpen_Ioo
    (convex_Ioo (b - δ) (b + δ)).isPreconnected
    (fun s hs => (hg.contDiffAt (hU.mem_nhds (hODE s hs).1)).differentiableAt (by simp))
    hsym (fun s hs => hKoszul _ (hODE s hs).1)
    (fun s hs => (hODE s hs).2.1) (fun s hs => (hODE s hs).2.2) ht href
  exact hconst.trans hEref
theorem Helpers.exists_uniform_radius_control_of_joint_spray_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} (hg : ContDiffOn ℝ 1 g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} {r ε R τ : ℝ} {K : NNReal} (hr : 0 < r) (hε : 0 < ε)
    (hτ : τ ∈ Set.Ioo (-ε) ε)
    (hLip : LipschitzOnWith K (fun z : E × E => (z.2, -Γ z.1 z.2 z.2))
      (Metric.ball (p, 0) R))
    (hdom : ∀ z ∈ Metric.ball (p, (0 : E)) R, z.1 ∈ U)
    {Φ : ℝ × (E × E) → E × E}
    (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r))
    (hΦ0 : ∀ z ∈ Metric.ball (p, 0) r, Φ (0, z) = z)
    (hΦF : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
      Φ z ∈ Metric.ball (p, 0) R ∧
      HasDerivAt (fun t : ℝ => Φ (t, z.2))
        ((Φ z).2, -Γ (Φ z).1 (Φ z).2 (Φ z).2) z.1)
    (hΦp : Φ (τ, (p, 0)) = (p, 0))
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (he0 : (p, (0 : E)) ∈ e.source)
    (hef : ∀ z : E × E, e z = (z.1, (Φ (τ, z)).1))
    (hei : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e.symm (p, p)) :
    ∃ ρ > (0 : ℝ), Metric.ball p ρ ⊆ U ∧
      ContDiffOn ℝ 1 (fun z : E × E => (e.symm z).2)
        (Metric.ball p ρ ×ˢ Metric.ball p ρ) ∧
      (∀ q ∈ Metric.ball p ρ, (q, (0 : E)) ∈ e.source ∧ e (q, 0) = (q, q)) ∧
      ∀ q ∈ Metric.ball p ρ,
        (∀ z ∈ Metric.ball p ρ, (q, z) ∈ e.target ∧
          e.symm (q, z) ∈ Metric.ball (p, 0) (r / 2)) ∧
        (∀ d > (0 : ℝ), ContDiffOn ℝ 1
          (fun z => Real.sqrt ((τ ^ 2 • g q) (e.symm (q, z)).2
            (e.symm (q, z)).2 + d)) (Metric.ball p ρ)) ∧
        (∀ d > (0 : ℝ), ∀ z ∈ Metric.ball p ρ, ∀ w : E,
          |fderiv ℝ (fun y => Real.sqrt ((τ ^ 2 • g q) (e.symm (q, y)).2
            (e.symm (q, y)).2 + d)) z w| ≤ Real.sqrt (g z w w)) := by
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hep : e (p, 0) = (p, p) := by rw [hef, hΦp]
  have hpt : (p, p) ∈ e.target := hep ▸ e.map_source he0
  have hback : e.symm (p, p) = (p, 0) := by rw [← hep]; exact e.left_inv he0
  obtain ⟨A, hAp, hInvA⟩ := hei.contDiffOn (m := 1) (by simp) (by simp)
  have hN : A ∩ (e.target ∩ e.symm ⁻¹' Metric.ball (p, (0 : E)) (r / 2)) ∈
      nhds (p, p) :=
    Filter.inter_mem hAp ((e.isOpen_inter_preimage_symm Metric.isOpen_ball).mem_nhds
      ⟨hpt, by
        change e.symm (p, p) ∈ Metric.ball (p, 0) (r / 2)
        rw [hback]; exact Metric.mem_ball_self (half_pos hr)⟩)
  obtain ⟨b, hb, hbsub⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨a, ha, hasub⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  let ρ := min b (min a (r / 2))
  have hρ : 0 < ρ := lt_min hb (lt_min ha (half_pos hr))
  have hρb : ρ ≤ b := min_le_left _ _
  have hρa : ρ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ ≤ r / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hpairs {q z : E} (hq : q ∈ Metric.ball p ρ) (hz : z ∈ Metric.ball p ρ) :
      (q, z) ∈ Metric.ball (p, p) b := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro ((Metric.mem_ball.mp hq).trans_le hρb)
        ((Metric.mem_ball.mp hz).trans_le hρb)
  have hbase {q : E} (hq : q ∈ Metric.ball p ρ) : dist q p < r / 2 :=
    (Metric.mem_ball.mp hq).trans_le hρr
  have hinitial {q u : E} (hq : q ∈ Metric.ball p ρ) (hu : ‖u‖ < r / 2) :
      (q, u) ∈ Metric.ball (p, 0) r := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right]
    exact ⟨by linarith [hbase hq], by linarith⟩
  have hdiag {q : E} (hq : q ∈ Metric.ball p ρ) :
      (q, (0 : E)) ∈ e.source ∧ e (q, 0) = (q, q) := by
    have hq0 : (q, (0 : E)) ∈ Metric.ball (p, 0) r :=
      hinitial hq (by simpa using half_pos hr)
    have hqR : (q, (0 : E)) ∈ Metric.ball (p, 0) R := by
      simpa only [hΦ0 _ hq0] using (hΦF (0, (q, 0)) ⟨hzero, hq0⟩).1
    have hstationary := Helpers.eq_const_of_lipschitz_ode hLip hqR
      (show ((0 : E), -Γ q 0 0) = (0 : E × E) by simp) hzero
      (X := fun t => Φ (t, (q, 0)))
      (fun t ht => ⟨(hΦF (t, (q, 0)) ⟨ht, hq0⟩).2,
        (hΦF (t, (q, 0)) ⟨ht, hq0⟩).1⟩) (hΦ0 _ hq0)
    refine ⟨hasub ?_, ?_⟩
    · simpa [Metric.mem_ball, Prod.dist_eq, max_lt_iff, ha] using
        (Metric.mem_ball.mp hq).trans_le hρa
    · rw [hef, hstationary τ hτ]
  have hUρ : Metric.ball p ρ ⊆ U := by
    intro q hq
    have hq0 := hinitial hq (u := 0) (by simpa using half_pos hr)
    have hqR : (q, (0 : E)) ∈ Metric.ball (p, 0) R := by
      simpa only [hΦ0 _ hq0] using (hΦF (0, (q, 0)) ⟨hzero, hq0⟩).1
    exact hdom _ hqR
  refine ⟨ρ, hρ, hUρ, contDiff_snd.comp_contDiffOn
    (hInvA.mono (fun z hz => (hbsub (hpairs hz.1 hz.2)).1)),
    (fun q hq => hdiag hq), ?_⟩
  intro q hq
  let f : E → E := fun z => (e.symm (q, z)).2
  let F : E → E := fun u => (Φ (τ, (q, u))).1
  have hf : ContDiffOn ℝ 1 f (Metric.ball p ρ) :=
    contDiff_snd.comp_contDiffOn (hInvA.comp
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => (hbsub (hpairs hq hz)).1))
  have hFinv {z : E} (hz : z ∈ Metric.ball p ρ) : F (f z) = z := by
    have hh := e.right_inv (hbsub (hpairs hq hz)).2.1
    have hfirst : (e.symm (q, z)).1 = q := by
      simpa only [hef] using congrArg Prod.fst hh
    have hrep : (q, f z) = e.symm (q, z) := Prod.ext hfirst.symm rfl
    change (Φ (τ, (q, f z))).1 = z
    rw [hrep]
    simpa only [hef] using congrArg Prod.snd hh
  have hfnorm {z : E} (hz : z ∈ Metric.ball p ρ) : ‖f z‖ < r / 2 := by
    have hh := (hbsub (hpairs hq hz)).2.2
    simpa only [f, dist_zero_right] using
      (max_lt_iff.mp (Metric.mem_ball.mp hh)).2
  have hshift : Metric.ball (q, (0 : E)) (r / 2) ⊆ Metric.ball (p, 0) r := by
    intro z hz
    have hdist : dist (q, (0 : E)) (p, (0 : E)) < r / 2 := by
      simpa [Prod.dist_eq] using hbase hq
    exact Metric.mem_ball.mpr ((dist_triangle z (q, 0) (p, 0)).trans_lt
      (by linarith [Metric.mem_ball.mp hz]))
  have hΦq : ContDiffOn ℝ 2 Φ
      (Set.Ioo (-ε) ε ×ˢ Metric.ball (q, 0) (r / 2)) :=
    hΦ.mono (Set.prod_mono_right hshift)
  have hODEq : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (q, 0) (r / 2),
      (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2))
        ((Φ z).2, -Γ (Φ z).1 (Φ z).2 (Φ z).2) z.1 :=
    fun z hz => ⟨hdom _ (hΦF z ⟨hz.1, hshift hz.2⟩).1,
      (hΦF z ⟨hz.1, hshift hz.2⟩).2⟩
  have hF : ContDiffOn ℝ 2 F (Metric.ball 0 (r / 2)) :=
    contDiff_fst.comp_contDiffOn (hΦ.comp
      (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
      (fun u hu => ⟨hτ, hinitial hq (by simpa using hu)⟩))
  let B : E →L[ℝ] E →L[ℝ] ℝ := τ ^ 2 • g q
  have hBsym : ∀ u v, B u v = B v u := by
    intro u v
    change τ ^ 2 * g q u v = τ ^ 2 * g q v u
    rw [hsym]
  have hn : ∀ z ∈ U, ∀ u, 0 ≤ g z u u := by
    intro z hz u
    by_cases hu : u = 0
    · simp [hu]
    · exact (hpos z hz u hu).le
  refine ⟨(fun z hz => ⟨(hbsub (hpairs hq hz)).2.1,
    (hbsub (hpairs hq hz)).2.2⟩), ?_, ?_⟩
  · intro d hd
    exact ((((contDiffOn_const (c := B)).clm_apply hf).clm_apply hf).add
      contDiffOn_const).sqrt (fun z hz => ne_of_gt (by
        have hbnonneg : 0 ≤ B (f z) (f z) :=
          mul_nonneg (sq_nonneg τ) (hn q (hUρ hq) _)
        linarith))
  · intro d hd z hz w
    have hdf := (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt_one
    have hdz : f z ∈ Metric.ball 0 (r / 2) := by simpa using hfnorm hz
    have hdF := (hF.contDiffAt (Metric.isOpen_ball.mem_nhds hdz)).differentiableAt
      (by norm_num)
    have hcomp := hdF.hasFDerivAt.comp z hdf.hasFDerivAt
    have hEq : (fun y => F (f y)) =ᶠ[nhds z] id := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy using hFinv hy
    have hid := hcomp.congr_of_eventuallyEq hEq.symm
    have hcancel : ∀ u, fderiv ℝ F (f z) (fderiv ℝ f z u) = u := by
      intro u
      exact congrArg (fun L : E →L[ℝ] E => L u) (hid.unique (hasFDerivAt_id z))
    apply Helpers.regularized_radius_fderiv_bound_of_gauss (g z) B (hsym z)
      (hn z (hUρ hz)) hBsym hdf (fderiv ℝ F (f z)) ?_ hcancel hd w
    have hv : (q, f z) ∈ Metric.ball (q, 0) (r / 2) := by
      simpa [Metric.mem_ball, Prod.dist_eq] using hfnorm hz
    have hscale : ∀ κ ∈ Set.Icc (0 : ℝ) 1,
        (Φ (τ, (q, κ • f z))).1 = (Φ (κ * τ, (q, f z))).1 := by
      intro κ hκ
      apply congrArg Prod.fst
        (Helpers.coordinate_spray_flow_rescale_in_common_ball Γ (fun t u => Φ (t, u)) p q
          hε hLip (fun u hu => hΦ0 _ (hinitial hq hu))
          (fun u hu t ht => ⟨(hΦF (t, (q, u)) ⟨abs_lt.mp ht, hinitial hq hu⟩).2,
            (hΦF (t, (q, u)) ⟨abs_lt.mp ht, hinitial hq hu⟩).1⟩)
          κ τ (f z) (by simpa [abs_of_nonneg hκ.1] using hκ.2)
          (abs_lt.mpr hτ) (hfnorm hz))
    have hgauss := Helpers.coordinate_spray_endpoint_gauss hU hg hsym hKoszul hε hΦq
      (fun u hu => hΦ0 u (hshift hu)) hODEq hv hτ hscale
    simpa only [F, f, B, hFinv hz, smul_apply, smul_eq_mul] using hgauss
theorem Helpers.exists_pairwise_radius_lower_bound_of_local_path_control : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      [IsRiemannianManifold I M] [ConnectedSpace M]
      (p : M) (A : Set M) (hA : IsOpen A) (hpA : p ∈ A)
      (ρ : M × M → ℝ) (hρ : ContinuousAt ρ (p, p))
      (hρzero : ∀ q ∈ A, ρ (q, q) = 0)
      (hρnonneg : ∀ q z, 0 ≤ ρ (q, z))
      (hbound : ∀ q ∈ A, ∀ (γ : ℝ → M) (a b : ℝ), a ≤ b →
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b) →
        Set.MapsTo γ (Set.Icc a b) A →
        enorm (ρ (q, γ b) - ρ (q, γ a)) ≤ Manifold.pathELength I γ a b),
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ A ∧
        ∀ q ∈ V, ∀ z ∈ V, ENNReal.ofReal (ρ (q, z)) ≤ edist q z := by
  intro E _ _ H _ I M _ _ _ _ _ _ p A hA hpA ρ hρ hρzero hρnonneg hbound
  letI : MetricSpace M := EMetricSpace.toMetricSpace Helpers.edist_ne_top_of_preconnected
  letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun x : M => TangentSpace I x) x
  obtain ⟨R, hR, hRA⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds hpA)
  have hsmall : {z : M × M | ρ z < R / 2} ∈ nhds (p, p) :=
    hρ.preimage_mem_nhds (Iio_mem_nhds (by rw [hρzero p hpA]; exact half_pos hR))
  obtain ⟨η, hη, hηρ⟩ := Metric.mem_nhds_iff.mp hsmall
  let δ := min η (R / 4)
  have hδ : 0 < δ := lt_min hη (by positivity)
  have hnear {q : M} (hq : q ∈ Metric.ball p δ) : dist q p < R / 4 :=
    (Metric.mem_ball.mp hq).trans_le (min_le_right _ _)
  have hVA : Metric.ball p δ ⊆ A := fun q hq => hRA
    (Metric.mem_ball.mpr (by linarith [hnear hq]))
  refine ⟨Metric.ball p δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, hVA, ?_⟩
  intro q hq z hz
  have hρsmall : ρ (q, z) < R / 2 := by
    apply hηρ
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro ((Metric.mem_ball.mp hq).trans_le (min_le_left _ _))
        ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _))
  rw [IsRiemannianManifold.out (I := I)]
  by_contra h
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt (lt_of_not_ge h)
  by_cases hstay : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (Metric.ball p R)
  · have hb := hbound q (hVA hq) γ 0 1 zero_le_one hγ
      (fun t ht => hRA (hstay ht))
    have hb' : ENNReal.ofReal (ρ (q, z)) ≤ Manifold.pathELength I γ 0 1 := by
      simpa only [hγ0, hγ1, hρzero q (hVA hq), sub_zero,
        Real.enorm_eq_ofReal (hρnonneg q z)] using hb
    exact (not_lt_of_ge hb') hlen
  · obtain ⟨t, ht, htU⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball p R := by
      simpa only [Set.MapsTo, not_forall, exists_prop] using hstay
    have hRle : R ≤ dist (γ t) p := not_lt.mp (by simpa [Metric.mem_ball] using htU)
    have hpre : edist q (γ t) ≤ Manifold.pathELength I γ 0 1 := by
      rw [IsRiemannianManifold.out (I := I)]
      exact (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1).trans
          (Manifold.pathELength_mono le_rfl ht.2)
    have hfinite := (hlen.trans ENNReal.ofReal_lt_top).ne
    have hpre' := ENNReal.toReal_mono hfinite hpre
    have hlen' := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlen
    simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hpre'
    rw [ENNReal.toReal_ofReal (hρnonneg q z)] at hlen'
    have htri := dist_triangle (γ t) q p
    rw [dist_comm (γ t) q] at htri
    linarith [hnear hq]
theorem Helpers.exists_scaled_phase_endpoints_in_joint_spray_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p : E}
    {R r ε τ : ℝ} {K : NNReal} (hR : 0 < R) (hr : 0 < r)
    (hε : 0 < ε) (hτ : 0 < τ) (hτε : τ < ε)
    (hLip : LipschitzOnWith K (fun z : E × E => (z.2, -Γ z.1 z.2 z.2))
      (Metric.ball (p, 0) R))
    {Φ : ℝ × (E × E) → E × E}
    (hΦ0 : ∀ z ∈ Metric.ball (p, 0) r, Φ (0, z) = z)
    (hΦF : ∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
      Φ z ∈ Metric.ball (p, 0) R ∧
      HasDerivAt (fun t : ℝ => Φ (t, z.2))
        ((Φ z).2, -Γ (Φ z).1 (Φ z).2 (Φ z).2) z.1)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (he0 : (p, (0 : E)) ∈ e.source)
    (hef : ∀ z : E × E, e z = (z.1, (Φ (τ, z)).1))
    {x v : ℝ → E} {a : ℝ} (ha : 0 < a) (hx0 : x 0 = p)
    (hx : ContinuousAt x 0) (hv : ContinuousAt v 0)
    (hODE : ∀ t ∈ Set.Ioo (-a) a,
      HasDerivAt x (v t) t ∧ HasDerivAt v (-Γ (x t) (v t) (v t)) t) :
    ∃ δ > (0 : ℝ), δ ≤ a ∧
      ∀ s ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Ioo (-δ) δ, s ≤ t →
        (x s, ((t - s) / τ) • v s) ∈ e.source ∧
        e (x s, ((t - s) / τ) • v s) = (x s, x t) := by
  let Z : ℝ × ℝ → E × E := fun z => (x z.1, z.2 • v z.1)
  have hZ : ContinuousAt Z (0, 0) := by
    have hx' : ContinuousAt (fun z : ℝ × ℝ => x z.1) (0, 0) :=
      hx.comp (f := fun z : ℝ × ℝ => z.1) (x := (0, 0)) continuousAt_fst
    have hv' : ContinuousAt (fun z : ℝ × ℝ => v z.1) (0, 0) :=
      hv.comp (f := fun z : ℝ × ℝ => z.1) (x := (0, 0)) continuousAt_fst
    exact hx'.prodMk (continuousAt_snd.smul hv')
  have hZ0 : Z (0, 0) = (p, 0) := by simp [Z, hx0]
  let S := e.source ∩ (Metric.ball (p, (0 : E)) r ∩ Metric.ball (p, 0) R)
  have hS : S ∈ nhds (p, 0) := Filter.inter_mem (e.open_source.mem_nhds he0)
    (Filter.inter_mem (Metric.ball_mem_nhds _ hr) (Metric.ball_mem_nhds _ hR))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
    (hZ.preimage_mem_nhds (hZ0.symm ▸ hS))
  let δ := min (a / 2) (min (η / 2) (τ * η / 4))
  have hδ : 0 < δ := lt_min (half_pos ha) (lt_min (half_pos hη) (by positivity))
  have hδa : δ ≤ a := (min_le_left _ _).trans (by linarith)
  have hδη : δ ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδτη : δ ≤ τ * η / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδa, ?_⟩
  intro s hs t ht hst
  let κ := (t - s) / τ
  have hκnonneg : 0 ≤ κ := div_nonneg (sub_nonneg.mpr hst) hτ.le
  have hκτ : κ * τ = t - s := div_mul_cancel₀ _ hτ.ne'
  have hκsmall : |κ| < η := by
    rw [abs_of_nonneg hκnonneg]
    apply (div_lt_iff₀ hτ).mpr
    have := hs.1
    have := ht.2
    nlinarith
  have hscaled {u : ℝ} (hu : u ∈ Set.Ioo (-δ) δ) : (x u, κ • v u) ∈ S := by
    change Z (u, κ) ∈ S
    apply hηsub
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa only [Real.dist_eq, sub_zero] using
      (abs_lt.mpr hu).trans_le (hδη.trans (by linarith)), by
      simpa only [Real.dist_eq, sub_zero] using hκsmall⟩
  have hinterval {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) τ) :
      s + κ * u ∈ Set.Ioo (-δ) δ := by
    have hlo : 0 ≤ κ * u := mul_nonneg hκnonneg hu.1
    have hhi : κ * u ≤ κ * τ := mul_le_mul_of_nonneg_left hu.2 hκnonneg
    constructor <;> linarith [hs.1, ht.2]
  have htime {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) τ) : u ∈ Set.Ioo (-ε) ε :=
    ⟨by linarith [hu.1], hu.2.trans_lt hτε⟩
  have hD (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) τ) :
      HasDerivAt (fun z => (x (s + κ * z), κ • v (s + κ * z)))
        (κ • v (s + κ * u), -Γ (x (s + κ * u))
          (κ • v (s + κ * u)) (κ • v (s + κ * u))) u := by
    have harg : s + κ * u ∈ Set.Ioo (-a) a :=
      ⟨(neg_le_neg hδa).trans_lt (hinterval hu).1, (hinterval hu).2.trans_le hδa⟩
    have hdu : HasDerivAt (fun z : ℝ => s + κ * z) κ u := by
      simpa using ((hasDerivAt_id u).const_mul κ).const_add s
    have hdx := (hODE _ harg).1.scomp u hdu
    have hdv := ((hODE _ harg).2.scomp u hdu).const_smul κ
    simpa only [Function.comp_def, Pi.smul_apply, map_smul, smul_apply, smul_neg] using hdx.prodMk hdv
  have hstart := hscaled hs
  have hFlowC : ContinuousOn (fun u => Φ (u, (x s, κ • v s))) (Set.Icc 0 τ) :=
    fun u hu => (hΦF (u, (x s, κ • v s)) ⟨htime hu, hstart.2.1⟩).2.continuousAt.continuousWithinAt
  have hOldC : ContinuousOn (fun u => (x (s + κ * u), κ • v (s + κ * u)))
      (Set.Icc 0 τ) := fun u hu => (hD u hu).continuousAt.continuousWithinAt
  have huniq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ (z : E × E) => (z.2, -Γ z.1 z.2 z.2))
    (s := fun _ => Metric.ball (p, 0) R)
    (fun _ _ => hLip) hFlowC
    (fun u hu => (hΦF (u, (x s, κ • v s)) ⟨htime ⟨hu.1, hu.2.le⟩,
      hstart.2.1⟩).2.hasDerivWithinAt)
    (fun u hu => (hΦF (u, (x s, κ • v s)) ⟨htime ⟨hu.1, hu.2.le⟩,
      hstart.2.1⟩).1) hOldC
    (fun u hu => (hD u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => (hscaled (hinterval ⟨hu.1, hu.2.le⟩)).2.2)
    (by simpa only [mul_zero, add_zero] using hΦ0 _ hstart.2.1)
  have hend := huniq (show τ ∈ Set.Icc (0 : ℝ) τ from ⟨hτ.le, le_rfl⟩)
  change Φ (τ, (x s, κ • v s)) =
    (x (s + κ * τ), κ • v (s + κ * τ)) at hend
  refine ⟨hstart.1, ?_⟩
  change e (x s, κ • v s) = (x s, x t)
  rw [hef, hend]
  have heq : s + κ * τ = t := by linarith
  simp only [heq]
theorem Helpers.exists_chart_pairwise_radius_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [ConnectedSpace M]
    (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContinuousOn g (extChartAt I p).target)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
      g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
    (e : OpenPartialHomeomorph (E × E) (E × E)) (τ ρ : ℝ) (hρ : 0 < ρ)
    (hInv : ContDiffOn ℝ 1 (fun z : E × E => (e.symm z).2)
      (Metric.ball (extChartAt I p p) ρ ×ˢ Metric.ball (extChartAt I p p) ρ))
    (hdiag : ∀ q ∈ Metric.ball (extChartAt I p p) ρ,
      (q, (0 : E)) ∈ e.source ∧ e (q, 0) = (q, q))
    (hsmooth : ∀ q ∈ Metric.ball (extChartAt I p p) ρ, ∀ d > (0 : ℝ),
      ContDiffOn ℝ 1 (fun z => Real.sqrt ((τ ^ 2 • g q) (e.symm (q, z)).2
        (e.symm (q, z)).2 + d)) (Metric.ball (extChartAt I p p) ρ))
    (hbound : ∀ q ∈ Metric.ball (extChartAt I p p) ρ, ∀ d > (0 : ℝ),
      ∀ z ∈ Metric.ball (extChartAt I p p) ρ, ∀ w : E,
      |fderiv ℝ (fun y => Real.sqrt ((τ ^ 2 • g q) (e.symm (q, y)).2
        (e.symm (q, y)).2 + d)) z w| ≤ Real.sqrt (g z w w)) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      V ⊆ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) ρ ∧
      ∀ q ∈ V, ∀ z ∈ V,
        ENNReal.ofReal (Real.sqrt ((τ ^ 2 • g (extChartAt I p q))
          (e.symm (extChartAt I p q, extChartAt I p z)).2
          (e.symm (extChartAt I p q, extChartAt I p z)).2)) ≤ edist q z := by
  let A := (extChartAt I p).source ∩
    (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) ρ
  have hA : IsOpen A := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hpA : p ∈ A := ⟨mem_extChartAt_source p, Metric.mem_ball_self hρ⟩
  let F : E × E → ℝ := fun z =>
    (τ ^ 2 • g z.1) (e.symm z).2 (e.symm z).2
  let Q : M × M → ℝ := fun z => Real.sqrt (F (extChartAt I p z.1, extChartAt I p z.2))
  have hG : ContinuousAt (fun z : E × E => g z.1) (extChartAt I p p, extChartAt I p p) :=
    (hg.continuousAt ((isOpen_extChartAt_target p).mem_nhds
      (mem_extChartAt_target p))).comp (f := fun z : E × E => z.1)
        (x := (extChartAt I p p, extChartAt I p p)) continuousAt_fst
  have hV : ContinuousAt (fun z : E × E => (e.symm z).2)
      (extChartAt I p p, extChartAt I p p) :=
    (hInv.contDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨Metric.mem_ball_self hρ, Metric.mem_ball_self hρ⟩)).continuousAt
  have hB : ContinuousAt (fun z : E × E => τ ^ 2 • g z.1)
      (extChartAt I p p, extChartAt I p p) := hG.const_smul (τ ^ 2)
  have hF : ContinuousAt F (extChartAt I p p, extChartAt I p p) :=
    (hB.clm_apply hV).clm_apply hV
  have hC : ContinuousAt (fun z : M × M =>
      (extChartAt I p z.1, extChartAt I p z.2)) (p, p) :=
    ((continuousAt_extChartAt p).comp (f := fun z : M × M => z.1)
      (x := (p, p)) continuousAt_fst).prodMk
    ((continuousAt_extChartAt p).comp (f := fun z : M × M => z.2)
      (x := (p, p)) continuousAt_snd)
  have hQ : ContinuousAt Q (p, p) := hF.sqrt.comp
    (f := fun z : M × M => (extChartAt I p z.1, extChartAt I p z.2))
    (x := (p, p)) hC
  apply Helpers.exists_pairwise_radius_lower_bound_of_local_path_control I M p A hA hpA
    Q hQ ?_ (fun q z => Real.sqrt_nonneg _) ?_
  · intro q hq
    have hd := hdiag (extChartAt I p q) hq.2
    have hi : e.symm (extChartAt I p q, extChartAt I p q) = (extChartAt I p q, 0) := by
      rw [← hd.2]
      exact e.left_inv hd.1
    change Real.sqrt ((τ ^ 2 • g (extChartAt I p q))
      (e.symm (extChartAt I p q, extChartAt I p q)).2
      (e.symm (extChartAt I p q, extChartAt I p q)).2) = 0
    rw [hi]
    simp
  · intro q hq γ a b hab hγ hγA
    let P : E → ℝ := fun z => (τ ^ 2 • g (extChartAt I p q))
      (e.symm (extChartAt I p q, z)).2 (e.symm (extChartAt I p q, z)).2
    letI : (y : M) → NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun x : M => TangentSpace I x) y
    have hlim (z : M) : Filter.Tendsto
        (fun d : ℝ => Real.sqrt (P (extChartAt I p z) + d))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt (P (extChartAt I p z)))) := by
      have hc : Continuous (fun d : ℝ => Real.sqrt (P (extChartAt I p z) + d)) := by fun_prop
      simpa only [add_zero] using
        (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    change enorm (Real.sqrt (P (extChartAt I p (γ b))) -
      Real.sqrt (P (extChartAt I p (γ a)))) ≤ _
    apply le_of_tendsto (continuous_enorm.continuousAt.tendsto.comp
      ((hlim (γ b)).sub (hlim (γ a))))
    filter_upwards [self_mem_nhdsWithin] with d hd
    apply Helpers.enorm_sub_le_pathELength_of_coordinate_bound I A hA
      (Metric.ball (extChartAt I p p) ρ) Metric.isOpen_ball (extChartAt I p)
      (contMDiffOn_extChartAt.mono (fun _ hx => by
        simpa only [extChartAt_source] using hx.1)) (fun _ hx => hx.2)
      (fun z => Real.sqrt (P z + d)) (hsmooth _ hq.2 d hd) ?_ γ a b hab hγ hγA
    intro z hz w
    rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (hbound _ hq.2 d hd _ hz.2 _).trans_eq
      (Helpers.sqrt_coordinate_metric_chart_derivative_eq_norm p g hnorm z hz.1 w)
theorem Helpers.coordinate_spray_locally_distance_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v : E, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v : E,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w : E,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    {x v : ℝ → E} {ε : ℝ} {c : NNReal}
    (hε : 0 < ε) (hx0 : x 0 = extChartAt I p p)
    (hphase : ContDiffOn ℝ ∞ (fun t : ℝ => (x t, v t)) (Set.Ioo (-ε) ε))
    (hODE : ∀ t ∈ Set.Ioo (-ε) ε, x t ∈ (extChartAt I p).target ∧
      HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t)
    (hEnergy : ∀ t ∈ Set.Ioo (-ε) ε, g (x t) (v t) (v t) = (c : ℝ) ^ 2) :
    ∃ δ > (0 : ℝ), δ ≤ ε ∧
      ∀ s ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Ioo (-δ) δ,
        edist ((extChartAt I p).symm (x s)) ((extChartAt I p).symm (x t)) =
          (c : ENNReal) * ENNReal.ofReal |t - s| := by
  let P := extChartAt I p p
  have hU := isOpen_extChartAt_target (I := I) p
  have hpU := mem_extChartAt_target (I := I) p
  obtain ⟨R, hR, K, hLip, hdom, r, hr, a, ha, Φ, hΦ, hΦ0, hΦF, hΦp⟩ :=
    Helpers.exists_coordinate_spray_flow_in_lipschitz_ball hU hΓ hpU
  let τ := a / 2
  have hτ : 0 < τ := half_pos ha
  have hτa : τ < a := by dsimp [τ]; linarith
  have hτtime : τ ∈ Set.Ioo (-a) a := ⟨by linarith, hτa⟩
  have hΦat : ContDiffAt ℝ ∞ Φ (τ, (P, 0)) :=
    hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨hτtime, Metric.mem_ball_self hr⟩)
  have hlin := Helpers.coordinate_spray_flow_linearization hU hpU
    ((hΓ.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)) hr ha
    (hΦ.of_le (by simp)) hΦ0 hΦp (fun z hz => (hΦF z hz).2)
  obtain ⟨e, he0, hept, hef, he, hei⟩ :=
    Helpers.exists_joint_inverse_of_spray_flow_linearization hτ.ne' hΦat (hΦp τ hτtime)
      (hlin τ hτtime)
  obtain ⟨ρ, hρ, hρU, hInv, hdiag, hcontrol⟩ :=
    Helpers.exists_uniform_radius_control_of_joint_spray_inverse hU
      (hg.of_le (by simp)) hsym hpos hKoszul hr ha hτtime hLip hdom
      (hΦ.of_le (by simp)) hΦ0 hΦF (hΦp τ hτtime) e he0 hef hei
  obtain ⟨V, hV, hpV, hVA, hLower⟩ :=
    Helpers.exists_chart_pairwise_radius_lower_bound I M p g hg.continuousOn hnorm e τ ρ hρ
      hInv hdiag (fun q hq => (hcontrol q hq).2.1)
      (fun q hq => (hcontrol q hq).2.2)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hphase0 := (hphase.contDiffAt (isOpen_Ioo.mem_nhds hzero)).continuousAt
  obtain ⟨δ₀, hδ₀, hδ₀ε, hPair⟩ :=
    Helpers.exists_scaled_phase_endpoints_in_joint_spray_inverse hR hr ha hτ hτa hLip
      hΦ0 hΦF e he0 hef hε hx0 hphase0.fst hphase0.snd (fun t ht => (hODE t ht).2)
  let η : ℝ → M := fun t => (extChartAt I p).symm (x t)
  have hη0 : η 0 = p := by
    change (extChartAt I p).symm (x 0) = p
    rw [hx0]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hη : ContinuousAt η 0 :=
    ((continuousOn_extChartAt_symm p).continuousAt (hU.mem_nhds hpU)).comp_of_eq
      hphase0.fst hx0
  obtain ⟨b, hb, hbV⟩ := Metric.mem_nhds_iff.mp
    (hη.preimage_mem_nhds (hV.mem_nhds (hη0.symm ▸ hpV)))
  let δ := min δ₀ b
  have hδ : 0 < δ := lt_min hδ₀ hb
  have hsmall : Set.Ioo (-δ) δ ⊆ Set.Ioo (-δ₀) δ₀ := fun t ht =>
    ⟨(neg_le_neg (min_le_left _ _)).trans_lt ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hold : Set.Ioo (-δ) δ ⊆ Set.Ioo (-ε) ε := fun t ht =>
    ⟨(neg_le_neg hδ₀ε).trans_lt (hsmall ht).1, (hsmall ht).2.trans_le hδ₀ε⟩
  have hηV {t : ℝ} (ht : t ∈ Set.Ioo (-δ) δ) : η t ∈ V := by
    apply hbV
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (abs_lt.mpr ht).trans_le (min_le_right δ₀ b)
  have hordered : ∀ s ∈ Set.Ioo (-δ) δ, ∀ t ∈ Set.Ioo (-δ) δ, s ≤ t →
      edist (η s) (η t) = (c : ENNReal) * ENNReal.ofReal |t - s| := by
    intro s hs t ht hst
    have hsε := hold hs
    have htε := hold ht
    have hpair := hPair s (hsmall hs) t (hsmall ht) hst
    have hi := e.left_inv hpair.1
    rw [hpair.2] at hi
    have hvel : (e.symm (x s, x t)).2 = ((t - s) / τ) • v s := congrArg Prod.snd hi
    have hcoordS : extChartAt I p (η s) = x s :=
      (extChartAt I p).right_inv (hODE s hsε).1
    have hcoordT : extChartAt I p (η t) = x t :=
      (extChartAt I p).right_inv (hODE t htε).1
    have hRadius : Real.sqrt ((τ ^ 2 • g (x s)) (e.symm (x s, x t)).2
        (e.symm (x s, x t)).2) = (c : ℝ) * (t - s) := by
      rw [hvel]
      have hsq : (τ ^ 2 • g (x s)) (((t - s) / τ) • v s)
          (((t - s) / τ) • v s) = ((c : ℝ) * (t - s)) ^ 2 := by
        simp only [smul_apply, map_smul, smul_eq_mul]
        rw [hEnergy s hsε]
        calc
          _ = ((c : ℝ) * (τ * ((t - s) / τ))) ^ 2 := by ring
          _ = ((c : ℝ) * (t - s)) ^ 2 := by
            rw [mul_comm τ ((t - s) / τ), div_mul_cancel₀ _ hτ.ne']
      rw [hsq, Real.sqrt_sq (mul_nonneg c.coe_nonneg (sub_nonneg.mpr hst))]
    have hlower : ENNReal.ofReal ((c : ℝ) * (t - s)) ≤ edist (η s) (η t) := by
      simpa only [hcoordS, hcoordT, hRadius] using
        hLower (η s) (hηV hs) (η t) (hηV ht)
    have hIcc : Set.Icc s t ⊆ Set.Ioo (-ε) ε := fun u hu =>
      ⟨hsε.1.trans_le hu.1, hu.2.trans_lt htε.2⟩
    have hxc : ContDiffOn ℝ 1 x (Set.Icc s t) :=
      ((contDiff_fst.comp_contDiffOn hphase).of_le (by simp)).mono hIcc
    have hupper := Helpers.riemannianEDist_inverse_chart_le_of_constant_energy I p g hnorm
      x v s t (c : ℝ) hst c.coe_nonneg
      (fun u hu => (hODE u (hIcc hu)).1) hxc
      (fun u hu => (hODE u (hIcc hu)).2.1.hasDerivWithinAt)
      (fun u hu => hEnergy u (hIcc hu))
    have htarget : (c : ENNReal) * ENNReal.ofReal |t - s| =
        ENNReal.ofReal ((c : ℝ) * (t - s)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hst), ENNReal.ofReal_mul c.coe_nonneg,
        ENNReal.ofReal_coe_nnreal]
    rw [htarget]
    apply le_antisymm ?_ hlower
    rw [IsRiemannianManifold.out (I := I)]
    simpa only [mul_comm (t - s) (c : ℝ)] using hupper
  refine ⟨δ, hδ, (min_le_left δ₀ b).trans hδ₀ε, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s hs t ht hst
  · simpa only [edist_comm, abs_sub_comm] using hordered t ht s hs hts
theorem Helpers.eq_of_bilinear_norm_add_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ u v, B u v = B v u)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    {u v : E} {c : ℝ} (hu : B u u = c ^ 2) (hv : B v v = c ^ 2)
    (hadd : (2 * c) ^ 2 ≤ B (u + v) (u + v)) : u = v := by
  by_contra hne
  have hp := hpos (u - v) (sub_ne_zero.mpr hne)
  simp only [map_sub, sub_apply, map_add, add_apply] at hp hadd
  rw [hsym v u] at hp hadd
  nlinarith
theorem Helpers.riemannianEDist_inverse_chart_le_of_speed_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
    (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
      g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
    (x v : ℝ → E) (a b k : ℝ) (hab : a ≤ b) (hk : 0 ≤ k)
    (hx : Set.MapsTo x (Set.Icc a b) (extChartAt I p).target)
    (hCx : ContDiffOn ℝ 1 x (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (v t) (Set.Icc a b) t)
    (hspeed : ∀ t ∈ Set.Icc a b, Real.sqrt (g (x t) (v t) (v t)) ≤ k) :
    Manifold.riemannianEDist I ((extChartAt I p).symm (x a))
      ((extChartAt I p).symm (x b)) ≤ ENNReal.ofReal ((b - a) * k) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp [Manifold.riemannianEDist_self]
  have hpath : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1
      ((extChartAt I p).symm ∘ x) (Set.Icc a b) :=
    (contMDiffOn_extChartAt_symm p).comp (contMDiffOn_iff_contDiffOn.mpr hCx) hx
  apply (Manifold.riemannianEDist_le_pathELength hpath rfl rfl hab).trans
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    (∫⁻ t in Set.Icc a b, ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I
        ((extChartAt I p).symm ∘ x) (Set.Icc a b) t 1‖ₑ) ≤
        ∫⁻ _t in Set.Icc a b, ENNReal.ofReal k := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ofReal_norm, Helpers.norm_mfderivWithin_inverse_chart_curve I p g hg x
        (Set.Icc a b) t (v t) hx ht (uniqueDiffOn_Icc hab' t ht) (hderiv t ht)]
      exact ENNReal.ofReal_le_ofReal (hspeed t ht)
    _ = ENNReal.ofReal ((b - a) * k) := by
      simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_Icc, ← ENNReal.ofReal_mul hk, mul_comm k]
theorem Helpers.exists_inverse_chart_chord_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
    (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContinuousOn g (extChartAt I p).target)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
      g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
    (w : E) (k : ℝ) (hk : Real.sqrt (g (extChartAt I p p) w w) < k) :
    ∃ r > (0 : ℝ), ∀ y z : E, ∀ h > (0 : ℝ),
      y ∈ Metric.ball (extChartAt I p p) r →
      z ∈ Metric.ball (extChartAt I p p) r →
      h⁻¹ • (z - y) ∈ Metric.ball w r →
      Manifold.riemannianEDist I ((extChartAt I p).symm y)
        ((extChartAt I p).symm z) ≤ ENNReal.ofReal (h * k) := by
  let q := extChartAt I p p
  have hgc : ContinuousAt g q := hg.continuousAt
    ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p))
  have hgprod : ContinuousAt (fun z : E × E => g z.1) (q,w) :=
    ContinuousAt.comp (f := fun z : E × E => z.1) (x := (q,w)) hgc continuousAt_fst
  have hsc : ContinuousAt (fun z : E × E => Real.sqrt (g z.1 z.2 z.2)) (q,w) :=
    Real.continuous_sqrt.continuousAt.comp
      ((hgprod.clm_apply continuousAt_snd).clm_apply continuousAt_snd)
  have hN : {z : E × E | z.1 ∈ (extChartAt I p).target ∧
      Real.sqrt (g z.1 z.2 z.2) < k} ∈ nhds (q,w) :=
    Filter.inter_mem
      (continuousAt_fst.preimage_mem_nhds
        ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)))
      (hsc.preimage_mem_nhds (Iio_mem_nhds hk))
  obtain ⟨r,hr,hrN⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨r,hr,?_⟩
  intro y z h hh hy hz hd
  let d : E := h⁻¹ • (z - y)
  let l : ℝ → E := fun t => (1-t) • y + t • z
  have hld (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (l t,d) ∈ Metric.ball (q,w) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    refine ⟨?_,Metric.mem_ball.mp hd⟩
    exact Metric.mem_ball.mp ((convex_ball q r) hy hz (by linarith [ht.1,ht.2])
      ht.1 (by ring))
  have hmaps : Set.MapsTo l (Set.Icc 0 1) (extChartAt I p).target :=
    fun t ht => (hrN (hld t ht)).1
  have hdx (t : ℝ) : HasDerivAt l (z-y) t := by
    convert ((((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const y).add
      ((hasDerivAt_id t).smul_const z)) using 1
    · ext s
      rfl
    · simp only [zero_sub, neg_one_smul, one_smul]
      abel
  have heq : z-y = h • d := by dsimp [d]; rw [smul_inv_smul₀ hh.ne']
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Real.sqrt (g (l t) (z-y) (z-y)) ≤ h*k := by
    rw [heq]
    have he : g (l t) (h • d) (h • d) = h^2 * g (l t) d d := by
      simp only [map_smul,smul_apply,smul_eq_mul]; ring
    rw [he,Real.sqrt_mul (sq_nonneg h),Real.sqrt_sq hh.le]
    exact mul_le_mul_of_nonneg_left (hrN (hld t ht)).2.le hh.le
  have H := Helpers.riemannianEDist_inverse_chart_le_of_speed_bound I p g hnorm
    l (fun _ => z-y) 0 1 (h*k) zero_le_one
    (mul_nonneg hh.le ((Real.sqrt_nonneg _).trans hk.le)) hmaps (by dsimp [l]; fun_prop)
    (fun t _ => (hdx t).hasDerivWithinAt) hbound
  simpa [l] using H
theorem Helpers.chart_velocity_sum_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun z : M => TangentSpace I z)]
    [IsRiemannianManifold I M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ}
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D))
    (ht₀ : t₀ ∈ Set.Ioo A D)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContinuousOn g (extChartAt I (γ t₀)).target)
    (hnorm : ∀ z ∈ (extChartAt I (γ t₀)).target, ∀ w : E,
      g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I (γ t₀)).symm (Set.range I) z w‖ ^ 2)
    {u v : E}
    (hu : HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) u (Set.Ici t₀) t₀)
    (hv : HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Iic t₀) t₀) :
    2 * (c : ℝ) ≤ Real.sqrt (g (extChartAt I (γ t₀) (γ t₀)) (u+v) (u+v)) := by
  let p := γ t₀
  let F : ℝ → E := fun t => extChartAt I p (γ t)
  have hγ : ContinuousAt γ t₀ :=
    hlin.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht₀)
  have hF : ContinuousAt F t₀ := (continuousAt_extChartAt p).comp hγ
  have hdu : HasDerivWithinAt (fun h : ℝ => F (t₀+h)) u (Set.Ici 0) 0 := by
    simpa [Function.comp_def, F, p] using hu.scomp_of_eq (s := Set.Ici 0) 0
      (((hasDerivAt_id (0 : ℝ)).const_add t₀).hasDerivWithinAt)
      (fun h (hh : 0 ≤ h) => show t₀ ≤ t₀+h by linarith) (by simp)
  have hdv : HasDerivWithinAt (fun h : ℝ => F (t₀-h)) (-v) (Set.Ici 0) 0 := by
    simpa [Function.comp_def, F, p] using hv.scomp_of_eq (s := Set.Ici 0) 0
      (((hasDerivAt_const (0 : ℝ) t₀).sub (hasDerivAt_id (0 : ℝ))).hasDerivWithinAt)
      (fun h (hh : 0 ≤ h) => show t₀-h ≤ t₀ by linarith) (by simp)
  have hX : HasDerivWithinAt (fun h : ℝ => F (t₀+h) - F (t₀-h)) (u+v)
      (Set.Ioi 0) 0 := by
    convert (hdu.sub hdv).Ioi_of_Ici using 1
    simp only [sub_neg_eq_add]
  have hrescale : Filter.Tendsto
      (fun h : ℝ => h⁻¹ • (F (t₀+h) - F (t₀-h))) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (u+v)) := by
    have hh := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp hX
    convert hh using 1
    ext h
    simp [slope_def_module]
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  obtain ⟨k,hk,hkc⟩ := exists_between hlt
  obtain ⟨r,hr,hchord⟩ := Helpers.exists_inverse_chart_chord_bound I p g hg hnorm (u+v) k hk
  have hplus : Filter.Tendsto (fun h : ℝ => t₀+h) (nhds 0) (nhds t₀) := by
    simpa only [add_zero, Function.id_def] using
      (tendsto_const_nhds.add (Filter.tendsto_id : Filter.Tendsto id (nhds (0 : ℝ)) (nhds 0)))
  have hminus : Filter.Tendsto (fun h : ℝ => t₀-h) (nhds 0) (nhds t₀) := by
    simpa only [sub_zero, Function.id_def] using
      (tendsto_const_nhds.sub (Filter.tendsto_id : Filter.Tendsto id (nhds (0 : ℝ)) (nhds 0)))
  have hR : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      F (t₀+h) ∈ Metric.ball (extChartAt I p p) r := by
    have H := hF.tendsto.comp hplus
    exact (H.eventually (Metric.ball_mem_nhds _ hr)).filter_mono nhdsWithin_le_nhds
  have hL : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      F (t₀-h) ∈ Metric.ball (extChartAt I p p) r := by
    have H := hF.tendsto.comp hminus
    exact (H.eventually (Metric.ball_mem_nhds _ hr)).filter_mono nhdsWithin_le_nhds
  have hSource : ∀ᶠ h : ℝ in nhds 0,
      γ (t₀+h) ∈ (extChartAt I p).source ∧ γ (t₀-h) ∈ (extChartAt I p).source := by
    have hS : ∀ᶠ t in nhds t₀, γ t ∈ (extChartAt I p).source :=
      hγ.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) p)
    exact (hplus.eventually hS).and (hminus.eventually hS)
  obtain ⟨δ,hδ,hEq⟩ := hlin.on_open isOpen_Ioo ht₀
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < δ :=
    (show ∀ᶠ h : ℝ in nhds 0, h < δ from Iio_mem_nhds hδ).filter_mono
      nhdsWithin_le_nhds
  have hImpossible : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), False := by
    filter_upwards [hR,hL,hrescale.eventually (Metric.ball_mem_nhds _ hr),
      hSource.filter_mono nhdsWithin_le_nhds,hsmall,self_mem_nhdsWithin] with h hR hL hd hS hs hh
    change 0 < h at hh
    have hb := hchord (F (t₀-h)) (F (t₀+h)) h hh hL hR hd
    rw [← IsRiemannianManifold.out (I := I)] at hb
    have hleft : (extChartAt I p).symm (F (t₀-h)) = γ (t₀-h) := (extChartAt I p).left_inv hS.2
    have hright : (extChartAt I p).symm (F (t₀+h)) = γ (t₀+h) := (extChartAt I p).left_inv hS.1
    rw [hleft,hright,hEq (t₀-h) (t₀+h) (by constructor <;> linarith)
      (by constructor <;> linarith)] at hb
    have habs : |t₀+h-(t₀-h)| = 2*h := by rw [abs_of_pos (by linarith)]; ring
    rw [habs,← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul c.coe_nonneg] at hb
    have hb' := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hh.le ((Real.sqrt_nonneg _).trans hk.le))).mp hb
    have hc' : 2*(c : ℝ) ≤ k := by nlinarith
    exact (not_le_of_gt hkc) hc'
  obtain ⟨h, hh⟩ := hImpossible.exists
  exact hh
theorem Helpers.eq_chart_velocity_of_one_sided_energy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} {u v : E}
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D))
    (ht₀ : t₀ ∈ Set.Ioo A D)
    (hu : HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) u (Set.Ici t₀) t₀)
    (hv : HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Iic t₀) t₀)
    (hEu : ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (γ t₀)).symm
      (Set.range I) (extChartAt I (γ t₀) (γ t₀)) u‖ ^ 2 = (c : ℝ) ^ 2)
    (hEv : ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (γ t₀)).symm
      (Set.range I) (extChartAt I (γ t₀) (γ t₀)) v‖ ^ 2 = (c : ℝ) ^ 2) : u = v := by
  obtain ⟨g, hg, hsym, hpos, hnorm⟩ := Helpers.exists_smooth_coordinate_metric I (γ t₀)
  rw [← hnorm _ (mem_extChartAt_target (γ t₀))] at hEu hEv
  have hsum := Helpers.chart_velocity_sum_lower_bound I hlin ht₀ g hg.continuousOn hnorm hu hv
  have hnonneg : 0 ≤ g (extChartAt I (γ t₀) (γ t₀)) (u+v) (u+v) := by
    rw [hnorm _ (mem_extChartAt_target (γ t₀))]
    exact sq_nonneg _
  apply Helpers.eq_of_bilinear_norm_add_ge
    (g (extChartAt I (γ t₀) (γ t₀))) (hsym _) (hpos _ (mem_extChartAt_target (γ t₀))) hEu hEv
  nlinarith [Real.sq_sqrt hnonneg,
    Real.sqrt_nonneg (g (extChartAt I (γ t₀) (γ t₀)) (u+v) (u+v)), c.coe_nonneg]
theorem Helpers.matching_chart_velocity_of_one_sided_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ}
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D)
    (hR : ContDiffWithinAt ℝ ∞ (fun t => extChartAt I (γ t₀) (γ t)) (Set.Ici t₀) t₀)
    (hL : ContDiffWithinAt ℝ ∞ (fun t => extChartAt I (γ t₀) (γ t)) (Set.Iic t₀) t₀)
    (hER : ∀ v : E,
      HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Ici t₀) t₀ →
      ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (γ t₀)).symm
        (Set.range I) (extChartAt I (γ t₀) (γ t₀)) v‖ ^ 2 = (c : ℝ) ^ 2)
    (hEL : ∀ v : E,
      HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Iic t₀) t₀ →
      ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (γ t₀)).symm
        (Set.range I) (extChartAt I (γ t₀) (γ t₀)) v‖ ^ 2 = (c : ℝ) ^ 2) :
    ∃ v : E,
      HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Ici t₀) t₀ ∧
      HasDerivWithinAt (fun t => extChartAt I (γ t₀) (γ t)) v (Set.Iic t₀) t₀ := by
  have hu := (hR.differentiableWithinAt (by simp)).hasDerivWithinAt
  have hv := (hL.differentiableWithinAt (by simp)).hasDerivWithinAt
  have heq := Helpers.eq_chart_velocity_of_one_sided_energy I hlin ht₀ hu hv (hER _ hu) (hEL _ hv)
  rw [← heq] at hv
  exact ⟨_, hu, hv⟩
theorem Helpers.bilinear_derivative_energy_eq_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {x : ℝ → E} {x' : E} {t₀ c : ℝ} {s : Set ℝ}
    [Filter.NeBot (nhdsWithin t₀ s)] (hs : t₀ ∉ s)
    (hx : HasDerivWithinAt x x' s t₀) (hx₀ : x t₀ = 0)
    (henergy : ∀ᶠ t in nhdsWithin t₀ s,
      B (x t) (x t) = c ^ 2 * (t - t₀) ^ 2) : B x' x' = c ^ 2 := by
  have hlim : Filter.Tendsto (fun t => B (slope x t₀ t) (slope x t₀ t))
      (nhdsWithin t₀ s) (nhds (B x' x')) :=
    (B.continuous.clm_apply continuous_id).continuousAt.tendsto.comp
      ((hasDerivWithinAt_iff_tendsto_slope' hs).mp hx)
  have heq : (fun t => B (slope x t₀ t) (slope x t₀ t)) =ᶠ[nhdsWithin t₀ s]
      (fun _ => c ^ 2) := by
    filter_upwards [henergy, self_mem_nhdsWithin] with t ht hts
    have hne : t ≠ t₀ := by rintro rfl; exact hs hts
    simp only [slope_def_module, hx₀, sub_zero, map_smul, smul_apply, smul_eq_mul]
    rw [ht]
    have hsub : t - t₀ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
theorem Helpers.energy_eq_of_normal_radius_derivative_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g B : E →L[ℝ] E →L[ℝ] ℝ) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source)
    (he : DifferentiableAt ℝ e 0) (hi : DifferentiableAt ℝ e.symm (e 0))
    (hmetric : ∀ v, g (fderiv ℝ e 0 v) (fderiv ℝ e 0 v) = B v v)
    {x : ℝ → E} {x' : E} {t₀ c : ℝ} {s : Set ℝ}
    [Filter.NeBot (nhdsWithin t₀ s)] (hs : t₀ ∉ s)
    (hx : HasDerivWithinAt x x' s t₀) (hx₀ : x t₀ = e 0)
    (henergy : ∀ᶠ t in nhdsWithin t₀ s,
      B (e.symm (x t)) (e.symm (x t)) = c ^ 2 * (t - t₀) ^ 2) :
    g x' x' = c ^ 2 := by
  have he' : HasFDerivAt e (fderiv ℝ e 0) (e.symm (e 0)) := by
    rw [e.left_inv he0]
    exact he.hasFDerivAt
  have hcomp := he'.comp (e 0) hi.hasFDerivAt
  have hEq : (fun y => e (e.symm y)) =ᶠ[nhds (e 0)] id :=
    e.eventually_right_inverse (e.map_source he0)
  have hid := hcomp.congr_of_eventuallyEq hEq.symm
  have hcancel : ∀ v, fderiv ℝ e 0 (fderiv ℝ e.symm (e 0) v) = v := by
    intro v
    have hh := congrArg (fun L : E →L[ℝ] E => L v) (hid.unique (hasFDerivAt_id (e 0)))
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      e.left_inv he0] using hh
  have hi' : HasFDerivAt e.symm (fderiv ℝ e.symm (e 0)) (x t₀) := by
    rw [hx₀]
    exact hi.hasFDerivAt
  have hdx := hi'.comp_hasDerivWithinAt t₀ hx
  have hzero : e.symm (x t₀) = 0 := by rw [hx₀]; exact e.left_inv he0
  have h := Helpers.bilinear_derivative_energy_eq_within B hs hdx hzero henergy
  rw [← hmetric, hcancel] at h
  exact h
theorem Helpers.energy_eq_of_local_normal_distance_within
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [EMetricSpace M] (F : M → E) (p : M)
    (g B : E →L[ℝ] E →L[ℝ] ℝ) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source) (hp : F p = e 0)
    (he : DifferentiableAt ℝ e 0) (hi : DifferentiableAt ℝ e.symm (e 0))
    (hmetric : ∀ v, g (fderiv ℝ e 0 v) (fderiv ℝ e 0 v) = B v v)
    (hB : ∀ v, 0 ≤ B v v)
    {V : Set M} (hV : V ∈ nhds p)
    (hdist : ∀ q ∈ V, edist p q = ENNReal.ofReal
      (Real.sqrt (B (e.symm (F q)) (e.symm (F q)))))
    {γ : ℝ → M} {v : E} {t₀ : ℝ} {c : NNReal} {s : Set ℝ}
    [Filter.NeBot (nhdsWithin t₀ s)] (hs : t₀ ∉ s)
    (hγ : ContinuousAt γ t₀) (hγ₀ : γ t₀ = p)
    (hx : HasDerivWithinAt (fun t => F (γ t)) v s t₀)
    (hlinear : ∀ᶠ t in nhdsWithin t₀ s,
      edist p (γ t) = (c : ENNReal) * ENNReal.ofReal |t - t₀|) :
    g v v = (c : ℝ) ^ 2 := by
  apply Helpers.energy_eq_of_normal_radius_derivative_within g B e he0 he hi hmetric hs hx
    (by rw [hγ₀, hp])
  have hγVn : ∀ᶠ t in nhds t₀, γ t ∈ V :=
    hγ.preimage_mem_nhds (by simpa only [hγ₀] using hV)
  have hγV : ∀ᶠ t in nhdsWithin t₀ s, γ t ∈ V :=
    hγVn.filter_mono nhdsWithin_le_nhds
  filter_upwards [hγV, hlinear] with t ht hlin
  have hh := (hdist (γ t) ht).symm.trans hlin
  have hh' : Real.sqrt (B (e.symm (F (γ t))) (e.symm (F (γ t)))) =
      (c : ℝ) * |t - t₀| := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (mul_nonneg c.coe_nonneg (abs_nonneg _))).mp
    simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hh
  calc
    _ = (Real.sqrt (B (e.symm (F (γ t))) (e.symm (F (γ t))))) ^ 2 :=
      (Real.sq_sqrt (hB _)).symm
    _ = (c : ℝ) ^ 2 * (t - t₀) ^ 2 := by rw [hh', mul_pow, sq_abs]
theorem Helpers.bilinear_derivative_energy_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {x : ℝ → E} {x' : E} {t₀ c : ℝ}
    (hx : HasDerivAt x x' t₀) (hx₀ : x t₀ = 0)
    (henergy : ∀ᶠ t in nhds t₀, B (x t) (x t) = c ^ 2 * (t - t₀) ^ 2) :
    B x' x' = c ^ 2 := by
  have hlim : Filter.Tendsto
      (fun t => B (slope x t₀ t) (slope x t₀ t))
      (nhdsWithin t₀ {t₀}ᶜ) (nhds (B x' x')) :=
    (B.continuous.clm_apply continuous_id).continuousAt.tendsto.comp hx.tendsto_slope
  have heq : (fun t => B (slope x t₀ t) (slope x t₀ t)) =ᶠ[
      nhdsWithin t₀ {t₀}ᶜ] (fun _ => c ^ 2) := by
    filter_upwards [henergy.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
    simp only [slope_def_module, hx₀, sub_zero, map_smul, smul_apply, smul_eq_mul]
    rw [ht]
    have hsub : t - t₀ ≠ 0 := sub_ne_zero.mpr hne
    field_simp
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
theorem Helpers.hasDerivAt_center_chart_of_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {γ : ℝ → M} {t : ℝ} {v : E}
    (hγ : ContinuousAt γ t) (hp : γ t ∈ (extChartAt I p).source)
    (hx : HasDerivAt (fun s => extChartAt I p (γ s)) v t) :
    HasDerivAt (fun s => extChartAt I (γ t) (γ s))
      (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
        (Set.range I) (extChartAt I p (γ t)) v) t := by
  have hInv := (mdifferentiableWithinAt_extChartAt_symm
    ((extChartAt I p).map_source hp)).hasMFDerivWithinAt
  have hInv' : HasMFDerivAt (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (extChartAt I p (γ t))
      (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
        (Set.range I) (extChartAt I p (γ t))) := by
    simpa only [I.range_eq_univ, hasMFDerivWithinAt_univ] using hInv
  have hcomp := hInv'.comp t hx.hasFDerivAt.hasMFDerivAt
  have heq : γ =ᶠ[nhds t] (fun s => (extChartAt I p).symm (extChartAt I p (γ s))) := by
    filter_upwards [hγ.preimage_mem_nhds (extChartAt_source_mem_nhds' hp)] with s hs
    exact ((extChartAt I p).left_inv hs).symm
  have hγ' := hcomp.congr_of_eventuallyEq_abuse heq
  have hcenter := (mdifferentiableAt_extChartAt
    (mem_chart_source H (γ t))).hasMFDerivAt.comp t hγ'
  set_option backward.isDefEq.respectTransparency false in
    rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply hcenter.congr_mfderiv
    ext
    dsimp only [TangentSpace, instModuleTangentSpace, instAddCommGroupTangentSpace,
      instTopologicalSpaceTangentSpace]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul]
    exact congrArg (fun A => A ((mfderivWithin (modelWithCornersSelf ℝ E) I
      (extChartAt I p).symm (Set.range I) (extChartAt I p (γ t))) v))
      (mfderiv_extChartAt_self (I := I) (x := γ t))
theorem Helpers.chart_speed_eq_of_center_chart_speed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    (p : M) {γ : ℝ → M} {t₀ k : ℝ} {v : E}
    (hγ : ContinuousAt γ t₀) (hp : γ t₀ ∈ (extChartAt I p).source)
    (hx : HasDerivAt (fun t => extChartAt I p (γ t)) v t₀)
    (hSpeed : ∀ w : E,
      HasDerivAt (fun t => extChartAt I (γ t₀) (γ t)) w t₀ →
      ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (γ t₀)).symm
        (Set.range I) (extChartAt I (γ t₀) (γ t₀)) w‖ ^ 2 = k) :
    ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range I) (extChartAt I p (γ t₀)) v‖ ^ 2 = k := by
  have hx' := Helpers.hasDerivAt_center_chart_of_chart I p hγ hp hx
  have hs := hSpeed _ hx'
  rw [mfderivWithin_range_extChartAt_symm] at hs
  dsimp only [TangentSpace, instModuleTangentSpace, instAddCommGroupTangentSpace,
    instTopologicalSpaceTangentSpace] at hs
  set_option backward.isDefEq.respectTransparency false in
    simp only [ContinuousLinearMap.id_apply] at hs
    let N : M → E → ℝ := fun q w => @norm (TangentSpace I q) inferInstance w
    change N ((extChartAt I (γ t₀)).symm (extChartAt I (γ t₀) (γ t₀)))
      ((mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
        (Set.range I) (extChartAt I p (γ t₀))) v) ^ 2 = k at hs
    change N ((extChartAt I p).symm (extChartAt I p (γ t₀)))
      ((mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
        (Set.range I) (extChartAt I p (γ t₀))) v) ^ 2 = k
    simpa only [(extChartAt I p).left_inv hp,
      (extChartAt I (γ t₀)).left_inv (mem_extChartAt_source (γ t₀))] using hs
theorem Helpers.hasDerivAt_of_normal_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {F : ℝ → E} {v : E} {t : ℝ}
    (hF : ContinuousAt F t) (ht : F t ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm (F t)))
    (hx : HasDerivAt (fun s => e.symm (F s)) v t) :
    HasDerivAt F (fderiv ℝ e (e.symm (F t)) v) t := by
  have hi : (fun y => e (e.symm y)) =ᶠ[nhds (F t)] id := e.eventually_right_inverse ht
  have hEq : F =ᶠ[nhds t] (fun s => e (e.symm (F s))) :=
    (hi.comp_tendsto hF.tendsto).symm
  exact (he.hasFDerivAt.comp_hasDerivAt t hx).congr_of_eventuallyEq hEq
theorem Helpers.injective_fderiv_of_partial_homeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {u : E} (hu : u ∈ e.source)
    (he : DifferentiableAt ℝ e u) (hi : DifferentiableAt ℝ e.symm (e u)) :
    Function.Injective (fderiv ℝ e u) := by
  have hcomp := hi.hasFDerivAt.comp u he.hasFDerivAt
  have hEq : (fun y => e.symm (e y)) =ᶠ[nhds u] id := e.eventually_left_inverse hu
  have hcancel := (hcomp.congr_of_eventuallyEq hEq.symm).unique (hasFDerivAt_id u)
  intro v w hvw
  have hh := congrArg (fun L : E →L[ℝ] E => L v) hcancel
  have hh' := congrArg (fun L : E →L[ℝ] E => L w) hcancel
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hvw] at hh hh'
  exact hh.symm.trans hh'
theorem Helpers.radial_of_normal_coordinates_sharp_speed : open MeasureTheory in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (e : OpenPartialHomeomorph E E) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
      (B : E →L[ℝ] E →L[ℝ] ℝ) (F : ℝ → E)
      (K : NNReal) (r a b t₀ c : ℝ),
      (∀ u v, B u v = B v u) → 0 < c → t₀ < a → a ≤ b →
      ContDiffOn ℝ 1 e (Metric.ball 0 r) →
      (∀ t ∈ Set.Icc a b, F t ∈ e.target ∧ e.symm (F t) ∈ Metric.ball 0 r) →
      (∀ t ∈ Set.Icc a b, ContinuousAt F t) →
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ e.symm (F t)) →
      LipschitzOnWith K (fun t => e.symm (F t)) (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, ∀ u v, g (F t) u v = g (F t) v u) →
      (∀ t ∈ Set.Icc a b, ∀ v, v ≠ 0 → 0 < g (F t) v v) →
      (∀ t ∈ Set.Icc a b, ∀ w,
        g (F t) (fderiv ℝ e (e.symm (F t)) (e.symm (F t)))
          (fderiv ℝ e (e.symm (F t)) w) = B (e.symm (F t)) w) →
      (∀ t ∈ Set.Icc a b, ∀ v, HasDerivAt F v t → g (F t) v v = c ^ 2) →
      (∀ t ∈ Set.Icc a b, Real.sqrt (B (e.symm (F t)) (e.symm (F t))) =
        c * (t - t₀)) →
      ∃ w : E, ∀ t ∈ Set.Icc a b, e.symm (F t) = (t - t₀) • w := by
  intro E _ _ _ e g B F K r a b t₀ c hB hc ht₀ hab he hMaps hF hi hLip
    hsym hpos hGauss hSharp hRadius
  have heDiff (t : ℝ) (ht : t ∈ Set.Icc a b) :
      DifferentiableAt ℝ e (e.symm (F t)) :=
    (he.contDiffAt (Metric.isOpen_ball.mem_nhds (hMaps t ht).2)).differentiableAt_one
  refine Helpers.radial_of_gauss_speed_bound B (fun t => g (F t))
    (fun t => fderiv ℝ e (e.symm (F t))) (fun t => e.symm (F t)) K a b t₀ c
    hB hc ht₀ hab hLip hsym hpos ?_ hGauss hRadius ?_
  · intro t ht
    exact Helpers.injective_fderiv_of_partial_homeomorph e
      (e.map_target (hMaps t ht).1) (heDiff t ht)
      (by simpa only [e.right_inv (hMaps t ht).1] using hi t ht)
  · filter_upwards [Helpers.ae_hasDerivAt_of_lipschitzOnWith_Icc hLip] with t hdt ht
    exact (hSharp t ht _ (Helpers.hasDerivAt_of_normal_coordinates e (hF t ht)
      (hMaps t ht).1 (heDiff t ht) (hdt ht))).le
theorem Helpers.MetricLocallyLinear.continuousAt
    {M : Type*} [EMetricSpace M] {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : Helpers.MetricLocallyLinear γ c S) (hS : IsOpen S) {t : ℝ} (ht : t ∈ S) :
    ContinuousAt γ t :=
  h.continuousOn.continuousAt (hS.mem_nhds ht)
theorem Helpers.MetricLocallyLinear.eventually_edist_eq
    {M : Type*} [EMetricSpace M] {γ : ℝ → M} {c : NNReal} {S : Set ℝ}
    (h : Helpers.MetricLocallyLinear γ c S) (hS : IsOpen S) {t : ℝ} (ht : t ∈ S) :
    ∀ᶠ s in nhds t, edist (γ t) (γ s) = (c : ENNReal) * ENNReal.ofReal |s - t| := by
  obtain ⟨δ, hδ, H⟩ := h.on_open hS ht
  filter_upwards [Ioo_mem_nhds (by linarith : t - δ < t) (by linarith : t < t + δ)]
    with s hs
  exact H t s (by constructor <;> linarith) hs
theorem Helpers.right_radial_germ_of_compact_radial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} (F : ℝ → E) (γ : ℝ → M) (G : E → M) (t₀ d : ℝ)
    (hd : 0 < d) (hF₀ : F t₀ = 0) (hγ₀ : γ t₀ = G 0)
    (hRig : ∀ a b : ℝ, t₀ < a → a ≤ b → b < t₀ + d →
      ∃ w : E, ∀ t ∈ Set.Icc a b,
        F t = (t - t₀) • w ∧ γ t = G ((t - t₀) • w)) :
    ∃ w : E, ∀ t ∈ Set.Icc t₀ (t₀ + d / 2),
      F t = (t - t₀) • w ∧ γ t = G ((t - t₀) • w) := by
  let m := t₀ + d / 4
  have hm : t₀ < m := by dsimp [m]; linarith
  let w := (m - t₀)⁻¹ • F m
  refine ⟨w, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    simpa only [sub_self, zero_smul] using And.intro hF₀ hγ₀
  · obtain ⟨u, hu⟩ := hRig (min t m) (max t m) (lt_min h hm) min_le_max
      (max_lt (by linarith [ht.2]) (by dsimp [m]; linarith))
    have hmI : m ∈ Set.Icc (min t m) (max t m) :=
      ⟨min_le_right _ _, le_max_right _ _⟩
    have hw : w = u := by
      dsimp [w]
      rw [(hu m hmI).1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hm.ne'), one_smul]
    simpa only [hw] using hu t ⟨min_le_left _ _, le_max_left _ _⟩
theorem Helpers.contDiffWithinAt_chart_of_right_radial_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (p : M)
    {γ : ℝ → M} {t₀ ε : ℝ} {e : E → E} {w : E}
    (hε : 0 < ε) (hep : e 0 = extChartAt I p p) (he : ContDiffAt ℝ ∞ e 0)
    (hRep : ∀ t ∈ Set.Icc t₀ (t₀ + ε),
      γ t = (extChartAt I p).symm (e ((t - t₀) • w))) :
    ContDiffWithinAt ℝ ∞ (fun t => extChartAt I p (γ t)) (Set.Ici t₀) t₀ := by
  have hLine : ContDiff ℝ ∞ (fun t : ℝ => (t - t₀) • w) :=
    (contDiff_id.sub contDiff_const).smul contDiff_const
  have he' : ContDiffAt ℝ ∞ e ((t₀ - t₀) • w) := by
    simpa only [sub_self, zero_smul] using he
  have hSmooth : ContDiffAt ℝ ∞ (fun t : ℝ => e ((t - t₀) • w)) t₀ :=
    he'.comp t₀ hLine.contDiffAt
  have hTarget : ∀ᶠ t in nhds t₀, e ((t - t₀) • w) ∈ (extChartAt I p).target :=
    hSmooth.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target p).mem_nhds (by
        rw [sub_self, zero_smul, hep]
        exact mem_extChartAt_target p))
  have hlt : ∀ᶠ t in nhds t₀, t < t₀ + ε := Iio_mem_nhds (by linarith)
  apply hSmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ (show t₀ ∈ Set.Ici t₀ by simp)
  filter_upwards [self_mem_nhdsWithin,
    hlt.filter_mono nhdsWithin_le_nhds,
    hTarget.filter_mono nhdsWithin_le_nhds] with t ht hlt htarget
  rw [hRep t ⟨ht, hlt.le⟩]
  exact (extChartAt I p).right_inv htarget
theorem Helpers.radial_energy_eq_of_radial_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {r : ℝ} {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    {e : E → E} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContinuousOn g U) (he : ContDiffOn ℝ 1 e (Metric.ball 0 r))
    (heU : Set.MapsTo e (Metric.ball 0 r) U)
    (hradial : ∀ u ∈ Metric.ball 0 r,
      g (e u) (fderiv ℝ e u u) (fderiv ℝ e u u) = B u u)
    {v : E} (hv : v ∈ Metric.ball 0 r) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g (e (t • v)) (fderiv ℝ e (t • v) v) (fderiv ℝ e (t • v) v) = B v v := by
  have hmaps : Set.MapsTo (fun t : ℝ => t • v) (Set.Icc 0 1) (Metric.ball 0 r) := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    calc
      ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ < r := by simpa using hv
  have hsmul : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
  have hD : ContinuousOn (fun t : ℝ => fderiv ℝ e (t • v) v) (Set.Icc 0 1) :=
    ((he.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).comp
      hsmul.continuousOn hmaps).clm_apply continuousOn_const
  have hG : ContinuousOn (fun t : ℝ => g (e (t • v))) (Set.Icc 0 1) :=
    hg.comp (he.continuousOn.comp hsmul.continuousOn hmaps) (heU.comp hmaps)
  have heq : Set.EqOn
      (fun t : ℝ => g (e (t • v)) (fderiv ℝ e (t • v) v)
        (fderiv ℝ e (t • v) v)) (fun _ => B v v) (Set.Ioc 0 1) := by
    intro t ht
    have h := hradial (t • v) (hmaps ⟨ht.1.le, ht.2⟩)
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    exact mul_left_cancel₀ ht.1.ne' (mul_left_cancel₀ ht.1.ne' h)
  exact heq.of_subset_closure ((hG.clm_apply hD).clm_apply hD) continuousOn_const
    Set.Ioc_subset_Icc_self (by rw [closure_Ioc (show (0 : ℝ) ≠ 1 by norm_num)])
theorem Helpers.riemannianEDist_radial_le : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
      (_hg : ContinuousOn g (extChartAt I p).target)
      (_hnorm : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
      (B : E →L[ℝ] E →L[ℝ] ℝ) (e : E → E) (r : ℝ)
      (_he : ContDiffOn ℝ 1 e (Metric.ball 0 r))
      (_htarget : Set.MapsTo e (Metric.ball 0 r) (extChartAt I p).target)
      (_hradial : ∀ u ∈ Metric.ball 0 r,
        g (e u) (fderiv ℝ e u u) (fderiv ℝ e u u) = B u u)
      (v : E) (_hv : v ∈ Metric.ball 0 r) (_hB : 0 ≤ B v v),
      Manifold.riemannianEDist I ((extChartAt I p).symm (e 0))
        ((extChartAt I p).symm (e v)) ≤ ENNReal.ofReal (Real.sqrt (B v v)) := by
  intro E _ _ H _ I M _ _ _ _ p g hg hnorm B e r he htarget hradial v hv hB
  have hmaps : Set.MapsTo (fun t : ℝ => t • v) (Set.Icc 0 1) (Metric.ball 0 r) := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    calc
      ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ < r := by simpa using hv
  have hcurve : ContDiffOn ℝ 1 (fun t : ℝ => e (t • v)) (Set.Icc 0 1) :=
    he.comp (contDiff_id.smul contDiff_const).contDiffOn hmaps
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => e (s • v)) (fderiv ℝ e (t • v) v)
        (Set.Icc 0 1) t := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    exact (((he.contDiffAt (Metric.isOpen_ball.mem_nhds (hmaps ht))).differentiableAt_one
      ).hasFDerivAt.comp_hasDerivAt t hline).hasDerivWithinAt
  have henergy := Helpers.radial_energy_eq_of_radial_identity B hg he htarget hradial hv
  have h := Helpers.riemannianEDist_inverse_chart_le_of_constant_energy I p g hnorm
    (fun t : ℝ => e (t • v)) (fun t : ℝ => fderiv ℝ e (t • v) v)
    0 1 (Real.sqrt (B v v)) zero_le_one (Real.sqrt_nonneg _) (htarget.comp hmaps)
    hcurve hderiv (by intro t ht; rw [henergy t ht, Real.sq_sqrt hB])
  simpa only [zero_smul, one_smul, sub_zero, one_mul] using h
theorem Helpers.radial_metric_at_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {r : ℝ} (hr : 0 < r)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {e : E → E}
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContinuousOn g U) (he : ContDiffOn ℝ 1 e (Metric.ball 0 r))
    (heU : Set.MapsTo e (Metric.ball 0 r) U)
    (hradial : ∀ u ∈ Metric.ball 0 r,
      g (e u) (fderiv ℝ e u u) (fderiv ℝ e u u) = B u u) :
    ∀ v, g (e 0) (fderiv ℝ e 0 v) (fderiv ℝ e 0 v) = B v v := by
  intro v
  have hnear : ∀ᶠ t : ℝ in nhds (0 : ℝ), t • v ∈ Metric.ball 0 r :=
    (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa using Metric.mem_ball_self (x := (0 : E)) hr))
  obtain ⟨t, ht, hne⟩ :=
    ((hnear.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin :
      ∀ᶠ t : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ,
        t • v ∈ Metric.ball 0 r ∧ t ≠ 0).exists
  have h := Helpers.radial_energy_eq_of_radial_identity B hg he heU hradial ht 0
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
  simp only [zero_smul, map_smul, smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hne (mul_left_cancel₀ hne h)
theorem Helpers.energy_eq_of_normal_radius_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g B : E →L[ℝ] E →L[ℝ] ℝ) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source)
    (he : DifferentiableAt ℝ e 0) (hi : DifferentiableAt ℝ e.symm (e 0))
    (hmetric : ∀ v, g (fderiv ℝ e 0 v) (fderiv ℝ e 0 v) = B v v)
    {x : ℝ → E} {x' : E} {t₀ c : ℝ}
    (hx : HasDerivAt x x' t₀) (hx₀ : x t₀ = e 0)
    (henergy : ∀ᶠ t in nhds t₀,
      B (e.symm (x t)) (e.symm (x t)) = c ^ 2 * (t - t₀) ^ 2) :
    g x' x' = c ^ 2 := by
  have he' : HasFDerivAt e (fderiv ℝ e 0) (e.symm (e 0)) := by
    rw [e.left_inv he0]
    exact he.hasFDerivAt
  have hcomp := he'.comp (e 0) hi.hasFDerivAt
  have hEq : (fun y => e (e.symm y)) =ᶠ[nhds (e 0)] id :=
    e.eventually_right_inverse (e.map_source he0)
  have hid := hcomp.congr_of_eventuallyEq hEq.symm
  have hcancel : ∀ v, fderiv ℝ e 0 (fderiv ℝ e.symm (e 0) v) = v := by
    intro v
    have hh := congrArg (fun L : E →L[ℝ] E => L v) (hid.unique (hasFDerivAt_id (e 0)))
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      e.left_inv he0] using hh
  have hdx : HasDerivAt (fun t => e.symm (x t))
      (fderiv ℝ e.symm (e 0) x') t₀ := by
    have hi' : HasFDerivAt e.symm (fderiv ℝ e.symm (e 0)) (x t₀) := by
      rw [hx₀]
      exact hi.hasFDerivAt
    exact hi'.comp_hasDerivAt t₀ hx
  have hzero : e.symm (x t₀) = 0 := by rw [hx₀]; exact e.left_inv he0
  have h := Helpers.bilinear_derivative_energy_eq B hdx hzero henergy
  rw [← hmetric, hcancel] at h
  exact h
theorem Helpers.energy_eq_of_local_normal_distance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [EMetricSpace M] (F : M → E) (p : M)
    (g B : E →L[ℝ] E →L[ℝ] ℝ) (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source) (hp : F p = e 0)
    (he : DifferentiableAt ℝ e 0) (hi : DifferentiableAt ℝ e.symm (e 0))
    (hmetric : ∀ v, g (fderiv ℝ e 0 v) (fderiv ℝ e 0 v) = B v v)
    (hB : ∀ v, 0 ≤ B v v)
    {V : Set M} (hV : V ∈ nhds p)
    (hdist : ∀ q ∈ V, edist p q = ENNReal.ofReal (Real.sqrt (B (e.symm (F q)) (e.symm (F q)))))
    {γ : ℝ → M} {v : E} {t₀ : ℝ} {c : NNReal}
    (hγ : ContinuousAt γ t₀) (hγ₀ : γ t₀ = p)
    (hx : HasDerivAt (fun t => F (γ t)) v t₀)
    (hlinear : ∀ᶠ t in nhds t₀,
      edist p (γ t) = (c : ENNReal) * ENNReal.ofReal |t - t₀|) :
    g v v = (c : ℝ) ^ 2 := by
  apply Helpers.energy_eq_of_normal_radius_derivative g B e he0 he hi hmetric hx
    (by rw [hγ₀, hp])
  have hγV : ∀ᶠ t in nhds t₀, γ t ∈ V :=
    hγ.preimage_mem_nhds (by simpa only [hγ₀] using hV)
  filter_upwards [hγV, hlinear] with t ht hlin
  have hh := (hdist (γ t) ht).symm.trans hlin
  have hh' : Real.sqrt (B (e.symm (F (γ t))) (e.symm (F (γ t)))) =
      (c : ℝ) * |t - t₀| := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (mul_nonneg c.coe_nonneg (abs_nonneg _))).mp
    simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hh
  calc
    _ = (Real.sqrt (B (e.symm (F (γ t))) (e.symm (F (γ t))))) ^ 2 :=
      (Real.sq_sqrt (hB _)).symm
    _ = (c : ℝ) ^ 2 * (t - t₀) ^ 2 := by rw [hh', mul_pow, sq_abs]
theorem Helpers.exists_coordinate_normal_radius_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} (hp : p ∈ U) :
    ∃ τ > (0 : ℝ), ∃ r > (0 : ℝ), ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e (Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball 0 r, e v ∈ U ∧ ∀ w,
        g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = τ ^ 2 * g p v w) ∧
      ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∩ e.target ∧
        (∀ z ∈ W, e.symm z ∈ Metric.ball 0 r) ∧
        ContDiffOn ℝ 1 e.symm W ∧
        (∀ δ > (0 : ℝ), ContDiffOn ℝ 1
          (fun z => Real.sqrt ((τ ^ 2 • g p) (e.symm z) (e.symm z) + δ)) W) ∧
        (∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w,
          |fderiv ℝ (fun y => Real.sqrt
            ((τ ^ 2 • g p) (e.symm y) (e.symm y) + δ)) z w| ≤
              Real.sqrt (g z w w)) := by
  obtain ⟨τ, hτ, r, hr, e, he0, hpt, hep, he, hei, hGauss⟩ :=
    Helpers.exists_coordinate_normal_chart hU (hg.of_le (by simp)) hsym hΓ hKoszul hp
  obtain ⟨A, hAp, hInvA⟩ := hei.contDiffOn (m := 1) (by simp) (by simp)
  obtain ⟨A', hA'A, hA', hpA'⟩ := mem_nhds_iff.mp hAp
  let W := (A' ∩ U) ∩ (e.target ∩ e.symm ⁻¹' Metric.ball 0 r)
  have hW : IsOpen W :=
    (hA'.inter hU).inter (e.isOpen_inter_preimage_symm Metric.isOpen_ball)
  have hInvp : e.symm p = 0 := by rw [← hep]; exact e.left_inv he0
  have hpW : p ∈ W :=
    ⟨⟨hpA', hp⟩, hpt, by
      change e.symm p ∈ Metric.ball 0 r
      rw [hInvp]
      exact Metric.mem_ball_self hr⟩
  have hInvW : ContDiffOn ℝ 1 e.symm W :=
    hInvA.mono (fun z hz => hA'A hz.1.1)
  let B : E →L[ℝ] E →L[ℝ] ℝ := τ ^ 2 • g p
  have hBsym : ∀ u v, B u v = B v u := by
    intro u v
    change τ ^ 2 * g p u v = τ ^ 2 * g p v u
    rw [hsym p u v]
  have hnonneg : ∀ z ∈ U, ∀ v, 0 ≤ g z v v := by
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos z hz v hv).le
  have hBn : ∀ v, 0 ≤ B v v := by
    intro v
    change 0 ≤ τ ^ 2 * g p v v
    exact mul_nonneg (sq_nonneg _) (hnonneg p hp v)
  refine ⟨τ, hτ, r, hr, e, he0, hep, he, hGauss, W, hW, hpW,
    (fun z hz => ⟨hz.1.2, hz.2.1⟩), (fun z hz => hz.2.2), hInvW, ?_, ?_⟩
  · intro δ hδ
    have hQ : ContDiffOn ℝ 1 (fun z => B (e.symm z) (e.symm z) + δ) W :=
      (((contDiffOn_const (c := B)).clm_apply hInvW).clm_apply hInvW).add
        contDiffOn_const
    exact hQ.sqrt (fun z _ => ne_of_gt (by linarith [hBn (e.symm z)]))
  · intro δ hδ z hz w
    have hF : DifferentiableAt ℝ e.symm z :=
      (hInvW.contDiffAt (hW.mem_nhds hz)).differentiableAt_one
    have hE : DifferentiableAt ℝ e (e.symm z) :=
      (he.contDiffAt (Metric.isOpen_ball.mem_nhds hz.2.2)).differentiableAt (by simp)
    have hcomp := hE.hasFDerivAt.comp z hF.hasFDerivAt
    have hEq : (fun y => e (e.symm y)) =ᶠ[nhds z] id :=
      e.eventually_right_inverse hz.2.1
    have hid := hcomp.congr_of_eventuallyEq hEq.symm
    have hcancel : ∀ u, fderiv ℝ e (e.symm z) (fderiv ℝ e.symm z u) = u := by
      intro u
      exact congrArg (fun L : E →L[ℝ] E => L u) (hid.unique (hasFDerivAt_id z))
    apply Helpers.regularized_radius_fderiv_bound_of_gauss (g z) B
      (hsym z) (hnonneg z hz.1.2) hBsym hF (fderiv ℝ e (e.symm z)) ?_ hcancel hδ w
    intro u
    simpa only [e.right_inv hz.2.1, B, smul_apply, smul_eq_mul] using
      (hGauss (e.symm z) hz.2.2).2 u
theorem Helpers.exists_riemannian_normal_distance_data_of_local_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p : M)
    (hLower : ∀ (g : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2) →
      ∀ (B : E →L[ℝ] E →L[ℝ] ℝ), (∀ v : E, v ≠ 0 → 0 < B v v) →
      ∀ (e : OpenPartialHomeomorph E E), (0 : E) ∈ e.source →
      e 0 = extChartAt I p p → ∀ (W : Set E), IsOpen W → extChartAt I p p ∈ W →
      (∀ δ > (0 : ℝ), ContDiffOn ℝ 1
        (fun z => Real.sqrt (B (e.symm z) (e.symm z) + δ)) W) →
      (∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w : E,
        |fderiv ℝ (fun y => Real.sqrt (B (e.symm y) (e.symm y) + δ)) z w| ≤
          Real.sqrt (g z w w)) →
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
        V ⊆ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W ∧
        V ⊆ (extChartAt I p) ⁻¹' e.target ∧ ∀ q ∈ V,
          ENNReal.ofReal (Real.sqrt
            (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) ≤
              Manifold.riemannianEDist I p q)
    (hLipComp : ∀ (f : E → E), ContDiffAt ℝ 1 f (extChartAt I p p) →
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V) :
    ∃ r > (0 : ℝ), ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
      ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∃ e : OpenPartialHomeomorph E E,
        ContinuousOn g (extChartAt I p).target ∧
        (∀ z u v, g z u v = g z v u) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v,
          g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I p).symm (Set.range I) z v‖ ^ 2) ∧
        (∀ u v, B u v = B v u) ∧ (∀ v, v ≠ 0 → 0 < B v v) ∧
        Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p p ∧
        ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
        (∀ v ∈ Metric.ball 0 r, e v ∈ (extChartAt I p).target ∧ ∀ w,
          g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = B v w) ∧
        ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ e.target ∧
          ContDiffOn ℝ 1 e.symm W ∧
          ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
            (∀ q ∈ V, extChartAt I p q ∈ W ∧
              e.symm (extChartAt I p q) ∈ Metric.ball 0 r) ∧
            (∃ K : NNReal, LipschitzOnWith K (fun q => e.symm (extChartAt I p q)) V) ∧
            ∀ q ∈ V, edist p q = ENNReal.ofReal
              (Real.sqrt (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) := by
  obtain ⟨g, Γ, hg, hsym, hpos, hnorm, hΓ, hKoszul⟩ :=
    Helpers.exists_smooth_coordinate_metric_and_koszul I p
  obtain ⟨τ, hτ, r, hr, e, he0, hep, he, hGauss, W, hW, hpW,
      hWU, hWr, hInv, hsmooth, hbound⟩ :=
    Helpers.exists_coordinate_normal_radius_control (isOpen_extChartAt_target p)
      hg hsym hpos hΓ hKoszul (mem_extChartAt_target p)
  obtain ⟨s, hs, hsource⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  let r' : ℝ := min r s
  have hr' : 0 < r' := lt_min hr hs
  have hrr : Metric.ball (0 : E) r' ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left r s)
  have hrs : Metric.ball (0 : E) r' ⊆ e.source :=
    (Metric.ball_subset_ball (min_le_right r s)).trans hsource
  let W' := W ∩ (e.target ∩ e.symm ⁻¹' Metric.ball 0 r')
  have hW' : IsOpen W' :=
    hW.inter (e.isOpen_inter_preimage_symm Metric.isOpen_ball)
  have hInvp : e.symm (extChartAt I p p) = 0 := by
    rw [← hep]
    exact e.left_inv he0
  have hpW' : extChartAt I p p ∈ W' := by
    refine ⟨hpW, (hWU hpW).2, ?_⟩
    change e.symm (extChartAt I p p) ∈ Metric.ball 0 r'
    rw [hInvp]
    exact Metric.mem_ball_self hr'
  let B : E →L[ℝ] E →L[ℝ] ℝ := τ ^ 2 • g (extChartAt I p p)
  have hBpos : ∀ v : E, v ≠ 0 → 0 < B v v := by
    intro v hv
    exact mul_pos (sq_pos_of_pos hτ) (hpos _ (mem_extChartAt_target p) v hv)
  have hBsym : ∀ u v, B u v = B v u := by
    intro u v
    change τ ^ 2 * g _ u v = τ ^ 2 * g _ v u
    rw [hsym]
  have hradial : ∀ v ∈ Metric.ball 0 r', e v ∈ (extChartAt I p).target ∧ ∀ w,
      g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = B v w := by
    intro v hv
    exact hGauss v (hrr hv)
  obtain ⟨V, hV, hpV, hVW', hVe, hdist⟩ :=
    hLower g hnorm B hBpos e he0 hep
      W' hW' hpW'
      (fun δ hδ => (hsmooth δ hδ).mono Set.inter_subset_left)
      (fun δ hδ z hz w => hbound δ hδ z hz.1 w)
  obtain ⟨A, hA, hpA, hAsource, K, hLip⟩ :=
    hLipComp e.symm
      (hInv.contDiffAt (hW.mem_nhds hpW))
  refine ⟨r', hr', g, B, e, hg.continuousOn, hsym, hpos, hnorm, hBsym, hBpos,
    hrs, hep, he.mono hrr, hradial, W, hW, hpW, (fun z hz => (hWU hz).2), hInv,
    V ∩ A, hV.inter hA, ⟨hpV, hpA⟩, (fun q hq => (hVW' hq.1).1), ?_,
    ⟨K, hLip.mono Set.inter_subset_right⟩, ?_⟩
  · intro q hq
    exact ⟨(hVW' hq.1).2.1, (hVW' hq.1).2.2.2⟩
  · intro q hq
    rw [IsRiemannianManifold.out (I := I)]
    apply le_antisymm ?_ (hdist q hq.1)
    have hu : e.symm (extChartAt I p q) ∈ Metric.ball 0 r' := (hVW' hq.1).2.2.2
    have hn : 0 ≤ B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)) := by
      rw [← (hradial _ hu).2 _, hnorm _ (hradial _ hu).1]
      exact sq_nonneg _
    have hupper := Helpers.riemannianEDist_radial_le I p g hg.continuousOn hnorm B e r'
      ((he.mono hrr).of_le (by simp)) (fun v hv => (hradial v hv).1)
      (fun v hv => (hradial v hv).2 v) (e.symm (extChartAt I p q)) hu hn
    simpa only [hep, e.right_inv (hVe hq.1),
      (extChartAt I p).left_inv (mem_extChartAt_source p),
      (extChartAt I p).left_inv (hVW' hq.1).1] using hupper
theorem Helpers.edist_extChartAt_le_mul_pathELength
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    (p : M) (U : Set M) (hU : U ⊆ (extChartAt I p).source) (C : NNReal)
    (hC : ∀ x ∈ U, ∀ v : TangentSpace I x,
      @enorm E _ (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v) ≤ C * ‖v‖ₑ)
    (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 γ (Set.Icc a b))
    (hγU : Set.MapsTo γ (Set.Icc a b) U) :
    edist (extChartAt I p (γ a)) (extChartAt I p (γ b)) ≤
      C * Manifold.pathELength I γ a b := by
  letI : (x : E) → NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ E) x) :=
    fun x => normedAddCommGroupTangentSpaceVectorSpace x
  letI : (x : E) → NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ E) x) :=
    fun x => normedSpaceTangentSpaceVectorSpace x
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let f := extChartAt I p ∘ γ
  have hf : ContDiffOn ℝ 1 f (Set.Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp
      (contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H p).source) hγ (fun t ht => by
        simpa only [Set.mem_preimage, extChartAt_source] using hU (hγU ht)))
  rw [edist_comm, edist_eq_enorm_sub]
  calc
    ‖f b - f a‖ₑ ≤ ∫⁻ t in Set.Icc a b, ‖derivWithin f (Set.Icc a b) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hf hab.le
    _ = ∫⁻ t in Set.Icc a b,
        ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
          f (Set.Icc a b) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Set.Icc a b, C *
        ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) I γ (Set.Icc a b) t 1‖ₑ := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd := mfderiv_comp_mfderivWithin t
        (mdifferentiableAt_extChartAt (by
          simpa only [Set.mem_preimage, extChartAt_source] using hU (hγU ht)))
        ((hγ t ht).mdifferentiableWithinAt one_ne_zero)
        (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_Icc hab t ht))
      change ‖mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
        (extChartAt I p ∘ γ) (Set.Icc a b) t 1‖ₑ ≤ _
      rw [hd, ContinuousLinearMap.comp_apply]
      exact hC _ (hγU ht) _
    _ = C * Manifold.pathELength I γ a b := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
theorem Helpers.exists_lipschitzOnWith_extChartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [LocallyCompactSpace M] [ConnectedSpace M] (p : M) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
      ∃ K : NNReal, LipschitzOnWith K (extChartAt I p) V := by
  letI : MetricSpace M := EMetricSpace.toMetricSpace Helpers.edist_ne_top_of_preconnected
  letI : (x : E) → NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ E) x) :=
    fun x => normedAddCommGroupTangentSpaceVectorSpace x
  letI : (x : E) → NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ E) x) :=
    fun x => normedSpaceTangentSpaceVectorSpace x
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderiv_extChartAt_lt I p
  have hCpos' : (0 : ℝ) < C := hCpos
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hC (extChartAt_source_mem_nhds (I := I) p))
  have hbound : ∀ x ∈ Metric.ball p r, ∀ v : TangentSpace I x,
      @enorm E _ (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I p) x v) ≤
        C * ‖v‖ₑ := by
    intro x hx v
    apply (ContinuousLinearMap.le_opENorm _ _).trans
    gcongr
    exact (hrU hx).1.le
  have hsource : Metric.ball p r ⊆ (extChartAt I p).source := fun x hx => (hrU hx).2
  have hnb : Metric.ball p (r / 4) ∩
      (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) ((C : ℝ) * r / 4) ∈ nhds p :=
    Filter.inter_mem (Metric.ball_mem_nhds p (by positivity))
      ((continuousAt_extChartAt p).preimage_mem_nhds
        (Metric.ball_mem_nhds _ (by positivity)))
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hnb
  have hsmall : Metric.ball p ε ⊆ Metric.ball p r := by
    intro x hx
    have := Metric.mem_ball.mp (hεV hx).1
    exact Metric.mem_ball.mpr (by linarith)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    fun x hx => hsource (hsmall hx), C, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_contra h
  have hlt : (C : ℝ) * dist x y < dist (extChartAt I p x) (extChartAt I p y) :=
    lt_of_not_ge h
  have hquot : dist x y < dist (extChartAt I p x) (extChartAt I p y) / C :=
    (lt_div_iff₀ hCpos').mpr (by simpa only [mul_comm] using hlt)
  have hpos : 0 < dist (extChartAt I p x) (extChartAt I p y) / C :=
    (dist_nonneg.trans_lt hquot)
  have hriem : Manifold.riemannianEDist I x y <
      ENNReal.ofReal (dist (extChartAt I p x) (extChartAt I p y) / C) := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hquot
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hriem
  have hfinite : Manifold.pathELength I γ 0 1 ≠ ⊤ :=
    (hlen.trans ENNReal.ofReal_lt_top).ne
  have hlen' : (Manifold.pathELength I γ 0 1).toReal <
      dist (extChartAt I p x) (extChartAt I p y) / C := by
    have := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlen
    simpa only [ENNReal.toReal_ofReal hpos.le] using this
  by_cases hstay : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) (Metric.ball p r)
  · have hb := Helpers.edist_extChartAt_le_mul_pathELength I p (Metric.ball p r)
      hsource C hbound γ 0 1 zero_le_one hγ hstay
    have hb' := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite) hb
    simp only [hγ0, hγ1, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_mul, ENNReal.coe_toReal] at hb'
    have hlen'' := (lt_div_iff₀ hCpos').mp hlen'
    nlinarith
  · obtain ⟨t, ht, htU⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ Metric.ball p r := by
      simpa only [Set.MapsTo, not_forall, exists_prop] using hstay
    have hrle : r ≤ dist (γ t) p := not_lt.mp (by simpa only [Metric.mem_ball] using htU)
    have hpre : edist x (γ t) ≤ Manifold.pathELength I γ 0 1 := by
      rw [IsRiemannianManifold.out (I := I)]
      exact (Manifold.riemannianEDist_le_pathELength
        (hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1).trans
          (Manifold.pathELength_mono le_rfl ht.2)
    have hpre' := ENNReal.toReal_mono hfinite hpre
    simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hpre'
    have hx' := Metric.mem_ball.mp (hεV hx).1
    have hfx := Metric.mem_ball.mp (hεV hx).2
    have hfy := Metric.mem_ball.mp (hεV hy).2
    have hdiam := dist_triangle (extChartAt I p x) (extChartAt I p p) (extChartAt I p y)
    rw [dist_comm (extChartAt I p p)] at hdiam
    have htri := dist_triangle (γ t) x p
    rw [dist_comm (γ t) x] at htri
    have hlen'' := (lt_div_iff₀ hCpos').mp hlen'
    nlinarith
theorem Helpers.exists_lipschitzOnWith_smooth_chart_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) (f : E → E) (hf : ContDiffAt ℝ 1 f (extChartAt I p p)) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
      ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V := by
  obtain ⟨U, hU, hpU, hUsource, K, hK⟩ := Helpers.exists_lipschitzOnWith_extChartAt I M p
  obtain ⟨L, A, hA, hL⟩ := hf.exists_lipschitzOnWith
  have hpre : (extChartAt I p) ⁻¹' A ∈ nhds p :=
    (continuousAt_extChartAt p).preimage_mem_nhds hA
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hpU) hpre)
  refine ⟨V, hV, hpV, (fun q hq => hUsource (hVU hq).1), L * K, ?_⟩
  exact hL.comp (hK.mono (fun q hq => (hVU hq).1)) (fun q hq => (hVU hq).2)
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
theorem Helpers.exists_riemannian_normal_distance_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p : M) :
    ∃ r > (0 : ℝ), ∃ g : E → E →L[ℝ] E →L[ℝ] ℝ,
      ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∃ e : OpenPartialHomeomorph E E,
        ContinuousOn g (extChartAt I p).target ∧
        (∀ z u v, g z u v = g z v u) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v) ∧
        (∀ z ∈ (extChartAt I p).target, ∀ v,
          g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I p).symm (Set.range I) z v‖ ^ 2) ∧
        (∀ u v, B u v = B v u) ∧ (∀ v, v ≠ 0 → 0 < B v v) ∧
        Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p p ∧
        ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
        (∀ v ∈ Metric.ball 0 r, e v ∈ (extChartAt I p).target ∧ ∀ w,
          g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = B v w) ∧
        ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧ W ⊆ e.target ∧
          ContDiffOn ℝ 1 e.symm W ∧
          ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
            (∀ q ∈ V, extChartAt I p q ∈ W ∧
              e.symm (extChartAt I p q) ∈ Metric.ball 0 r) ∧
            (∃ K : NNReal, LipschitzOnWith K (fun q => e.symm (extChartAt I p q)) V) ∧
            ∀ q ∈ V, edist p q = ENNReal.ofReal
              (Real.sqrt (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) := by
  exact Helpers.exists_riemannian_normal_distance_data_of_local_bounds I M p
    (Helpers.exists_normal_radius_lower_bound I p)
    (Helpers.exists_lipschitzOnWith_smooth_chart_comp I M p)
theorem Helpers.metric_speed_eq_of_hasDerivAt_center_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) {γ : ℝ → M} {t₀ : ℝ} {c : NNReal} {v : E}
    (hγ : ContinuousAt γ t₀) (hγ₀ : γ t₀ = p)
    (hx : HasDerivAt (fun t => extChartAt I p (γ t)) v t₀)
    (hlinear : ∀ᶠ t in nhds t₀,
      edist p (γ t) = (c : ENNReal) * ENNReal.ofReal |t - t₀|) :
    ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range I) (extChartAt I p p) v‖ ^ 2 = (c : ℝ) ^ 2 := by
  obtain ⟨r, hr, g, B, e, hg, hsym, hpos, hnorm, hBsym, hBpos, hsource,
      hep, he, hGauss, W, hW, hpW, hWt, hInv, V, hV, hpV, hVs, hVi, hLip, hdist⟩ :=
    Helpers.exists_riemannian_normal_distance_data I M p
  have hz : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hmetric : ∀ w, g (e 0) (fderiv ℝ e 0 w) (fderiv ℝ e 0 w) = B w w :=
    Helpers.radial_metric_at_zero hr B hg (he.of_le (by simp))
      (fun u hu => (hGauss u hu).1) (fun u hu => (hGauss u hu).2 u)
  have hB : ∀ w, 0 ≤ B w w := by
    intro w
    rw [← hmetric w, hnorm _ (hGauss 0 hz).1]
    exact sq_nonneg _
  have hEDiff : DifferentiableAt ℝ e 0 :=
    (he.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hIDiff : DifferentiableAt ℝ e.symm (e 0) := by
    rw [hep]
    exact (hInv.contDiffAt (hW.mem_nhds hpW)).differentiableAt_one
  have hs := Helpers.energy_eq_of_local_normal_distance (extChartAt I p) p (g (e 0)) B e
    (hsource hz) hep.symm hEDiff hIDiff hmetric hB (hV.mem_nhds hpV) hdist
    hγ hγ₀ hx hlinear
  rw [hep, hnorm _ (mem_extChartAt_target p)] at hs
  exact hs
theorem Helpers.metric_speed_eq_of_hasDerivAt_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) {γ : ℝ → M} {t₀ : ℝ} {c : NNReal} {v : E}
    (hγ : ContinuousAt γ t₀) (hp : γ t₀ ∈ (extChartAt I p).source)
    (hx : HasDerivAt (fun t => extChartAt I p (γ t)) v t₀)
    (hlinear : ∀ᶠ t in nhds t₀,
      edist (γ t₀) (γ t) = (c : ENNReal) * ENNReal.ofReal |t - t₀|) :
    ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range I) (extChartAt I p (γ t₀)) v‖ ^ 2 = (c : ℝ) ^ 2 := by
  exact Helpers.chart_speed_eq_of_center_chart_speed I p hγ hp hx
    (fun w hw => Helpers.metric_speed_eq_of_hasDerivAt_center_chart I M (γ t₀)
      hγ rfl hw hlinear)
theorem Helpers.exists_riemannian_radial_rigidity_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p : M) :
    ∃ r > (0 : ℝ), ∃ e : OpenPartialHomeomorph E E,
      Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p p ∧
      ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∀ (γ : ℝ → M) (c : NNReal) (A D a b t₀ : ℝ),
          0 < c → A < a → a ≤ b → b < D → t₀ < a →
          Helpers.MetricLocallyLinear γ c (Set.Ioo A D) →
          Set.MapsTo γ (Set.Icc a b) V →
          (∀ t ∈ Set.Icc a b, edist p (γ t) =
            (c : ENNReal) * ENNReal.ofReal (t - t₀)) →
          ∃ w : E, ∀ t ∈ Set.Icc a b,
            e.symm (extChartAt I p (γ t)) = (t - t₀) • w ∧
            γ t = (extChartAt I p).symm (e ((t - t₀) • w)) := by
  obtain ⟨r, hr, g, B, e, hg, hsym, hpos, hnorm, hBsym, hBpos, hsource,
      hep, he, hGauss, W, hW, hpW, hWt, hInv, V, hV, hpV, hVs, hVi,
      ⟨K, hLip⟩, hdist⟩ := Helpers.exists_riemannian_normal_distance_data I M p
  refine ⟨r, hr, e, hsource, hep, he, V, hV, hpV, hVs, ?_⟩
  intro γ c A D a b t₀ hc hAa hab hbD ht₀ hlin hγV hAnchor
  have hSub : Set.Icc a b ⊆ Set.Ioo A D := by
    intro t ht
    exact ⟨hAa.trans_le ht.1, ht.2.trans_lt hbD⟩
  have hMaps (t : ℝ) (ht : t ∈ Set.Icc a b) :
      extChartAt I p (γ t) ∈ e.target ∧
        e.symm (extChartAt I p (γ t)) ∈ Metric.ball 0 r :=
    ⟨hWt (hVi (γ t) (hγV ht)).1, (hVi (γ t) (hγV ht)).2⟩
  have hSharp (t : ℝ) (ht : t ∈ Set.Icc a b) (v : E)
      (hv : HasDerivAt (fun s => extChartAt I p (γ s)) v t) :
      g (extChartAt I p (γ t)) v v = (c : ℝ) ^ 2 := by
    rw [hnorm _ ((extChartAt I p).map_source (hVs (hγV ht))) v]
    exact Helpers.metric_speed_eq_of_hasDerivAt_chart I M p
      (hlin.continuousAt isOpen_Ioo (hSub ht)) (hVs (hγV ht)) hv
      (hlin.eventually_edist_eq isOpen_Ioo (hSub ht))
  have hRadius (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (B (e.symm (extChartAt I p (γ t))) (e.symm (extChartAt I p (γ t)))) =
        (c : ℝ) * (t - t₀) := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (mul_nonneg c.coe_nonneg (by linarith [ht.1]))).mp
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ← hdist (γ t) (hγV ht)]
    exact hAnchor t ht
  obtain ⟨w, hw⟩ := Helpers.radial_of_normal_coordinates_sharp_speed e g B
    (fun t => extChartAt I p (γ t)) (K * c) r a b t₀ c hBsym hc ht₀ hab
    (he.of_le (by simp)) hMaps
    (fun t ht => (continuousAt_extChartAt' (hVs (hγV ht))).comp
      (hlin.continuousAt isOpen_Ioo (hSub ht)))
    (fun t ht => (hInv.contDiffAt (hW.mem_nhds (hVi (γ t) (hγV ht)).1)).differentiableAt_one)
    (hLip.comp ((hlin.lipschitzOn Set.ordConnected_Ioo).mono hSub) hγV)
    (fun t _ u v => hsym _ u v)
    (fun t ht v hv => hpos _ ((extChartAt I p).map_source (hVs (hγV ht))) v hv)
    (fun t ht w => by
      have hh := (hGauss _ (hMaps t ht).2).2 w
      simpa only [e.right_inv (hMaps t ht).1] using hh)
    hSharp hRadius
  refine ⟨w, fun t ht => ⟨hw t ht, ?_⟩⟩
  rw [← hw t ht, e.right_inv (hMaps t ht).1]
  exact ((extChartAt I p).left_inv (hVs (hγV ht))).symm
theorem Helpers.exists_riemannian_right_radial_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = extChartAt I (γ t₀) (γ t₀) ∧
      ContDiffAt ℝ ∞ e 0 ∧ ∃ ε > (0 : ℝ), ∃ w : E,
        ∀ t ∈ Set.Icc t₀ (t₀ + ε),
          γ t = (extChartAt I (γ t₀)).symm (e ((t - t₀) • w)) := by
  obtain ⟨r, hr, e, hsource, hep, he, V, hV, hpV, hVs, hRig⟩ :=
    Helpers.exists_riemannian_radial_rigidity_chart I M (γ t₀)
  obtain ⟨δ, hδ, hEq⟩ := hlin.on_open isOpen_Ioo ht₀
  have hN : Set.Ioo A D ∩
      (Set.Ioo (t₀ - δ) (t₀ + δ) ∩ γ ⁻¹' V) ∈ nhds t₀ := by
    exact Filter.inter_mem (isOpen_Ioo.mem_nhds ht₀)
      (Filter.inter_mem (Ioo_mem_nhds (by linarith) (by linarith))
        ((hlin.continuousAt isOpen_Ioo ht₀).preimage_mem_nhds (hV.mem_nhds hpV)))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hN
  have htime (t : ℝ) (ht : t ∈ Set.Ioo t₀ (t₀ + d)) :
      t ∈ Set.Ioo A D ∩ (Set.Ioo (t₀ - δ) (t₀ + δ) ∩ γ ⁻¹' V) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  have hCompact : ∀ a b : ℝ, t₀ < a → a ≤ b → b < t₀ + d →
      ∃ w : E, ∀ t ∈ Set.Icc a b,
        e.symm (extChartAt I (γ t₀) (γ t)) = (t - t₀) • w ∧
        γ t = (extChartAt I (γ t₀)).symm (e ((t - t₀) • w)) := by
    intro a b hta hab hbd
    have hI (t : ℝ) (ht : t ∈ Set.Icc a b) : t ∈ Set.Ioo t₀ (t₀ + d) :=
      ⟨hta.trans_le ht.1, ht.2.trans_lt hbd⟩
    apply hRig γ c A D a b t₀ hc
      (htime a ⟨hta, hab.trans_lt hbd⟩).1.1 hab
      (htime b ⟨hta.trans_le hab, hbd⟩).1.2 hta hlin
      (fun t ht => (htime t (hI t ht)).2.2)
    intro t ht
    have hh := hEq t₀ t (by constructor <;> linarith) (htime t (hI t ht)).2.1
    simpa only [abs_of_pos (sub_pos.mpr (hI t ht).1)] using hh
  have hzero : e.symm (extChartAt I (γ t₀) (γ t₀)) = 0 := by
    rw [← hep, e.left_inv (hsource (Metric.mem_ball_self hr))]
  have hγzero : γ t₀ = (extChartAt I (γ t₀)).symm (e 0) := by
    rw [hep]
    exact ((extChartAt I (γ t₀)).left_inv (mem_extChartAt_source (γ t₀))).symm
  obtain ⟨w, hw⟩ := Helpers.right_radial_germ_of_compact_radial
    (fun t => e.symm (extChartAt I (γ t₀) (γ t))) γ
    (fun v => (extChartAt I (γ t₀)).symm (e v)) t₀ d hd hzero hγzero hCompact
  exact ⟨e, hsource (Metric.mem_ball_self hr), hep,
    he.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    d / 2, half_pos hd, w, fun t ht => (hw t ht).2⟩
theorem Helpers.contDiffWithinAt_right_chart_of_metricLocallyLinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D) :
    ContDiffWithinAt ℝ ∞ (fun t => extChartAt I (γ t₀) (γ t)) (Set.Ici t₀) t₀ := by
  obtain ⟨e, he0, hep, he, ε, hε, w, hw⟩ :=
    Helpers.exists_riemannian_right_radial_germ I M hc hlin ht₀
  exact Helpers.contDiffWithinAt_chart_of_right_radial_germ I (γ t₀) hε hep he hw
theorem Helpers.contDiffWithinAt_left_chart_of_metricLocallyLinear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D) :
    ContDiffWithinAt ℝ ∞ (fun t => extChartAt I (γ t₀) (γ t)) (Set.Iic t₀) t₀ := by
  have hlin' : Helpers.MetricLocallyLinear (fun t => γ (-t)) c (Set.Ioo (-D) (-A)) := by
    apply hlin.reflect.mono
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ht₀' : -t₀ ∈ Set.Ioo (-D) (-A) := ⟨neg_lt_neg ht₀.2, neg_lt_neg ht₀.1⟩
  have hh := Helpers.contDiffWithinAt_right_chart_of_metricLocallyLinear I M hc hlin' ht₀'
  have hneg : ContDiffWithinAt ℝ ∞ (fun t : ℝ => -t) (Set.Iic t₀) t₀ :=
    contDiff_neg.contDiffWithinAt
  have hcomp := hh.comp t₀ hneg (fun t (ht : t ≤ t₀) => neg_le_neg ht)
  simpa only [Function.comp_def, neg_neg] using hcomp
theorem Helpers.metric_speed_eq_of_hasDerivWithinAt_center_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) {γ : ℝ → M} {t₀ : ℝ} {c : NNReal} {v : E} {s : Set ℝ}
    [Filter.NeBot (nhdsWithin t₀ s)] (hs : t₀ ∉ s)
    (hγ : ContinuousAt γ t₀) (hγ₀ : γ t₀ = p)
    (hx : HasDerivWithinAt (fun t => extChartAt I p (γ t)) v s t₀)
    (hlinear : ∀ᶠ t in nhdsWithin t₀ s,
      edist p (γ t) = (c : ENNReal) * ENNReal.ofReal |t - t₀|) :
    ‖mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range I) (extChartAt I p p) v‖ ^ 2 = (c : ℝ) ^ 2 := by
  obtain ⟨r, hr, g, B, e, hg, hsym, hpos, hnorm, hBsym, hBpos, hsource,
      hep, he, hGauss, W, hW, hpW, hWt, hInv, V, hV, hpV, hVs, hVi, hLip, hdist⟩ :=
    Helpers.exists_riemannian_normal_distance_data I M p
  have hz : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hmetric : ∀ w, g (e 0) (fderiv ℝ e 0 w) (fderiv ℝ e 0 w) = B w w :=
    Helpers.radial_metric_at_zero hr B hg (he.of_le (by simp))
      (fun u hu => (hGauss u hu).1) (fun u hu => (hGauss u hu).2 u)
  have hB : ∀ w, 0 ≤ B w w := by
    intro w
    rw [← hmetric w, hnorm _ (hGauss 0 hz).1]
    exact sq_nonneg _
  have hEDiff : DifferentiableAt ℝ e 0 :=
    (he.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hIDiff : DifferentiableAt ℝ e.symm (e 0) := by
    rw [hep]
    exact (hInv.contDiffAt (hW.mem_nhds hpW)).differentiableAt_one
  have hspeed := Helpers.energy_eq_of_local_normal_distance_within
    (extChartAt I p) p (g (e 0)) B e (hsource hz) hep.symm hEDiff hIDiff
    hmetric hB (hV.mem_nhds hpV) hdist hs hγ hγ₀ hx hlinear
  rw [hep, hnorm _ (mem_extChartAt_target p)] at hspeed
  exact hspeed
theorem Helpers.metricLocallyLinear_has_matching_chart_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D) :
    ∃ v : E,
      HasDerivWithinAt (fun t : ℝ => extChartAt I (γ t₀) (γ t)) v (Set.Ici t₀) t₀ ∧
      HasDerivWithinAt (fun t : ℝ => extChartAt I (γ t₀) (γ t)) v (Set.Iic t₀) t₀ := by
  apply Helpers.matching_chart_velocity_of_one_sided_regularity I hlin ht₀
    (Helpers.contDiffWithinAt_right_chart_of_metricLocallyLinear I M hc hlin ht₀)
    (Helpers.contDiffWithinAt_left_chart_of_metricLocallyLinear I M hc hlin ht₀)
  · intro v hv
    exact Helpers.metric_speed_eq_of_hasDerivWithinAt_center_chart I M (γ t₀)
      (s := Set.Ioi t₀) (by simp) (hlin.continuousAt isOpen_Ioo ht₀) rfl hv.Ioi_of_Ici
      ((hlin.eventually_edist_eq isOpen_Ioo ht₀).filter_mono nhdsWithin_le_nhds)
  · intro v hv
    exact Helpers.metric_speed_eq_of_hasDerivWithinAt_center_chart I M (γ t₀)
      (s := Set.Iio t₀) (by simp) (hlin.continuousAt isOpen_Ioo ht₀) rfl hv.Iio_of_Iic
      ((hlin.eventually_edist_eq isOpen_Ioo ht₀).filter_mono nhdsWithin_le_nhds)
theorem Helpers.exists_coordinate_normal_radius_control_with_radial_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U)
    {g : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g U)
    (hsym : ∀ x u v, g x u v = g x v u)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    (hKoszul : ∀ x ∈ U, ∀ u v w,
      2 * g x (Γ x u v) w = (fderiv ℝ g x u) v w +
        (fderiv ℝ g x v) u w - (fderiv ℝ g x w) u v)
    {p : E} (hp : p ∈ U) :
    ∃ τ > (0 : ℝ), ∃ r > (0 : ℝ), ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) e (Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball 0 r, e v ∈ U ∧ ∀ w,
        g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = τ ^ 2 * g p v w) ∧
      (∀ v ∈ Metric.ball 0 r, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => e (s • v)) (fderiv ℝ e (t • v) v) t ∧
        HasDerivAt (fun s : ℝ => fderiv ℝ e (s • v) v)
          (-(Γ (e (t • v)) (fderiv ℝ e (t • v) v)
            (fderiv ℝ e (t • v) v))) t) ∧
      ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∩ e.target ∧
        (∀ z ∈ W, e.symm z ∈ Metric.ball 0 r) ∧
        ContDiffOn ℝ 1 e.symm W ∧
        (∀ δ > (0 : ℝ), ContDiffOn ℝ 1
          (fun z => Real.sqrt ((τ ^ 2 • g p) (e.symm z) (e.symm z) + δ)) W) ∧
        (∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w,
          |fderiv ℝ (fun y => Real.sqrt
            ((τ ^ 2 • g p) (e.symm y) (e.symm y) + δ)) z w| ≤
              Real.sqrt (g z w w)) := by
  obtain ⟨τ, hτ, r, hr, e, he0, hpt, hep, he, hei, hGauss, hODE⟩ :=
    Helpers.exists_coordinate_normal_chart_with_radial_ode hU (hg.of_le (by simp)) hsym hΓ hKoszul hp
  obtain ⟨A, hAp, hInvA⟩ := hei.contDiffOn (m := 1) (by simp) (by simp)
  obtain ⟨A', hA'A, hA', hpA'⟩ := mem_nhds_iff.mp hAp
  let W := (A' ∩ U) ∩ (e.target ∩ e.symm ⁻¹' Metric.ball 0 r)
  have hW : IsOpen W :=
    (hA'.inter hU).inter (e.isOpen_inter_preimage_symm Metric.isOpen_ball)
  have hInvp : e.symm p = 0 := by rw [← hep]; exact e.left_inv he0
  have hpW : p ∈ W :=
    ⟨⟨hpA', hp⟩, hpt, by
      change e.symm p ∈ Metric.ball 0 r
      rw [hInvp]
      exact Metric.mem_ball_self hr⟩
  have hInvW : ContDiffOn ℝ 1 e.symm W :=
    hInvA.mono (fun z hz => hA'A hz.1.1)
  let B : E →L[ℝ] E →L[ℝ] ℝ := τ ^ 2 • g p
  have hBsym : ∀ u v, B u v = B v u := by
    intro u v
    change τ ^ 2 * g p u v = τ ^ 2 * g p v u
    rw [hsym p u v]
  have hnonneg : ∀ z ∈ U, ∀ v, 0 ≤ g z v v := by
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos z hz v hv).le
  have hBn : ∀ v, 0 ≤ B v v := by
    intro v
    change 0 ≤ τ ^ 2 * g p v v
    exact mul_nonneg (sq_nonneg _) (hnonneg p hp v)
  refine ⟨τ, hτ, r, hr, e, he0, hep, he, hGauss, hODE, W, hW, hpW,
    (fun z hz => ⟨hz.1.2, hz.2.1⟩), (fun z hz => hz.2.2), hInvW, ?_, ?_⟩
  · intro δ hδ
    have hQ : ContDiffOn ℝ 1 (fun z => B (e.symm z) (e.symm z) + δ) W :=
      (((contDiffOn_const (c := B)).clm_apply hInvW).clm_apply hInvW).add
        contDiffOn_const
    exact hQ.sqrt (fun z _ => ne_of_gt (by linarith [hBn (e.symm z)]))
  · intro δ hδ z hz w
    have hF : DifferentiableAt ℝ e.symm z :=
      (hInvW.contDiffAt (hW.mem_nhds hz)).differentiableAt_one
    have hE : DifferentiableAt ℝ e (e.symm z) :=
      (he.contDiffAt (Metric.isOpen_ball.mem_nhds hz.2.2)).differentiableAt (by simp)
    have hcomp := hE.hasFDerivAt.comp z hF.hasFDerivAt
    have hEq : (fun y => e (e.symm y)) =ᶠ[nhds z] id :=
      e.eventually_right_inverse hz.2.1
    have hid := hcomp.congr_of_eventuallyEq hEq.symm
    have hcancel : ∀ u, fderiv ℝ e (e.symm z) (fderiv ℝ e.symm z u) = u := by
      intro u
      exact congrArg (fun L : E →L[ℝ] E => L u) (hid.unique (hasFDerivAt_id z))
    apply Helpers.regularized_radius_fderiv_bound_of_gauss (g z) B
      (hsym z) (hnonneg z hz.1.2) hBsym hF (fderiv ℝ e (e.symm z)) ?_ hcancel hδ w
    intro u
    simpa only [e.right_inv hz.2.1, B, smul_apply, smul_eq_mul] using
      (hGauss (e.symm z) hz.2.2).2 u
theorem Helpers.exists_normal_radius_lower_bound_in_fixed_chart : open scoped Bundle in
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
      {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I 1 M]
      [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
      (p q₀ : M) (hq₀ : q₀ ∈ (extChartAt I p).source) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
      (hg : ∀ z ∈ (extChartAt I p).target, ∀ w : E,
        g z w w = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I p).symm (Set.range I) z w‖ ^ 2)
      (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
      (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
      (hep : e 0 = extChartAt I p q₀) (W : Set E) (hW : IsOpen W)
      (hpW : extChartAt I p q₀ ∈ W)
      (hsmooth : ∀ δ > (0 : ℝ), ContDiffOn ℝ 1
        (fun z => Real.sqrt (B (e.symm z) (e.symm z) + δ)) W)
      (hbound : ∀ δ > (0 : ℝ), ∀ z ∈ W, ∀ w : E,
        |fderiv ℝ (fun y => Real.sqrt (B (e.symm y) (e.symm y) + δ)) z w| ≤
          Real.sqrt (g z w w)),
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧
        V ⊆ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W ∧
        V ⊆ (extChartAt I p) ⁻¹' e.target ∧
        ∀ q ∈ V, ENNReal.ofReal
          (Real.sqrt (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) ≤
            Manifold.riemannianEDist I q₀ q := by
  intro E _ _ _ H _ I _ M _ _ _ _ _ p q₀ hq₀ g hg B hpos e he0 hep W hW hpW hsmooth hbound
  let c : OpenPartialHomeomorph M E := {
    toPartialEquiv := extChartAt I p
    open_source := isOpen_extChartAt_source p
    open_target := isOpen_extChartAt_target p
    continuousOn_toFun := continuousOn_extChartAt p
    continuousOn_invFun := continuousOn_extChartAt_symm p }
  let f : OpenPartialHomeomorph E M := e.trans c.symm
  have hf0 : (0 : E) ∈ f.source :=
    ⟨he0, by change e 0 ∈ (extChartAt I p).target; rw [hep]; exact (extChartAt I p).map_source hq₀⟩
  have hfp : f 0 = q₀ := by
    change (extChartAt I p).symm (e 0) = q₀
    rw [hep]
    exact (extChartAt I p).left_inv hq₀
  let A := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' W
  have hA : IsOpen A := isOpen_extChartAt_preimage' p hW
  obtain ⟨k,hk,V,hV,hV0,hVA,hVf,hfront,hinside⟩ :=
    Helpers.exists_inner_bilinear_radius_neighborhood B hpos f hf0 A hA
      (by rw [hfp]; exact ⟨hq₀,hpW⟩)
  have hpV : q₀ ∈ V := hfp ▸ hV0
  have hsub (q : M) (hq : q ∈ V) : q ∈ f.target := hVf (subset_closure hq)
  refine ⟨V,hV,hpV,(fun q hq => hVA (subset_closure hq)),
    (fun q hq => (hsub q hq).2),?_⟩
  intro q hq
  letI : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := fun x : M => TangentSpace I x) x
  apply Helpers.ofReal_radius_le_riemannianEDist_of_first_exit I A V hV hVA
    (fun y => Real.sqrt (B (f.symm y) (f.symm y))) q₀ q k hpV
  · have hzero : f.symm q₀ = 0 := by rw [← hfp]; exact f.left_inv hf0
    simp only [hzero,map_zero,ContinuousLinearMap.zero_apply,Real.sqrt_zero]
  · exact Real.sqrt_nonneg _
  · exact (hinside q hq).le
  · exact hfront
  · intro γ a b hab hγ hγA
    exact Helpers.enorm_sqrt_sub_le_pathELength_of_chart_regularized_bound I p g hg W hW
      (fun z => B (e.symm z) (e.symm z)) hsmooth hbound γ a b hab hγ hγA
theorem Helpers.exists_normal_distance_data_in_fixed_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p q₀ : M)
    (hq₀ : q₀ ∈ (extChartAt I p).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    (hLipComp : ∀ f : E → E, ContDiffAt ℝ 1 f (extChartAt I p q₀) →
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V) :
    ∃ r > (0 : ℝ), ∃ B : E →L[ℝ] E →L[ℝ] ℝ,
      ∃ e : OpenPartialHomeomorph E E,
        (∀ u v, B u v = B v u) ∧ (∀ v, v ≠ 0 → 0 < B v v) ∧
        Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p q₀ ∧
        ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
        (∀ v ∈ Metric.ball 0 r, e v ∈ (extChartAt I p).target ∧ ∀ w,
          g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = B v w) ∧
        (∀ v ∈ Metric.ball 0 r, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
          HasDerivAt (fun s : ℝ => e (s • v)) (fderiv ℝ e (t • v) v) t ∧
          HasDerivAt (fun s : ℝ => fderiv ℝ e (s • v) v)
            (-(Γ (e (t • v)) (fderiv ℝ e (t • v) v)
              (fderiv ℝ e (t • v) v))) t) ∧
        ∃ W : Set E, IsOpen W ∧ extChartAt I p q₀ ∈ W ∧ W ⊆ e.target ∧
          ContDiffOn ℝ 1 e.symm W ∧
          ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
            (∀ q ∈ V, extChartAt I p q ∈ W ∧
              e.symm (extChartAt I p q) ∈ Metric.ball 0 r) ∧
            (∃ K : NNReal, LipschitzOnWith K (fun q => e.symm (extChartAt I p q)) V) ∧
            ∀ q ∈ V, edist q₀ q = ENNReal.ofReal
              (Real.sqrt (B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)))) := by
  obtain ⟨τ, hτ, r, hr, e, he0, hep, he, hGauss, hODE, W, hW, hpW,
      hWU, hWr, hInv, hsmooth, hbound⟩ :=
    Helpers.exists_coordinate_normal_radius_control_with_radial_ode (isOpen_extChartAt_target p)
      hg hsym hpos hΓ hKoszul ((extChartAt I p).map_source hq₀)
  obtain ⟨s, hs, hsource⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds he0)
  let r' : ℝ := min r s
  have hr' : 0 < r' := lt_min hr hs
  have hrr : Metric.ball (0 : E) r' ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left r s)
  have hrs : Metric.ball (0 : E) r' ⊆ e.source :=
    (Metric.ball_subset_ball (min_le_right r s)).trans hsource
  let W' := W ∩ (e.target ∩ e.symm ⁻¹' Metric.ball 0 r')
  have hW' : IsOpen W' :=
    hW.inter (e.isOpen_inter_preimage_symm Metric.isOpen_ball)
  have hInvp : e.symm (extChartAt I p q₀) = 0 := by
    rw [← hep]
    exact e.left_inv he0
  have hpW' : extChartAt I p q₀ ∈ W' := by
    refine ⟨hpW, (hWU hpW).2, ?_⟩
    change e.symm (extChartAt I p q₀) ∈ Metric.ball 0 r'
    rw [hInvp]
    exact Metric.mem_ball_self hr'
  let B : E →L[ℝ] E →L[ℝ] ℝ := τ ^ 2 • g (extChartAt I p q₀)
  have hBpos : ∀ v : E, v ≠ 0 → 0 < B v v := by
    intro v hv
    exact mul_pos (sq_pos_of_pos hτ) (hpos _ ((extChartAt I p).map_source hq₀) v hv)
  have hBsym : ∀ u v, B u v = B v u := by
    intro u v
    change τ ^ 2 * g _ u v = τ ^ 2 * g _ v u
    rw [hsym]
  have hradial : ∀ v ∈ Metric.ball 0 r', e v ∈ (extChartAt I p).target ∧ ∀ w,
      g (e v) (fderiv ℝ e v v) (fderiv ℝ e v w) = B v w := by
    intro v hv
    exact hGauss v (hrr hv)
  obtain ⟨V, hV, hpV, hVW', hVe, hdist⟩ :=
    Helpers.exists_normal_radius_lower_bound_in_fixed_chart I p q₀ hq₀ g hnorm B hBpos e he0 hep
      W' hW' hpW'
      (fun δ hδ => (hsmooth δ hδ).mono Set.inter_subset_left)
      (fun δ hδ z hz w => hbound δ hδ z hz.1 w)
  obtain ⟨A, hA, hpA, hAsource, K, hLip⟩ :=
    hLipComp e.symm
      (hInv.contDiffAt (hW.mem_nhds hpW))
  refine ⟨r', hr', B, e, hBsym, hBpos,
    hrs, hep, he.mono hrr, hradial,
    (fun v hv => hODE v (hrr hv)), W, hW, hpW, (fun z hz => (hWU hz).2), hInv,
    V ∩ A, hV.inter hA, ⟨hpV, hpA⟩, (fun q hq => (hVW' hq.1).1), ?_,
    ⟨K, hLip.mono Set.inter_subset_right⟩, ?_⟩
  · intro q hq
    exact ⟨(hVW' hq.1).2.1, (hVW' hq.1).2.2.2⟩
  · intro q hq
    rw [IsRiemannianManifold.out (I := I)]
    apply le_antisymm ?_ (hdist q hq.1)
    have hu : e.symm (extChartAt I p q) ∈ Metric.ball 0 r' := (hVW' hq.1).2.2.2
    have hn : 0 ≤ B (e.symm (extChartAt I p q)) (e.symm (extChartAt I p q)) := by
      rw [← (hradial _ hu).2 _, hnorm _ (hradial _ hu).1]
      exact sq_nonneg _
    have hupper := Helpers.riemannianEDist_radial_le I p g hg.continuousOn hnorm B e r'
      ((he.mono hrr).of_le (by simp)) (fun v hv => (hradial v hv).1)
      (fun v hv => (hradial v hv).2 v) (e.symm (extChartAt I p q)) hu hn
    simpa only [hep, e.right_inv (hVe hq.1),
      (extChartAt I p).left_inv hq₀,
      (extChartAt I p).left_inv (hVW' hq.1).1] using hupper
theorem Helpers.exists_radial_rigidity_in_fixed_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p q₀ : M)
    (hq₀ : q₀ ∈ (extChartAt I p).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    (hLipComp : ∀ f : E → E, ContDiffAt ℝ 1 f (extChartAt I p q₀) →
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V) :
    ∃ r > (0 : ℝ), ∃ e : OpenPartialHomeomorph E E,
      Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p q₀ ∧
      ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball 0 r, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => e (s • v)) (fderiv ℝ e (t • v) v) t ∧
        HasDerivAt (fun s : ℝ => fderiv ℝ e (s • v) v)
          (-(Γ (e (t • v)) (fderiv ℝ e (t • v) v)
            (fderiv ℝ e (t • v) v))) t) ∧
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∀ (γ : ℝ → M) (c : NNReal) (A D a b t₀ : ℝ),
          0 < c → A < a → a ≤ b → b < D → t₀ < a →
          Helpers.MetricLocallyLinear γ c (Set.Ioo A D) →
          Set.MapsTo γ (Set.Icc a b) V →
          (∀ t ∈ Set.Icc a b, edist q₀ (γ t) =
            (c : ENNReal) * ENNReal.ofReal (t - t₀)) →
          ∃ w : E, ∀ t ∈ Set.Icc a b,
            e.symm (extChartAt I p (γ t)) = (t - t₀) • w ∧
            γ t = (extChartAt I p).symm (e ((t - t₀) • w)) := by
  obtain ⟨r, hr, B, e, hBsym, hBpos, hsource,
      hep, he, hGauss, hODE, W, hW, hpW, hWt, hInv, V, hV, hpV, hVs, hVi,
      ⟨K, hLip⟩, hdist⟩ := Helpers.exists_normal_distance_data_in_fixed_chart I M p q₀ hq₀ g Γ
    hg hsym hpos hnorm hΓ hKoszul hLipComp
  refine ⟨r, hr, e, hsource, hep, he, hODE, V, hV, hpV, hVs, ?_⟩
  intro γ c A D a b t₀ hc hAa hab hbD ht₀ hlin hγV hAnchor
  have hSub : Set.Icc a b ⊆ Set.Ioo A D := by
    intro t ht
    exact ⟨hAa.trans_le ht.1, ht.2.trans_lt hbD⟩
  have hMaps (t : ℝ) (ht : t ∈ Set.Icc a b) :
      extChartAt I p (γ t) ∈ e.target ∧
        e.symm (extChartAt I p (γ t)) ∈ Metric.ball 0 r :=
    ⟨hWt (hVi (γ t) (hγV ht)).1, (hVi (γ t) (hγV ht)).2⟩
  have hSharp (t : ℝ) (ht : t ∈ Set.Icc a b) (v : E)
      (hv : HasDerivAt (fun s => extChartAt I p (γ s)) v t) :
      g (extChartAt I p (γ t)) v v = (c : ℝ) ^ 2 := by
    rw [hnorm _ ((extChartAt I p).map_source (hVs (hγV ht))) v]
    exact Helpers.metric_speed_eq_of_hasDerivAt_chart I M p
      (hlin.continuousAt isOpen_Ioo (hSub ht)) (hVs (hγV ht)) hv
      (hlin.eventually_edist_eq isOpen_Ioo (hSub ht))
  have hRadius (t : ℝ) (ht : t ∈ Set.Icc a b) :
      Real.sqrt (B (e.symm (extChartAt I p (γ t))) (e.symm (extChartAt I p (γ t)))) =
        (c : ℝ) * (t - t₀) := by
    apply (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (mul_nonneg c.coe_nonneg (by linarith [ht.1]))).mp
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ← hdist (γ t) (hγV ht)]
    exact hAnchor t ht
  obtain ⟨w, hw⟩ := Helpers.radial_of_normal_coordinates_sharp_speed e g B
    (fun t => extChartAt I p (γ t)) (K * c) r a b t₀ c hBsym hc ht₀ hab
    (he.of_le (by simp)) hMaps
    (fun t ht => (continuousAt_extChartAt' (hVs (hγV ht))).comp
      (hlin.continuousAt isOpen_Ioo (hSub ht)))
    (fun t ht => (hInv.contDiffAt (hW.mem_nhds (hVi (γ t) (hγV ht)).1)).differentiableAt_one)
    (hLip.comp ((hlin.lipschitzOn Set.ordConnected_Ioo).mono hSub) hγV)
    (fun t _ u v => hsym _ u v)
    (fun t ht v hv => hpos _ ((extChartAt I p).map_source (hVs (hγV ht))) v hv)
    (fun t ht w => by
      have hh := (hGauss _ (hMaps t ht).2).2 w
      simpa only [e.right_inv (hMaps t ht).1] using hh)
    hSharp hRadius
  refine ⟨w, fun t ht => ⟨hw t ht, ?_⟩⟩
  rw [← hw t ht, e.right_inv (hMaps t ht).1]
  exact ((extChartAt I p).left_inv (hVs (hγV ht))).symm
theorem Helpers.exists_right_radial_germ_in_fixed_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p q₀ : M)
    (hq₀ : q₀ ∈ (extChartAt I p).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    (hLipComp : ∀ f : E → E, ContDiffAt ℝ 1 f (extChartAt I p q₀) →
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V)
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D)
    (hγ₀ : γ t₀ = q₀) :
    ∃ r > (0 : ℝ), ∃ e : OpenPartialHomeomorph E E,
      Metric.ball 0 r ⊆ e.source ∧ e 0 = extChartAt I p q₀ ∧
      ContDiffOn ℝ ∞ e (Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball 0 r, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => e (s • v)) (fderiv ℝ e (t • v) v) t ∧
        HasDerivAt (fun s : ℝ => fderiv ℝ e (s • v) v)
          (-(Γ (e (t • v)) (fderiv ℝ e (t • v) v)
            (fderiv ℝ e (t • v) v))) t) ∧
      ∃ ε > (0 : ℝ), ∃ w : E,
        ∀ t ∈ Set.Icc t₀ (t₀ + ε),
          γ t = (extChartAt I p).symm (e ((t - t₀) • w)) := by
  obtain ⟨r, hr, e, hsource, hep, he, hODE, V, hV, hpV, hVs, hRig⟩ :=
    Helpers.exists_radial_rigidity_in_fixed_chart I M p q₀ hq₀ g Γ
      hg hsym hpos hnorm hΓ hKoszul hLipComp
  obtain ⟨δ, hδ, hEq⟩ := hlin.on_open isOpen_Ioo ht₀
  have hN : Set.Ioo A D ∩
      (Set.Ioo (t₀ - δ) (t₀ + δ) ∩ γ ⁻¹' V) ∈ nhds t₀ := by
    exact Filter.inter_mem (isOpen_Ioo.mem_nhds ht₀)
      (Filter.inter_mem (Ioo_mem_nhds (by linarith) (by linarith))
        ((hlin.continuousAt isOpen_Ioo ht₀).preimage_mem_nhds (hV.mem_nhds (hγ₀.symm ▸ hpV))))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hN
  have htime (t : ℝ) (ht : t ∈ Set.Ioo t₀ (t₀ + d)) :
      t ∈ Set.Ioo A D ∩ (Set.Ioo (t₀ - δ) (t₀ + δ) ∩ γ ⁻¹' V) := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
    linarith [ht.2]
  have hCompact : ∀ a b : ℝ, t₀ < a → a ≤ b → b < t₀ + d →
      ∃ w : E, ∀ t ∈ Set.Icc a b,
        e.symm (extChartAt I p (γ t)) = (t - t₀) • w ∧
        γ t = (extChartAt I p).symm (e ((t - t₀) • w)) := by
    intro a b hta hab hbd
    have hI (t : ℝ) (ht : t ∈ Set.Icc a b) : t ∈ Set.Ioo t₀ (t₀ + d) :=
      ⟨hta.trans_le ht.1, ht.2.trans_lt hbd⟩
    apply hRig γ c A D a b t₀ hc
      (htime a ⟨hta, hab.trans_lt hbd⟩).1.1 hab
      (htime b ⟨hta.trans_le hab, hbd⟩).1.2 hta hlin
      (fun t ht => (htime t (hI t ht)).2.2)
    intro t ht
    have hh := hEq t₀ t (by constructor <;> linarith) (htime t (hI t ht)).2.1
    simpa only [hγ₀, abs_of_pos (sub_pos.mpr (hI t ht).1)] using hh
  have hzero : e.symm (extChartAt I p (γ t₀)) = 0 := by
    rw [hγ₀, ← hep, e.left_inv (hsource (Metric.mem_ball_self hr))]
  have hγzero : γ t₀ = (extChartAt I p).symm (e 0) := by
    rw [hγ₀, hep]
    exact ((extChartAt I p).left_inv hq₀).symm
  obtain ⟨w, hw⟩ := Helpers.right_radial_germ_of_compact_radial
    (fun t => e.symm (extChartAt I p (γ t))) γ
    (fun v => (extChartAt I p).symm (e v)) t₀ d hd hzero hγzero hCompact
  exact ⟨r, hr, e, hsource, hep, he, hODE,
    d / 2, half_pos hd, w, fun t ht => (hw t ht).2⟩
theorem Helpers.exists_right_spray_germ_in_fixed_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] (p q₀ : M)
    (hq₀ : q₀ ∈ (extChartAt I p).source)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    (hLipComp : ∀ f : E → E, ContDiffAt ℝ 1 f (extChartAt I p q₀) →
      ∃ V : Set M, IsOpen V ∧ q₀ ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ K : NNReal, LipschitzOnWith K (fun q => f (extChartAt I p q)) V)
    {γ : ℝ → M} {c : NNReal} {A D t₀ : ℝ} (hc : 0 < c)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo A D)) (ht₀ : t₀ ∈ Set.Ioo A D)
    (hγ₀ : γ t₀ = q₀) :
    ∃ ε > (0 : ℝ), ∃ x v : ℝ → E,
        (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
          x t ∈ (extChartAt I p).target ∧
          HasDerivAt x (v t) t ∧ HasDerivAt v (-(Γ (x t) (v t) (v t))) t) ∧
        ∀ t ∈ Set.Icc t₀ (t₀ + ε), extChartAt I p (γ t) = x t := by
  obtain ⟨r, hr, e, hsource, hep, he,
    hODE, θ, hθ, w, hw⟩ :=
    Helpers.exists_right_radial_germ_in_fixed_chart I M p q₀ hq₀ g Γ
      hg hsym hpos hnorm hΓ hKoszul hLipComp hc hlin ht₀ hγ₀
  obtain ⟨δ, hδ, hphase⟩ := Helpers.exists_deriv_radial_spray_of_normal_chart hr hODE w t₀
  let x : ℝ → E := fun t => e ((t - t₀) • w)
  let v : ℝ → E := fun t => fderiv ℝ e ((t - t₀) • w) w
  have htδ : t₀ ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := by constructor <;> linarith
  have hxt : x t₀ ∈ (extChartAt I p).target := by
    simpa only [x, sub_self, zero_smul, hep] using (extChartAt I p).map_source hq₀
  have hx : ContinuousAt x t₀ := (hphase t₀ htδ).1.continuousAt
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    (hx.preimage_mem_nhds ((isOpen_extChartAt_target (I := I) p).mem_nhds hxt))
  let ε := min θ (min δ ρ) / 2
  have hε : 0 < ε := half_pos (lt_min hθ (lt_min hδ hρ))
  have hεθ : ε ≤ θ := by dsimp [ε]; linarith [min_le_left θ (min δ ρ)]
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    linarith [min_le_right θ (min δ ρ), min_le_left δ ρ]
  have hερ : ε < ρ := by
    dsimp [ε]
    linarith [min_le_right θ (min δ ρ), min_le_right δ ρ]
  refine ⟨ε, hε, x, v, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := by
      constructor <;> linarith [ht.1, ht.2]
    refine ⟨hρsub ?_, (hphase t ht').1, (hphase t ht').2⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    rw [hw t ⟨ht.1, ht.2.trans (by linarith)⟩]
    exact (extChartAt I p).right_inv (hρsub (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]))
theorem Helpers.differentiableAt_fixed_chart_of_center_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ContinuousAt γ t₀) (hp : γ t₀ ∈ (extChartAt I p).source)
    (hx : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀) :
    DifferentiableAt ℝ (fun t => extChartAt I p (γ t)) t₀ := by
  have ht : extChartAt I (γ t₀) (γ t₀) ∈
      ((extChartAt I (γ t₀)).symm ≫ extChartAt I p).source := by
    refine ⟨mem_extChartAt_target (γ t₀), ?_⟩
    change (extChartAt I (γ t₀)).symm (extChartAt I (γ t₀) (γ t₀)) ∈
      (extChartAt I p).source
    rwa [(extChartAt I (γ t₀)).left_inv (mem_extChartAt_source (γ t₀))]
  have hchange : ContDiffWithinAt ℝ 1
      (extChartAt I p ∘ (extChartAt I (γ t₀)).symm) (Set.range I)
      (extChartAt I (γ t₀) (γ t₀)) := contDiffWithinAt_ext_coord_change p (γ t₀) ht
  have hchange' : ContDiffAt ℝ 1
      (extChartAt I p ∘ (extChartAt I (γ t₀)).symm)
      (extChartAt I (γ t₀) (γ t₀)) := by
    simpa only [I.range_eq_univ, contDiffWithinAt_univ] using hchange
  have heq : (fun t => extChartAt I p (γ t)) =ᶠ[nhds t₀]
      (fun t => (extChartAt I p ∘ (extChartAt I (γ t₀)).symm)
        (extChartAt I (γ t₀) (γ t))) := by
    filter_upwards [hγ.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (γ t₀))]
      with t ht
    simp only [Function.comp_apply, (extChartAt I (γ t₀)).left_inv ht]
  exact (hchange'.differentiableAt_one.comp t₀ hx).congr_of_eventuallyEq heq
theorem Helpers.exists_lipschitzOnWith_fixed_chart_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [EMetricSpace M] [ChartedSpace H M]
    (p q : M) (U : Set M) (hU : IsOpen U) (hq : q ∈ U)
    (hUsource : U ⊆ (extChartAt I p).source) (K : NNReal)
    (hLip : LipschitzOnWith K (extChartAt I p) U)
    (f : E → E) (hf : ContDiffAt ℝ 1 f (extChartAt I p q)) :
    ∃ V : Set M, IsOpen V ∧ q ∈ V ∧ V ⊆ (extChartAt I p).source ∧
      ∃ L : NNReal, LipschitzOnWith L (fun y => f (extChartAt I p y)) V := by
  obtain ⟨L, A, hA, hL⟩ := hf.exists_lipschitzOnWith
  have hpre : (extChartAt I p) ⁻¹' A ∈ nhds q :=
    (continuousAt_extChartAt' (hUsource hq)).preimage_mem_nhds hA
  obtain ⟨V, hVU, hV, hqV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hq) hpre)
  refine ⟨V, hV, hqV, (fun y hy => hUsource (hVU hy).1), L * K, ?_⟩
  exact hL.comp (hLip.mono (fun y hy => (hVU hy).1)) (fun y hy => (hVU hy).2)
theorem Helpers.metricLocallyLinear_fixed_endpoint_chart_phase
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M]
    (p : M) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hg : ContDiffOn ℝ ∞ g (extChartAt I p).target)
    (hΓ : ContDiffOn ℝ ∞ Γ (extChartAt I p).target)
    (hsym : ∀ z u v, g z u v = g z v u)
    (hpos : ∀ z ∈ (extChartAt I p).target, ∀ v : E, v ≠ 0 → 0 < g z v v)
    (hnorm : ∀ z ∈ (extChartAt I p).target, ∀ v : E,
      g z v v = ‖mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I p).symm (Set.range I) z v‖ ^ 2)
    (hKoszul : ∀ z ∈ (extChartAt I p).target, ∀ u v w : E,
      2 * g z (Γ z u v) w = (fderiv ℝ g z u) v w +
        (fderiv ℝ g z v) u w - (fderiv ℝ g z w) u v)
    {γ : ℝ → M} {c : NNReal} {a b : ℝ} (hc : 0 < c) (hab : a < b)
    (hlin : Helpers.MetricLocallyLinear γ c (Set.Ioo a b))
    (hγ : Filter.Tendsto γ (nhdsWithin b (Set.Ioo a b)) (nhds p)) :
    ∃ a' ∈ Set.Ioo a b, ∃ v : ℝ → E, ∀ t ∈ Set.Ioo a' b,
      γ t ∈ (extChartAt I p).source ∧
      extChartAt I p (γ t) ∈ (extChartAt I p).target ∧
      HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) (v t) t ∧
      HasDerivAt v (-(Γ (extChartAt I p (γ t)) (v t) (v t))) t ∧
      g (extChartAt I p (γ t)) (v t) (v t) = (c : ℝ) ^ 2 := by
  obtain ⟨U, hU, hpU, hUsource, K, hLip⟩ := Helpers.exists_lipschitzOnWith_extChartAt I M p
  have hγU : ∀ᶠ t in nhdsWithin b (Set.Ioo a b), γ t ∈ U :=
    hγ.eventually (hU.mem_nhds hpU)
  rw [nhdsWithin_Ioo_eq_nhdsLT hab] at hγU
  obtain ⟨d, hd, hdU⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).mp hγU
  let a' : ℝ := (d + b) / 2
  have ha' : a' ∈ Set.Ioo a b := ⟨by dsimp [a']; linarith [hd.1, hd.2],
    by dsimp [a']; linarith [hd.2]⟩
  have hsub : Set.Ioo a' b ⊆ Set.Ioo a b := fun t ht => ⟨ha'.1.trans ht.1, ht.2⟩
  have hmaps : Set.MapsTo γ (Set.Ioo a' b) U := by
    intro t ht
    apply hdU
    exact ⟨by dsimp [a'] at ht; linarith [ht.1, hd.2], ht.2⟩
  let x : ℝ → E := fun s => extChartAt I p (γ s)
  have hdiff : ∀ t ∈ Set.Ioo a' b, DifferentiableAt ℝ x t := by
    intro t ht
    obtain ⟨w, hwR, hwL⟩ := Helpers.metricLocallyLinear_has_matching_chart_velocity I M hc hlin (hsub ht)
    have hw : HasDerivAt (fun s => extChartAt I (γ t) (γ s)) w t := by
      simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hwL.union hwR
    exact Helpers.differentiableAt_fixed_chart_of_center_chart I p
      (hlin.continuousAt isOpen_Ioo (hsub ht)) (hUsource (hmaps ht)) hw.differentiableAt
  refine ⟨a', ha', deriv x, ?_⟩
  intro t ht
  have hsource : γ t ∈ (extChartAt I p).source := hUsource (hmaps ht)
  have htarget : x t ∈ (extChartAt I p).target := (extChartAt I p).map_source hsource
  have hLipComp : ∀ f : E → E, ContDiffAt ℝ 1 f (extChartAt I p (γ t)) →
      ∃ V : Set M, IsOpen V ∧ γ t ∈ V ∧ V ⊆ (extChartAt I p).source ∧
        ∃ L : NNReal, LipschitzOnWith L (fun q => f (extChartAt I p q)) V :=
    Helpers.exists_lipschitzOnWith_fixed_chart_comp I p (γ t) U hU (hmaps ht) hUsource K hLip
  obtain ⟨εR, hεR, XR, VR, hRphase, hRrep⟩ :=
    Helpers.exists_right_spray_germ_in_fixed_chart I M p (γ t) hsource g Γ
      hg hsym hpos hnorm hΓ hKoszul hLipComp hc hlin (hsub ht) rfl
  have hlinL : Helpers.MetricLocallyLinear (fun s => γ (-s)) c (Set.Ioo (-b) (-a)) := by
    apply hlin.reflect.mono
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  obtain ⟨εL, hεL, XL₀, VL₀, hLphase, hLrep⟩ :=
    Helpers.exists_right_spray_germ_in_fixed_chart I M p (γ t) hsource g Γ
      hg hsym hpos hnorm hΓ hKoszul hLipComp
      (γ := fun s => γ (-s)) (t₀ := -t) hc hlinL
      ⟨neg_lt_neg (hsub ht).2, neg_lt_neg (hsub ht).1⟩ (by simp)
  have hdiffEv : ∀ᶠ s in nhds t, DifferentiableAt ℝ x s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hdiff s hs
  have hRODE : ∀ᶠ s in nhds t,
      HasDerivAt XR (VR s) s ∧ HasDerivAt VR (-(Γ (XR s) (VR s) (VR s))) s := by
    filter_upwards [Ioo_mem_nhds (show t - εR < t by linarith)
      (show t < t + εR by linarith)] with s hs
    exact (hRphase s hs).2
  have hReq : x =ᶠ[nhdsWithin t (Set.Ici t)] XR := by
    have htime : ∀ᶠ s in nhds t, s < t + εR := Iio_mem_nhds (by linarith)
    filter_upwards [self_mem_nhdsWithin,
      htime.filter_mono nhdsWithin_le_nhds] with s hs hsR
    exact hRrep s ⟨hs, hsR.le⟩
  have hRacc := Helpers.hasDerivWithinAt_deriv_of_spray_germ (Γ := Γ)
    (show t ∈ Set.Ici t by simp) (uniqueDiffOn_Ici t) hdiffEv hRODE hReq
  let XL : ℝ → E := fun s => XL₀ (-s)
  let VL : ℝ → E := fun s => -(VL₀ (-s))
  have hLODE : ∀ᶠ s in nhds t,
      HasDerivAt XL (VL s) s ∧ HasDerivAt VL (-(Γ (XL s) (VL s) (VL s))) s := by
    filter_upwards [Ioo_mem_nhds (show t - εL < t by linarith)
      (show t < t + εL by linarith)] with s hs
    have hneg : -s ∈ Set.Ioo (-t - εL) (-t + εL) :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hxL := (hLphase (-s) hneg).2.1.scomp s (hasDerivAt_id s).neg
    have hvL := ((hLphase (-s) hneg).2.2.scomp s (hasDerivAt_id s).neg).neg
    change HasDerivAt (fun r => -(VL₀ (-r))) _ s at hvL
    constructor
    · simpa [XL, VL, Function.comp_def] using hxL
    · simpa only [XL, VL, Function.comp_def, Pi.neg_apply, neg_one_smul,
        map_neg, neg_apply, neg_neg] using hvL
  have hLeq : x =ᶠ[nhdsWithin t (Set.Iic t)] XL := by
    have htime : ∀ᶠ s in nhds t, t - εL < s := Ioi_mem_nhds (by linarith)
    filter_upwards [self_mem_nhdsWithin,
      htime.filter_mono nhdsWithin_le_nhds] with s hs hsL
    have hh := hLrep (-s) ⟨neg_le_neg (show s ≤ t from hs), by linarith [hsL]⟩
    simpa only [x, XL, neg_neg] using hh
  have hLacc := Helpers.hasDerivWithinAt_deriv_of_spray_germ (Γ := Γ)
    (show t ∈ Set.Iic t by simp) (uniqueDiffOn_Iic t) hdiffEv hLODE hLeq
  have hacc : HasDerivAt (deriv x) (-(Γ (x t) (deriv x t) (deriv x t))) t := by
    simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hLacc.union hRacc
  refine ⟨hsource, htarget, (hdiff t ht).hasDerivAt, hacc, ?_⟩
  rw [hnorm _ htarget]
  exact Helpers.metric_speed_eq_of_hasDerivAt_chart I M p
    (hlin.continuousAt isOpen_Ioo (hsub ht)) hsource (hdiff t ht).hasDerivAt
    (hlin.eventually_edist_eq isOpen_Ioo (hsub ht))
theorem Helpers.exists_smooth_two_point_spray_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set E} (hU : IsOpen U) {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Γ U)
    {p : E} (hp : p ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ τ ∈ Set.Ioo (0 : ℝ) ε,
      ∃ Φ : ℝ × (E × E) → E × E,
        ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ
          (Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r) ∧
        (∀ z ∈ Metric.ball (p, 0) r, Φ (0, z) = z) ∧
        (∀ z ∈ Set.Ioo (-ε) ε ×ˢ Metric.ball (p, 0) r,
          (Φ z).1 ∈ U ∧ HasDerivAt (fun t : ℝ => Φ (t, z.2))
            ((Φ z).2, -(Γ (Φ z).1 (Φ z).2 (Φ z).2)) z.1) ∧
        ∃ ρ > (0 : ℝ), ∃ v : E × E → E,
          ContDiffOn ℝ 1 v (Metric.ball p ρ ×ˢ Metric.ball p ρ) ∧
          v (p, p) = 0 ∧
          ∀ x ∈ Metric.ball p ρ, ∀ y ∈ Metric.ball p ρ,
            (x, v (x, y)) ∈ Metric.ball (p, 0) r ∧
            (Φ (τ, (x, v (x, y)))).1 = y := by
  obtain ⟨R, hR, K, hLip, hdom, r, hr, ε, hε, Φ, hΦ, hΦ0, hΦF, hΦp⟩ :=
    Helpers.exists_coordinate_spray_flow_in_lipschitz_ball hU hΓ hp
  let τ : ℝ := ε / 2
  have hτpos : 0 < τ := half_pos hε
  have hτε : τ < ε := by dsimp [τ]; linarith
  have hτ : τ ∈ Set.Ioo (-ε) ε := ⟨by linarith, hτε⟩
  have hΦat : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ (τ, (p, 0)) :=
    hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds
      ⟨hτ, Metric.mem_ball_self hr⟩)
  have hlin := Helpers.coordinate_spray_flow_linearization hU hp
    ((hΓ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) hr hε
    (hΦ.of_le (by simp)) hΦ0 hΦp (fun z hz => (hΦF z hz).2)
  obtain ⟨e, he0, hept, hef, he, hei⟩ :=
    Helpers.exists_joint_inverse_of_spray_flow_linearization hτpos.ne' hΦat (hΦp τ hτ)
      (hlin τ hτ)
  have hep : e (p, 0) = (p, p) := by rw [hef, hΦp τ hτ]
  obtain ⟨ρ, hρ, v, hv, hv0, hpair⟩ :=
    Helpers.exists_pair_neighborhood_of_joint_endpoint_inverse e he0 hep hef hei
      Metric.isOpen_ball (Metric.mem_ball_self hr)
  refine ⟨r, hr, ε, hε, τ, ⟨hτpos, hτε⟩, Φ, hΦ, hΦ0, ?_, ρ, hρ, v, hv, hv0, ?_⟩
  · intro z hz
    exact ⟨hdom _ (hΦF z hz).1, (hΦF z hz).2⟩
  · intro x hx y hy
    exact ⟨(hpair x hx y hy).1, (hpair x hx y hy).2.2⟩
theorem Helpers.riemannian_endpointGerm_continuation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [LocallyCompactSpace M] [ConnectedSpace M] :
    let L : (ℝ → M) → NNReal → Set ℝ → Prop := fun γ c S =>
      ∀ t₀ ∈ S, ∃ δ > (0 : ℝ), ∀ s t : ℝ,
        s ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
        t ∈ S ∩ Set.Ioo (t₀ - δ) (t₀ + δ) →
        edist (γ s) (γ t) = (c : ENNReal) * ENNReal.ofReal |t - s|
    ∀ (a b : ℝ) (γ : ℝ → M) (c : NNReal) (p : M), a < b →
      L γ c (Set.Ioo a b) →
      Filter.Tendsto γ (nhdsWithin b (Set.Ioo a b)) (nhds p) →
      ∃ ε > (0 : ℝ), ∃ η : ℝ → M,
        L η c (Set.Ioo (b - ε) (b + ε)) ∧
        ∀ t ∈ Set.Ioo (max a (b - ε)) b, η t = γ t := by
  dsimp only
  intro a b γ c p hab hlin hγ
  change Helpers.MetricLocallyLinear γ c (Set.Ioo a b) at hlin
  change ∃ ε > (0 : ℝ), ∃ η : ℝ → M,
    Helpers.MetricLocallyLinear η c (Set.Ioo (b - ε) (b + ε)) ∧
      ∀ t ∈ Set.Ioo (max a (b - ε)) b, η t = γ t
  by_cases hc : c = 0
  · subst c
    exact Helpers.metricEndpointGerm_of_zero_speed hab hlin
  have hcpos : 0 < c := (show 0 ≤ c from zero_le).lt_of_ne (Ne.symm hc)
  obtain ⟨g, Γ, hg, hsym, hpos, hnorm, hΓ, hKoszul⟩ :=
    Helpers.exists_smooth_coordinate_metric_and_koszul I p
  obtain ⟨a', ha', v, hv⟩ := Helpers.metricLocallyLinear_fixed_endpoint_chart_phase
    I M p g Γ hg hΓ hsym hpos hnorm hKoszul hcpos hab hlin hγ
  have hU : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  have hpU : extChartAt I p p ∈ (extChartAt I p).target := mem_extChartAt_target p
  have hxlim : Filter.Tendsto (fun t : ℝ => extChartAt I p (γ t))
      (nhdsWithin b (Set.Ioo a' b)) (nhds (extChartAt I p p)) := by
    have h := (continuousAt_extChartAt (I := I) p).tendsto.comp hγ
    simpa only [Function.comp_def, nhdsWithin_Ioo_eq_nhdsLT hab,
      nhdsWithin_Ioo_eq_nhdsLT ha'.2] using h
  obtain ⟨r, hr, X, V, hXb, hphase, hODE, hEnergy, heq⟩ :=
    Helpers.exists_energy_preserving_spray_continuation hU (hg.of_le (by simp)) hΓ
      hsym hKoszul ha'.2 hpU (hpos _ hpU)
      (fun t ht => ⟨(hv t ht).2.2.1, (hv t ht).2.2.2.1⟩) hxlim
      (fun t ht => (hv t ht).2.2.2.2)
  have hshift (t : ℝ) (ht : t ∈ Set.Ioo (-r) r) :
      t + b ∈ Set.Ioo (b - r) (b + r) := by
    constructor <;> linarith [ht.1, ht.2]
  have hphaseShift : ContDiffOn ℝ ∞ (fun t : ℝ => (X (t + b), V (t + b)))
      (Set.Ioo (-r) r) :=
    hphase.comp (contDiff_id.add contDiff_const).contDiffOn hshift
  have hODEShift : ∀ t ∈ Set.Ioo (-r) r,
      X (t + b) ∈ (extChartAt I p).target ∧
      HasDerivAt (fun s : ℝ => X (s + b)) (V (t + b)) t ∧
      HasDerivAt (fun s : ℝ => V (s + b))
        (-(Γ (X (t + b)) (V (t + b)) (V (t + b)))) t := by
    intro t ht
    have h := hODE (t + b) (hshift t ht)
    refine ⟨h.1, ?_, ?_⟩
    · simpa only [Function.comp_def, id_eq, one_smul] using
        h.2.1.scomp t ((hasDerivAt_id t).add_const b)
    · simpa only [Function.comp_def, id_eq, one_smul] using
        h.2.2.scomp t ((hasDerivAt_id t).add_const b)
  obtain ⟨δ, hδ, hδr, hdist⟩ := Helpers.coordinate_spray_locally_distance_linear
    I M p g Γ hg hΓ hsym hpos hnorm hKoszul hr (by simpa using hXb)
      hphaseShift hODEShift (fun t ht => hEnergy (t + b) (hshift t ht))
  let ε := min δ (b - a')
  have hε : 0 < ε := lt_min hδ (sub_pos.mpr ha'.2)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεa' : ε ≤ b - a' := min_le_right _ _
  let η : ℝ → M := fun t => (extChartAt I p).symm (X t)
  refine ⟨ε, hε, η, ?_, ?_⟩
  · intro t₀ ht₀
    refine ⟨1, zero_lt_one, ?_⟩
    intro s t hs ht
    have hs' : s - b ∈ Set.Ioo (-δ) δ := by
      constructor <;> linarith [hs.1.1, hs.1.2]
    have ht' : t - b ∈ Set.Ioo (-δ) δ := by
      constructor <;> linarith [ht.1.1, ht.1.2]
    have hdiff : (t - b) - (s - b) = t - s := by ring
    simpa only [η, sub_add_cancel, hdiff] using hdist (s - b) hs' (t - b) ht'
  · intro t ht
    have htbε : b - ε < t := (le_max_right a (b - ε)).trans_lt ht.1
    have hta' : a' < t := by linarith
    have htr : t ∈ Set.Ioo (b - r) b :=
      ⟨by linarith, ht.2⟩
    change (extChartAt I p).symm (X t) = γ t
    rw [(heq t htr).1]
    exact (extChartAt I p).left_inv (hv t ⟨hta', ht.2⟩).1
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
  constructor
  · exact Helpers.completeSpace_of_isGeodesicallyComplete I M
  · intro hcomplete
    letI : CompleteSpace M := hcomplete
    exact Helpers.isGeodesicallyComplete_of_endpointGerm M
      (Helpers.riemannian_endpointGerm_continuation I M)
end Submission
