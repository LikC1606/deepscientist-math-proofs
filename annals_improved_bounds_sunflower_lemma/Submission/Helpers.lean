import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import ChallengeDeps
namespace Submission.Helpers

theorem isSunflower_preimage_equiv {X Y : Type*} (e : X ≃ Y) {r : ℕ}
    {S : Set (Set Y)} (hS : Set.IsSunflower r S) :
    Set.IsSunflower r (Set.preimage e '' S) := by
  refine ⟨?_, ?_⟩
  · rw [Set.ncard_image_of_injective S (Set.preimage_injective.mpr e.surjective)]
    exact hS.1
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    have hne : A ≠ B := fun h ↦ hAB (congrArg (Set.preimage e) h)
    rw [← Set.preimage_inter, hS.2 hA hB hne, Set.preimage_sInter, Set.sInter_image]
theorem transfer_from_numbered_ground_sets
    (c : ℝ)
    (hc : ∀ (r : ℕ), 3 ≤ r → ∀ (n : ℕ) (ℱ : Set (Set (Fin n))) (w : ℕ),
      2 ≤ w → Set.IsSystem w ℱ →
      _root_.ImprovedBoundsSunflowerLemma.lowerBound r c w ≤ (ℱ.ncard : ℝ) →
      ∃ S ⊆ ℱ, Set.IsSunflower r S)
    (r : ℕ) (hr : 3 ≤ r) (X : Type*) [Finite X] (ℱ : Set (Set X)) (w : ℕ)
    (hw : 2 ≤ w) (hℱ₁ : Set.IsSystem w ℱ)
    (hℱ₂ : _root_.ImprovedBoundsSunflowerLemma.lowerBound r c w ≤ (ℱ.ncard : ℝ)) :
    ∃ S ⊆ ℱ, Set.IsSunflower r S := by
  classical
  letI := Fintype.ofFinite X
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let ℱ' : Set (Set (Fin (Fintype.card X))) := Set.image (Set.image e) ℱ
  have hℱ₁' : Set.IsSystem w ℱ' := by
    rintro _ ⟨A, hA, rfl⟩
    rw [Set.ncard_image_of_injective A e.injective]
    exact hℱ₁ A hA
  have hℱ₂' :
      _root_.ImprovedBoundsSunflowerLemma.lowerBound r c w ≤ (ℱ'.ncard : ℝ) := by
    change _ ≤ ((Set.image (Set.image e) ℱ).ncard : ℝ)
    rw [Set.ncard_image_of_injective ℱ e.injective.image_injective]
    exact hℱ₂
  obtain ⟨S, hSℱ, hS⟩ := hc r hr (Fintype.card X) ℱ' w hw hℱ₁' hℱ₂'
  refine ⟨Set.preimage e '' S, ?_, isSunflower_preimage_equiv e hS⟩
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨B, hB, hBA⟩ := hSℱ hA
  simpa only [← hBA, Set.preimage_image_eq B e.injective] using hB
theorem one_lt_logb_of_two_le (w : ℕ) (hw : 2 ≤ w) :
    1 < Real.logb (1.9 : ℝ) (w : ℝ) := by
  have hwR : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  apply (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 1.9)
    (by linarith : 0 < (w : ℝ))).2
  simpa using (lt_of_lt_of_le (by norm_num : (1.9 : ℝ) < 2) hwR)
theorem positive_log_factors (w : ℕ) (hw : 2 ≤ w) :
    0 < Real.logb (1.9 : ℝ) (w : ℝ) ∧
      0 < Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  have hlog := one_lt_logb_of_two_le w hw
  exact ⟨lt_trans zero_lt_one hlog, Real.logb_pos (by norm_num) hlog⟩
theorem rational_log_factors_lower_bounds (w : ℕ) (hw : 2 ≤ w) :
    (15 / 14 : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) ∧
      (1 / 10 : ℝ) ≤ Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  have hb : (1 : ℝ) < 1.9 := by norm_num
  have hpow₁ : (1.9 : ℝ) ^ 15 ≤ (2 : ℝ) ^ 14 := by norm_num
  have h₁ := Real.logb_le_logb_of_le hb
    (pow_pos (by norm_num : (0 : ℝ) < 1.9) 15) hpow₁
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb] at h₁
  have hwR : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hmono₁ := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 2) hwR
  have hfirst : (15 / 14 : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
    norm_num at h₁
    linarith
  refine ⟨hfirst, ?_⟩
  have hpow₂ : (1.9 : ℝ) ≤ (15 / 14 : ℝ) ^ 10 := by norm_num
  have h₂ := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 1.9) hpow₂
  rw [Real.logb_self_eq_one hb, Real.logb_pow] at h₂
  have hmono₂ := Real.logb_le_logb_of_le hb
    (by norm_num : (0 : ℝ) < 15 / 14) hfirst
  norm_num at h₂
  linarith
theorem log_product_lower_bound (w : ℕ) (hw : 2 ≤ w) :
    (3 / 28 : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) *
      Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) := by
  obtain ⟨hfirst, hsecond⟩ := rational_log_factors_lower_bounds w hw
  calc
    (3 / 28 : ℝ) = (15 / 14 : ℝ) * (1 / 10 : ℝ) := by norm_num
    _ ≤ Real.logb (1.9 : ℝ) (w : ℝ) *
        Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) :=
      mul_le_mul hfirst hsecond (by norm_num) (le_trans (by norm_num) hfirst)
theorem minimal_fragment_decode {X ι : Type*} [Finite X]
    (f : ι → Set X) (i j j₀ : ι) (W : Set X) (t : ℕ)
    (hj : f j ⊆ f i ∪ W) (ht : (f j \ W).ncard = t)
    (hmin : ∀ a, f a ⊆ f i ∪ W → t ≤ (f a \ W).ncard)
    (h₀ : f j₀ ⊆ W ∪ (f j \ W)) : f j₀ \ W = f j \ W := by
  have hsub : f j₀ \ W ⊆ f j \ W := by
    intro x hx
    rcases h₀ hx.1 with hxW | hxT
    · exact False.elim (hx.2 hxW)
    · exact hxT
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [ht]
  apply hmin j₀
  intro x hx
  rcases h₀ hx with hxW | hxT
  · exact Or.inr hxW
  · exact hj hxT.1
theorem ncard_mul_le_of_fiber_bounds {α β : Type*} [Fintype α] [Fintype β]
    (s : Set α) (t : Set β) (f : α → β) (a b : ℝ)
    (hf : ∀ x ∈ s, f x ∈ t)
    (hb : ∀ y ∈ t, ({x | x ∈ s ∧ f x = y}.ncard : ℝ) * a ≤ b) :
    (s.ncard : ℝ) * a ≤ (t.ncard : ℝ) * b := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := s.toFinset) (t := t.toFinset) (f := f)
    (by
      intro x hx
      simpa using hf x (by simpa using hx))
  have he (y : β) :
      {x | x ∈ s ∧ f x = y}.toFinset = {x ∈ s.toFinset | f x = y} := by
    ext x
    simp
  have hc' : (s.ncard : ℝ) =
      ∑ y ∈ t.toFinset, ({x | x ∈ s ∧ f x = y}.ncard : ℝ) := by
    simp_rw [Set.ncard_eq_toFinset_card', he]
    exact_mod_cast hc
  calc
    (s.ncard : ℝ) * a =
        ∑ y ∈ t.toFinset, ({x | x ∈ s ∧ f x = y}.ncard : ℝ) * a := by
      rw [← Finset.sum_mul, ← hc']
    _ ≤ ∑ _y ∈ t.toFinset, b := Finset.sum_le_sum fun y hy ↦ hb y (by simpa using hy)
    _ = (t.ncard : ℝ) * b := by simp [Set.ncard_eq_toFinset_card']
theorem maximal_weighted_link (n w : ℕ) (ℱ : Set (Set (Fin n))) (κ : ℝ)
    (hκ : 2 ≤ κ) (hsys : Set.IsSystem w ℱ) (hsize : κ ^ w < (ℱ.ncard : ℝ)) :
    ∃ T : Set (Fin n),
      2 ≤ {A : Set (Fin n) | A ∈ ℱ ∧ T ⊆ A}.ncard ∧
      ∀ U : Set (Fin n),
        ({A : Set (Fin n) | A ∈ ℱ ∧ U ⊆ A}.ncard : ℝ) * κ ^ U.ncard ≤
          ({A : Set (Fin n) | A ∈ ℱ ∧ T ⊆ A}.ncard : ℝ) * κ ^ T.ncard := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  let L (T : Set (Fin n)) : Set (Set (Fin n)) := {A | A ∈ ℱ ∧ T ⊆ A}
  let score (T : Set (Fin n)) : ℝ := (L T).ncard * κ ^ T.ncard
  obtain ⟨T, _, hmax⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  have hmax' (U : Set (Fin n)) : score U ≤ score T := hmax U (Finset.mem_univ U)
  have hbot : score ∅ = (ℱ.ncard : ℝ) := by simp [score, L]
  have hlarge : κ ^ w < score T := lt_of_lt_of_le hsize (hbot ▸ hmax' ∅)
  have hκpos : 0 < κ := by linarith
  have hscorepos : 0 < score T := lt_trans (pow_pos hκpos w) hlarge
  have hLpos : 0 < (L T).ncard := by
    by_contra h
    have hzero : (L T).ncard = 0 := Nat.eq_zero_of_not_pos h
    simp [score, hzero] at hscorepos
  obtain ⟨A, hA⟩ := (Set.ncard_pos (Set.toFinite (L T))).mp hLpos
  have hTcard : T.ncard ≤ w := le_trans (Set.ncard_le_ncard hA.2) (hsys A hA.1)
  have htwo : 2 ≤ (L T).ncard := by
    by_contra h
    have hle : ((L T).ncard : ℝ) ≤ 1 := by exact_mod_cast (by omega : (L T).ncard ≤ 1)
    have hscorele : score T ≤ κ ^ T.ncard := by
      simpa [score] using mul_le_mul_of_nonneg_right hle (le_of_lt (pow_pos hκpos T.ncard))
    have hpowle : κ ^ T.ncard ≤ κ ^ w := pow_le_pow_right₀ (by linarith) hTcard
    exact (not_lt_of_ge (hscorele.trans hpowle)) hlarge
  exact ⟨T, htwo, hmax'⟩
theorem extract_spread_petals (n w : ℕ) (ℱ : Set (Set (Fin n))) (κ : ℝ)
    (hκ : 2 ≤ κ) (hsys : Set.IsSystem w ℱ) (hsize : κ ^ w < (ℱ.ncard : ℝ)) :
    ∃ (T : Set (Fin n)) (ℋ : Set (Set (Fin n))),
      ℋ.Nonempty ∧ (∅ : Set (Fin n)) ∉ ℋ ∧ Set.IsSystem w ℋ ∧
      (∀ A ∈ ℋ, Disjoint T A ∧ T ∪ A ∈ ℱ) ∧
      (∀ U : Set (Fin n),
        ({A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A}.ncard : ℝ) * (κ / 2) ^ U.ncard ≤
          (ℋ.ncard : ℝ)) := by
  classical
  obtain ⟨T, htwo, hmax⟩ := maximal_weighted_link n w ℱ κ hκ hsys hsize
  let L (U : Set (Fin n)) : Set (Set (Fin n)) := {A | A ∈ ℱ ∧ U ⊆ A}
  let G : Set (Set (Fin n)) := (fun A : Set (Fin n) ↦ A \ T) '' L T
  let ℋ : Set (Set (Fin n)) := G \ {∅}
  have hκpos : 0 < κ := by linarith
  have hrec (A : Set (Fin n)) (hA : A ∈ L T) : T ∪ (A \ T) = A := by
    rw [Set.union_comm]
    exact Set.sdiff_union_of_subset hA.2
  have hinj : Set.InjOn (fun A : Set (Fin n) ↦ A \ T) (L T) := by
    intro A hA B hB hAB
    calc
      A = T ∪ (A \ T) := (hrec A hA).symm
      _ = T ∪ (B \ T) := congrArg (fun U ↦ T ∪ U) hAB
      _ = B := hrec B hB
  have hGcard : G.ncard = (L T).ncard := hinj.ncard_image
  have hHcard : (L T).ncard ≤ ℋ.ncard + 1 := by
    rw [← hGcard]
    have hsub : G ⊆ insert (∅ : Set (Fin n)) ℋ := by
      intro A hA
      by_cases he : A = ∅
      · exact Or.inl he
      · exact Or.inr ⟨hA, by simpa using he⟩
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_insert_le _ _)
  have hHpos : 0 < ℋ.ncard := by change 2 ≤ (L T).ncard at htwo; omega
  have hhalf : ((L T).ncard : ℝ) ≤ 2 * (ℋ.ncard : ℝ) := by
    have hnat : (L T).ncard ≤ 2 * ℋ.ncard := by omega
    exact_mod_cast hnat
  have hproperties (A : Set (Fin n)) (hA : A ∈ ℋ) :
      Disjoint T A ∧ T ∪ A ∈ ℱ := by
    obtain ⟨B, hB, rfl⟩ := hA.1
    exact ⟨Set.disjoint_sdiff_right, (hrec B hB).symm ▸ hB.1⟩
  have hsysH : Set.IsSystem w ℋ := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA.1
    exact (Set.ncard_le_ncard Set.sdiff_subset).trans (hsys B hB.1)
  refine ⟨T, ℋ, (Set.ncard_pos (Set.toFinite ℋ)).mp hHpos, ?_, hsysH,
    hproperties, ?_⟩
  · simp [ℋ]
  · intro U
    by_cases hU : U = ∅
    · simp [hU]
    by_cases hdis : Disjoint T U
    · let K : Set (Set (Fin n)) := {A | A ∈ ℋ ∧ U ⊆ A}
      have hrecovery (A : Set (Fin n)) (hA : A ∈ ℋ) : (T ∪ A) \ T = A := by
        ext x
        constructor
        · intro hx
          exact hx.1.resolve_left hx.2
        · intro hx
          exact ⟨Or.inr hx, fun hxT ↦ Set.disjoint_left.mp (hproperties A hA).1 hxT hx⟩
      have hrootinj : Set.InjOn (fun A : Set (Fin n) ↦ T ∪ A) K := by
        intro A hA B hB hAB
        calc
          A = (T ∪ A) \ T := (hrecovery A hA.1).symm
          _ = (T ∪ B) \ T := congrArg (fun D ↦ D \ T) hAB
          _ = B := hrecovery B hB.1
      have hrootmap : (fun A : Set (Fin n) ↦ T ∪ A) '' K ⊆ L (T ∪ U) := by
        rintro _ ⟨A, hA, rfl⟩
        refine ⟨(hproperties A hA.1).2, ?_⟩
        intro x hx
        exact hx.elim Or.inl (fun hxU ↦ Or.inr (hA.2 hxU))
      have hKcard : K.ncard ≤ (L (T ∪ U)).ncard := by
        rw [← hrootinj.ncard_image]
        exact Set.ncard_le_ncard hrootmap
      have hfull : ((L (T ∪ U)).ncard : ℝ) * κ ^ U.ncard ≤ ((L T).ncard : ℝ) := by
        apply (mul_le_mul_iff_left₀ (pow_pos hκpos T.ncard)).mp
        calc
          ((L (T ∪ U)).ncard : ℝ) * κ ^ U.ncard * κ ^ T.ncard =
              ((L (T ∪ U)).ncard : ℝ) * κ ^ (T ∪ U).ncard := by
            rw [Set.ncard_union_eq hdis, pow_add]
            ring
          _ ≤ ((L T).ncard : ℝ) * κ ^ T.ncard := hmax (T ∪ U)
      have hcount : (K.ncard : ℝ) * κ ^ U.ncard ≤ ((L T).ncard : ℝ) := by
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hKcard)
          (le_of_lt (pow_pos hκpos U.ncard))).trans hfull
      have hUpos : 1 ≤ U.ncard := by
        exact (Set.ncard_pos (Set.toFinite U)).mpr (Set.nonempty_iff_ne_empty.mpr hU)
      have hpowtwo : (2 : ℝ) ≤ (2 : ℝ) ^ U.ncard := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hUpos)
      have hpow : 2 * (κ / 2) ^ U.ncard ≤ κ ^ U.ncard := by
        calc
          2 * (κ / 2) ^ U.ncard ≤ (2 : ℝ) ^ U.ncard * (κ / 2) ^ U.ncard :=
            mul_le_mul_of_nonneg_right hpowtwo (pow_nonneg (by linarith) _)
          _ = (2 * (κ / 2)) ^ U.ncard := (mul_pow _ _ _).symm
          _ = κ ^ U.ncard := by congr 1; ring
      have hscaled := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg K.ncard : (0 : ℝ) ≤ K.ncard)
      change (K.ncard : ℝ) * (κ / 2) ^ U.ncard ≤ (ℋ.ncard : ℝ)
      nlinarith
    · have hzero : {A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro A hA
        apply hdis
        exact Set.disjoint_left.mpr fun x hxT hxU ↦
          Set.disjoint_left.mp (hproperties A hA.1).1 hxT (hA.2 hxU)
      rw [hzero]
      simp
theorem codegree_bound_of_injective_shrinking
    {X ι ι' : Type*} [Finite X] [Finite ι] [Finite ι']
    (f : ι → Set X) (g : ι' → Set X) (e : ι' → ι)
    (he : Function.Injective e) (hgf : ∀ i, g i ⊆ f (e i))
    (κ N : ℝ) (hκ : 0 ≤ κ)
    (hbound : ∀ U : Set X,
      ({i : ι | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ∀ U : Set X, ({i : ι' | U ⊆ g i}.ncard : ℝ) * κ ^ U.ncard ≤ N := by
  intro U
  have hc : {i : ι' | U ⊆ g i}.ncard ≤ {i : ι | U ⊆ f i}.ncard :=
    Set.ncard_le_ncard_of_injOn e
      (fun i hi ↦ Set.Subset.trans hi (hgf i))
      (fun i _ j _ hij ↦ he hij)
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
    (pow_nonneg hκ _)).trans (hbound U)
theorem fragment_shrinks_current_edge {X ι : Type*}
    (f : ι → Set X) (i j : ι) (W : Set X)
    (hj : f j ⊆ f i ∪ W) : f j \ W ⊆ f i := by
  intro x hx
  rcases hj hx.1 with hxi | hxW
  · exact hxi
  · exact False.elim (hx.2 hxW)
theorem fragment_preserves_existential_provenance {X ι : Type*}
    (ℱ : Set (Set X)) (f : ι → Set X) (Wold W : Set X) (j : ι)
    (hprov : ∀ i, ∃ A ∈ ℱ, A ⊆ f i ∪ Wold) :
    ∃ A ∈ ℱ, A ⊆ (f j \ W) ∪ (Wold ∪ W) := by
  obtain ⟨A, hA, hsub⟩ := hprov j
  refine ⟨A, hA, ?_⟩
  intro x hx
  rcases hsub hx with hxj | hxold
  · by_cases hxW : x ∈ W
    · exact Or.inr (Or.inr hxW)
    · exact Or.inl ⟨hxj, hxW⟩
  · exact Or.inr (Or.inl hxold)
theorem fragment_code_fiber_bound {X ι : Type*} [Finite X] [Fintype ι]
    (f : ι → Set X) (s : Set (ι × Set X)) (T : ι × Set X → Set X)
    (Z E : Set X) (k t : ℕ) (κ N : ℝ)
    (hκ : 0 ≤ κ) (hN : 0 ≤ N) (hE : E.ncard ≤ k)
    (hcode : ∀ U : Set X, ({i : ι | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N)
    (hZ : ∀ p ∈ s, p.2 ∪ T p = Z)
    (hdis : ∀ p ∈ s, Disjoint p.2 (T p))
    (hTE : ∀ p ∈ s, T p ⊆ E)
    (ht : ∀ p ∈ s, (T p).ncard = t)
    (hf : ∀ p ∈ s, T p ⊆ f p.1) :
    (s.ncard : ℝ) * κ ^ t ≤ (k.choose t : ℝ) * N := by
  classical
  letI := Fintype.ofFinite (Set X)
  have hrecover (A : Set X) (p : ι × Set X) (hp : p ∈ s) (hA : T p = A) :
      p.2 = Z \ A := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · rw [← hZ p hp]
        exact Or.inl hx
      · intro hxA
        exact Set.disjoint_left.mp (hdis p hp) hx (by simpa only [hA] using hxA)
    · rintro ⟨hxZ, hxA⟩
      rw [← hZ p hp] at hxZ
      rcases hxZ with hxW | hxT
      · exact hxW
      · exact False.elim (hxA (by simpa only [hA] using hxT))
  have hbound (A : Set X) (hA : A ⊆ E ∧ A.ncard = t) :
      ({p | p ∈ s ∧ T p = A}.ncard : ℝ) * κ ^ t ≤ N := by
    have hc : {p | p ∈ s ∧ T p = A}.ncard ≤ {i : ι | A ⊆ f i}.ncard := by
      apply Set.ncard_le_ncard_of_injOn Prod.fst
      · intro p hp
        change A ⊆ f p.1
        simpa only [← hp.2] using hf p hp.1
      · intro p hp q hq hpq
        apply Prod.ext hpq
        exact (hrecover A p hp.1 hp.2).trans (hrecover A q hq.1 hq.2).symm
    rw [← hA.2]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
      (pow_nonneg hκ _)).trans (hcode A)
  have hsum := ncard_mul_le_of_fiber_bounds s {A : Set X | A ⊆ E ∧ A.ncard = t}
    T (κ ^ t) N (fun p hp ↦ ⟨hTE p hp, ht p hp⟩) hbound
  rw [Set.ncard_powerset_ncard (Set.toFinite E) t] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_choose t hE) hN)
theorem minimal_fragment_count (n d k m t : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N : ℝ) (hκ : 0 < κ) (hN : 0 ≤ N)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ k)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ({p : Fin d × Set (Fin n) |
        p.2 ⊆ V ∧ p.2.ncard = m ∧
        (∀ j : Fin d, f j ⊆ f p.1 ∪ p.2 → t ≤ (f j \ p.2).ncard) ∧
        (∃ j : Fin d, f j ⊆ f p.1 ∪ p.2 ∧ (f j \ p.2).ncard = t)}.ncard : ℝ) *
        κ ^ t ≤ (V.ncard.choose (m + t) : ℝ) * (k.choose t : ℝ) * N := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  let S : Set (Fin d × Set (Fin n)) := {p |
    p.2 ⊆ V ∧ p.2.ncard = m ∧
    (∀ a : Fin d, f a ⊆ f p.1 ∪ p.2 → t ≤ (f a \ p.2).ncard) ∧
    (∃ a : Fin d, f a ⊆ f p.1 ∪ p.2 ∧ (f a \ p.2).ncard = t)}
  let j (p : Fin d × Set (Fin n)) : Fin d :=
    if h : ∃ a : Fin d, f a ⊆ f p.1 ∪ p.2 ∧ (f a \ p.2).ncard = t
    then Classical.choose h else p.1
  have hj (p : Fin d × Set (Fin n)) (hp : p ∈ S) :
      f (j p) ⊆ f p.1 ∪ p.2 ∧ (f (j p) \ p.2).ncard = t := by
    dsimp [j]
    split_ifs with h
    · exact Classical.choose_spec h
    · exact False.elim (h hp.2.2.2)
  let T (p : Fin d × Set (Fin n)) : Set (Fin n) := f (j p) \ p.2
  let Z (p : Fin d × Set (Fin n)) : Set (Fin n) := p.2 ∪ T p
  have hTcard (p : Fin d × Set (Fin n)) (hp : p ∈ S) : (T p).ncard = t :=
    (hj p hp).2
  have hTsub (p : Fin d × Set (Fin n)) (hp : p ∈ S) : T p ⊆ f p.1 :=
    fragment_shrinks_current_edge f p.1 (j p) p.2 (hj p hp).1
  have hTdis (p : Fin d × Set (Fin n)) : Disjoint p.2 (T p) :=
    Set.disjoint_sdiff_right
  have hmaps (p : Fin d × Set (Fin n)) (hp : p ∈ S) :
      Z p ⊆ V ∧ (Z p).ncard = m + t := by
    refine ⟨Set.union_subset hp.1 (Set.sdiff_subset.trans (hsys (j p)).1), ?_⟩
    change (p.2 ∪ T p).ncard = m + t
    rw [Set.ncard_union_eq (hTdis p), hp.2.1, hTcard p hp]
  have hedge (p : Fin d × Set (Fin n)) : f (j p) ⊆ Z p := by
    intro x hx
    by_cases hxW : x ∈ p.2
    · exact Or.inl hxW
    · exact Or.inr ⟨hx, hxW⟩
  have hbound (Z₀ : Set (Fin n)) (_hZ₀ : Z₀ ⊆ V ∧ Z₀.ncard = m + t) :
      ({p | p ∈ S ∧ Z p = Z₀}.ncard : ℝ) * κ ^ t ≤ (k.choose t : ℝ) * N := by
    let sZ : Set (Fin d × Set (Fin n)) := {p | p ∈ S ∧ Z p = Z₀}
    change (sZ.ncard : ℝ) * κ ^ t ≤ (k.choose t : ℝ) * N
    by_cases hne : sZ.Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      have hcanonical : f (j p₀) ⊆ Z₀ := by
        rw [← hp₀.2]
        exact hedge p₀
      apply fragment_code_fiber_bound f sZ T Z₀ (f (j p₀)) k t κ N
        (le_of_lt hκ) hN (hsys (j p₀)).2 hcode
      · intro p hp
        exact hp.2
      · intro p _hp
        exact hTdis p
      · intro p hp
        have hdecode : f (j p₀) \ p.2 = T p := by
          apply minimal_fragment_decode f p.1 (j p) (j p₀) p.2 t
            (hj p hp.1).1 (hj p hp.1).2 hp.1.2.2.1
          change f (j p₀) ⊆ Z p
          rw [hp.2]
          exact hcanonical
        rw [← hdecode]
        exact Set.sdiff_subset
      · intro p hp
        exact hTcard p hp.1
      · intro p hp
        exact hTsub p hp.1
    · have hzero : sZ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simpa only [hzero, Set.ncard_empty, Nat.cast_zero, zero_mul] using
        mul_nonneg (Nat.cast_nonneg (k.choose t) : (0 : ℝ) ≤ k.choose t) hN
  have hsum := ncard_mul_le_of_fiber_bounds S
    {Z₀ : Set (Fin n) | Z₀ ⊆ V ∧ Z₀.ncard = m + t} Z
    (κ ^ t) ((k.choose t : ℝ) * N) hmaps hbound
  rw [Set.ncard_powerset_ncard (Set.toFinite V) (m + t)] at hsum
  simpa only [mul_assoc] using hsum
theorem sunflower_of_disjoint_petals
    (n r : ℕ) (ℱ : Set (Set (Fin n))) (T : Set (Fin n)) (P : Set (Set (Fin n)))
    (_hr : 2 ≤ r) (hcard : P.ncard = r) (hdis : P.Pairwise Disjoint)
    (hprop : ∀ A ∈ P, Disjoint T A ∧ T ∪ A ∈ ℱ) :
    ∃ S ⊆ ℱ, Set.IsSunflower r S := by
  have hrecovery (A : Set (Fin n)) (hA : A ∈ P) : (T ∪ A) \ T = A := by
    ext x
    constructor
    · intro hx
      exact hx.1.resolve_left hx.2
    · intro hx
      exact ⟨Or.inr hx, fun hxT ↦ Set.disjoint_left.mp (hprop A hA).1 hxT hx⟩
  have hinj : Set.InjOn (fun A : Set (Fin n) ↦ T ∪ A) P := by
    intro A hA B hB hAB
    calc
      A = (T ∪ A) \ T := (hrecovery A hA).symm
      _ = (T ∪ B) \ T := congrArg (fun D ↦ D \ T) hAB
      _ = B := hrecovery B hB
  refine ⟨(fun A : Set (Fin n) ↦ T ∪ A) '' P, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact (hprop A hA).2
  · refine ⟨?_, ?_⟩
    · rw [hinj.ncard_image]
      exact hcard
    · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
      have hne : A ≠ B := fun h ↦ hAB (congrArg (fun D ↦ T ∪ D) h)
      have hd : Disjoint A B := hdis hA hB hne
      ext x
      constructor
      · intro hx
        have hxT : x ∈ T := by
          by_contra hxT
          exact Set.disjoint_left.mp hd (hx.1.resolve_left hxT) (hx.2.resolve_left hxT)
        apply Set.mem_sInter.mpr
        rintro _ ⟨D, _hD, rfl⟩
        exact Or.inl hxT
      · intro hx
        exact ⟨Set.mem_sInter.mp hx _ ⟨A, hA, rfl⟩,
          Set.mem_sInter.mp hx _ ⟨B, hB, rfl⟩⟩
theorem scalar_threshold_comparison (r w : ℕ) (hr : 3 ≤ r) (hw : 2 ≤ w) :
    2 ≤ 520 * (r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ) ∧
      520 * (r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ) <
        40000 * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
          Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) ∧
      w < 2 ^ (Nat.log 2 w + 1) := by
  have hb : (1 : ℝ) < 1.9 := by norm_num
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hwR : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hL := one_lt_logb_of_two_le w hw
  have hLL := (rational_log_factors_lower_bounds w hw).2
  have hcompare : Real.logb (2 : ℝ) (w : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) := by
    change Real.log (w : ℝ) / Real.log 2 ≤ Real.log (w : ℝ) / Real.log 1.9
    exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (Real.log_pos hb)
      (Real.log_le_log (by norm_num) (by norm_num))
  have hnatlog : (Nat.log 2 w : ℝ) ≤ Real.logb (1.9 : ℝ) (w : ℝ) :=
    (Real.natLog_le_logb w 2).trans hcompare
  have hell : ((Nat.log 2 w + 1 : ℕ) : ℝ) ≤ 2 * Real.logb (1.9 : ℝ) (w : ℝ) := by
    push_cast
    linarith
  have hellone : (1 : ℝ) ≤ ((Nat.log 2 w + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (Nat.log 2 w)))
  have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ (r : ℝ)) 3
  have hr3pos : (0 : ℝ) < (r : ℝ) ^ 3 := lt_of_lt_of_le zero_lt_one hr3
  have hLpos : 0 < Real.logb (1.9 : ℝ) (w : ℝ) := lt_trans zero_lt_one hL
  refine ⟨?_, ?_, ?_⟩
  · have hmul : (1 : ℝ) ≤ (r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ) := by
      simpa using mul_le_mul hr3 hellone (by norm_num : (0 : ℝ) ≤ 1) hr3pos.le
    calc
      (2 : ℝ) ≤ 520 * 1 := by norm_num
      _ ≤ 520 * ((r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 520 * (r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ) := by ring
  · calc
      520 * (r : ℝ) ^ 3 * ((Nat.log 2 w + 1 : ℕ) : ℝ) ≤
          520 * (r : ℝ) ^ 3 * (2 * Real.logb (1.9 : ℝ) (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hell (mul_nonneg (by norm_num) hr3pos.le)
      _ = 1040 * ((r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ)) := by ring
      _ < 4000 * ((r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ)) :=
        mul_lt_mul_of_pos_right (by norm_num) (mul_pos hr3pos hLpos)
      _ = (40000 * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ)) * (1 / 10) := by ring
      _ ≤ 40000 * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
          Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hLL
          (mul_nonneg (mul_nonneg (by norm_num) hr3pos.le) hLpos.le)
  · simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) w
theorem exists_perm_image_eq_of_ncard_eq {α : Type*} [Finite α]
    (A B : Set α) (h : A.ncard = B.ncard) :
    ∃ σ : Equiv.Perm α, σ '' A = B := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A.toFinset B.toFinset
    (by simpa only [← Set.ncard_eq_toFinset_card'] using h)
  refine ⟨σ, ?_⟩
  have he := congrArg (fun D : Finset α ↦ (D : Set α)) hσ
  simpa using he
theorem permutation_image_fiber_ncard_eq {α : Type*} [Fintype α]
    (A U : Set α) (h : A.ncard = U.ncard) :
    {σ : Equiv.Perm α | σ '' A = A}.ncard =
      {σ : Equiv.Perm α | σ '' A = U}.ncard := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_image_eq_of_ncard_eq A U h
  apply Set.ncard_congr (fun σ _ ↦ σ.trans τ)
  · intro σ hσ
    change (τ ∘ σ) '' A = U
    calc
      (τ ∘ σ) '' A = τ '' (σ '' A) := (Set.image_image τ σ A).symm
      _ = U := by rw [hσ, hτ]
  · intro σ π _ _ he
    apply Equiv.ext
    intro x
    exact τ.injective (congrArg (fun e : Equiv.Perm α ↦ e x) he)
  · intro π hπ
    refine ⟨π.trans τ.symm, ?_, ?_⟩
    · change (τ.symm ∘ π) '' A = A
      calc
        (τ.symm ∘ π) '' A = τ.symm '' (π '' A) := (Set.image_image τ.symm π A).symm
        _ = A := by rw [hπ, ← hτ]; simp [Set.image_image]
    · apply Equiv.ext
      intro x
      exact τ.apply_symm_apply (π x)
theorem ncard_eq_sum_fiber_ncard {α β : Type*} [Fintype α] [Fintype β]
    (S : Set α) (T : Finset β) (f : α → β) (hf : ∀ x ∈ S, f x ∈ T) :
    S.ncard = ∑ y ∈ T, {x | x ∈ S ∧ f x = y}.ncard := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := S.toFinset) (t := T) (f := f)
    (by intro x hx; simpa using hf x (by simpa using hx))
  have he (y : β) :
      {x | x ∈ S ∧ f x = y}.toFinset = {x ∈ S.toFinset | f x = y} := by
    ext x
    simp
  simpa only [Set.ncard_eq_toFinset_card', he] using hc
theorem permutation_image_family_ncard_mul {α : Type*} [Fintype α]
    (A : Set α) (H : Set (Set α)) (hH : ∀ U ∈ H, U.ncard = A.ncard) :
    {σ : Equiv.Perm α | σ '' A ∈ H}.ncard * {U : Set α | U.ncard = A.ncard}.ncard =
      H.ncard * (Set.univ : Set (Equiv.Perm α)).ncard := by
  classical
  let K := {σ : Equiv.Perm α | σ '' A = A}.ncard
  have hc (G : Set (Set α)) (hG : ∀ U ∈ G, U.ncard = A.ncard) :
      {σ : Equiv.Perm α | σ '' A ∈ G}.ncard = G.ncard * K := by
    rw [ncard_eq_sum_fiber_ncard _ G.toFinset (fun σ : Equiv.Perm α ↦ σ '' A)
      (by intro σ hσ; simpa using hσ)]
    calc
      (∑ U ∈ G.toFinset,
          {σ : Equiv.Perm α | σ '' A ∈ G ∧ σ '' A = U}.ncard) =
          ∑ _U ∈ G.toFinset, K := by
        apply Finset.sum_congr rfl
        intro U hU
        have hUG : U ∈ G := by simpa using hU
        have he : {σ : Equiv.Perm α | σ '' A ∈ G ∧ σ '' A = U} =
            {σ : Equiv.Perm α | σ '' A = U} := by
          ext σ
          exact ⟨And.right, fun h ↦ ⟨h ▸ hUG, h⟩⟩
        rw [he]
        exact (permutation_image_fiber_ncard_eq A U (hG U hUG).symm).symm
      _ = G.ncard * K := by
        simp only [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card', Nat.cast_id]
  let T : Set (Set α) := {U | U.ncard = A.ncard}
  have htotal : {σ : Equiv.Perm α | σ '' A ∈ T} = Set.univ := by
    ext σ
    simp [T, Set.ncard_image_of_injective A σ.injective]
  have hall := hc T (fun _ h ↦ h)
  rw [htotal] at hall
  calc
    _ = (H.ncard * K) * T.ncard := by rw [hc H hH]
    _ = H.ncard * (T.ncard * K) := by ac_rfl
    _ = _ := by rw [← hall]
theorem numbered_disjoint_blocks (n r s : ℕ) (hrs : r * s ≤ n) :
    ∃ A : Fin r → Set (Fin n), (∀ i, (A i).ncard = s) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r × Fin s) (β := Fin n) (by simpa using hrs)
  let A : Fin r → Set (Fin n) := fun i ↦ Set.range (fun j : Fin s ↦ e (i, j))
  refine ⟨A, ?_, ?_⟩
  · intro i
    have hi : Function.Injective (fun j : Fin s ↦ e (i, j)) := by
      intro j k hjk
      exact congrArg Prod.snd (e.injective hjk)
    simpa [A] using Set.ncard_range_of_injective hi
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    exact hij (congrArg Prod.fst (e.injective (ha.trans hb.symm)))
theorem disjoint_blocks_from_dense_family
    (n r s : ℕ) (𝒢 : Set (Set (Fin n))) (hrs : r * s ≤ n)
    (h𝒢 : ∀ U ∈ 𝒢, U.ncard = s)
    (hdense : (r : ℝ) * ((n.choose s : ℝ) - (𝒢.ncard : ℝ)) < (n.choose s : ℝ)) :
    ∃ B : Fin r → Set (Fin n), (∀ i, B i ∈ 𝒢) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) := by
  classical
  obtain ⟨A, hA, hAdis⟩ := numbered_disjoint_blocks n r s hrs
  let T : Set (Set (Fin n)) := {U | U.ncard = s}
  let H : Set (Set (Fin n)) := T \ 𝒢
  have hGT : 𝒢 ⊆ T := fun U hU ↦ h𝒢 U hU
  have hTcard : T.ncard = n.choose s := by
    simpa [T] using Set.ncard_powerset_ncard
      (Set.toFinite (Set.univ : Set (Fin n))) s
  have hHcard : (H.ncard : ℝ) = (n.choose s : ℝ) - (𝒢.ncard : ℝ) := by
    have hc := Set.ncard_sdiff_add_ncard_of_subset hGT
    have hcR : (H.ncard : ℝ) + (𝒢.ncard : ℝ) = (n.choose s : ℝ) := by
      exact_mod_cast hc.trans hTcard
    linarith
  have hgood : ∃ σ : Equiv.Perm (Fin n), ∀ i, σ '' A i ∈ 𝒢 := by
    by_contra hnone
    have hbad : ∀ σ : Equiv.Perm (Fin n), ∃ i, σ '' A i ∈ H := by
      intro σ
      have hnot : ¬ ∀ i, σ '' A i ∈ 𝒢 := fun h ↦ hnone ⟨σ, h⟩
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      refine ⟨i, ?_, hi⟩
      change (σ '' A i).ncard = s
      rw [Set.ncard_image_of_injective _ σ.injective, hA i]
    let S : Set (Equiv.Perm (Fin n) × Fin r) := {p | p.1 '' A p.2 ∈ H}
    have hP_le : (Set.univ : Set (Equiv.Perm (Fin n))).ncard ≤ S.ncard := by
      apply Set.ncard_le_ncard_of_injOn (fun σ ↦ (σ, (hbad σ).choose))
      · intro σ _
        exact (hbad σ).choose_spec
      · intro σ π _ _ he
        exact congrArg Prod.fst he
    have hfiber (i : Fin r) :
        {p : Equiv.Perm (Fin n) × Fin r | p ∈ S ∧ p.2 = i}.ncard =
          {σ : Equiv.Perm (Fin n) | σ '' A i ∈ H}.ncard := by
      apply Set.ncard_congr (fun p _ ↦ p.1)
      · intro p hp
        change p.1 '' A i ∈ H
        simpa only [S, Set.mem_ofPred_eq, hp.2] using hp.1
      · intro p q hp hq he
        exact Prod.ext he (hp.2.trans hq.2.symm)
      · intro σ hσ
        exact ⟨(σ, i), ⟨hσ, rfl⟩, rfl⟩
    have hbound (i : Fin r) :
        ({p : Equiv.Perm (Fin n) × Fin r | p ∈ S ∧ p.2 = i}.ncard : ℝ) *
            (n.choose s : ℝ) ≤
          (H.ncard : ℝ) * ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ) := by
      rw [hfiber i]
      have hc := permutation_image_family_ncard_mul (A i) H
        (fun U hU ↦ hU.1.trans (hA i).symm)
      rw [hA i] at hc
      change _ * T.ncard = _ at hc
      rw [hTcard] at hc
      exact le_of_eq (by exact_mod_cast hc)
    have hsum := ncard_mul_le_of_fiber_bounds S (Set.univ : Set (Fin r))
      Prod.snd (n.choose s : ℝ)
      ((H.ncard : ℝ) * ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ))
      (fun _ _ ↦ Set.mem_univ _) (fun i _ ↦ hbound i)
    have hPpos : 0 < ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ) := by
      exact_mod_cast ((Set.ncard_pos (Set.toFinite _)).mpr
        (⟨Equiv.refl (Fin n), Set.mem_univ _⟩ :
          (Set.univ : Set (Equiv.Perm (Fin n))).Nonempty))
    have hleft : ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ) *
        (n.choose s : ℝ) ≤ (S.ncard : ℝ) * (n.choose s : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hP_le) (by positivity)
    have hsum' : ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ) *
        (n.choose s : ℝ) ≤ (r : ℝ) * ((n.choose s : ℝ) - (𝒢.ncard : ℝ)) *
          ((Set.univ : Set (Equiv.Perm (Fin n))).ncard : ℝ) := by
      simpa only [Set.ncard_univ, Nat.card_fin, hHcard, mul_assoc] using hleft.trans hsum
    have hd := mul_lt_mul_of_pos_right hdense hPpos
    nlinarith
  obtain ⟨σ, hσ⟩ := hgood
  refine ⟨fun i ↦ σ '' A i, hσ, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
  have hab : a = b := σ.injective (hax.trans hbx.symm)
  exact Set.disjoint_left.mp (hAdis i j hij) ha (hab ▸ hb)
theorem choose_add_mul_pow_le (v m t : ℕ) :
    v.choose (m + t) * m ^ t ≤ v.choose m * v ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : v.choose (m + t + 1) * m ≤ v.choose (m + t) * v := by
      calc
        v.choose (m + t + 1) * m ≤ v.choose (m + t + 1) * (m + t + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = v.choose (m + t) * (v - (m + t)) := Nat.choose_succ_right_eq v (m + t)
        _ ≤ v.choose (m + t) * v := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc
      v.choose (m + (t + 1)) * m ^ (t + 1) =
          (v.choose (m + t + 1) * m) * m ^ t := by ring
      _ ≤ (v.choose (m + t) * v) * m ^ t := Nat.mul_le_mul_right _ hstep
      _ = (v.choose (m + t) * m ^ t) * v := by ring
      _ ≤ (v.choose m * v ^ t) * v := Nat.mul_le_mul_right _ ih
      _ = v.choose m * v ^ (t + 1) := by rw [pow_succ]; ring
theorem binomial_upper_half_tail (w : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    (∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ) * (q⁻¹) ^ (2 * t)) ≤
      (2 / q) ^ w := by
  have hqpos : 0 < q := by linarith
  have hinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  have hinvone : q⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr (by linarith)
  have hsum : (∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ)) ≤ (2 : ℝ) ^ w := by
    calc
      (∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ)) ≤
          ∑ t ∈ Finset.range (w + 1), (w.choose t : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          simp only [Finset.mem_Icc] at ht
          exact Finset.mem_range.mpr (by omega)
        · intro t _ _
          exact Nat.cast_nonneg _
      _ = (2 : ℝ) ^ w := by exact_mod_cast Nat.sum_range_choose w
  calc
    (∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ) * (q⁻¹) ^ (2 * t)) ≤
        ∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ) * (q⁻¹) ^ w := by
      apply Finset.sum_le_sum
      intro t ht
      have hwt : w ≤ 2 * t := by
        simp only [Finset.mem_Icc] at ht
        omega
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hinv hinvone hwt)
        (Nat.cast_nonneg _)
    _ = (∑ t ∈ Finset.Icc (w / 2 + 1) w, (w.choose t : ℝ)) * (q⁻¹) ^ w :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (2 : ℝ) ^ w * (q⁻¹) ^ w := mul_le_mul_of_nonneg_right hsum (pow_nonneg hinv _)
    _ = (2 / q) ^ w := by rw [← mul_pow, div_eq_mul_inv]
theorem exists_minimal_fragment_label (n d : ℕ) (f : Fin d → Set (Fin n))
    (i : Fin d) (W : Set (Fin n)) :
    ∃ j : Fin d, f j ⊆ f i ∪ W ∧
      ∀ a : Fin d, f a ⊆ f i ∪ W → (f j \ W).ncard ≤ (f a \ W).ncard := by
  classical
  let s : Finset (Fin d) := Finset.univ.filter fun j ↦ f j ⊆ f i ∪ W
  have hi : i ∈ s := by simp [s, Set.subset_union_left]
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s (fun j ↦ (f j \ W).ncard) ⟨i, hi⟩
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro a ha
  exact hmin a (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩)
noncomputable def minimalFragmentLabel {n d : ℕ} (f : Fin d → Set (Fin n))
    (i : Fin d) (W : Set (Fin n)) : Fin d :=
  Classical.choose (exists_minimal_fragment_label n d f i W)
noncomputable def minimalFragment {n d : ℕ} (f : Fin d → Set (Fin n))
    (i : Fin d) (W : Set (Fin n)) : Set (Fin n) :=
  f (minimalFragmentLabel f i W) \ W
theorem minimalFragment_spec {n d : ℕ} (f : Fin d → Set (Fin n))
    (i : Fin d) (W : Set (Fin n)) :
    f (minimalFragmentLabel f i W) ⊆ f i ∪ W ∧
      ∀ a : Fin d, f a ⊆ f i ∪ W → (minimalFragment f i W).ncard ≤ (f a \ W).ncard :=
  Classical.choose_spec (exists_minimal_fragment_label n d f i W)
theorem minimalFragment_subset {n d : ℕ} (f : Fin d → Set (Fin n))
    (i : Fin d) (W : Set (Fin n)) : minimalFragment f i W ⊆ f i :=
  fragment_shrinks_current_edge f i (minimalFragmentLabel f i W) W
    (minimalFragment_spec f i W).1
theorem ncard_eq_sum_ncard_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    (s : Set α) (t : Finset β) (f : α → β) (hf : ∀ x ∈ s, f x ∈ t) :
    (s.ncard : ℝ) = ∑ y ∈ t, ({x | x ∈ s ∧ f x = y}.ncard : ℝ) := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := s.toFinset) (t := t) (f := f)
    (by intro x hx; exact hf x (by simpa using hx))
  have he (y : β) :
      {x | x ∈ s ∧ f x = y}.toFinset = {x ∈ s.toFinset | f x = y} := by
    ext x
    simp
  simp_rw [Set.ncard_eq_toFinset_card', he]
  exact_mod_cast hc
theorem normalize_fragment_rank_bound (v k m t : ℕ) (c κ N q : ℝ)
    (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hN : 0 ≤ N) (hq : 2 ≤ q) (hv : 0 < v)
    (hscale : q ^ 2 * (v : ℝ) ≤ (m : ℝ) * κ)
    (hcount : c * κ ^ t ≤ (v.choose (m + t) : ℝ) * (k.choose t : ℝ) * N) :
    c ≤ (v.choose m : ℝ) * (k.choose t : ℝ) * N * (q⁻¹) ^ (2 * t) := by
  have hqpos : 0 < q := by linarith
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hbinom : (v.choose (m + t) : ℝ) * (m : ℝ) ^ t ≤
      (v.choose m : ℝ) * (v : ℝ) ^ t := by exact_mod_cast choose_add_mul_pow_le v m t
  have hscale_pow := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg q) (Nat.cast_nonneg v)) hscale t
  have hmain : (c * q ^ (2 * t)) * (v : ℝ) ^ t ≤
      ((v.choose m : ℝ) * (k.choose t : ℝ) * N) * (v : ℝ) ^ t := by
    calc
      (c * q ^ (2 * t)) * (v : ℝ) ^ t = c * (q ^ 2 * (v : ℝ)) ^ t := by
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ c * ((m : ℝ) * κ) ^ t := mul_le_mul_of_nonneg_left hscale_pow hc
      _ = (c * κ ^ t) * (m : ℝ) ^ t := by rw [mul_pow]; ring
      _ ≤ ((v.choose (m + t) : ℝ) * (k.choose t : ℝ) * N) * (m : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right hcount (pow_nonneg (Nat.cast_nonneg m) t)
      _ ≤ ((v.choose m : ℝ) * (k.choose t : ℝ) * N) * (v : ℝ) ^ t := by
        convert mul_le_mul_of_nonneg_right hbinom
          (mul_nonneg (Nat.cast_nonneg (k.choose t)) hN) using 1 <;> ring
  have hcancel := (mul_le_mul_iff_left₀ (pow_pos hvpos t)).mp hmain
  have hnorm := mul_le_mul_of_nonneg_right hcancel
    (pow_nonneg (inv_nonneg.mpr hqpos.le) (2 * t))
  simpa only [inv_pow, mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hqpos (2 * t))),
    mul_one] using hnorm
theorem minimal_fragment_rank_bound (n d k m t : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N q : ℝ) (hκ : 0 < κ) (hN : 0 ≤ N)
    (hq : 2 ≤ q) (hV : 0 < V.ncard)
    (hscale : q ^ 2 * (V.ncard : ℝ) ≤ (m : ℝ) * κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ k)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ({p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
      (minimalFragment f p.1 p.2).ncard = t}.ncard : ℝ) ≤
      (V.ncard.choose m : ℝ) * (k.choose t : ℝ) * N * (q⁻¹) ^ (2 * t) := by
  have hsub : {p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
      (minimalFragment f p.1 p.2).ncard = t} ⊆
      {p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
        (∀ j : Fin d, f j ⊆ f p.1 ∪ p.2 → t ≤ (f j \ p.2).ncard) ∧
        (∃ j : Fin d, f j ⊆ f p.1 ∪ p.2 ∧ (f j \ p.2).ncard = t)} := by
    intro p hp
    refine ⟨hp.1, hp.2.1, ?_, ?_⟩
    · intro a ha
      rw [← hp.2.2]
      exact (minimalFragment_spec f p.1 p.2).2 a ha
    · exact ⟨minimalFragmentLabel f p.1 p.2, (minimalFragment_spec f p.1 p.2).1, hp.2.2⟩
  apply normalize_fragment_rank_bound V.ncard k m t _ κ N q
    (Nat.cast_nonneg _) hκ.le hN hq hV hscale
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Set.ncard_le_ncard hsub)
    (pow_nonneg hκ.le t)).trans (minimal_fragment_count n d k m t V f κ N hκ hN hsys hcode)
theorem bad_fragment_pair_count (n d k m : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N q : ℝ) (hκ : 0 < κ) (hN : 0 ≤ N)
    (hq : 2 ≤ q) (hV : 0 < V.ncard)
    (hscale : q ^ 2 * (V.ncard : ℝ) ≤ (m : ℝ) * κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ k)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ({p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
      k / 2 < (minimalFragment f p.1 p.2).ncard}.ncard : ℝ) ≤
      (V.ncard.choose m : ℝ) * N * (2 / q) ^ k := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  let s : Set (Fin d × Set (Fin n)) := {p | p.2 ⊆ V ∧ p.2.ncard = m ∧
    k / 2 < (minimalFragment f p.1 p.2).ncard}
  let rank (p : Fin d × Set (Fin n)) := (minimalFragment f p.1 p.2).ncard
  have hmap (p : Fin d × Set (Fin n)) (hp : p ∈ s) :
      rank p ∈ Finset.Icc (k / 2 + 1) k := by
    have hle := (Set.ncard_le_ncard (minimalFragment_subset f p.1 p.2)).trans (hsys p.1).2
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hp.2.2, hle⟩
  change (s.ncard : ℝ) ≤ _
  rw [ncard_eq_sum_ncard_fibers s (Finset.Icc (k / 2 + 1) k) rank hmap]
  calc
    (∑ t ∈ Finset.Icc (k / 2 + 1) k, ({p | p ∈ s ∧ rank p = t}.ncard : ℝ)) ≤
        ∑ t ∈ Finset.Icc (k / 2 + 1) k,
          (V.ncard.choose m : ℝ) * (k.choose t : ℝ) * N * (q⁻¹) ^ (2 * t) := by
      apply Finset.sum_le_sum
      intro t _ht
      have hsub : {p | p ∈ s ∧ rank p = t} ⊆
          {p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
            (minimalFragment f p.1 p.2).ncard = t} := by
        intro p hp
        exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
      have hc : ({p | p ∈ s ∧ rank p = t}.ncard : ℝ) ≤
          ({p : Fin d × Set (Fin n) | p.2 ⊆ V ∧ p.2.ncard = m ∧
            (minimalFragment f p.1 p.2).ncard = t}.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsub
      exact hc.trans
        (minimal_fragment_rank_bound n d k m t V f κ N q hκ hN hq hV hscale hsys hcode)
    _ = (V.ncard.choose m : ℝ) * N *
        (∑ t ∈ Finset.Icc (k / 2 + 1) k, (k.choose t : ℝ) * (q⁻¹) ^ (2 * t)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ (V.ncard.choose m : ℝ) * N * (2 / q) ^ k :=
      mul_le_mul_of_nonneg_left (binomial_upper_half_tail k q hq)
        (mul_nonneg (Nat.cast_nonneg _) hN)
theorem retained_fragment_family (n d k : ℕ) (V W : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N : ℝ) (hκ : 0 ≤ κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ k)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ∃ (d' : ℕ) (g : Fin d' → Set (Fin n)) (e : Fin d' → Fin d),
      Function.Injective e ∧
      d' = {i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}.ncard ∧
      (∀ a, g a ⊆ f (e a)) ∧
      (∀ a, g a ⊆ V \ W ∧ (g a).ncard ≤ k / 2) ∧
      (∀ U : Set (Fin n),
        ({a : Fin d' | U ⊆ g a}.ncard : ℝ) * κ ^ U.ncard ≤ N) ∧
      (∀ a, ∃ i : Fin d, f i ⊆ g a ∪ W) := by
  classical
  let L : Set (Fin d) := {i | (minimalFragment f i W).ncard ≤ k / 2}
  let b : Fin (Fintype.card L) ≃ L := (Fintype.equivFin L).symm
  let e (a : Fin (Fintype.card L)) : Fin d := (b a).val
  let g (a : Fin (Fintype.card L)) : Set (Fin n) := minimalFragment f (e a) W
  have he : Function.Injective e := fun a a' h ↦ b.injective (Subtype.ext h)
  have hshrink (a : Fin (Fintype.card L)) : g a ⊆ f (e a) :=
    minimalFragment_subset f (e a) W
  refine ⟨Fintype.card L, g, e, he, ?_, hshrink, ?_, ?_, ?_⟩
  · simpa only [Nat.card_coe_set_eq] using
      (show Fintype.card L = Nat.card L from Nat.card_eq_fintype_card.symm)
  · intro a
    refine ⟨?_, (b a).property⟩
    intro x hx
    exact ⟨(hsys (e a)).1 (hshrink a hx), hx.2⟩
  · exact codegree_bound_of_injective_shrinking f g e he hshrink κ N hκ hcode
  · intro a
    refine ⟨minimalFragmentLabel f (e a) W, ?_⟩
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl ⟨hx, hxW⟩
theorem dyadic_loss_step (w : ℕ) (hw : 0 < w) (a : ℝ) (ha : 0 ≤ a) :
    (∑ j ∈ Finset.Icc 1 (w / 2), a ^ j) + a ^ w ≤
      ∑ j ∈ Finset.Icc 1 w, a ^ j := by
  have hnot : w ∉ Finset.Icc 1 (w / 2) := by simp only [Finset.mem_Icc]; omega
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_Icc.mpr ⟨hw, le_rfl⟩
    · exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2.trans (Nat.div_le_self _ _)⟩
  · intro j _ _
    exact pow_nonneg ha j
theorem ncard_pair_snd_fiber {α β : Type*} [Finite α] [Finite β]
    (P : α → β → Prop) (b : β) :
    {p : α × β | P p.1 p.2 ∧ p.2 = b}.ncard = {a : α | P a b}.ncard := by
  classical
  have he : {p : α × β | P p.1 p.2 ∧ p.2 = b} =
      (fun a : α ↦ (a, b)) '' {a : α | P a b} := by
    ext p
    constructor
    · rintro ⟨hp, hb⟩
      refine ⟨p.1, ?_, ?_⟩
      · change P p.1 b
        simpa only [hb] using hp
      · exact Prod.ext rfl hb.symm
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, rfl⟩
  rw [he, Set.ncard_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)]
theorem ncard_pair_fst_fiber {α β : Type*} [Finite α] [Finite β]
    (P : α → β → Prop) (a : α) :
    {p : α × β | P p.1 p.2 ∧ p.1 = a}.ncard = {b : β | P a b}.ncard := by
  classical
  have he : {p : α × β | P p.1 p.2 ∧ p.1 = a} =
      (fun b : β ↦ (a, b)) '' {b : β | P a b} := by
    ext p
    constructor
    · rintro ⟨hp, ha⟩
      refine ⟨p.2, ?_, ?_⟩
      · change P a p.2
        simpa only [ha] using hp
      · exact Prod.ext ha.symm rfl
    · rintro ⟨b, hb, rfl⟩
      exact ⟨hb, rfl⟩
  rw [he, Set.ncard_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h)]
theorem retained_fragment_average (n d k m : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N q : ℝ) (hκ : 0 < κ) (hN : 0 ≤ N)
    (hq : 2 ≤ q) (hV : 0 < V.ncard)
    (hscale : q ^ 2 * (V.ncard : ℝ) ≤ (m : ℝ) * κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ k)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ((d : ℝ) - N * (2 / q) ^ k) * (V.ncard.choose m : ℝ) ≤
      ∑ W ∈ (Set.toFinite {W : Set (Fin n) | W ⊆ V ∧ W.ncard = m}).toFinset,
        ({i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}.ncard : ℝ) := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  let B : Set (Set (Fin n)) := {W | W ⊆ V ∧ W.ncard = m}
  let bad : Set (Fin d × Set (Fin n)) := {p | p.2 ∈ B ∧
    k / 2 < (minimalFragment f p.1 p.2).ncard}
  have hbad : (bad.ncard : ℝ) ≤ (V.ncard.choose m : ℝ) * N * (2 / q) ^ k := by
    convert bad_fragment_pair_count n d k m V f κ N q hκ hN hq hV hscale hsys hcode using 1
    congr 2
    ext p
    simp only [bad, B, Set.mem_setOf_eq, and_assoc]
  have hpartition : (bad.ncard : ℝ) =
      ∑ W ∈ B.toFinset, ({i : Fin d | k / 2 < (minimalFragment f i W).ncard}.ncard : ℝ) := by
    rw [ncard_eq_sum_ncard_fibers bad B.toFinset Prod.snd
      (fun p hp ↦ Set.mem_toFinset.mpr hp.1)]
    apply Finset.sum_congr rfl
    intro W hW
    change ({p : Fin d × Set (Fin n) | (p.2 ∈ B ∧
      k / 2 < (minimalFragment f p.1 p.2).ncard) ∧ p.2 = W}.ncard : ℝ) = _
    rw [ncard_pair_snd_fiber (fun i W ↦ W ∈ B ∧
      k / 2 < (minimalFragment f i W).ncard) W]
    have hWB := Set.mem_toFinset.mp hW
    simp only [hWB, true_and]
  have hcompl (W : Set (Fin n)) :
      ({i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}.ncard : ℝ) =
        (d : ℝ) - ({i : Fin d | k / 2 < (minimalFragment f i W).ncard}.ncard : ℝ) := by
    have he : {i : Fin d | k / 2 < (minimalFragment f i W).ncard} =
        {i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}ᶜ := by
      ext i
      simp
    have hc := Set.ncard_add_ncard_compl
      {i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}
    rw [← he] at hc
    have hcR : ({i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}.ncard : ℝ) +
        ({i : Fin d | k / 2 < (minimalFragment f i W).ncard}.ncard : ℝ) = d := by
      simpa only [Nat.cast_add, Nat.card_fin] using congrArg (fun z : ℕ ↦ (z : ℝ)) hc
    linarith
  rw [Set.toFinite_toFinset]
  change ((d : ℝ) - N * (2 / q) ^ k) * (V.ncard.choose m : ℝ) ≤
    ∑ W ∈ B.toFinset,
      ({i : Fin d | (minimalFragment f i W).ncard ≤ k / 2}.ncard : ℝ)
  simp_rw [hcompl]
  rw [Finset.sum_sub_distrib, ← hpartition]
  have hBcard : (B.toFinset.card : ℝ) = (V.ncard.choose m : ℝ) := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_powerset_ncard (Set.toFinite V) m]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hBcard]
  nlinarith
theorem disjoint_union_pair_count (n a b : ℕ)
    (P : Set (Set (Fin n) × Set (Fin n))) (G : Set (Set (Fin n)))
    (hG : ∀ U ∈ G, U.ncard = a + b)
    (hunion : ∀ p ∈ P, p.1 ∪ p.2 ∈ G)
    (hcard : ∀ p ∈ P, p.1.ncard = a)
    (hdis : ∀ p ∈ P, Disjoint p.1 p.2) :
    (P.ncard : ℝ) ≤ (G.ncard : ℝ) * ((a + b).choose a : ℝ) := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  have hfiber (U : Set (Fin n)) (hU : U ∈ G) :
      ({p | p ∈ P ∧ p.1 ∪ p.2 = U}.ncard : ℝ) ≤ ((a + b).choose a : ℝ) := by
    have hrecover (p : Set (Fin n) × Set (Fin n)) (hp : p ∈ P)
        (hpU : p.1 ∪ p.2 = U) : p.2 = U \ p.1 := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, fun hx₁ ↦ Set.disjoint_left.mp (hdis p hp) hx₁ hx⟩
        rw [← hpU]
        exact Or.inr hx
      · rintro ⟨hxU, hx₁⟩
        rw [← hpU] at hxU
        exact hxU.resolve_left hx₁
    have hc : {p | p ∈ P ∧ p.1 ∪ p.2 = U}.ncard ≤
        {W : Set (Fin n) | W ⊆ U ∧ W.ncard = a}.ncard := by
      apply Set.ncard_le_ncard_of_injOn Prod.fst
      · intro p hp
        refine ⟨?_, hcard p hp.1⟩
        rw [← hp.2]
        exact Set.subset_union_left
      · intro p hp q hq hpq
        apply Prod.ext hpq
        rw [hrecover p hp.1 hp.2, hrecover q hq.1 hq.2, hpq]
    rw [Set.ncard_powerset_ncard (Set.toFinite U) a, hG U hU] at hc
    exact_mod_cast hc
  simpa only [mul_one] using
    ncard_mul_le_of_fiber_bounds P G (fun p ↦ p.1 ∪ p.2)
      1 ((a + b).choose a : ℝ) hunion (by
        intro U hU
        simpa only [mul_one] using hfiber U hU)
theorem choose_block_identity (v m s : ℕ) :
    (v.choose m : ℝ) * ((v - m).choose s : ℝ) =
      (v.choose (m + s) : ℝ) * ((m + s).choose m : ℝ) := by
  have h := Nat.choose_mul (n := v) (k := m + s) (s := m) (Nat.le_add_right m s)
  simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
    congrArg (fun z : ℕ ↦ (z : ℝ)) h.symm
theorem zero_width_hitting (n d s : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (N : ℝ) (hN : 0 ≤ N) (hdN : (d : ℝ) ≤ N)
    (hf : ∀ i, (f i).ncard = 0) :
    (d : ℝ) * (V.ncard.choose s : ℝ) ≤ N *
      ({U : Set (Fin n) | U ⊆ V ∧ U.ncard = s ∧ ∃ i : Fin d, f i ⊆ U}.ncard : ℝ) := by
  by_cases hd : d = 0
  · subst d
    simpa only [Nat.cast_zero, zero_mul] using
      mul_nonneg hN (Nat.cast_nonneg
        {U : Set (Fin n) | U ⊆ V ∧ U.ncard = s ∧ ∃ i : Fin 0, f i ⊆ U}.ncard :
          (0 : ℝ) ≤ _)
  · let i : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hempty : f i = ∅ := (Set.ncard_eq_zero (Set.toFinite (f i))).mp (hf i)
    have hG : {U : Set (Fin n) | U ⊆ V ∧ U.ncard = s ∧ ∃ i : Fin d, f i ⊆ U} =
        {U : Set (Fin n) | U ⊆ V ∧ U.ncard = s} := by
      ext U
      constructor
      · intro hU
        exact ⟨hU.1, hU.2.1⟩
      · intro hU
        exact ⟨hU.1, hU.2, i, by rw [hempty]; exact Set.empty_subset U⟩
    rw [hG, Set.ncard_powerset_ncard (Set.toFinite V) s]
    exact mul_le_mul_of_nonneg_right hdN (Nat.cast_nonneg _)
theorem labelled_halving_hitting_step (n d w ℓ m : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N q : ℝ) (hκ : 0 < κ) (hN : 0 < N)
    (hq : 2 ≤ q) (hw : 0 < w) (hV : 0 < V.ncard)
    (hscale : q ^ 2 * (V.ncard : ℝ) ≤ (m : ℝ) * κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ w)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N)
    (hchild : ∀ W ⊆ V, W.ncard = m → ∀ (d' : ℕ) (g : Fin d' → Set (Fin n)),
      (∀ a, g a ⊆ V \ W ∧ (g a).ncard ≤ w / 2) →
      (∀ U : Set (Fin n), ({a : Fin d' | U ⊆ g a}.ncard : ℝ) * κ ^ U.ncard ≤ N) →
      ((d' : ℝ) - N * (∑ j ∈ Finset.Icc 1 (w / 2), (2 / q) ^ j)) *
          ((V \ W).ncard.choose (ℓ * m) : ℝ) ≤ N *
        ({U : Set (Fin n) | U ⊆ V \ W ∧ U.ncard = ℓ * m ∧
          ∃ a : Fin d', g a ⊆ U}.ncard : ℝ)) :
    ((d : ℝ) - N * (∑ j ∈ Finset.Icc 1 w, (2 / q) ^ j)) *
        (V.ncard.choose ((ℓ + 1) * m) : ℝ) ≤ N *
      ({U : Set (Fin n) | U ⊆ V ∧ U.ncard = (ℓ + 1) * m ∧
        ∃ i : Fin d, f i ⊆ U}.ncard : ℝ) := by
  classical
  letI := Fintype.ofFinite (Set (Fin n))
  let B : Set (Set (Fin n)) := {W | W ⊆ V ∧ W.ncard = m}
  let L (k : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 k, (2 / q) ^ j
  choose dW gW eW hdata using
    (fun W : Set (Fin n) ↦ retained_fragment_family n d w V W f κ N hκ.le hsys hcode)
  have hdim (W : Set (Fin n)) :
      dW W = {i : Fin d | (minimalFragment f i W).ncard ≤ w / 2}.ncard :=
    (hdata W).2.1
  let hit (W : Set (Fin n)) : Set (Set (Fin n)) :=
    {U | U ⊆ V \ W ∧ U.ncard = ℓ * m ∧ ∃ a : Fin (dW W), gW W a ⊆ U}
  let H : Set (Set (Fin n) × Set (Fin n)) := {p | p.1 ∈ B ∧ p.2 ∈ hit p.1}
  let G : Set (Set (Fin n)) :=
    {U | U ⊆ V ∧ U.ncard = (ℓ + 1) * m ∧ ∃ i : Fin d, f i ⊆ U}
  have hHsum : (H.ncard : ℝ) = ∑ W ∈ B.toFinset, ((hit W).ncard : ℝ) := by
    rw [ncard_eq_sum_ncard_fibers H B.toFinset Prod.fst
      (fun p hp ↦ Set.mem_toFinset.mpr hp.1)]
    apply Finset.sum_congr rfl
    intro W hW
    change ({p : Set (Fin n) × Set (Fin n) |
      (p.1 ∈ B ∧ p.2 ∈ hit p.1) ∧ p.1 = W}.ncard : ℝ) = _
    rw [ncard_pair_fst_fiber (fun W U ↦ W ∈ B ∧ U ∈ hit W) W]
    have hWB := Set.mem_toFinset.mp hW
    simp only [hWB, true_and, Set.setOf_mem_eq]
  have hBcard : (B.toFinset.card : ℝ) = (V.ncard.choose m : ℝ) := by
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_powerset_ncard (Set.toFinite V) m]
  have havg : ((d : ℝ) - N * (2 / q) ^ w) * (V.ncard.choose m : ℝ) ≤
      ∑ W ∈ B.toFinset, (dW W : ℝ) := by
    simpa only [hdim, Set.toFinite_toFinset] using
      retained_fragment_average n d w m V f κ N q hκ hN.le hq hV hscale hsys hcode
  have hsum : (∑ W ∈ B.toFinset,
      ((dW W : ℝ) - N * L (w / 2)) * ((V.ncard - m).choose (ℓ * m) : ℝ)) ≤
      ∑ W ∈ B.toFinset, N * ((hit W).ncard : ℝ) := by
    apply Finset.sum_le_sum
    intro W hW
    have hWB := Set.mem_toFinset.mp hW
    have hc := hchild W hWB.1 hWB.2 (dW W) (gW W)
      (hdata W).2.2.2.1 (hdata W).2.2.2.2.1
    have hrem : (V \ W).ncard = V.ncard - m := by
      have hc := Set.ncard_sdiff_add_ncard_of_subset hWB.1
      rw [hWB.2] at hc
      omega
    rw [hrem] at hc
    exact hc
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    hBcard, ← Finset.mul_sum, ← hHsum] at hsum
  have hloss : L (w / 2) + (2 / q) ^ w ≤ L w :=
    dyadic_loss_step w hw (2 / q) (div_nonneg (by norm_num) (by linarith))
  have hloss_scaled := mul_le_mul_of_nonneg_left hloss hN.le
  have hloss_scaled' := mul_le_mul_of_nonneg_left hloss_scaled
    (Nat.cast_nonneg (V.ncard.choose m) : (0 : ℝ) ≤ V.ncard.choose m)
  have hlower :
      ((d : ℝ) - N * L w) * (V.ncard.choose m : ℝ) *
          ((V.ncard - m).choose (ℓ * m) : ℝ) ≤ N * (H.ncard : ℝ) := by
    apply le_trans ?_ hsum
    apply mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    nlinarith [havg, hloss_scaled']
  have htotal : (ℓ + 1) * m = m + ℓ * m := by ring
  have hdis (p : Set (Fin n) × Set (Fin n)) (hp : p ∈ H) : Disjoint p.1 p.2 := by
    exact Set.disjoint_left.mpr fun x hxW hxU ↦ (hp.2.1 hxU).2 hxW
  have hHbound : (H.ncard : ℝ) ≤ (G.ncard : ℝ) * ((m + ℓ * m).choose m : ℝ) := by
    apply disjoint_union_pair_count n m (ℓ * m) H G
    · intro U hU
      exact hU.2.1.trans htotal
    · intro p hp
      refine ⟨Set.union_subset hp.1.1 (fun x hx ↦ (hp.2.1 hx).1), ?_, ?_⟩
      · rw [Set.ncard_union_eq (hdis p hp), hp.1.2, hp.2.2.1, htotal]
      · obtain ⟨a, ha⟩ := hp.2.2.2
        obtain ⟨i, hi⟩ := (hdata p.1).2.2.2.2.2 a
        refine ⟨i, ?_⟩
        intro x hx
        rcases hi hx with hxg | hxW
        · exact Or.inr (ha hxg)
        · exact Or.inl hxW
    · intro p hp
      exact hp.1.2
    · exact hdis
  change ((d : ℝ) - N * L w) * (V.ncard.choose ((ℓ + 1) * m) : ℝ) ≤ N * (G.ncard : ℝ)
  have hchoosepos : (0 : ℝ) < ((m + ℓ * m).choose m : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m (ℓ * m))
  apply (mul_le_mul_iff_left₀ hchoosepos).mp
  calc
    (((d : ℝ) - N * L w) * (V.ncard.choose ((ℓ + 1) * m) : ℝ)) *
        ((m + ℓ * m).choose m : ℝ) =
        ((d : ℝ) - N * L w) * (V.ncard.choose m : ℝ) *
          ((V.ncard - m).choose (ℓ * m) : ℝ) := by
      rw [htotal, mul_assoc, ← choose_block_identity]
      ring
    _ ≤ N * (H.ncard : ℝ) := hlower
    _ ≤ N * ((G.ncard : ℝ) * ((m + ℓ * m).choose m : ℝ)) :=
      mul_le_mul_of_nonneg_left hHbound hN.le
    _ = (N * (G.ncard : ℝ)) * ((m + ℓ * m).choose m : ℝ) := by ring
theorem labelled_halving_hitting (n d w ℓ m : ℕ) (V : Set (Fin n))
    (f : Fin d → Set (Fin n)) (κ N q : ℝ) (hκ : 0 < κ) (hN : 0 < N)
    (hq : 2 ≤ q) (hm : 0 < m) (hroom : ℓ * m ≤ V.ncard) (hw : w < 2 ^ ℓ)
    (hscale : q ^ 2 * (V.ncard : ℝ) ≤ (m : ℝ) * κ)
    (hsys : ∀ i, f i ⊆ V ∧ (f i).ncard ≤ w)
    (hcode : ∀ U : Set (Fin n),
      ({i : Fin d | U ⊆ f i}.ncard : ℝ) * κ ^ U.ncard ≤ N) :
    ((d : ℝ) - N * (∑ j ∈ Finset.Icc 1 w, (2 / q) ^ j)) *
        (V.ncard.choose (ℓ * m) : ℝ) ≤ N *
      ({U : Set (Fin n) | U ⊆ V ∧ U.ncard = ℓ * m ∧
        ∃ i : Fin d, f i ⊆ U}.ncard : ℝ) := by
  induction ℓ generalizing d w V f with
  | zero =>
    have hwzero : w = 0 := by simpa using hw
    subst w
    have hdN : (d : ℝ) ≤ N := by simpa using hcode ∅
    simpa using zero_width_hitting n d 0 V f N hN.le hdN
      (fun i ↦ Nat.eq_zero_of_le_zero (hsys i).2)
  | succ ℓ ih =>
    by_cases hwzero : w = 0
    · subst w
      have hdN : (d : ℝ) ≤ N := by simpa using hcode ∅
      simpa using zero_width_hitting n d ((ℓ + 1) * m) V f N hN.le hdN
        (fun i ↦ Nat.eq_zero_of_le_zero (hsys i).2)
    · have hV : 0 < V.ncard := by
        have hmle : m ≤ (ℓ + 1) * m := by rw [Nat.add_mul]; omega
        exact hm.trans_le (hmle.trans hroom)
      apply labelled_halving_hitting_step n d w ℓ m V f κ N q hκ hN hq
        (Nat.pos_of_ne_zero hwzero) hV hscale hsys hcode
      intro W hWV hWcard d' g hgsys hgcode
      apply ih (d := d') (w := w / 2) (V := V \ W) (f := g)
      · have hc := Set.ncard_sdiff_add_ncard_of_subset hWV
        rw [hWcard] at hc
        rw [Nat.succ_mul] at hroom
        omega
      · rw [pow_succ] at hw
        omega
      · apply le_trans _ hscale
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg q)
        exact_mod_cast Set.ncard_le_ncard (Set.sdiff_subset : V \ W ⊆ V)
      · exact hgsys
      · exact hgcode
theorem spread_parameter_le_ground_size (n : ℕ) (ℋ : Set (Set (Fin n)))
    (κ : ℝ) (hκ : 0 ≤ κ) (hne : ℋ.Nonempty) (hempty : (∅ : Set (Fin n)) ∉ ℋ)
    (hcode : ∀ U : Set (Fin n),
      ({A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A}.ncard : ℝ) * κ ^ U.ncard ≤
        (ℋ.ncard : ℝ)) : κ ≤ n := by
  classical
  letI := Fintype.ofFinite ℋ
  have hA (A : ℋ) : (A : Set (Fin n)).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    exact hempty (he ▸ A.property)
  let p (A : ℋ) : Fin n := (hA A).choose
  have hp (A : ℋ) : p A ∈ (A : Set (Fin n)) := (hA A).choose_spec
  have htotal := ncard_mul_le_of_fiber_bounds
    (Set.univ : Set ℋ) (Set.univ : Set (Fin n)) p κ (ℋ.ncard : ℝ)
    (fun _ _ ↦ Set.mem_univ _) (by
      intro x _
      have hfib : {A : ℋ | A ∈ Set.univ ∧ p A = x}.ncard ≤
          {A : Set (Fin n) | A ∈ ℋ ∧ ({x} : Set (Fin n)) ⊆ A}.ncard := by
        apply Set.ncard_le_ncard_of_injOn (fun A : ℋ ↦ A.val)
        · intro A hAx
          refine ⟨A.property, Set.singleton_subset_iff.mpr ?_⟩
          exact hAx.2 ▸ hp A
        · intro A _ B _ hAB
          exact Subtype.ext hAB
      have hmul := mul_le_mul_of_nonneg_right
        (show ({A : ℋ | A ∈ Set.univ ∧ p A = x}.ncard : ℝ) ≤
          ({A : Set (Fin n) | A ∈ ℋ ∧ ({x} : Set (Fin n)) ⊆ A}.ncard : ℝ)
          by exact_mod_cast hfib) hκ
      exact hmul.trans (by simpa using hcode {x}))
  have hsource : (Set.univ : Set ℋ).ncard = ℋ.ncard := by
    rw [Set.ncard_univ, Nat.card_coe_set_eq]
  have htarget : (Set.univ : Set (Fin n)).ncard = n := by simp
  rw [hsource, htarget] at htotal
  have hmass : (0 : ℝ) < (ℋ.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos).mpr hne
  nlinarith
theorem spread_matching_block_parameters (r n ℓ : ℕ) (κ : ℝ)
    (hr : 3 ≤ r) (hℓ : 0 < ℓ) (hκ : 0 < κ) (hκn : κ ≤ n)
    (hlarge : 260 * (r : ℝ) ^ 3 * (ℓ : ℝ) ≤ κ) :
    ∃ m : ℕ, 0 < m ∧ r * (ℓ * m) ≤ n ∧ ℓ * m ≤ n ∧
      (8 * (r : ℝ)) ^ 2 * (n : ℝ) ≤ (m : ℝ) * κ := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hn : (0 : ℝ) < n := hκ.trans_le hκn
  let x : ℝ := 64 * (r : ℝ) ^ 2 * (n : ℝ) / κ
  have hx : 0 < x := by dsimp [x]; positivity
  let m : ℕ := Nat.ceil x
  have hm : 0 < m := Nat.ceil_pos.mpr hx
  have hlower : 64 * (r : ℝ) ^ 2 * (n : ℝ) ≤ (m : ℝ) * κ := by
    exact (div_le_iff₀ hκ).mp (Nat.le_ceil x)
  have hupper : (m : ℝ) * κ ≤ 65 * (r : ℝ) ^ 2 * (n : ℝ) := by
    have hmceil : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
    have hceil := (mul_lt_mul_iff_left₀ hκ).mpr hmceil
    have hxeq : x * κ = 64 * (r : ℝ) ^ 2 * (n : ℝ) := by
      dsimp [x]
      exact div_mul_cancel₀ _ hκ.ne'
    have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hlast := mul_le_mul_of_nonneg_right hr2 hn.le
    nlinarith
  have hcoef : 65 * (r : ℝ) ^ 3 * (ℓ : ℝ) ≤ κ := by
    have hnonneg : (0 : ℝ) ≤ (r : ℝ) ^ 3 * (ℓ : ℝ) := by positivity
    linarith
  have hroomR : (r : ℝ) * ((ℓ : ℝ) * (m : ℝ)) ≤ n := by
    apply (mul_le_mul_iff_left₀ hκ).mp
    calc
      (r : ℝ) * ((ℓ : ℝ) * (m : ℝ)) * κ =
          ((r : ℝ) * (ℓ : ℝ)) * ((m : ℝ) * κ) := by ring
      _ ≤ ((r : ℝ) * (ℓ : ℝ)) * (65 * (r : ℝ) ^ 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = (65 * (r : ℝ) ^ 3 * (ℓ : ℝ)) * (n : ℝ) := by ring
      _ ≤ κ * (n : ℝ) := mul_le_mul_of_nonneg_right hcoef hn.le
      _ = (n : ℝ) * κ := by ring
  have hroom : r * (ℓ * m) ≤ n := by exact_mod_cast hroomR
  refine ⟨m, hm, hroom, ?_, ?_⟩
  · exact (Nat.le_mul_of_pos_left (ℓ * m) (by omega : 0 < r)).trans hroom
  · nlinarith [hlower]
theorem matching_of_dense_hitting_sets (n r s : ℕ) (ℋ : Set (Set (Fin n)))
    (hempty : (∅ : Set (Fin n)) ∉ ℋ) (hroom : r * s ≤ n)
    (hdense : (r : ℝ) * ((n.choose s : ℝ) -
      ({U : Set (Fin n) | U.ncard = s ∧ ∃ A ∈ ℋ, A ⊆ U}.ncard : ℝ)) <
        (n.choose s : ℝ)) :
    ∃ P ⊆ ℋ, P.ncard = r ∧ P.Pairwise Disjoint := by
  classical
  obtain ⟨B, hB, hBdis⟩ := disjoint_blocks_from_dense_family n r s
    {U : Set (Fin n) | U.ncard = s ∧ ∃ A ∈ ℋ, A ⊆ U}
    hroom (fun U hU ↦ hU.1) hdense
  choose A hA hAsub using fun i ↦ (hB i).2
  have hAdis (i j : Fin r) (hij : i ≠ j) : Disjoint (A i) (A j) :=
    (hBdis i j hij).mono (hAsub i) (hAsub j)
  have hAinj : Function.Injective A := by
    intro i j heq
    by_contra hij
    have hself : Disjoint (A i) (A i) := by simpa only [← heq] using hAdis i j hij
    have hzero : A i = ∅ := disjoint_self.mp hself
    exact hempty (hzero ▸ hA i)
  refine ⟨Set.range A, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hA i
  · rw [Set.ncard_range_of_injective hAinj]
    simp
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hAdis i j (fun hij ↦ hne (congrArg A hij))
theorem geometric_spread_loss (r w : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) * (∑ j ∈ Finset.Icc 1 w, (2 / (8 * (r : ℝ))) ^ j) ≤ 1 / 2 := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  let z : ℝ := 2 / (8 * (r : ℝ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzhalf : z ≤ 1 / 2 := by
    dsimp [z]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (r : ℝ))).mpr
    linarith
  have hzlt : z < 1 := by linarith
  have hsum : (∑ j ∈ Finset.Icc 1 w, z ^ j) ≤ z / (1 - z) := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa only [pow_one] using
      (geom_sum_Ico_le_of_lt_one (m := 1) (n := w + 1) hz hzlt)
  have hratio : z / (1 - z) ≤ 2 * z := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - z)).mpr
    nlinarith
  have hrz : (r : ℝ) * (2 * z) = 1 / 2 := by
    dsimp [z]
    field_simp
    <;> ring
  calc
    (r : ℝ) * (∑ j ∈ Finset.Icc 1 w, z ^ j) ≤ (r : ℝ) * (2 * z) :=
      mul_le_mul_of_nonneg_left (hsum.trans hratio) hrpos.le
    _ = 1 / 2 := hrz
theorem spread_hitting_density (r n w ℓ m : ℕ) (ℋ : Set (Set (Fin n)))
    (κ : ℝ) (hr : 3 ≤ r) (hκ : 0 < κ) (hne : ℋ.Nonempty)
    (hm : 0 < m) (hroom : ℓ * m ≤ n) (hw : w < 2 ^ ℓ)
    (hscale : (8 * (r : ℝ)) ^ 2 * (n : ℝ) ≤ (m : ℝ) * κ)
    (hsys : Set.IsSystem w ℋ)
    (hcode : ∀ U : Set (Fin n),
      ({A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A}.ncard : ℝ) * κ ^ U.ncard ≤
        (ℋ.ncard : ℝ)) :
    (r : ℝ) * ((n.choose (ℓ * m) : ℝ) -
      ({U : Set (Fin n) | U.ncard = ℓ * m ∧ ∃ A ∈ ℋ, A ⊆ U}.ncard : ℝ)) <
        (n.choose (ℓ * m) : ℝ) := by
  classical
  letI := Fintype.ofFinite ℋ
  let b : Fin (Fintype.card ℋ) ≃ ℋ := (Fintype.equivFin ℋ).symm
  let f (i : Fin (Fintype.card ℋ)) : Set (Fin n) := (b i).val
  have hd : Fintype.card ℋ = ℋ.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hmass : (0 : ℝ) < (ℋ.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos).mpr hne
  have henum (U : Set (Fin n)) :
      {i : Fin (Fintype.card ℋ) | U ⊆ f i}.ncard =
        {A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A}.ncard := by
    apply Set.ncard_congr (fun i _ ↦ f i)
    · intro i hi
      exact ⟨(b i).property, hi⟩
    · intro i j _ _ heq
      exact b.injective (Subtype.ext heq)
    · intro A hA
      obtain ⟨i, hi⟩ := b.surjective ⟨A, hA.1⟩
      have hfi : f i = A := congrArg Subtype.val hi
      exact ⟨i, by simpa only [Set.mem_setOf_eq, hfi] using hA.2, hfi⟩
  have hVcard : (Set.univ : Set (Fin n)).ncard = n := by simp
  have hgood :
      {U : Set (Fin n) | U ⊆ Set.univ ∧ U.ncard = ℓ * m ∧
        ∃ i : Fin (Fintype.card ℋ), f i ⊆ U} =
      {U : Set (Fin n) | U.ncard = ℓ * m ∧ ∃ A ∈ ℋ, A ⊆ U} := by
    ext U
    constructor
    · rintro ⟨_, hsize, i, hi⟩
      exact ⟨hsize, f i, (b i).property, hi⟩
    · rintro ⟨hsize, A, hA, hAU⟩
      obtain ⟨i, hi⟩ := b.surjective ⟨A, hA⟩
      have hfi : f i = A := congrArg Subtype.val hi
      exact ⟨Set.subset_univ U, hsize, i, hfi ▸ hAU⟩
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hhit := labelled_halving_hitting n (Fintype.card ℋ) w ℓ m Set.univ f κ
    (ℋ.ncard : ℝ) (8 * (r : ℝ)) hκ hmass (by linarith) hm
    (by simpa only [hVcard] using hroom) hw
    (by simpa only [hVcard] using hscale)
    (fun i ↦ ⟨Set.subset_univ _, hsys _ (b i).property⟩)
    (fun U ↦ by rw [henum U]; exact hcode U)
  rw [hVcard, hgood, hd] at hhit
  let E : ℝ := ∑ j ∈ Finset.Icc 1 w, (2 / (8 * (r : ℝ))) ^ j
  let B : ℝ := (n.choose (ℓ * m) : ℝ)
  let G : ℝ :=
    ({U : Set (Fin n) | U.ncard = ℓ * m ∧ ∃ A ∈ ℋ, A ⊆ U}.ncard : ℝ)
  have hnormalized : (1 - E) * B ≤ G := by
    apply (mul_le_mul_iff_right₀ hmass).mp
    change (ℋ.ncard : ℝ) * ((1 - E) * B) ≤ (ℋ.ncard : ℝ) * G
    change ((ℋ.ncard : ℝ) - (ℋ.ncard : ℝ) * E) * B ≤
      (ℋ.ncard : ℝ) * G at hhit
    nlinarith only [hhit]
  have hB : 0 < B := by
    change (0 : ℝ) < (n.choose (ℓ * m) : ℝ)
    exact_mod_cast Nat.choose_pos hroom
  have hloss : (r : ℝ) * E ≤ 1 / 2 := geometric_spread_loss r w hr
  have hbad : (r : ℝ) * (B - G) ≤ ((r : ℝ) * E) * B := by
    have hdiff : B - G ≤ E * B := by nlinarith only [hnormalized]
    have hmul := mul_le_mul_of_nonneg_left hdiff (by positivity : (0 : ℝ) ≤ r)
    nlinarith only [hmul]
  have hbound := mul_le_mul_of_nonneg_right hloss hB.le
  change (r : ℝ) * (B - G) < B
  nlinarith only [hbad, hbound, hB]
theorem dyadic_spread_matching (r n w ℓ : ℕ) (ℋ : Set (Set (Fin n))) (κ : ℝ)
    (hr : 3 ≤ r) (hw : 0 < w) (hdyadic : w < 2 ^ ℓ) (hκ : 0 < κ)
    (hlarge : 260 * (r : ℝ) ^ 3 * (ℓ : ℝ) ≤ κ) (hne : ℋ.Nonempty)
    (hempty : (∅ : Set (Fin n)) ∉ ℋ) (hsys : Set.IsSystem w ℋ)
    (hcode : ∀ U : Set (Fin n),
      ({A : Set (Fin n) | A ∈ ℋ ∧ U ⊆ A}.ncard : ℝ) * κ ^ U.ncard ≤
        (ℋ.ncard : ℝ)) :
    ∃ P ⊆ ℋ, P.ncard = r ∧ P.Pairwise Disjoint := by
  have hℓ : 0 < ℓ := by
    by_contra hzero
    have heq : ℓ = 0 := by omega
    simp only [heq, pow_zero] at hdyadic
    omega
  have hκn := spread_parameter_le_ground_size n ℋ κ hκ.le hne hempty hcode
  obtain ⟨m, hm, hroom, hroom', hscale⟩ :=
    spread_matching_block_parameters r n ℓ κ hr hℓ hκ hκn hlarge
  exact matching_of_dense_hitting_sets n r (ℓ * m) ℋ hempty hroom
    (spread_hitting_density r n w ℓ m ℋ κ hr hκ hne hm hroom' hdyadic hscale hsys hcode)
theorem exists_uniform_sunflower_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), 3 ≤ r →
      ∀ (n : ℕ) (ℱ : Set (Set (Fin n))) (w : ℕ), 2 ≤ w → Set.IsSystem w ℱ →
        _root_.ImprovedBoundsSunflowerLemma.lowerBound r c w ≤ (ℱ.ncard : ℝ) →
        ∃ S ⊆ ℱ, Set.IsSunflower r S := by
  refine ⟨40000, by norm_num, ?_⟩
  intro r hr n ℱ w hw hsys hsize
  let ℓ : ℕ := Nat.log 2 w + 1
  let κ : ℝ := 520 * (r : ℝ) ^ 3 * (ℓ : ℝ)
  obtain ⟨hκ, hthreshold, hdyadic⟩ := scalar_threshold_comparison r w hr hw
  change 2 ≤ κ at hκ
  change κ < 40000 * (r : ℝ) ^ 3 * Real.logb (1.9 : ℝ) (w : ℝ) *
    Real.logb (1.9 : ℝ) (Real.logb (1.9 : ℝ) (w : ℝ)) at hthreshold
  change w < 2 ^ ℓ at hdyadic
  have hκpos : 0 < κ := by linarith
  have hstrict : κ ^ w < (ℱ.ncard : ℝ) := by
    apply lt_of_lt_of_le ?_ hsize
    exact pow_lt_pow_left₀ hthreshold hκpos.le (by omega : w ≠ 0)
  obtain ⟨T, ℋ, hne, hempty, hsysH, hprop, hcode⟩ :=
    extract_spread_petals n w ℱ κ hκ hsys hstrict
  have hscale : 260 * (r : ℝ) ^ 3 * (ℓ : ℝ) ≤ κ / 2 := by
    dsimp [κ]
    ring_nf
    exact le_rfl
  obtain ⟨P, hPH, hcard, hdis⟩ :=
    dyadic_spread_matching r n w ℓ ℋ (κ / 2) hr (by omega) hdyadic
      (div_pos hκpos (by norm_num)) hscale hne hempty hsysH hcode
  exact sunflower_of_disjoint_petals n r ℱ T P (by omega) hcard hdis
    (fun A hA ↦ hprop A (hPH hA))
theorem chosen_constant_sunflower
    (r : ℕ) (hr : 3 ≤ r) (X : Type*) [Finite X] (ℱ : Set (Set X)) (w : ℕ)
    (hw : 2 ≤ w) (hℱ₁ : Set.IsSystem w ℱ)
    (hℱ₂ : _root_.ImprovedBoundsSunflowerLemma.lowerBound r
      (Classical.choose Submission.Helpers.exists_uniform_sunflower_constant) w ≤
        (ℱ.ncard : ℝ)) :
    ∃ S ⊆ ℱ, Set.IsSunflower r S := by
  exact transfer_from_numbered_ground_sets
    (Classical.choose exists_uniform_sunflower_constant)
    (Classical.choose_spec exists_uniform_sunflower_constant).2
    r hr X ℱ w hw hℱ₁ hℱ₂
end Submission.Helpers
