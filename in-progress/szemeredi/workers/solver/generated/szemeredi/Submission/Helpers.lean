import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Expect

namespace Submission.Helpers

theorem ternary_cube_threeAPFree (m : ℕ) :
    ThreeAPFree ((Behrend.map 3) ''
      {e : Fin m → ℕ | ∀ i, e i < 2}) := by
  have hfree : ThreeAPFree {e : Fin m → ℕ | ∀ i, e i < 2} := by
    intro x hx y hy z hz hsum
    funext i
    have hi := congrFun hsum i
    have hxi := hx i
    have hyi := hy i
    have hzi := hz i
    change x i + z i = y i + y i at hi
    omega
  apply ThreeAPFree.image' (Behrend.map 3) ?_ hfree
  apply Behrend.map_injOn.mono
  rw [Set.add_subset_iff]
  intro x hx y hy i
  change x i + y i < 3
  have hxi := hx i
  have hyi := hy i
  omega

theorem subset_sum_cubes_do_not_force_ap (m : ℕ) :
    ∃ s : Finset ℕ,
      (∀ t : Finset (Fin m), (∑ i ∈ t, 3 ^ (i : ℕ)) ∈ s) ∧
      ¬ (∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < 3 → a + b * j ∈ s) := by
  classical
  let s := (Behrend.box m 2).image (Behrend.map 3)
  have hfree : ThreeAPFree (s : Set ℕ) := by
    have hbox : (Behrend.box m 2 : Set (Fin m → ℕ)) =
        {e : Fin m → ℕ | ∀ i, e i < 2} := by
      ext e
      exact Behrend.mem_box
    simpa only [s, Finset.coe_image, hbox] using ternary_cube_threeAPFree m
  refine ⟨s, ?_, ?_⟩
  · intro t
    refine Finset.mem_image.mpr ⟨(fun i => if i ∈ t then 1 else 0), ?_, ?_⟩
    · rw [Behrend.mem_box]
      intro i
      split_ifs <;> omega
    · simp [Behrend.map_apply]
  · rintro ⟨a, b, hb, hap⟩
    have h0 := hap 0 (by omega)
    have h1 := hap 1 (by omega)
    have h2 := hap 2 (by omega)
    have heq := hfree h0 h1 h2 (by omega)
    omega

theorem ap3_of_not_threeAPFree (A : Set Nat) (h : ¬ ThreeAPFree A) :
    ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < 3 → a + b * j ∈ A := by
  classical
  have ordered (x y z : Nat) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
      (hsum : x + z = y + y) (hxy : x < y) :
      ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < 3 → a + b * j ∈ A := by
    refine ⟨x, y - x, by omega, ?_⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · simpa using hx
    · have heq : x + (y - x) * 1 = y := by omega
      rwa [heq]
    · have heq : x + (y - x) * 2 = z := by omega
      rwa [heq]
  unfold ThreeAPFree at h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hsum, hne⟩ := h
  by_cases hxy : x < y
  · exact ordered x y z hx hy hz hsum hxy
  · exact ordered z y x hz hy hx (by omega) (by omega)

theorem finite_density_not_threeAPFree (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ,
      s ⊆ Finset.range n → epsilon * (n : ℝ) ≤ (s.card : ℝ) →
        ¬ ThreeAPFree (s : Set ℕ) := by
  refine ⟨cornersTheoremBound (epsilon / 3), ?_⟩
  intro n hn s hs hd
  exact roth_3ap_theorem_nat epsilon hepsilon hn s hs hd

theorem finite_density_short_progressions (k : ℕ) (hk : k ≤ 3)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ,
      s ⊆ Finset.range n → epsilon * (n : ℝ) ≤ (s.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s := by
  obtain ⟨N, hN⟩ := finite_density_not_threeAPFree epsilon hepsilon
  refine ⟨N, ?_⟩
  intro n hn s hs hd
  obtain ⟨a, b, hb, hap⟩ := ap3_of_not_threeAPFree (s : Set ℕ) (hN n hn s hs hd)
  exact ⟨a, b, hb, fun j hj => hap j (lt_of_lt_of_le hj hk)⟩

theorem consecutive_of_card_gt_blocks (k n : ℕ) (hk : 0 < k)
    (s : Finset ℕ) (hs : s ⊆ Finset.range n)
    (hcard : (n / k + 1) * (k - 1) < s.card) :
    ∃ a : ℕ, ∀ j : ℕ, j < k → a + j ∈ s := by
  have hmaps : ∀ x ∈ s, x / k ∈ Finset.range (n / k + 1) := by
    intro x hx
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp (hs hx))))
  obtain ⟨a, ha, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
      (by simpa only [Finset.card_range] using hcard)
  let block := (Finset.range k).image (fun j => k * a + j)
  have hsub : s.filter (fun x => x / k = a) ⊆ block := by
    intro x hx
    obtain ⟨_, hxa⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨x % k, Finset.mem_range.mpr (Nat.mod_lt x hk), ?_⟩
    rw [← hxa]
    exact Nat.div_add_mod x k
  have hblock : block.card = k := by
    rw [Finset.card_image_of_injective _ (fun x y hxy => Nat.add_left_cancel hxy)]
    exact Finset.card_range k
  have hfull : s.filter (fun x => x / k = a) = block := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hblock]
    omega
  refine ⟨k * a, ?_⟩
  intro j hj
  have hmem : k * a + j ∈ block :=
    Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  rw [← hfull] at hmem
  exact (Finset.mem_filter.mp hmem).1

theorem finite_density_consecutive (k : ℕ) (hk : 0 < k) (epsilon : ℝ)
    (hepsilon : ((k - 1 : ℕ) : ℝ) < epsilon * (k : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ,
      s ⊆ Finset.range n → epsilon * (n : ℝ) ≤ (s.card : ℝ) →
        ∃ a : ℕ, ∀ j : ℕ, j < k → a + j ∈ s := by
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hgap : 0 < epsilon * (k : ℝ) - ((k - 1 : ℕ) : ℝ) := sub_pos.mpr hepsilon
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((k : ℝ) * ((k - 1 : ℕ) : ℝ) /
      (epsilon * (k : ℝ) - ((k - 1 : ℕ) : ℝ)))
  refine ⟨N, ?_⟩
  intro n hn s hs hd
  apply consecutive_of_card_gt_blocks k n hk s hs
  have hbound := (div_lt_iff₀ hgap).mp hN
  have hmon := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn : (N : ℝ) ≤ n) hgap.le
  have hdiv : ((n / k : ℕ) : ℝ) * (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self n k
  have hmul := mul_le_mul_of_nonneg_right hdiv
    (by positivity : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ))
  have hd' := mul_le_mul_of_nonneg_left hd hkreal.le
  have hcard : ((((n / k + 1) * (k - 1) : ℕ) : ℝ)) < (s.card : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hkreal).mp
    push_cast
    nlinarith
  exact_mod_cast hcard

theorem ap_of_aligned_grid (A : Set Nat) (a b c k r : Nat) (hk : 0 < k)
    (hc : c = b * k)
    (hgrid : ∀ i : Nat, i < r → ∀ j : Nat, j < k → a + c * i + b * j ∈ A) :
    ∀ m : Nat, m < r * k → a + b * m ∈ A := by
  intro m hm
  have hi : m / k < r := (Nat.div_lt_iff_lt_mul hk).mpr hm
  have h := hgrid (m / k) hi (m % k) (Nat.mod_lt m hk)
  have heq : a + c * (m / k) + b * (m % k) = a + b * m := by
    rw [hc]
    calc
      _ = a + b * (m % k + k * (m / k)) := by ring
      _ = a + b * m := by rw [Nat.mod_add_div]
  rwa [heq] at h

theorem finite_common_extension (s t u : Finset Nat) (hs : s ⊆ u) (ht : t ⊆ u)
    (hcard : u.card < s.card + t.card) : ∃ a : Nat, a ∈ s ∧ a ∈ t := by
  classical
  have hbound : (s ∪ t).card ≤ u.card :=
    Finset.card_le_card (Finset.union_subset hs ht)
  have hsum := Finset.card_union_add_card_inter s t
  have hnonempty : (s ∩ t).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hnonempty
  exact ⟨a, Finset.mem_inter.mp ha⟩

theorem ap_succ_of_start_end_card (s : Finset Nat) (n k b : Nat) (hb : 1 ≤ b)
    (hcard : n <
      ((Finset.range n).filter (fun a => ∀ j : Nat, j < k → a + b * j ∈ s)).card +
      ((Finset.range n).filter (fun a => a + b * k ∈ s)).card) :
    ∃ a : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k + 1 → a + b * j ∈ s := by
  classical
  obtain ⟨a, hstart, hend⟩ := finite_common_extension
    ((Finset.range n).filter (fun a => ∀ j : Nat, j < k → a + b * j ∈ s))
    ((Finset.range n).filter (fun a => a + b * k ∈ s))
    (Finset.range n) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (by simpa only [Finset.card_range] using hcard)
  refine ⟨a, hb, ?_⟩
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjk | rfl
  · exact (Finset.mem_filter.mp hstart).2 j hjk
  · exact (Finset.mem_filter.mp hend).2

theorem ap_of_affine_indices (s t : Finset ℕ) (u v k : ℕ) (hv : 1 ≤ v)
    (ht : ∀ x ∈ t, u + v * x ∈ s)
    (hap : ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ t) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s := by
  obtain ⟨a, b, hb, hab⟩ := hap
  refine ⟨u + v * a, v * b, by nlinarith, ?_⟩
  intro j hj
  convert ht (a + b * j) (hab j hj) using 1
  ring

theorem card_affine_indices (s : Finset ℕ) (u v m : ℕ) (hv : 1 ≤ v) :
    (((Finset.range m).filter (fun x => u + v * x ∈ s)).image
      (fun x => u + v * x)).card =
      ((Finset.range m).filter (fun x => u + v * x ∈ s)).card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  have heq : v * x = v * y := Nat.add_left_cancel hxy
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < v) heq

theorem density_above_one_impossible (eta : ℝ) (heta : 1 < eta)
    (n : Nat) (hn : 1 ≤ n) (s : Finset Nat) (hs : s ⊆ Finset.range n)
    (hdensity : eta * (n : ℝ) ≤ (s.card : ℝ)) : False := by
  have hcard : (s.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (Finset.card_range n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlt := mul_lt_mul_of_pos_right heta hnpos
  nlinarith

theorem finite_density_of_increment (P : Finset Nat → Prop) (epsilon0 delta : ℝ)
    (hdelta : 0 < delta)
    (hincrement : ∀ eta : ℝ, epsilon0 ≤ eta → eta ≤ 1 → ∀ M : Nat,
      ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ s : Finset Nat,
        s ⊆ Finset.range n → eta * (n : ℝ) ≤ (s.card : ℝ) →
        P s ∨ ∃ m : Nat, M ≤ m ∧ ∃ t : Finset Nat,
          t ⊆ Finset.range m ∧ (eta + delta) * (m : ℝ) ≤ (t.card : ℝ) ∧
          (P t → P s)) :
    ∃ N : Nat, 1 ≤ N ∧ ∀ n : Nat, N ≤ n → ∀ s : Finset Nat,
      s ⊆ Finset.range n → epsilon0 * (n : ℝ) ≤ (s.card : ℝ) → P s := by
  have terminate : ∀ r : Nat, ∀ eta : ℝ, epsilon0 ≤ eta →
      1 < eta + (r : ℝ) * delta →
      ∃ N : Nat, 1 ≤ N ∧ ∀ n : Nat, N ≤ n → ∀ s : Finset Nat,
        s ⊆ Finset.range n → eta * (n : ℝ) ≤ (s.card : ℝ) → P s := by
    intro r
    induction r with
    | zero =>
      intro eta hepsilon heta
      refine ⟨1, le_refl 1, ?_⟩
      intro n hn s hs hdensity
      exact (density_above_one_impossible eta (by simpa using heta) n hn s hs hdensity).elim
    | succ r ih =>
      intro eta hepsilon heta
      by_cases htop : 1 < eta
      · refine ⟨1, le_refl 1, ?_⟩
        intro n hn s hs hdensity
        exact (density_above_one_impossible eta htop n hn s hs hdensity).elim
      · have hnext : 1 < eta + delta + (r : ℝ) * delta := by
          push_cast at heta
          nlinarith
        obtain ⟨M, hMpos, hM⟩ := ih (eta + delta) (by linarith) hnext
        obtain ⟨N, hN⟩ := hincrement eta hepsilon (le_of_not_gt htop) M
        refine ⟨max N 1, le_max_right _ _, ?_⟩
        intro n hn s hs hdensity
        rcases hN n (le_trans (le_max_left _ _) hn) s hs hdensity with hap | hinc
        · exact hap
        · obtain ⟨m, hm, t, ht, hdensity', hlift⟩ := hinc
          exact hlift (hM m hm t ht hdensity')
  obtain ⟨r, hr⟩ := exists_nat_gt ((1 - epsilon0) / delta)
  have htop : 1 < epsilon0 + (r : ℝ) * delta := by
    have hmul := (div_lt_iff₀ hdelta).mp hr
    linarith
  exact terminate r epsilon0 (le_refl _) htop

theorem finite_density_ap_of_increment (k : Nat) (epsilon0 delta : ℝ)
    (hdelta : 0 < delta)
    (hincrement : ∀ eta : ℝ, epsilon0 ≤ eta → eta ≤ 1 → ∀ M : Nat,
      ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ s : Finset Nat,
        s ⊆ Finset.range n → eta * (n : ℝ) ≤ (s.card : ℝ) →
        (∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k → a + b * j ∈ s) ∨
        ∃ m : Nat, M ≤ m ∧ ∃ t : Finset Nat,
          t ⊆ Finset.range m ∧ (eta + delta) * (m : ℝ) ≤ (t.card : ℝ) ∧
          ((∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k → a + b * j ∈ t) →
            ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k → a + b * j ∈ s)) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ s : Finset Nat,
      s ⊆ Finset.range n → epsilon0 * (n : ℝ) ≤ (s.card : ℝ) →
      ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k → a + b * j ∈ s := by
  obtain ⟨N, hNpos, hN⟩ := finite_density_of_increment
    (fun s => ∃ a b : Nat, 1 ≤ b ∧ ∀ j : Nat, j < k → a + b * j ∈ s)
    epsilon0 delta hdelta hincrement
  exact ⟨N, hN⟩

theorem sum_card_translate_inter {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (s t : Finset G) :
    Finset.univ.sum (fun x : G => (s ∩ t.image (fun y => x + y)).card) =
      s.card * t.card := by
  have hfiber (x : G) :
      ((s ×ˢ t).filter (fun p : G × G => p.1 - p.2 = x)).card =
        (s ∩ t.image (fun y => x + y)).card := by
    apply Finset.card_nbij' (fun p : G × G => p.1) (fun z : G => (z, z - x))
    · intro p hp
      obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hps, hpt⟩ := Finset.mem_product.mp hp
      exact Finset.mem_inter.mpr ⟨hps,
        Finset.mem_image.mpr ⟨p.2, hpt, (sub_eq_iff_eq_add.mp heq).symm⟩⟩
    · intro z hz
      obtain ⟨hzs, hzt⟩ := Finset.mem_inter.mp hz
      obtain ⟨y, hyt, hy⟩ := Finset.mem_image.mp hzt
      change (z, z - x) ∈ (s ×ˢ t).filter (fun p : G × G => p.1 - p.2 = x)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hzs, ?_⟩, by simp⟩
      have heq : z - x = y := by rw [← hy]; abel
      rwa [heq]
    · intro p hp
      have heq := (Finset.mem_filter.mp hp).2
      change (p.1, p.1 - x) = p
      apply Prod.ext
      · rfl
      · change p.1 - x = p.2
        rw [sub_eq_iff_eq_add.mp heq]
        abel
    · intro z hz
      rfl
  calc
    _ = Finset.univ.sum (fun x : G =>
        ((s ×ˢ t).filter (fun p : G × G => p.1 - p.2 = x)).card) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (hfiber x).symm
    _ = (s ×ˢ t).card :=
      (Finset.card_eq_sum_card_fiberwise
        (f := fun p : G × G => p.1 - p.2) (by intro p hp; simp)).symm
    _ = _ := Finset.card_product s t

theorem exists_translate_inter_le_average {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (s t : Finset G) :
    ∃ x : G, Fintype.card G * (s ∩ t.image (fun y => x + y)).card ≤
      s.card * t.card := by
  have hsum : Finset.univ.sum
      (fun x : G => Fintype.card G * (s ∩ t.image (fun y => x + y)).card) =
        Finset.univ.sum (fun _ : G => s.card * t.card) := by
    rw [← Finset.mul_sum, sum_card_translate_inter]
    simp
  obtain ⟨x, hx, hle⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset G)) Finset.univ_nonempty hsum.le
  exact ⟨x, hle⟩

theorem exists_translate_union_growth {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (s t : Finset G) :
    ∃ x : G, Fintype.card G * (s.card + t.card) ≤
      Fintype.card G * (s ∪ t.image (fun y => x + y)).card + s.card * t.card := by
  obtain ⟨x, hx⟩ := exists_translate_inter_le_average s t
  refine ⟨x, ?_⟩
  have hcard : (t.image (fun y => x + y)).card = t.card :=
    Finset.card_image_of_injective _ (add_right_injective x)
  have hsum := Finset.card_union_add_card_inter s (t.image (fun y => x + y))
  rw [hcard] at hsum
  nlinarith

theorem exists_translates_card_bound {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (t : Finset G) (r : ℕ) :
    ∃ F : Finset G, F.card ≤ r ∧
      (Fintype.card G < 2 * (F.biUnion (fun x => t.image (fun y => x + y))).card ∨
        r * t.card ≤ 2 * (F.biUnion (fun x => t.image (fun y => x + y))).card) := by
  induction r with
  | zero => exact ⟨∅, by simp, Or.inr (by simp)⟩
  | succ r ih =>
    obtain ⟨F, hF, hU⟩ := ih
    let U := F.biUnion (fun x => t.image (fun y => x + y))
    by_cases hhalf : Fintype.card G < 2 * U.card
    · exact ⟨F, by omega, Or.inl hhalf⟩
    have hU' : r * t.card ≤ 2 * U.card := hU.resolve_left hhalf
    obtain ⟨x, hx⟩ := exists_translate_union_growth U t
    have hc : 0 < Fintype.card G := Fintype.card_pos
    have hscaled : Fintype.card G * (2 * U.card + t.card) ≤
        Fintype.card G * (2 * (U ∪ t.image (fun y => x + y)).card) := by
      have hbound := Nat.mul_le_mul_right t.card (Nat.le_of_not_gt hhalf)
      nlinarith
    have hstep : 2 * U.card + t.card ≤
        2 * (U ∪ t.image (fun y => x + y)).card := by
      apply (mul_le_mul_iff_right₀ hc).mp
      simpa only [Nat.mul_comm] using hscaled
    refine ⟨insert x F, (Finset.card_insert_le x F).trans (by omega), Or.inr ?_⟩
    rw [Finset.biUnion_insert, Finset.union_comm]
    change (r + 1) * t.card ≤ 2 * (U ∪ t.image (fun y => x + y)).card
    nlinarith

theorem exists_translates_majority {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (t : Finset G) (r : ℕ)
    (hr : Fintype.card G < r * t.card) :
    ∃ F : Finset G, F.card ≤ r ∧
      Fintype.card G < 2 * (F.biUnion (fun x => t.image (fun y => x + y))).card := by
  obtain ⟨F, hF, hU⟩ := exists_translates_card_bound t r
  refine ⟨F, hF, ?_⟩
  rcases hU with hU | hU
  · exact hU
  · exact hr.trans_le hU

theorem exists_translates_majority_of_density (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ r : ℕ, ∀ (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
      (t : Finset G), epsilon * (Fintype.card G : ℝ) ≤ (t.card : ℝ) →
      ∃ F : Finset G, F.card ≤ r ∧
        Fintype.card G < 2 * (F.biUnion (fun x => t.image (fun y => x + y))).card := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / epsilon)
  refine ⟨r, ?_⟩
  intro G _ _ _ t ht
  apply exists_translates_majority t r
  have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hboost := mul_lt_mul_of_pos_right ((div_lt_iff₀ hepsilon).mp hr) hc
  have hscaled := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  have hcard : (Fintype.card G : ℝ) < (r : ℝ) * (t.card : ℝ) := by nlinarith
  exact_mod_cast hcard

theorem ap_of_cyclic_mod_membership (s : Set Nat) (k a b n : Nat)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (ha : a < n)
    (hspan : b * (2 * k - 2) < n)
    (hmem : ∀ j : Nat, j < 2 * k - 1 → (a + b * j) % n ∈ s) :
    ∃ c d : Nat, 1 ≤ d ∧ ∀ j : Nat, j < k → c + d * j ∈ s := by
  by_cases hmid : a + b * (k - 1) < n
  · refine ⟨a, b, hb, ?_⟩
    intro j hj
    have hjle : j ≤ k - 1 := by omega
    have hmul := Nat.mul_le_mul_left b hjle
    have hterm : a + b * j < n := by omega
    simpa only [Nat.mod_eq_of_lt hterm] using hmem j (by omega)
  · have hcross : n ≤ a + b * (k - 1) := by omega
    refine ⟨a + b * (k - 1) - n, b, hb, ?_⟩
    intro j hj
    have hindex : k - 1 + j < 2 * k - 1 := by omega
    have hleft := Nat.mul_le_mul_left b (show k - 1 ≤ k - 1 + j by omega)
    have hright := Nat.mul_le_mul_left b (show k - 1 + j ≤ 2 * k - 2 by omega)
    have hlower : n ≤ a + b * (k - 1 + j) := by omega
    have hupper : a + b * (k - 1 + j) < n + n := by omega
    have hmod : (a + b * (k - 1 + j)) % n = a + b * (k - 1 + j) - n := by
      rw [Nat.mod_eq_sub_mod hlower]
      exact Nat.mod_eq_of_lt (by omega)
    have heq : a + b * (k - 1) - n + b * j = a + b * (k - 1 + j) - n := by
      rw [Nat.mul_add]
      omega
    have hm := hmem (k - 1 + j) hindex
    rwa [hmod, ← heq] at hm

theorem ap_of_shifted_mod_membership (s : Set Nat) (k a b shift n : Nat)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hspan : b * (2 * k - 2) < n)
    (hmem : ∀ j : Nat, j < 2 * k - 1 → (a + b * j + shift) % n ∈ s) :
    ∃ c d : Nat, 1 ≤ d ∧ ∀ j : Nat, j < k → c + d * j ∈ s := by
  refine ap_of_cyclic_mod_membership s k ((a + shift) % n) b n hk hb
    (Nat.mod_lt _ (by omega)) hspan ?_
  intro j hj
  simpa only [Nat.mod_add_mod, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using hmem j hj

theorem line_sum_affine {ι : Type*} [Fintype ι] (k : ℕ)
    (l : Combinatorics.Line (Fin (k + 1)) ι) :
    ∃ a b : ℕ, 1 ≤ b ∧
      ∀ j : Fin (k + 1), (∑ i, (l j i).val) = a + b * j.val := by
  classical
  let V : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  let a : ℕ := ∑ i ∈ Vᶜ, ((l.idxFun i).map Fin.val).getD 0
  refine ⟨a, V.card, ?_, ?_⟩
  · apply Finset.card_pos.mpr
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · intro j
    have hvar : (∑ i ∈ V, (l j i).val) = V.card * j.val := by
      calc
        _ = ∑ _ ∈ V, j.val := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [l.apply_none _ _ (Finset.mem_filter.mp hi).2]
        _ = _ := by simp
    have hconst : (∑ i ∈ Vᶜ, (l j i).val) = a := by
      apply Finset.sum_congr rfl
      intro i hi
      have hne : l.idxFun i ≠ none := by
        simpa only [V, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp hne
      simp [Combinatorics.Line.coe_apply, ← hx]
    rw [← Finset.sum_add_sum_compl V, hvar, hconst, Nat.add_comm]

theorem finite_van_der_waerden (k r : ℕ) :
    ∃ N : ℕ, k ≤ N ∧ ∀ C : ℕ → Fin r,
      ∃ a b : ℕ, 1 ≤ b ∧ ∃ c : Fin r,
        ∀ j : ℕ, j < k → a + b * j < N ∧ C (a + b * j) = c := by
  classical
  obtain ⟨ι, hιfin, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin (k + 1)) (Fin r)
  refine ⟨Fintype.card ι * k + k + 1, by omega, ?_⟩
  intro C
  obtain ⟨l, c, hcolor⟩ := hι (fun v => C (∑ i, (v i).val))
  obtain ⟨a, b, hb, hsum⟩ := line_sum_affine k l
  refine ⟨a, b, hb, c, ?_⟩
  intro j hj
  let x : Fin (k + 1) := ⟨j, by omega⟩
  have hbound : (∑ i, (l x i).val) ≤ Fintype.card ι * k := by
    calc
      _ ≤ ∑ _ : ι, k := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.le_of_lt_succ (l x i).isLt
      _ = _ := by simp
  have heq : (∑ i, (l x i).val) = a + b * j := hsum x
  refine ⟨by omega, ?_⟩
  have hc := hcolor x
  change C (∑ i, (l x i).val) = c at hc
  simpa only [heq] using hc

theorem finite_van_der_waerden_on_interval (k r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, k ≤ N ∧ ∀ C : Fin N → Fin r,
      ∃ a b : ℕ, 1 ≤ b ∧ ∃ c : Fin r,
        ∀ j : ℕ, j < k → ∃ hj : a + b * j < N,
          C ⟨a + b * j, hj⟩ = c := by
  classical
  obtain ⟨N, hN, hmono⟩ := finite_van_der_waerden k r
  refine ⟨N, hN, ?_⟩
  intro C
  let D : ℕ → Fin r := fun i => if hi : i < N then C ⟨i, hi⟩ else ⟨0, by omega⟩
  obtain ⟨a, b, hb, c, hap⟩ := hmono D
  refine ⟨a, b, hb, c, ?_⟩
  intro j hj
  obtain ⟨hbound, hcolor⟩ := hap j hj
  exact ⟨hbound, by simpa only [D, dite_eq_left hbound] using hcolor⟩

theorem missing_permutation_of_no_ap (k : ℕ) (hk : 2 ≤ k)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (k * k))
    (hcard : k * (k - 1) ≤ s.card)
    (hno : ¬ ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s) :
    ∃ c : Fin k → Fin k, Function.Bijective c ∧
      ∀ x : ℕ, x < k * k →
        (x ∉ s ↔ ∃ i : Fin k, x = k * i.val + (c i).val) := by
  classical
  have hkpos : 0 < k := by omega
  have hmiss (a b : ℕ) (hb : 1 ≤ b) : ∃ j : ℕ, j < k ∧ a + b * j ∉ s := by
    by_contra! hn
    exact hno ⟨a, b, hb, hn⟩
  let t := Finset.range (k * k) \ s
  have htc : t.card ≤ k := by
    have heq : s.card + t.card = k * k := by
      have h := Finset.card_sdiff_add_card_eq_card hs
      simpa only [t, Finset.card_range, Nat.add_comm] using h
    have hsub : k - 1 + 1 = k := by omega
    nlinarith
  have hrows : ∀ i : Fin k, ∃ j : Fin k, k * i.val + j.val ∈ t := by
    intro i
    obtain ⟨j, hj, hjs⟩ := hmiss (k * i.val) 1 (by omega)
    refine ⟨⟨j, hj⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩⟩
    · have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt i.isLt)
      nlinarith
    · simpa only [one_mul] using hjs
  choose c hc using hrows
  let f : Fin k → ℕ := fun i => k * i.val + (c i).val
  have hfdiv (i : Fin k) : f i / k = i.val := by
    simp only [f, Nat.mul_add_div hkpos, Nat.div_eq_of_lt (c i).isLt, Nat.add_zero]
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have heq := congrArg (fun x => x / k) hij
    simpa only [hfdiv] using heq
  have himage : Finset.univ.image f = t := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hc i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      exact htc
  have hcsurj : Function.Surjective c := by
    intro z
    obtain ⟨j, hj, hjs⟩ := hmiss z.val k (by omega)
    have hxt : z.val + k * j ∈ t := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_range.mpr ?_, hjs⟩
      have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hj)
      nlinarith [z.isLt]
    rw [← himage] at hxt
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxt
    refine ⟨i, Fin.ext ?_⟩
    have heq := congrArg (fun x => x % k) hi
    simpa [f, Nat.add_mod, Nat.mod_eq_of_lt (c i).isLt,
      Nat.mod_eq_of_lt z.isLt] using heq
  refine ⟨c, ⟨Finite.injective_iff_surjective.mpr hcsurj, hcsurj⟩, ?_⟩
  intro x hx
  have hxt : x ∉ s ↔ x ∈ t := by simp [t, hx]
  rw [hxt, ← himage]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, f, eq_comm]

theorem ap_of_card_dense_square (k : ℕ) (hk : 3 ≤ k)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (k * k))
    (hcard : k * (k - 1) ≤ s.card) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s := by
  classical
  by_contra hno
  obtain ⟨c, hc, hholes⟩ :=
    missing_permutation_of_no_ap k (by omega) s hs hcard hno
  have hcinj := hc.1
  have hnext (i : ℕ) (hi : i + 1 < k) :
      (c ⟨i + 1, hi⟩).val < (c ⟨i, by omega⟩).val := by
    let i0 : Fin k := ⟨i, by omega⟩
    let i1 : Fin k := ⟨i + 1, hi⟩
    have hle : (c i1).val ≤ (c i0).val := by
      by_contra! hbig
      have hap : ∀ j : ℕ, j < k → k * i + (c i0).val + 1 + j ∈ s := by
        intro j hj
        have hxlt : k * i + (c i0).val + 1 + j < k * k := by
          have hm := Nat.mul_le_mul_left k (show i + 2 ≤ k by omega)
          nlinarith [(c i0).isLt]
        by_contra hnot
        obtain ⟨r, hr⟩ := (hholes _ hxlt).mp hnot
        have hrlo : i ≤ r.val := by
          by_contra! hlow
          have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hlow)
          nlinarith [(c r).isLt]
        have hrhi : r.val ≤ i + 1 := by
          by_contra! hhigh
          have hm := Nat.mul_le_mul_left k (show i + 2 ≤ r.val by omega)
          nlinarith [(c i0).isLt]
        have hr' : r = i0 ∨ r = i1 := by
          have hvals : r.val = i ∨ r.val = i + 1 := by omega
          exact hvals.imp Fin.ext Fin.ext
        rcases hr' with rfl | rfl
        · change k * i + (c i0).val + 1 + j = k * i + (c i0).val at hr
          omega
        · change k * i + (c i0).val + 1 + j = k * (i + 1) + (c i1).val at hr
          nlinarith
      exact hno ⟨k * i + (c i0).val + 1, 1, by omega,
        by simpa only [one_mul] using hap⟩
    have hne : (c i1).val ≠ (c i0).val := by
      intro heq
      have heq' := congrArg Fin.val (hcinj (Fin.ext heq))
      change i + 1 = i at heq'
      omega
    change (c i1).val < (c i0).val
    omega
  have hub : ∀ i : ℕ, ∀ hi : i < k, (c ⟨i, hi⟩).val + i < k := by
    intro i
    induction i with
    | zero =>
      intro hi
      simpa only [Nat.add_zero] using (c ⟨0, hi⟩).isLt
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      have hstep := hnext i hi
      omega
  have hdown : ∀ d : ℕ, ∀ hd : d < k,
      d ≤ (c ⟨k - 1 - d, by omega⟩).val := by
    intro d
    induction d with
    | zero => intro hd; omega
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      have hstep := hnext (k - 1 - (d + 1)) (by omega)
      have heq : k - 1 - (d + 1) + 1 = k - 1 - d := by omega
      simp only [heq] at hstep
      omega
  have hform (i : Fin k) : k * i.val + (c i).val = (k - 1) * (i.val + 1) := by
    have hu := hub i.val i.isLt
    change (c i).val + i.val < k at hu
    have hd := hdown (k - 1 - i.val) (by omega)
    have heq : k - 1 - (k - 1 - i.val) = i.val := by omega
    simp only [heq] at hd
    change k - 1 - i.val ≤ (c i).val at hd
    have hc : (c i).val + i.val = k - 1 := by omega
    have hk' : k - 1 + 1 = k := by omega
    nlinarith
  apply hno
  refine ⟨1, k - 1, by omega, ?_⟩
  intro j hj
  have hxlt : 1 + (k - 1) * j < k * k := by
    have hm := Nat.mul_le_mul_left (k - 1) (show j ≤ k - 1 by omega)
    have hk' : k - 1 + 1 = k := by omega
    nlinarith
  by_contra hnot
  obtain ⟨i, hi⟩ := (hholes _ hxlt).mp hnot
  rw [hform] at hi
  have hmod := congrArg (fun x => x % (k - 1)) hi
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < k - 1)] at hmod

theorem ap_of_card_gt_square_blocks (k n : ℕ) (hk : 3 ≤ k)
    (s : Finset ℕ) (hs : s ⊆ Finset.range n)
    (hcard : (n / (k * k) + 1) * (k * (k - 1) - 1) < s.card) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s := by
  classical
  let q := k * k
  have hq : 0 < q := Nat.mul_pos (by omega) (by omega)
  have hp : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
  have hmaps : ∀ x ∈ s, x / q ∈ Finset.range (n / q + 1) := by
    intro x hx
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt (Finset.mem_range.mp (hs hx))))
  obtain ⟨a, ha, hlarge⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
      (by simpa only [Finset.card_range] using hcard)
  let u := s.filter (fun x => x / q = a)
  let t := u.image (fun x => x % q)
  have hmodinj : Set.InjOn (fun x => x % q) u := by
    intro x hx y hy heq
    change x % q = y % q at heq
    have hxq := (Finset.mem_filter.mp hx).2
    have hyq := (Finset.mem_filter.mp hy).2
    have hx' := Nat.div_add_mod x q
    have hy' := Nat.div_add_mod y q
    rw [hxq] at hx'
    rw [hyq, ← heq] at hy'
    omega
  have hct : t.card = u.card := Finset.card_image_of_injOn hmodinj
  have ht : t ⊆ Finset.range (k * k) := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt y hq)
  have hct' : k * (k - 1) ≤ t.card := by
    change k * (k - 1) - 1 < u.card at hlarge
    omega
  have hap := ap_of_card_dense_square k hk t ht hct'
  apply ap_of_affine_indices s t (q * a) 1 k (by omega) ?_ hap
  intro x hx
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
  change y % q = x at heq
  obtain ⟨hys, hyq⟩ := Finset.mem_filter.mp hy
  have hy' := Nat.div_add_mod y q
  rw [hyq, heq] at hy'
  simpa only [one_mul, hy'] using hys

theorem finite_density_square (k : ℕ) (hk : 3 ≤ k) (epsilon : ℝ)
    (hepsilon : ((k * (k - 1) - 1 : ℕ) : ℝ) <
      epsilon * ((k * k : ℕ) : ℝ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : Finset ℕ,
      s ⊆ Finset.range n → epsilon * (n : ℝ) ≤ (s.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ s := by
  let m := k * k
  let c := k * (k - 1) - 1
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
  have hgap : 0 < epsilon * (m : ℝ) - (c : ℝ) := sub_pos.mpr hepsilon
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((m : ℝ) * (c : ℝ) / (epsilon * (m : ℝ) - (c : ℝ)))
  refine ⟨N, ?_⟩
  intro n hn s hs hd
  apply ap_of_card_gt_square_blocks k n hk s hs
  have hbound := (div_lt_iff₀ hgap).mp hN
  have hmon := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn : (N : ℝ) ≤ n) hgap.le
  have hdiv : ((n / m : ℕ) : ℝ) * (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self n m
  have hmul := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  have hd' := mul_le_mul_of_nonneg_left hd hm.le
  have hcard : ((((n / m + 1) * c : ℕ) : ℝ)) < (s.card : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hm).mp
    push_cast
    nlinarith
  exact_mod_cast hcard

theorem block_support_ap_does_not_lift :
    ∃ s : Finset ℕ, s ⊆ Finset.range 40 ∧
      (∀ i : ℕ, i < 4 → ∃ x ∈ s, x / 10 = i) ∧
      ¬ (∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < 4 → a + b * j ∈ s) := by
  let s : Finset ℕ := {0, 10, 20, 31}
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have hicases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hicases with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [s], by norm_num⟩
    · exact ⟨10, by simp [s], by norm_num⟩
    · exact ⟨20, by simp [s], by norm_num⟩
    · exact ⟨31, by simp [s], by norm_num⟩
  · rintro ⟨a, b, hb, hap⟩
    have h0 := hap 0 (by omega)
    have h1 := hap 1 (by omega)
    have h2 := hap 2 (by omega)
    have h3 := hap 3 (by omega)
    simp only [s, Finset.mem_insert, Finset.mem_singleton,
      Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1 h2 h3
    omega

theorem roth_tensor_obstruction :
    rothNumberNat 3 = 2 ∧ 5 ≤ rothNumberNat 9 := by
  have hupper : rothNumberNat 3 ≤ 2 := by
    obtain ⟨s, hs, hcard, hfree⟩ := rothNumberNat_spec 3
    by_contra h
    have heq : s = Finset.range 3 := Finset.eq_of_subset_of_card_le hs (by
      rw [Finset.card_range, hcard]
      omega)
    rw [heq] at hfree
    have h01 := hfree (by simp : 0 ∈ (Finset.range 3 : Set ℕ))
      (by simp : 1 ∈ (Finset.range 3 : Set ℕ))
      (by simp : 2 ∈ (Finset.range 3 : Set ℕ)) (by omega)
    omega
  have hlower : 2 ≤ rothNumberNat 3 := by
    let s : Finset ℕ := {0, 1}
    have hfree : ThreeAPFree (s : Set ℕ) := by
      intro x hx y hy z hz hsum
      simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
      omega
    exact hfree.le_rothNumberNat s (by
      intro x hx
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      omega) (by norm_num [s])
  refine ⟨by omega, ?_⟩
  let s : Finset ℕ := {0, 1, 3, 7, 8}
  have hfree : ThreeAPFree (s : Set ℕ) := by
    intro x hx y hy z hz hsum
    simp only [s, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    omega
  exact hfree.le_rothNumberNat s (by
    intro x hx
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
    omega) (by norm_num [s])

theorem rothNumberNat_not_submultiplicative :
    ¬ (∀ m n : ℕ, rothNumberNat (m * n) ≤ rothNumberNat m * rothNumberNat n) := by
  intro h
  obtain ⟨hthree, hnine⟩ := roth_tensor_obstruction
  have hbound := h 3 3
  norm_num [hthree] at hbound
  omega

theorem ap_face_sum_affine {R : Type*} [CommRing R] (k : ℕ)
    (x : Fin k → R) (i : Fin k) :
    Finset.univ.sum (fun j : Fin k => ((j.val : R) - (i.val : R)) * x j) =
      Finset.univ.sum (fun j : Fin k => (j.val : R) * x j) -
        (i.val : R) * Finset.univ.sum x := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

theorem ap_face_sum_independent {R : Type*} [CommRing R] (k : ℕ)
    (x y : Fin k → R) (i : Fin k)
    (hxy : ∀ j : Fin k, j ≠ i → x j = y j) :
    Finset.univ.sum (fun j : Fin k => ((j.val : R) - (i.val : R)) * x j) =
      Finset.univ.sum (fun j : Fin k => ((j.val : R) - (i.val : R)) * y j) := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · rw [hxy j hji]

theorem card_ap_diagonal_fiber {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (m : ℕ) (a : R) :
    Fintype.card {x : Fin (m + 2) → R //
      Finset.univ.sum x = 0 ∧
        Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) = a} =
      Fintype.card R ^ m := by
  classical
  have hsum (x : Fin (m + 2) → R) :
      Finset.univ.sum x = x 0 + x 1 +
        Finset.univ.sum (fun j : Fin m => x j.succ.succ) := by
    simp [Fin.sum_univ_succ, add_assoc]
  have hmoment (x : Fin (m + 2) → R) :
      Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) =
        x 1 + Finset.univ.sum (fun j : Fin m => ((j.val : R) + 2) * x j.succ.succ) := by
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.cast_zero,
      Nat.cast_add, Nat.cast_one, zero_mul, zero_add, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  let f : {x : Fin (m + 2) → R // Finset.univ.sum x = 0 ∧
      Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) = a} →
      (Fin m → R) := fun x j => x.val j.succ.succ
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have htail : (fun j : Fin m => x.val j.succ.succ) =
          (fun j : Fin m => y.val j.succ.succ) := hxy
      have hmx := x.property.2
      have hmy := y.property.2
      rw [hmoment] at hmx hmy
      have hweighted : Finset.univ.sum
          (fun j : Fin m => ((j.val : R) + 2) * x.val j.succ.succ) =
          Finset.univ.sum (fun j : Fin m => ((j.val : R) + 2) * y.val j.succ.succ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [congrFun htail j]
      have h1 : x.val 1 = y.val 1 := by
        rw [hweighted] at hmx
        exact add_right_cancel (hmx.trans hmy.symm)
      have hsx := x.property.1
      have hsy := y.property.1
      rw [hsum] at hsx hsy
      have h0 : x.val 0 = y.val 0 := by
        rw [htail, h1] at hsx
        exact add_right_cancel (add_right_cancel (hsx.trans hsy.symm))
      apply Subtype.ext
      funext j
      refine Fin.cases h0 (fun i => ?_) j
      exact Fin.cases h1 (fun i => congrFun htail i) i
    · intro z
      let w := Finset.univ.sum (fun j : Fin m => ((j.val : R) + 2) * z j)
      let x : Fin (m + 2) → R :=
        Fin.cons (-(a - w) - Finset.univ.sum z) (Fin.cons (a - w) z)
      have hxsum : Finset.univ.sum x = 0 := by
        rw [hsum]
        change (-(a - w) - Finset.univ.sum z) + (a - w) + Finset.univ.sum z = 0
        ring
      have hxmoment : Finset.univ.sum
          (fun j : Fin (m + 2) => (j.val : R) * x j) = a := by
        rw [hmoment]
        change a - w + w = a
        ring
      refine ⟨⟨x, hxsum, hxmoment⟩, ?_⟩
      funext j
      simp [f, x]
  simpa using Fintype.card_congr (Equiv.ofBijective f hf)

theorem card_ap_diagonal_labels {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (m : ℕ) (s : Finset R) :
    Fintype.card {x : Fin (m + 2) → R //
      Finset.univ.sum x = 0 ∧
        Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) ∈ s} =
      s.card * Fintype.card R ^ m := by
  classical
  let e : (Σ a : {a : R // a ∈ s}, {x : Fin (m + 2) → R //
      Finset.univ.sum x = 0 ∧
        Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) = a.val}) ≃
      {x : Fin (m + 2) → R // Finset.univ.sum x = 0 ∧
        Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) ∈ s} :=
    { toFun := fun p => ⟨p.2.val, p.2.property.1, by
        rw [p.2.property.2]
        exact p.1.property⟩
      invFun := fun x => ⟨⟨Finset.univ.sum
        (fun j : Fin (m + 2) => (j.val : R) * x.val j), x.property.2⟩,
          ⟨x.val, x.property.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨a, ha⟩, ⟨x, hx, hm⟩⟩
        dsimp
        dsimp only at hm
        subst a
        rfl
      right_inv := by
        rintro ⟨x, hx, hm⟩
        rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp [card_ap_diagonal_fiber]

theorem ap_diagonal_eq_of_face_eq {G : Type*} [AddCommGroup G] (k : ℕ)
    (x y : Fin k → G) (i : Fin k)
    (hx : Finset.univ.sum x = 0) (hy : Finset.univ.sum y = 0)
    (hface : ∀ j : Fin k, j ≠ i → x j = y j) : x = y := by
  classical
  have hsub : Finset.univ.sum (fun j : Fin k => x j - y j) = x i - y i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [hface j hji, sub_self]
    · simp
  rw [Finset.sum_sub_distrib, hx, hy, sub_self] at hsub
  have hi : x i = y i := sub_eq_zero.mp hsub.symm
  funext j
  by_cases hji : j = i
  · simpa only [hji] using hi
  · exact hface j hji

theorem ap_diagonal_deletion_bound {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (m : ℕ) (s : Finset R) (D : Fin (m + 2) → Finset (Fin (m + 2) → R))
    (hcover : ∀ x : Fin (m + 2) → R,
      Finset.univ.sum x = 0 →
        Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) ∈ s →
        ∃ i : Fin (m + 2), Function.update x i 0 ∈ D i) :
    s.card * Fintype.card R ^ m ≤ Finset.univ.sum (fun i => (D i).card) := by
  classical
  let T := {x : Fin (m + 2) → R // Finset.univ.sum x = 0 ∧
    Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) ∈ s}
  have hchoose : ∀ x : T, ∃ i : Fin (m + 2), Function.update x.val i 0 ∈ D i :=
    fun x => hcover x.val x.property.1 x.property.2
  choose c hc using hchoose
  let f : T → Σ i : Fin (m + 2), {y // y ∈ D i} :=
    fun x => ⟨c x, ⟨Function.update x.val (c x) 0, hc x⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hi := congrArg Sigma.fst hxy
    have hv := congrArg
      (fun p : Σ i : Fin (m + 2), {z // z ∈ D i} => p.2.val) hxy
    change c x = c y at hi
    change Function.update x.val (c x) 0 = Function.update y.val (c y) 0 at hv
    rw [← hi] at hv
    apply Subtype.ext
    apply ap_diagonal_eq_of_face_eq (m + 2) x.val y.val (c x)
      x.property.1 y.property.1
    intro j hj
    have heq := congrFun hv j
    simpa only [Function.update_of_ne hj] using heq
  have hcard := Fintype.card_le_of_injective f hf
  change Fintype.card {x : Fin (m + 2) → R // Finset.univ.sum x = 0 ∧
      Finset.univ.sum (fun j : Fin (m + 2) => (j.val : R) * x j) ∈ s} ≤ _ at hcard
  rw [card_ap_diagonal_labels] at hcard
  simpa only [Fintype.card_sigma, Fintype.card_coe] using hcard

theorem expect_mul_sq_le_expect_sq {I : Type*} [Fintype I] [Nonempty I]
    (f g : I → ℝ) (hg : ∀ i, |g i| ≤ 1) :
    (Finset.univ.expect fun i => f i * g i) ^ 2 ≤
      Finset.univ.expect fun i => f i ^ 2 := by
  have hg2 : (Finset.univ.expect fun i => g i ^ 2) ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro i hi
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hg i)
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : 0 ≤ 1 + g i)]
  calc
    (Finset.univ.expect fun i => f i * g i) ^ 2 ≤
        (Finset.univ.expect fun i => f i ^ 2) * (Finset.univ.expect fun i => g i ^ 2) :=
      Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f g
    _ ≤ (Finset.univ.expect fun i => f i ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hg2 (Finset.expect_nonneg fun i _ => sq_nonneg (f i))
    _ = _ := mul_one _

theorem expect_sq_eq_double {I : Type*} [Fintype I] (f : I → ℝ) :
    (Finset.univ.expect f) ^ 2 =
      Finset.univ.expect fun i => Finset.univ.expect fun j => f i * f j := by
  simpa only [pow_two] using Fintype.expect_mul_expect f f

theorem expect_pair_swap {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) :
    (Finset.univ.expect fun i => Finset.univ.expect fun j => f i j) =
      Finset.univ.expect fun j => Finset.univ.expect fun i => f i j := by
  exact Finset.expect_comm Finset.univ Finset.univ f

/-- Two applications of Cauchy--Schwarz bound correlation with bounded
one-coordinate tests by the rectangular box moment. -/
theorem box_two_correlation_bound {I J : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (f : I → J → ℝ) (g : I → ℝ) (h : J → ℝ)
    (hg : ∀ i, |g i| ≤ 1) (hh : ∀ j, |h j| ≤ 1) :
    (Finset.univ.expect fun i => Finset.univ.expect fun j =>
      f i j * g i * h j) ^ 4 ≤
    Finset.univ.expect fun j => Finset.univ.expect fun j' =>
      (Finset.univ.expect fun i => f i j * f i j') ^ 2 := by
  let C := Finset.univ.expect fun i => Finset.univ.expect fun j => f i j * g i * h j
  let Q := Finset.univ.expect fun i =>
    (Finset.univ.expect fun j => f i j * h j) ^ 2
  have hC : C ^ 2 ≤ Q := by
    have hc : C = Finset.univ.expect fun i =>
        (Finset.univ.expect fun j => f i j * h j) * g i := by
      dsimp [C]
      apply Finset.expect_congr rfl
      intro i hi
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro j hj
      ring
    rw [hc]
    exact expect_mul_sq_le_expect_sq _ g hg
  have hQ : Q = Finset.univ.expect fun j => Finset.univ.expect fun j' =>
      (Finset.univ.expect fun i => f i j * f i j') * (h j * h j') := by
    dsimp [Q]
    simp_rw [expect_sq_eq_double]
    rw [expect_pair_swap]
    apply Finset.expect_congr rfl
    intro j hj
    rw [expect_pair_swap]
    apply Finset.expect_congr rfl
    intro j' hj'
    rw [Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro i hi
    ring
  have hhprod : ∀ p : J × J, |h p.1 * h p.2| ≤ 1 := by
    intro p
    rw [abs_mul]
    exact (mul_le_mul (hh p.1) (hh p.2) (abs_nonneg _) (by positivity)).trans_eq (one_mul 1)
  have hQ2 := expect_mul_sq_le_expect_sq
    (fun p : J × J => Finset.univ.expect fun i => f i p.1 * f i p.2)
    (fun p : J × J => h p.1 * h p.2) hhprod
  have heq (u : J × J → ℝ) : Finset.univ.expect u =
      Finset.univ.expect fun j => Finset.univ.expect fun j' => u (j, j') := by
    simpa only [Finset.univ_product_univ] using
      Finset.expect_product (Finset.univ : Finset J) (Finset.univ : Finset J) u
  rw [heq, heq, ← hQ] at hQ2
  have hQnonneg : 0 ≤ Q := Finset.expect_nonneg fun i _ => sq_nonneg _
  have hsq : C ^ 2 * C ^ 2 ≤ Q * Q :=
    mul_le_mul hC hC (sq_nonneg C) hQnonneg
  change C ^ 4 ≤ _
  nlinarith

theorem expect_pair_eq {I J : Type*} [Fintype I] [Fintype J]
    (f : I × J → ℝ) : Finset.univ.expect f =
      Finset.univ.expect fun i => Finset.univ.expect fun j => f (i, j) := by
  simpa only [Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset I) (Finset.univ : Finset J) f

theorem expect_pow_four_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (Finset.univ.expect f) ^ 4 ≤ Finset.univ.expect fun i => f i ^ 4 := by
  have h1 : (Finset.univ.expect f) ^ 2 ≤ Finset.univ.expect fun i => f i ^ 2 := by
    simpa using expect_mul_sq_le_expect_sq f (fun _ => 1) (by simp)
  have h2 : (Finset.univ.expect fun i => f i ^ 2) ^ 2 ≤
      Finset.univ.expect fun i => f i ^ 4 := by
    calc
      _ ≤ Finset.univ.expect (fun i => (f i ^ 2) ^ 2) := by
        simpa only [mul_one] using
          expect_mul_sq_le_expect_sq (fun i => f i ^ 2) (fun _ => 1) (by simp)
      _ = _ := Finset.expect_congr rfl (by intro i hi; ring)
  have hnonneg : 0 ≤ Finset.univ.expect fun i => f i ^ 2 :=
    Finset.expect_nonneg fun i _ => sq_nonneg _
  have hmul := mul_le_mul h1 h1 (sq_nonneg (Finset.univ.expect f)) hnonneg
  nlinarith

theorem expect_four_rotate {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (f : I → J → K → L → ℝ) :
    (Finset.univ.expect fun i => Finset.univ.expect fun j =>
      Finset.univ.expect fun k => Finset.univ.expect fun l => f i j k l) =
    Finset.univ.expect fun k => Finset.univ.expect fun l =>
      Finset.univ.expect fun i => Finset.univ.expect fun j => f i j k l := by
  calc
    _ = Finset.univ.expect (fun p : I × J =>
        Finset.univ.expect fun q : K × L => f p.1 p.2 q.1 q.2) := by
      simp_rw [expect_pair_eq]
    _ = Finset.univ.expect (fun q : K × L =>
        Finset.univ.expect fun p : I × J => f p.1 p.2 q.1 q.2) := expect_pair_swap _
    _ = _ := by simp_rw [expect_pair_eq]

theorem abs_mul_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul ha hb (abs_nonneg _) (by positivity)).trans_eq (one_mul 1)

/-- A three-variable function correlated with bounded tests omitting one
coordinate is controlled by its eight-corner box moment. The final square
is the average over the last pair of corners. -/
theorem box_three_correlation_bound {I J K : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J] [Fintype K] [Nonempty K]
    (f : I → J → K → ℝ) (g : J → K → ℝ)
    (h : I → K → ℝ) (l : I → J → ℝ)
    (hg : ∀ j k, |g j k| ≤ 1)
    (hh : ∀ i k, |h i k| ≤ 1) (hl : ∀ i j, |l i j| ≤ 1) :
    (Finset.univ.expect fun j => Finset.univ.expect fun k =>
      Finset.univ.expect fun i => f i j k * g j k * h i k * l i j) ^ 8 ≤
    Finset.univ.expect fun i => Finset.univ.expect fun i' =>
      Finset.univ.expect fun k => Finset.univ.expect fun k' =>
        (Finset.univ.expect fun j =>
          (f i j k * f i' j k) * (f i j k' * f i' j k')) ^ 2 := by
  let C := Finset.univ.expect fun j => Finset.univ.expect fun k =>
    Finset.univ.expect fun i => f i j k * g j k * h i k * l i j
  let Q := Finset.univ.expect fun j => Finset.univ.expect fun k =>
    (Finset.univ.expect fun i => f i j k * h i k * l i j) ^ 2
  have hC : C ^ 2 ≤ Q := by
    have hc : C = Finset.univ.expect (fun p : J × K =>
        (Finset.univ.expect fun i => f i p.1 p.2 * h i p.2 * l i p.1) * g p.1 p.2) := by
      rw [expect_pair_eq]
      dsimp [C]
      apply Finset.expect_congr rfl
      intro j hj
      apply Finset.expect_congr rfl
      intro k hk
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro i hi
      ring
    rw [hc]
    simpa only [expect_pair_eq] using expect_mul_sq_le_expect_sq
      (fun p : J × K => Finset.univ.expect fun i => f i p.1 p.2 * h i p.2 * l i p.1)
      (fun p : J × K => g p.1 p.2) (fun p => hg p.1 p.2)
  let T := fun i i' : I => Finset.univ.expect fun j => Finset.univ.expect fun k =>
    (f i j k * f i' j k) * (l i j * l i' j) * (h i k * h i' k)
  have hQ : Q = Finset.univ.expect fun i => Finset.univ.expect fun i' => T i i' := by
    dsimp [Q, T]
    simp_rw [expect_sq_eq_double]
    rw [expect_four_rotate]
    apply Finset.expect_congr rfl
    intro i hi
    apply Finset.expect_congr rfl
    intro i' hi'
    apply Finset.expect_congr rfl
    intro j hj
    apply Finset.expect_congr rfl
    intro k hk
    ring
  have hQ4 : Q ^ 4 ≤ Finset.univ.expect fun i => Finset.univ.expect fun i' =>
      Finset.univ.expect fun k => Finset.univ.expect fun k' =>
        (Finset.univ.expect fun j =>
          (f i j k * f i' j k) * (f i j k' * f i' j k')) ^ 2 := by
    calc
      Q ^ 4 = (Finset.univ.expect fun p : I × I => T p.1 p.2) ^ 4 := by
        rw [expect_pair_eq, hQ]
      _ ≤ Finset.univ.expect fun p : I × I => T p.1 p.2 ^ 4 := expect_pow_four_le _
      _ = Finset.univ.expect (fun i => Finset.univ.expect fun i' => T i i' ^ 4) :=
        expect_pair_eq _
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro i hi
        apply Finset.expect_le_expect
        intro i' hi'
        exact box_two_correlation_bound (fun j k => f i j k * f i' j k)
          (fun j => l i j * l i' j) (fun k => h i k * h i' k)
          (fun j => abs_mul_le_one (hl i j) (hl i' j))
          (fun k => abs_mul_le_one (hh i k) (hh i' k))
  have hQnonneg : 0 ≤ Q :=
    Finset.expect_nonneg fun j _ => Finset.expect_nonneg fun k _ => sq_nonneg _
  have hC4 : C ^ 4 ≤ Q ^ 2 := by
    have hm := mul_le_mul hC hC (sq_nonneg C) hQnonneg
    nlinarith
  have hC8 : C ^ 8 ≤ Q ^ 4 := by
    have hm := mul_le_mul hC4 hC4 (by positivity : 0 ≤ C ^ 4) (sq_nonneg Q)
    nlinarith
  exact hC8.trans hQ4

theorem expect_pow_eight_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    (Finset.univ.expect f) ^ 8 ≤ Finset.univ.expect fun i => f i ^ 8 := by
  have h4 := expect_pow_four_le f
  have hnonneg : 0 ≤ Finset.univ.expect fun i => f i ^ 4 :=
    Finset.expect_nonneg fun i _ => by positivity
  have hm := mul_le_mul h4 h4 (by positivity : 0 ≤ (Finset.univ.expect f) ^ 4) hnonneg
  have h8 : (Finset.univ.expect f) ^ 8 ≤
      (Finset.univ.expect fun i => f i ^ 4) ^ 2 := by nlinarith
  calc
    _ ≤ (Finset.univ.expect fun i => f i ^ 4) ^ 2 := h8
    _ ≤ Finset.univ.expect (fun i => (f i ^ 4) ^ 2) := by
      simpa only [mul_one] using
        expect_mul_sq_le_expect_sq (fun i => f i ^ 4) (fun _ => 1) (by simp)
    _ = _ := Finset.expect_congr rfl (by intro i hi; ring)

/-- The tetrahedron correlation is controlled by one face's box moment,
uniformly over the size of the four finite vertex classes. This supplies
counting control when that moment is small; it asserts no regularity or
removal theorem. -/
theorem tetrahedron_correlation_bound {I J K L : Type*}
    [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    (f : I → J → K → ℝ) (g : J → K → L → ℝ)
    (h : I → K → L → ℝ) (l : I → J → L → ℝ)
    (hg : ∀ j k w, |g j k w| ≤ 1)
    (hh : ∀ i k w, |h i k w| ≤ 1) (hl : ∀ i j w, |l i j w| ≤ 1) :
    (Finset.univ.expect fun w => Finset.univ.expect fun j =>
      Finset.univ.expect fun k => Finset.univ.expect fun i =>
        f i j k * g j k w * h i k w * l i j w) ^ 8 ≤
    Finset.univ.expect fun i => Finset.univ.expect fun i' =>
      Finset.univ.expect fun k => Finset.univ.expect fun k' =>
        (Finset.univ.expect fun j =>
          (f i j k * f i' j k) * (f i j k' * f i' j k')) ^ 2 := by
  calc
    _ ≤ Finset.univ.expect (fun w =>
        (Finset.univ.expect fun j => Finset.univ.expect fun k =>
          Finset.univ.expect fun i => f i j k * g j k w * h i k w * l i j w) ^ 8) :=
      expect_pow_eight_le _
    _ ≤ Finset.univ.expect (fun _ : L =>
        Finset.univ.expect fun i => Finset.univ.expect fun i' =>
          Finset.univ.expect fun k => Finset.univ.expect fun k' =>
            (Finset.univ.expect fun j =>
              (f i j k * f i' j k) * (f i j k' * f i' j k')) ^ 2) := by
      apply Finset.expect_le_expect
      intro w hw
      exact box_three_correlation_bound f (fun j k => g j k w)
        (fun i k => h i k w) (fun i j => l i j w)
        (fun j k => hg j k w) (fun i k => hh i k w) (fun i j => hl i j w)
    _ = _ := Fintype.expect_const _

end Submission.Helpers
