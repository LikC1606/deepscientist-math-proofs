import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Asymptotics.Defs
namespace Submission.Helpers

theorem upper_spectralRadius_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) :
    spectralRadius ℝ (Matrix.reindex e e A) = spectralRadius ℝ A := by
  have hs := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ e) A
  change spectrum ℝ (Matrix.reindex e e A) = spectrum ℝ A at hs
  simp only [spectralRadius_eq_of_unital, hs]
theorem upper_eigenspace_finrank_reindex
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℝ) (lambda : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.reindex e e A).mulVecLin lambda) =
      Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) := by
  let B := Matrix.reindex e e A
  let E := LinearEquiv.funCongrLeft ℝ ℝ e.symm
  have hcomm (x : ι → ℝ) : B.mulVec (E x) = E (A.mulVec x) := by
    change B.mulVecLin (E x) = E (A.mulVec x)
    rw [Matrix.mulVecLin_reindex]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change E (A.mulVec (fun i => x (e.symm (e i)))) = E (A.mulVec x)
    simp only [e.symm_apply_apply]
  have hmap : (Module.End.eigenspace A.mulVecLin lambda).map E.toLinearMap =
      Module.End.eigenspace B.mulVecLin lambda := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      change B.mulVec (E x) = lambda • E x
      rw [hcomm]
      change E (A.mulVecLin x) = lambda • E x
      rw [Module.End.mem_eigenspace_iff.mp hx, map_smul]
    · intro hy
      refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
      apply Module.End.mem_eigenspace_iff.mpr
      apply E.injective
      change E (A.mulVec (E.symm y)) = E (lambda • E.symm y)
      rw [map_smul, ← hcomm, E.apply_symm_apply]
      exact Module.End.mem_eigenspace_iff.mp hy
  exact (LinearEquiv.ofSubmodules E _ _ hmap).finrank_eq.symm
theorem upper_relabel_connected_radius
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ H : SimpleGraph (Fin (Fintype.card ι)), H.Connected ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       spectralRadius ℝ (H.adjMatrix ℝ)) = spectralRadius ℝ (G.adjMatrix ℝ) := by
  classical
  let H := G.overFin (rfl : Fintype.card ι = Fintype.card ι)
  let e := G.overFinIso (rfl : Fintype.card ι = Fintype.card ι)
  refine ⟨H, e.connected_iff.mp hG, ?_⟩
  have hm := e.reindex_adjMatrix ℝ
  rw [← hm]
  exact upper_spectralRadius_reindex e.toEquiv (G.adjMatrix ℝ)
theorem upper_component_overFin_data
    (n : ℕ) (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent)
    (Δ : ℕ) (hΔ : ∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) :
    letI : Fintype C.supp := Fintype.ofFinite C.supp
    letI : DecidableEq C.supp := Classical.decEq C.supp
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj
    ∃ H : SimpleGraph (Fin (Fintype.card C.supp)), H.Connected ∧
      (∀ i, ({j | H.Adj i j} : Set (Fin (Fintype.card C.supp))).ncard ≤ Δ) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       spectralRadius ℝ (H.adjMatrix ℝ)) =
        spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ) ∧
      ∀ lambda : ℝ,
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
         Module.finrank ℝ (Module.End.eigenspace (H.adjMatrix ℝ).mulVecLin lambda)) =
        Module.finrank ℝ (Module.End.eigenspace
          (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite C.supp
  letI : DecidableEq C.supp := Classical.decEq C.supp
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj
  let H := C.toSimpleGraph.overFin (rfl : Fintype.card C.supp = Fintype.card C.supp)
  let e := C.toSimpleGraph.overFinIso (rfl : Fintype.card C.supp = Fintype.card C.supp)
  refine ⟨H, e.connected_iff.mp C.connected_toSimpleGraph, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hΔ (e.symm i).val)
    exact Set.ncard_le_ncard_of_injOn (fun j => (e.symm j).val)
      (fun j hj => e.symm.map_adj_iff.mpr hj)
      (fun x _ y _ h => e.symm.injective (Subtype.ext h))
  · rw [← e.reindex_adjMatrix ℝ]
    exact upper_spectralRadius_reindex e.toEquiv (C.toSimpleGraph.adjMatrix ℝ)
  · intro lambda
    rw [← e.reindex_adjMatrix ℝ]
    exact upper_eigenspace_finrank_reindex e.toEquiv (C.toSimpleGraph.adjMatrix ℝ) lambda
theorem upper_small_eigenspace_bound
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (lambda : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) ≤ Fintype.card ι := by
  simpa only [Module.finrank_pi, Module.finrank_self, mul_one] using
    (Module.End.eigenspace A.mulVecLin lambda).finrank_le
theorem upper_scaled_gram_psd_rank
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ)
    (w : Fin n → EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hgram : Matrix.gram ℝ w = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A) :
    let P := ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ : Fin n => (1 : ℝ))
    P.PosSemidef ∧ P.rank ≤ d := by
  classical
  dsimp only
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have hp : 0 < 1 / (2 * α) := one_div_pos.mpr (mul_pos (by norm_num) hα.1)
  have heq : ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) =
        (1 / (2 * α)) • Matrix.gram ℝ w := by
    rw [hgram]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hα0] <;> ring
  rw [heq]
  refine ⟨(Matrix.posSemidef_gram ℝ w).smul hp.le, ?_⟩
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_iff_ne_zero.mpr (ne_of_gt hp))]
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let M : Matrix (Fin d) (Fin n) ℝ := Matrix.of (fun i j => b.repr (w j) i)
  rw [Matrix.gram_eq_conjTranspose_mul b w]
  exact (Matrix.rank_mul_le_right M.conjTranspose M).trans
    (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height M)
theorem upper_floor_from_component_count
    (q n d t : ℕ) (hq : 2 ≤ q) (hcount : q * t ≤ n)
    (hrank : n + 1 - t ≤ d) :
    n ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have htn : t ≤ n := by nlinarith
  have hrNat : n + 1 ≤ d + t := by omega
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hcountR : (q : ℝ) * (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcount
  have hrR : (n : ℝ) + 1 ≤ (d : ℝ) + (t : ℝ) := by exact_mod_cast hrNat
  apply Nat.le_floor
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1)).mpr
  have hm := mul_le_mul_of_nonneg_left hrR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hm, hcountR]
theorem upper_floor_ge_dimension (q d : ℕ) (hq : 2 ≤ q) (hd : q ≤ d) :
    d ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hdR : (q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  apply Nat.le_floor
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1)).mpr
  nlinarith only [hdR]
theorem upper_floor_from_small_exception
    (q d n M : ℕ) (hq : 2 ≤ q)
    (hd : 2 * q + (q - 1) * M ≤ d) (hn : n ≤ d + 1 + M) :
    n ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hdR : 2 * (q : ℝ) + ((q : ℝ) - 1) * (M : ℝ) ≤ (d : ℝ) := by
    have hdR' : 2 * (q : ℝ) + ((q - 1 : ℕ) : ℝ) * (M : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast hd
    simpa only [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one] using hdR'
  have hnR : (n : ℝ) ≤ (d : ℝ) + 1 + (M : ℝ) := by exact_mod_cast hn
  apply Nat.le_floor
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1)).mpr
  have hm := mul_le_mul_of_nonneg_right hnR (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
  nlinarith only [hm, hdR]
theorem upper_floor_from_small_multiplicity
    (q d n : ℕ) (hq : 2 ≤ q) (hd : 4 * q ≤ d)
    (hn : (n : ℝ) ≤ (d : ℝ) + 1 + (1 / (2 * (q : ℝ))) * (n : ℝ)) :
    n ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hdR : 4 * (q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hqpos : 0 < (q : ℝ) := by linarith
  have hm := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 2 * (q : ℝ))
  have hcancel : (2 * (q : ℝ)) * ((1 / (2 * (q : ℝ))) * (n : ℝ)) = (n : ℝ) := by
    field_simp
  have hr : (2 * (q : ℝ) - 1) * (n : ℝ) ≤ 2 * (q : ℝ) * ((d : ℝ) + 1) := by
    nlinarith only [hm, hcancel]
  apply Nat.le_floor
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (q : ℝ) - 1)).mpr
  have hr' := mul_le_mul_of_nonneg_left hr (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
  have hd' : 0 ≤ (q : ℝ) * ((d : ℝ) - 4 * (q : ℝ) + 3) :=
    mul_nonneg hqpos.le (by linarith)
  nlinarith only [hr', hd', hqR]
theorem upper_rank_one_principal_psd
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (lambda : ℝ) (f : κ → ι) (hf : Function.Injective f)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef) :
    (lambda • (1 : Matrix κ κ ℝ) - A.submatrix f f +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef := by
  have heq : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).submatrix f f =
      lambda • (1 : Matrix κ κ ℝ) - A.submatrix f f +
        (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext i j
    simp [Matrix.one_apply, hf.eq_iff]
  rw [← heq]
  exact hP.submatrix f
theorem upper_rank_one_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lambda : ℝ) (x : ι → ℝ) :
    dotProduct x ((lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).mulVec x) =
        lambda * dotProduct x x - dotProduct x (A.mulVec x) +
          (1 / 2 : ℝ) * (∑ i, x i) ^ 2 := by
  have hJ : (Matrix.of (fun _ _ : ι => (1 : ℝ))).mulVec x = fun _ => ∑ i, x i := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul]
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, hJ]
  simp only [smul_eq_mul, dotProduct, Finset.sum_mul, pow_two]
theorem upper_psd_no_two_supercritical_eigenpairs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lambda rho tau : ℝ)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef)
    (x y : ι → ℝ) (hx : A.mulVec x = rho • x) (hy : A.mulVec y = tau • y)
    (hxx : dotProduct x x = 1) (hyy : dotProduct y y = 1)
    (hxy : dotProduct x y = 0) (hrho : lambda < rho) (htau : lambda < tau) : False := by
  let a := ∑ i, x i
  let b := ∑ i, y i
  have ha : a ≠ 0 := by
    intro ha
    have hn := hP.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hn
    rw [upper_rank_one_quadratic, hx, dotProduct_smul, smul_eq_mul, hxx] at hn
    change 0 ≤ lambda * 1 - rho * 1 + (1 / 2 : ℝ) * a ^ 2 at hn
    rw [ha] at hn
    nlinarith only [hn, hrho]
  let z := b • x - a • y
  have hyx : dotProduct y x = 0 := by rw [dotProduct_comm, hxy]
  have hzsum : ∑ i, z i = 0 := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    change b * a - a * b = 0
    ring
  have hzq : dotProduct z (A.mulVec z) = b ^ 2 * rho + a ^ 2 * tau := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hxy, hyx, hxx, hyy]
    ring
  have hzn : dotProduct z z = b ^ 2 + a ^ 2 := by
    simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hxy, hyx, hxx, hyy]
    ring
  have hn := hP.dotProduct_mulVec_nonneg z
  simp only [star_trivial] at hn
  rw [upper_rank_one_quadratic, hzsum, hzq, hzn] at hn
  have hs := mul_pos (sq_pos_of_ne_zero ha) (sub_pos.mpr htau)
  have hw := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hrho.le)
  nlinarith only [hn, hs, hw]
theorem upper_psd_eigenvalues_except_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (lambda : ℝ)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef) :
    ∃ j : ι, ∀ i : ι, i ≠ j → hA.eigenvalues i ≤ lambda := by
  classical
  have hn (i : ι) : dotProduct (hA.eigenvectorBasis i).ofLp
      (hA.eigenvectorBasis i).ofLp = 1 := by
    calc
      _ = ‖hA.eigenvectorBasis i‖ ^ 2 := by
        simpa only [dotProduct, ← pow_two] using
          (EuclideanSpace.real_norm_sq_eq (hA.eigenvectorBasis i)).symm
      _ = 1 := by rw [hA.eigenvectorBasis.norm_eq_one]; norm_num
  have ho (i j : ι) (hij : i ≠ j) : dotProduct (hA.eigenvectorBasis i).ofLp
      (hA.eigenvectorBasis j).ofLp = 0 := by
    have hh := hA.eigenvectorBasis.inner_eq_ite i j
    simpa only [PiLp.inner_apply, Real.inner_apply, dotProduct, if_neg hij] using hh
  by_cases hex : ∃ j, lambda < hA.eigenvalues j
  · obtain ⟨j, hj⟩ := hex
    refine ⟨j, ?_⟩
    intro i hij
    by_contra hi
    exact upper_psd_no_two_supercritical_eigenpairs A lambda
      (hA.eigenvalues i) (hA.eigenvalues j) hP
      (hA.eigenvectorBasis i).ofLp (hA.eigenvectorBasis j).ofLp
      (hA.mulVec_eigenvectorBasis i) (hA.mulVec_eigenvectorBasis j)
      (hn i) (hn j) (ho i j hij) (lt_of_not_ge hi) hj
  · refine ⟨Classical.arbitrary ι, ?_⟩
    intro i _
    exact le_of_not_gt (fun hi => hex ⟨i, hi⟩)
theorem supercritical_component_overFin_data
    (n : ℕ) (G : SimpleGraph (Fin n)) (C : G.ConnectedComponent)
    (Δ : ℕ) (hdegree : ∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    letI : Fintype C.supp := Fintype.ofFinite C.supp
    letI : DecidableEq C.supp := Classical.decEq C.supp
    letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj
    ∃ (H : SimpleGraph (Fin (Fintype.card C.supp)))
      (f : Fin (Fintype.card C.supp) → Fin n),
      H.Connected ∧ Function.Injective f ∧
      (∀ i, ({j | H.Adj i j} : Set (Fin (Fintype.card C.supp))).ncard ≤ Δ) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       (G.adjMatrix ℝ).submatrix f f = H.adjMatrix ℝ ∧
       ∀ lambda : ℝ,
         Module.finrank ℝ (Module.End.eigenspace (H.adjMatrix ℝ).mulVecLin lambda) =
         Module.finrank ℝ (Module.End.eigenspace
           (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda)) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : Fintype C.supp := Fintype.ofFinite C.supp
  letI : DecidableEq C.supp := Classical.decEq C.supp
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj
  let H := C.toSimpleGraph.overFin (rfl : Fintype.card C.supp = Fintype.card C.supp)
  let e := C.toSimpleGraph.overFinIso (rfl : Fintype.card C.supp = Fintype.card C.supp)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  let f : Fin (Fintype.card C.supp) → Fin n := fun i => (e.symm i).val
  have hf : Function.Injective f := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  refine ⟨H, f, e.connected_iff.mp C.connected_toSimpleGraph, hf, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hdegree (f i))
    exact Set.ncard_le_ncard_of_injOn f
      (fun j hj => e.symm.map_adj_iff.mpr hj)
      (fun _ _ _ _ hij => hf hij)
  · ext i j
    have ha : G.Adj (f i) (f j) ↔ H.Adj i j := e.symm.map_adj_iff
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, ha]
  · intro lambda
    rw [← e.reindex_adjMatrix ℝ]
    exact upper_eigenspace_finrank_reindex e.toEquiv (C.toSimpleGraph.adjMatrix ℝ) lambda
theorem error_term_of_bounds :
    ∀ (f : ℕ → ℕ), (∀ d : ℕ, d ≤ f d) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ d in Filter.atTop,
        (f d : ℝ) ≤ (1 + ε) * (d : ℝ)) →
      ∃ e : ℕ → ℝ, e =o[Filter.atTop] (Nat.cast : ℕ → ℝ) ∧
        ∀ d : ℕ, (f d : ℝ) = (d : ℝ) + e d := by
  intro f hlower hupper
  refine ⟨fun d => (f d : ℝ) - (d : ℝ), ?_, ?_⟩
  · apply Asymptotics.isLittleO_iff.mpr
    intro ε hε
    refine (hupper ε hε).mono ?_
    intro d hd
    change ‖(f d : ℝ) - (d : ℝ)‖ ≤ ε * ‖(d : ℝ)‖
    have hl : (d : ℝ) ≤ (f d : ℝ) := Nat.cast_le.mpr (hlower d)
    rw [Real.norm_of_nonneg (sub_nonneg.mpr hl),
      Real.norm_of_nonneg (Nat.cast_nonneg d)]
    linarith only [hd]
  · intro d
    dsimp only
    linarith
theorem real_inner_preserving_map_of_finrank_le
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (d : ℕ) (hd : Module.finrank ℝ E ≤ d) :
    ∃ f : E → EuclideanSpace ℝ (Fin d),
      ∀ x y, inner ℝ (f x) (f y) = inner ℝ x y := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let c := EuclideanSpace.basisFun (Fin d) ℝ
  let u : Fin (Module.finrank ℝ E) → EuclideanSpace ℝ (Fin d) :=
    fun i => c (Fin.castLE hd i)
  have hu : Orthonormal ℝ u := c.orthonormal.comp (Fin.castLE hd) (Fin.castLE_injective hd)
  refine ⟨fun x => ∑ i, b.repr x i • u i, ?_⟩
  intro x y
  calc
    inner ℝ (∑ i, b.repr x i • u i) (∑ i, b.repr y i • u i) =
        ∑ i, b.repr x i * b.repr y i := by
      simpa using hu.inner_sum (fun i => b.repr x i) (fun i => b.repr y i) Finset.univ
    _ = inner ℝ (b.repr x) (b.repr y) := by
      simp only [PiLp.inner_apply, Real.inner_apply]
    _ = inner ℝ x y := b.repr.inner_map_map x y
theorem positive_semidefinite_gram_realization :
    ∀ (n d : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
      M.PosSemidef → M.rank ≤ d →
      ∃ v : Fin n → EuclideanSpace ℝ (Fin d), Matrix.gram ℝ v = M := by
  classical
  intro n d M hM hd
  letI : PartialOrder (Matrix (Fin n) (Fin n) ℝ) := Matrix.instPartialOrder
  letI : StarOrderedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.instStarOrderedRing
  letI : NonnegSpectrumClass ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.instNonnegSpectrumClass
  obtain ⟨B, hB⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := M)).mp hM.nonneg
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin B
  let W := LinearMap.range L
  have hW : Module.finrank ℝ W = M.rank := by
    calc
      Module.finrank ℝ W = B.rank := by
        change Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin B)) = B.rank
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
        convert
          (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).symm using 1
      _ = M.rank := by
        rw [hB, Matrix.star_eq_conjTranspose, Matrix.rank_conjTranspose_mul_self]
  let w : Fin n → W := fun i =>
    ⟨WithLp.toLp 2 (B.transpose i), by
      refine ⟨WithLp.toLp 2 (Pi.single i 1), ?_⟩
      change WithLp.toLp 2 (B.mulVec (Pi.single i 1)) = WithLp.toLp 2 (B.transpose i)
      exact congrArg (WithLp.toLp 2) (Matrix.mulVec_single_one B i)⟩
  obtain ⟨f, hf⟩ := real_inner_preserving_map_of_finrank_le W d (hW.symm ▸ hd)
  refine ⟨fun i => f (w i), ?_⟩
  ext i j
  rw [Matrix.gram_apply, hf, Submodule.coe_inner]
  change inner ℝ (WithLp.toLp 2 (B.transpose i)) (WithLp.toLp 2 (B.transpose j)) = M i j
  rw [inner_matrix_col_col]
  rw [hB, Matrix.star_eq_conjTranspose]
theorem real_matrix_eigenspace_finrank_toEuclidean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace A.mulVecLin μ) =
      Module.finrank ℝ (Module.End.eigenspace A.toEuclideanLin μ) := by
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  have hm : (Module.End.eigenspace A.toEuclideanLin μ).map e.toLinearMap =
      Module.End.eigenspace A.mulVecLin μ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      have h := congrArg e (Module.End.mem_eigenspace_iff.mp hy)
      simpa [e, Matrix.toLpLin_apply] using h
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply Module.End.mem_eigenspace_iff.mpr
      apply e.injective
      simpa [e, Matrix.toLpLin_apply] using Module.End.mem_eigenspace_iff.mp hx
  rw [← hm]
  exact e.finrank_map_eq _
theorem real_matrix_eigenspace_finrank_eq_card
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace A.mulVecLin μ) =
      (Finset.univ.filter fun i => hA.eigenvalues i = μ).card := by
  classical
  rw [real_matrix_eigenspace_finrank_toEuclidean]
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have hc : (Finset.univ.filter fun i => hA.eigenvalues i = μ).card =
      (Finset.univ.filter fun i => hA.eigenvalues₀ i = μ).card :=
    Finset.card_equiv e.symm (by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)
  rw [hc]
  exact ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).card_filter_eigenvalues_eq
    finrank_euclideanSpace μ).symm
theorem real_matrix_eigenspace_eq_bot_of_not_eigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ)
    (hμ : ∀ i, hA.eigenvalues i ≠ μ) :
    Module.End.eigenspace A.mulVecLin μ = ⊥ := by
  classical
  apply Submodule.finrank_eq_zero.mp
  rw [real_matrix_eigenspace_finrank_eq_card A hA μ]
  simp [hμ]
theorem real_matrix_trace_pow_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.diagonal_pow]
  simp only [Matrix.trace_diagonal, Pi.pow_apply, Function.comp_apply]
  rfl
theorem real_matrix_eigenspace_multiplicity_trace_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ) (t : ℕ) :
    (Module.finrank ℝ (Module.End.eigenspace A.mulVecLin μ) : ℝ) * μ ^ (2 * t) ≤
      (A ^ (2 * t)).trace := by
  classical
  rw [real_matrix_eigenspace_finrank_eq_card A hA μ,
    real_matrix_trace_pow_eq_sum A hA (2 * t)]
  have hs : (∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i = μ),
      (hA.eigenvalues i) ^ (2 * t)) =
      ((Finset.univ.filter (fun i => hA.eigenvalues i = μ)).card : ℝ) * μ ^ (2 * t) := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    simp
  rw [← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro i _ _
  rw [mul_comm 2 t, pow_mul]
  exact sq_nonneg _
theorem real_matrix_eigenspace_deletion_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (μ : ℝ) (s : Finset ι) :
    Module.finrank ℝ (Module.End.eigenspace A.mulVecLin μ) ≤
      s.card + Module.finrank ℝ (Module.End.eigenspace
        (A.submatrix (fun i : {i // i ∉ s} => i.val)
          (fun i : {i // i ∉ s} => i.val)).mulVecLin μ) := by
  classical
  let E := Module.End.eigenspace A.mulVecLin μ
  let f : E →ₗ[ℝ] (s → ℝ) :=
    LinearMap.pi fun i => (LinearMap.proj i.val).comp E.subtype
  have hz (x : LinearMap.ker f) (i : ι) (hi : i ∈ s) : x.val.val i = 0 := by
    exact congrFun (LinearMap.mem_ker.mp x.property) ⟨i, hi⟩
  let B := A.submatrix (fun i : {i // i ∉ s} => i.val)
    (fun i : {i // i ∉ s} => i.val)
  have he (x : LinearMap.ker f) :
      (fun i : {i // i ∉ s} => x.val.val i.val) ∈
        Module.End.eigenspace B.mulVecLin μ := by
    apply Module.End.mem_eigenspace_iff.mpr
    funext i
    change (∑ j : {j // j ∉ s}, A i.val j.val * x.val.val j.val) = μ * x.val.val i.val
    rw [← Finset.sum_subtype (Finset.univ.filter fun j => j ∉ s)
      (by intro j; simp) (fun j => A i.val j * x.val.val j)]
    have hsum : (∑ j ∈ Finset.univ.filter (fun j => j ∉ s), A i.val j * x.val.val j) =
        ∑ j, A i.val j * x.val.val j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ s
      · simp [hj, hz x j hj]
      · simp [hj]
    rw [hsum]
    exact congrFun (Module.End.mem_eigenspace_iff.mp x.val.property) i.val
  let g : LinearMap.ker f →ₗ[ℝ] Module.End.eigenspace B.mulVecLin μ :=
    { toFun := fun x => ⟨fun i => x.val.val i.val, he x⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · rw [hz x i hi, hz y i hi]
    · exact congrFun (congrArg Subtype.val h) ⟨i, hi⟩
  have hk := LinearMap.finrank_le_finrank_of_injective (f := g) hg
  have hr : Module.finrank ℝ (LinearMap.range f) ≤ s.card := by
    have h := (LinearMap.range f).finrank_le
    simpa using h
  have hn := f.finrank_range_add_finrank_ker
  dsimp only [E] at hn
  exact hn.symm.le.trans (Nat.add_le_add hr hk)
theorem real_unitary_dotProduct_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (x y : ι → ℝ) :
    dotProduct ((U : Matrix ι ι ℝ).mulVec x) ((U : Matrix ι ι ℝ).mulVec y) =
      dotProduct x y := by
  have hU : (U : Matrix ι ι ℝ).transpose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self U
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
theorem real_matrix_dotProduct_eq_eigen_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    dotProduct x x = ∑ i, ((star (hA.eigenvectorUnitary : Matrix ι ι ℝ)).mulVec x i) ^ 2 := by
  let U := hA.eigenvectorUnitary
  let y := (star (U : Matrix ι ι ℝ)).mulVec x
  have hx : (U : Matrix ι ι ℝ).mulVec y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mulVec]
  calc
    dotProduct x x = dotProduct ((U : Matrix ι ι ℝ).mulVec y)
        ((U : Matrix ι ι ℝ).mulVec y) := by rw [hx]
    _ = dotProduct y y := real_unitary_dotProduct_mulVec U y y
    _ = ∑ i, y i ^ 2 := by simp only [dotProduct, pow_two]
theorem real_matrix_quadratic_eq_eigen_coordinates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    dotProduct x (A.mulVec x) =
      ∑ i, hA.eigenvalues i * ((star (hA.eigenvectorUnitary : Matrix ι ι ℝ)).mulVec x i) ^ 2 := by
  let U := hA.eigenvectorUnitary
  let y := (star (U : Matrix ι ι ℝ)).mulVec x
  have hx : (U : Matrix ι ι ℝ).mulVec y = x := by
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mulVec]
  have hAx : A.mulVec x = (U : Matrix ι ι ℝ).mulVec
      ((Matrix.diagonal hA.eigenvalues).mulVec y) := by
    conv_lhs => rw [hA.spectral_theorem]
    change ((U : Matrix ι ι ℝ) * Matrix.diagonal hA.eigenvalues *
      star (U : Matrix ι ι ℝ)).mulVec x = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc
    dotProduct x (A.mulVec x) =
        dotProduct ((U : Matrix ι ι ℝ).mulVec y)
          ((U : Matrix ι ι ℝ).mulVec ((Matrix.diagonal hA.eigenvalues).mulVec y)) := by
      rw [hx, hAx]
    _ = dotProduct y ((Matrix.diagonal hA.eigenvalues).mulVec y) :=
      real_unitary_dotProduct_mulVec U y _
    _ = ∑ i, hA.eigenvalues i * (y i) ^ 2 := by
      simp only [Matrix.mulVec_diagonal, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
theorem real_matrix_rayleigh_le_of_eigenvalues_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ)
    (hμ : ∀ i, hA.eigenvalues i ≤ μ) (x : ι → ℝ) :
    dotProduct x (A.mulVec x) ≤ μ * dotProduct x x := by
  rw [real_matrix_quadratic_eq_eigen_coordinates A hA x,
    real_matrix_dotProduct_eq_eigen_coordinates A hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμ i) (sq_nonneg _)
theorem real_matrix_rayleigh_le_away_from_exception
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ) (j : ι)
    (hμ : ∀ i, i ≠ j → hA.eigenvalues i ≤ μ) (x : ι → ℝ)
    (hx : (star (hA.eigenvectorUnitary : Matrix ι ι ℝ)).mulVec x j = 0) :
    dotProduct x (A.mulVec x) ≤ μ * dotProduct x x := by
  rw [real_matrix_quadratic_eq_eigen_coordinates A hA x,
    real_matrix_dotProduct_eq_eigen_coordinates A hA x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = j
  · subst i
    simp only [hx, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right (hμ i hi) (sq_nonneg _)
theorem real_matrix_no_two_orthogonal_supercritical_vectors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ) (j : ι)
    (hμ : ∀ i, i ≠ j → hA.eigenvalues i ≤ μ)
    (x y : ι → ℝ)
    (hxy : dotProduct x y = 0)
    (hxyA : dotProduct x (A.mulVec y) = 0)
    (hx : μ * dotProduct x x < dotProduct x (A.mulVec x))
    (hy : μ * dotProduct y y < dotProduct y (A.mulVec y)) : False := by
  let U : Matrix ι ι ℝ := star (hA.eigenvectorUnitary : Matrix ι ι ℝ)
  let a := U.mulVec x j
  let b := U.mulVec y j
  have hAt : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hyxA : dotProduct y (A.mulVec x) = 0 := by
    rw [← hAt, Matrix.dotProduct_transpose_mulVec, hxyA]
  have hyx : dotProduct y x = 0 := by rw [dotProduct_comm, hxy]
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · exact (not_lt_of_ge (real_matrix_rayleigh_le_away_from_exception
        A hA μ j hμ x ha)) hx
    · let z := b • x - a • y
      have hz : U.mulVec z j = 0 := by
        simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        change b * a - a * b = 0
        ring
      have hbound := real_matrix_rayleigh_le_away_from_exception A hA μ j hμ z hz
      have hq : dotProduct z (A.mulVec z) =
          b ^ 2 * dotProduct x (A.mulVec x) + a ^ 2 * dotProduct y (A.mulVec y) := by
        simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
          dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hxyA, hyxA]
        ring
      have hn : dotProduct z z = b ^ 2 * dotProduct x x + a ^ 2 * dotProduct y y := by
        simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct,
          dotProduct_smul, smul_eq_mul, hxy, hyx]
        ring
      have hs := mul_pos (sq_pos_of_ne_zero hb) (sub_pos.mpr hx)
      rw [hq, hn, ha] at hbound
      simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at hbound
      nlinarith only [hs, hbound]
  · let z := b • x - a • y
    have hz : U.mulVec z j = 0 := by
      simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      change b * a - a * b = 0
      ring
    have hbound := real_matrix_rayleigh_le_away_from_exception A hA μ j hμ z hz
    have hq : dotProduct z (A.mulVec z) =
        b ^ 2 * dotProduct x (A.mulVec x) + a ^ 2 * dotProduct y (A.mulVec y) := by
      simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
        dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hxyA, hyxA]
      ring
    have hn : dotProduct z z = b ^ 2 * dotProduct x x + a ^ 2 * dotProduct y y := by
      simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hxy, hyx]
      ring
    have hs := mul_pos (sq_pos_of_ne_zero ha) (sub_pos.mpr hy)
    have hs' := mul_nonneg (sq_nonneg b) (le_of_lt (sub_pos.mpr hx))
    rw [hq, hn] at hbound
    nlinarith only [hs, hs', hbound]
theorem real_matrix_eigen_of_rayleigh_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ)
    (hμ : ∀ x, dotProduct x (A.mulVec x) ≤ μ * dotProduct x x)
    (p : ι → ℝ) (hp : dotProduct p (A.mulVec p) = μ * dotProduct p p) :
    A.mulVec p = μ • p := by
  have hB : (μ • (1 : Matrix ι ι ℝ) - A).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint μ)).sub hA)
    intro x
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      sub_nonneg] using hμ x
  have hz : dotProduct (star p) ((μ • (1 : Matrix ι ι ℝ) - A).mulVec p) = 0 := by
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hp, sub_self]
  have he := hB.dotProduct_mulVec_zero_iff.mp hz
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero, eq_comm] using he
theorem real_matrix_quadratic_le_abs
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ) :
    dotProduct x (A.mulVec x) ≤
      dotProduct (fun i => |x i|) (A.mulVec (fun i => |x i|)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    x i * (A i j * x j) = A i j * (x i * x j) := by ring
    _ ≤ A i j * |x i * x j| := mul_le_mul_of_nonneg_left (le_abs_self _) (hA i j)
    _ = |x i| * (A i j * |x j|) := by rw [abs_mul]; ring
theorem real_matrix_nonnegative_top_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j) :
    ∃ (ρ : ℝ) (p : ι → ℝ), p ≠ 0 ∧ (∀ i, 0 ≤ p i) ∧
      A.mulVec p = ρ • p ∧
      (∀ x, dotProduct x (A.mulVec x) ≤ ρ * dotProduct x x) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues Finset.univ_nonempty
  let ρ := hA.eigenvalues i
  let x : ι → ℝ := WithLp.ofLp (hA.eigenvectorBasis i)
  let p : ι → ℝ := fun j => |x j|
  have hx : x ≠ 0 := by
    intro hx
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
    exact hx
  have hp : p ≠ 0 := by
    intro hp
    apply hx
    funext j
    exact abs_eq_zero.mp (congrFun hp j)
  have hbound := real_matrix_rayleigh_le_of_eigenvalues_le A hA ρ
    (fun j => hi j (Finset.mem_univ j))
  have hnorm : dotProduct p p = dotProduct x x := by
    simp only [dotProduct, p]
    apply Finset.sum_congr rfl
    intro j _
    nlinarith only [sq_abs (x j)]
  have hqx : dotProduct x (A.mulVec x) = ρ * dotProduct x x := by
    rw [hA.mulVec_eigenvectorBasis i]
    exact dotProduct_smul ρ x x
  have heq : dotProduct p (A.mulVec p) = ρ * dotProduct p p := by
    apply le_antisymm (hbound p)
    rw [hnorm, ← hqx]
    exact real_matrix_quadratic_le_abs A hn x
  exact ⟨ρ, p, hp, fun j => abs_nonneg _,
    real_matrix_eigen_of_rayleigh_eq A hA ρ hbound p heq, hbound⟩
theorem adjacency_nonnegative_eigenvector_zero_of_zero
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (hG : G.Preconnected) (ρ : ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (he : (G.adjMatrix ℝ).mulVec p = ρ • p)
    (u : ι) (hu : p u = 0) : p = 0 := by
  classical
  have hstep {i j : ι} (hij : G.Adj i j) (hi : p i = 0) : p j = 0 := by
    have hsum := congrFun he i
    change (∑ k, G.adjMatrix ℝ i k * p k) = ρ * p i at hsum
    have ht : G.adjMatrix ℝ i j * p j ≤ ∑ k, G.adjMatrix ℝ i k * p k :=
      Finset.single_le_sum (fun k _ => mul_nonneg (by simp only [G.adjMatrix_apply]; split <;> norm_num)
        (hp k)) (Finset.mem_univ j)
    rw [hsum, hi, mul_zero, G.adjMatrix_apply, if_pos hij, one_mul] at ht
    exact le_antisymm ht (hp j)
  have hw {i j : ι} (w : G.Walk i j) : p i = 0 → p j = 0 := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hi => ih (hstep h hi)
  funext i
  obtain ⟨w⟩ := hG u i
  exact hw w hu
theorem multiplicity_connected_positive_eigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ (ρ : ℝ) (p : ι → ℝ), (∀ i, 0 < p i) ∧
      (G.adjMatrix ℝ).mulVec p = ρ • p ∧
      (∀ x, dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ ρ * dotProduct x x) := by
  classical
  letI : Nonempty ι := hG.nonempty
  have hA : (G.adjMatrix ℝ).IsHermitian := by
    change (G.adjMatrix ℝ).conjTranspose = G.adjMatrix ℝ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, G.transpose_adjMatrix]
  obtain ⟨ρ, p, hpne, hp, he, hb⟩ := real_matrix_nonnegative_top_eigenvector
    (G.adjMatrix ℝ) hA (fun i j => by simp only [G.adjMatrix_apply]; split <;> norm_num)
  refine ⟨ρ, p, ?_, he, hb⟩
  intro i
  apply lt_of_le_of_ne (hp i)
  intro hi
  exact hpne (adjacency_nonnegative_eigenvector_zero_of_zero G hG.preconnected ρ p hp he i hi.symm)
theorem adjacency_positive_eigenvector_eigenspace_finrank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected)
    (ρ : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (he : (G.adjMatrix ℝ).mulVec p = ρ • p) :
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin ρ) = 1 := by
  classical
  letI : Nonempty ι := hG.nonempty
  let E := Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin ρ
  have hpmem : p ∈ E := Module.End.mem_eigenspace_iff.mpr he
  let pE : E := ⟨p, hpmem⟩
  apply finrank_eq_one pE
  · intro h
    have hi := hp (Classical.choice hG.nonempty)
    have hz := congrFun (congrArg Subtype.val h) (Classical.choice hG.nonempty)
    exact (ne_of_gt hi) hz
  · intro x
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
      (fun j => - (x.val j / p j)) Finset.univ_nonempty
    let c := x.val i / p i
    have hc : ∀ j, c ≤ x.val j / p j := by
      intro j
      dsimp only [c]
      simpa only [neg_le_neg_iff] using hi j (Finset.mem_univ j)
    let z := x.val - c • p
    have hz : ∀ j, 0 ≤ z j := by
      intro j
      change 0 ≤ x.val j - c * p j
      exact sub_nonneg.mpr ((le_div_iff₀ (hp j)).mp (hc j))
    have hex : (G.adjMatrix ℝ).mulVec x.val = ρ • x.val :=
      Module.End.mem_eigenspace_iff.mp x.property
    have hei : (G.adjMatrix ℝ).mulVec z = ρ • z := by
      simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, he,
        hex, smul_sub, smul_smul]
      rw [mul_comm c ρ]
    have hzi : z i = 0 := by
      change x.val i - (x.val i / p i) * p i = 0
      rw [div_mul_cancel₀ _ (ne_of_gt (hp i)), sub_self]
    have hzero := adjacency_nonnegative_eigenvector_zero_of_zero G hG.preconnected
      ρ z hz hei i hzi
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact (sub_eq_zero.mp hzero).symm
theorem adjacency_mulVec_eq_neighbor_sum
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (p : ι → ℝ) (i : ι) :
    (G.adjMatrix ℝ).mulVec p i = ∑ j ∈ Finset.univ.filter (G.Adj i), p j := by
  classical
  simp only [Matrix.mulVec, dotProduct, G.adjMatrix_apply, Finset.sum_filter,
    ite_mul, one_mul, zero_mul]
theorem adjacency_positive_eigenvector_neighbor_le
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (ρ : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (he : (G.adjMatrix ℝ).mulVec p = ρ • p)
    {i j : ι} (hij : G.Adj i j) : p j ≤ ρ * p i := by
  classical
  have h := Finset.single_le_sum (a := j) (s := Finset.univ.filter (G.Adj i))
    (fun k _ => hp k) (by simp [hij])
  rw [← adjacency_mulVec_eq_neighbor_sum G p i, he] at h
  exact h
theorem adjacency_positive_eigenvalue_bounds
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (ρ Δ : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (he : (G.adjMatrix ℝ).mulVec p = ρ • p)
    (hΔ : ∀ i, ((Finset.univ.filter (G.Adj i)).card : ℝ) ≤ Δ) :
    0 ≤ ρ ∧ ρ ≤ Δ := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ p Finset.univ_nonempty
  have hsum : ∑ j ∈ Finset.univ.filter (G.Adj i), p j = ρ * p i := by
    rw [← adjacency_mulVec_eq_neighbor_sum G p i, he]
    rfl
  have hnonneg : 0 ≤ ρ * p i := by
    rw [← hsum]
    exact Finset.sum_nonneg fun j _ => le_of_lt (hp j)
  have hle : ρ * p i ≤ Δ * p i := by
    rw [← hsum]
    calc
      (∑ j ∈ Finset.univ.filter (G.Adj i), p j) ≤
          ∑ _j ∈ Finset.univ.filter (G.Adj i), p i :=
        Finset.sum_le_sum fun j _ => hi j (Finset.mem_univ j)
      _ = ((Finset.univ.filter (G.Adj i)).card : ℝ) * p i := by simp
      _ ≤ Δ * p i := mul_le_mul_of_nonneg_right (hΔ i) (le_of_lt (hp i))
  exact ⟨(mul_nonneg_iff_of_pos_right (hp i)).mp hnonneg,
    (mul_le_mul_iff_left₀ (hp i)).mp (by simpa only [mul_comm] using hle)⟩
theorem real_matrix_power_entry_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) :
    ∀ i j, (A ^ k) i j ≤ (B ^ k) i j := by
  induction k with
  | zero => intro i j; exact le_refl _
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul (ih i l) (hAB l j) (hn l j)
      (Matrix.pow_apply_nonneg (fun u v => (hn u v).trans (hAB u v)) k i l)
theorem real_matrix_diagonal_power_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (c : ℝ) (hc : 0 ≤ c) (hdiag : ∀ i, c ≤ A i i) (k : ℕ) (i : ι) :
    c ^ k ≤ (A ^ k) i i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    apply le_trans (mul_le_mul ih (hdiag i) hc
      (Matrix.pow_apply_nonneg hn k i i))
    exact Finset.single_le_sum (fun j _ => mul_nonneg
      (Matrix.pow_apply_nonneg hn k i j) (hn j i)) (Finset.mem_univ i)
theorem walk_power_entry_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (A : Matrix ι ι ℝ)
    (hn : ∀ i j, 0 ≤ A i j) (c : ℝ) (hc : 0 ≤ c)
    (hdiag : ∀ i, c ≤ A i i) (hedge : ∀ i j, G.Adj i j → c ≤ A i j)
    {i j : ι} (w : G.Walk i j) (k : ℕ) (hk : w.length ≤ k) :
    c ^ k ≤ (A ^ k) i j := by
  induction w generalizing k with
  | nil => exact real_matrix_diagonal_power_lower A hn c hc hdiag k _
  | @cons i l j h w ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : w.length ≤ k := Nat.succ_le_succ_iff.mp hk
      rw [pow_succ', pow_succ', Matrix.mul_apply]
      apply le_trans (mul_le_mul (hedge i l h) (ih k hlen)
        (pow_nonneg hc k) (hn i l))
      exact Finset.single_le_sum (fun v _ => mul_nonneg (hn i v)
        (Matrix.pow_apply_nonneg hn k v j)) (Finset.mem_univ l)
theorem nonnegative_matrix_power_rowsum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (c : ℝ) (hc : 0 ≤ c) (hrow : ∀ i, (∑ j, A i j) ≤ c) (k : ℕ) :
    ∀ i, (∑ j, (A ^ k) i j) ≤ c ^ k := by
  induction k with
  | zero => intro i; simp [Matrix.one_apply]
  | succ k ih =>
    intro i
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      (∑ l, (A ^ k) i l * ∑ j, A l j) ≤ ∑ l, (A ^ k) i l * c := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (hrow l) (Matrix.pow_apply_nonneg hn k i l)
      _ = (∑ l, (A ^ k) i l) * c := by rw [Finset.sum_mul]
      _ ≤ c ^ k * c := mul_le_mul_of_nonneg_right (ih i) hc
theorem nonnegative_matrix_block_power_rowsum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (c : ℝ) (hc : 0 ≤ c) (r : ℕ)
    (hrow : ∀ i, (∑ j, (A ^ r) i j) ≤ c) (k : ℕ) :
    ∀ i, (∑ j, (A ^ (r * k)) i j) ≤ c ^ k := by
  simpa only [pow_mul] using nonnegative_matrix_power_rowsum_bound (A ^ r)
    (Matrix.pow_apply_nonneg hn r) c hc hrow k
theorem killed_matrix_rowsum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P K : Matrix ι ι ℝ) (hK : ∀ i j, 0 ≤ K i j)
    (hKP : ∀ i j, K i j ≤ P i j) (hrow : ∀ i, (∑ j, P i j) ≤ 1)
    (r : ℕ) (i d : ι) (c : ℝ)
    (hdead : (K ^ r) i d = 0) (hescape : c ≤ (P ^ r) i d) :
    (∑ j, (K ^ r) i j) ≤ 1 - c := by
  have hmono := real_matrix_power_entry_mono K P hK hKP r
  have hP : ∀ i j, 0 ≤ P i j := fun i j => (hK i j).trans (hKP i j)
  have htotal := nonnegative_matrix_power_rowsum_bound P hP 1 zero_le_one hrow r i
  have hsum : (∑ j, (K ^ r) i j) + c ≤ ∑ j, (P ^ r) i j := by
    have ht : (∑ j, ((K ^ r) i j + (if j = d then c else 0))) ≤ ∑ j, (P ^ r) i j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = d
      · subst j
        simpa only [if_pos rfl, if_true, hdead, zero_add] using hescape
      · simpa only [if_neg hj, add_zero] using hmono i j
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using ht
  simp only [one_pow] at htotal
  linarith
theorem nonnegative_matrix_local_block_rowsum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ K i j)
    (c : ℝ) (hc : 0 ≤ c) (r k : ℕ) (i : ι)
    (hrow : ∀ a, a < k → ∀ j, (K ^ (r * a)) i j ≠ 0 →
      (∑ l, (K ^ r) j l) ≤ c) :
    (∑ j, (K ^ (r * k)) i j) ≤ c ^ k := by
  induction k with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    have hi := ih (fun a ha => hrow a (Nat.lt_succ_of_lt ha))
    simp only [Nat.mul_succ, pow_add, Matrix.mul_apply, pow_succ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      (∑ j, (K ^ (r * k)) i j * ∑ l, (K ^ r) j l) ≤
          ∑ j, (K ^ (r * k)) i j * c := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : (K ^ (r * k)) i j = 0
        · simp only [hj, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hrow k (Nat.lt_succ_self k) j hj)
            (Matrix.pow_apply_nonneg hn (r * k) i j)
      _ = (∑ j, (K ^ (r * k)) i j) * c := by rw [Finset.sum_mul]
      _ ≤ c ^ k * c := mul_le_mul_of_nonneg_right hi hc
theorem nonnegative_matrix_diagonal_le_initial_rowsum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, (∑ j, K i j) ≤ 1) (a b : ℕ) (i : ι) :
    (K ^ (a + b)) i i ≤ ∑ j, (K ^ a) i j := by
  rw [pow_add, Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro j _
  have hdiag : (K ^ b) j i ≤ 1 := by
    have ht := nonnegative_matrix_power_rowsum_bound K hn 1 zero_le_one hrow b j
    have he := Finset.single_le_sum (fun l _ => Matrix.pow_apply_nonneg hn b j l)
      (Finset.mem_univ i)
    exact he.trans (by simpa only [one_pow] using ht)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiag
    (Matrix.pow_apply_nonneg hn a i j)
theorem real_matrix_normalization_power
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B P : Matrix ι ι ℝ) (q : ℝ) (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (hP : ∀ i j, q * p i * P i j = B i j * p j) (k : ℕ) :
    ∀ i j, q ^ k * p i * (P ^ k) i j = (B ^ k) i j * p j := by
  induction k with
  | zero =>
    intro i j
    by_cases hij : i = j
    · subst j; simp [Matrix.one_apply]
    · simp [Matrix.one_apply, hij]
  | succ k ih =>
    intro i j
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply mul_left_cancel₀ (hp l)
    calc
      p l * (q ^ k * q * p i * ((P ^ k) i l * P l j)) =
          (q ^ k * p i * (P ^ k) i l) * (q * p l * P l j) := by ring
      _ = ((B ^ k) i l * p l) * (B l j * p j) := by rw [ih, hP]
      _ = p l * (((B ^ k) i l * B l j) * p j) := by ring
theorem real_matrix_normalization_power_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B P : Matrix ι ι ℝ) (q : ℝ) (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (hP : ∀ i j, q * p i * P i j = B i j * p j) (k : ℕ) (i : ι) :
    q ^ k * (P ^ k) i i = (B ^ k) i i := by
  have h := real_matrix_normalization_power B P q p hp hP k i i
  apply mul_right_cancel₀ (hp i)
  convert h using 1 <;> ring
theorem real_matrix_normalization_rowsum
    {ι : Type*} [Fintype ι]
    (B P : Matrix ι ι ℝ) (q : ℝ) (hq : q ≠ 0)
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (he : B.mulVec p = q • p)
    (hP : ∀ i j, q * p i * P i j = B i j * p j) :
    ∀ i, ∑ j, P i j = 1 := by
  intro i
  apply mul_left_cancel₀ (mul_ne_zero hq (hp i))
  rw [Finset.mul_sum]
  simp_rw [hP]
  have h := congrFun he i
  change (∑ j, B i j * p j) = q * p i at h
  simpa only [mul_one] using h
theorem real_matrix_local_survival_diagonal_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P K : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ K i j)
    (hKP : ∀ i j, K i j ≤ P i j)
    (hrow : ∀ i, (∑ j, P i j) ≤ 1)
    (c : ℝ) (hc : 0 ≤ 1 - c) (r k b : ℕ) (i : ι)
    (hescape : ∀ a, a < k → ∀ j, (K ^ (r * a)) i j ≠ 0 →
      ∃ d, (K ^ r) j d = 0 ∧ c ≤ (P ^ r) j d) :
    (K ^ (r * k + b)) i i ≤ (1 - c) ^ k := by
  have hKrow : ∀ i, (∑ j, K i j) ≤ 1 := by
    intro i
    exact (Finset.sum_le_sum fun j _ => hKP i j).trans (hrow i)
  apply (nonnegative_matrix_diagonal_le_initial_rowsum K hn hKrow (r * k) b i).trans
  apply nonnegative_matrix_local_block_rowsum_bound K hn (1 - c) hc r k i
  intro a ha j hj
  obtain ⟨d, hd, he⟩ := hescape a ha j hj
  exact killed_matrix_rowsum_bound P K hn hKP hrow r j d c hd he
theorem adjacency_positive_eigenvector_edge_transition_lower
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (ρ Δ : ℝ) (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (he : (G.adjMatrix ℝ).mulVec p = ρ • p)
    (hρ : 0 ≤ ρ) (hΔ : ρ ≤ Δ) (hΔpos : 0 ≤ Δ)
    {i j : ι} (hij : G.Adj i j) :
    1 / (Δ + 1) ^ 2 ≤ p j / ((ρ + 1) * p i) := by
  have hi : p i ≤ ρ * p j := adjacency_positive_eigenvector_neighbor_le G ρ p
    (fun i => le_of_lt (hp i)) he hij.symm
  have hnum : (ρ + 1) * p i ≤ (Δ + 1) ^ 2 * p j := by
    calc
      (ρ + 1) * p i ≤ (Δ + 1) * (Δ * p j) :=
        mul_le_mul (by linarith : ρ + 1 ≤ Δ + 1)
          (hi.trans (mul_le_mul_of_nonneg_right hΔ (le_of_lt (hp j))))
          (le_of_lt (hp i)) (by linarith)
      _ ≤ (Δ + 1) ^ 2 * p j := by
        nlinarith [hp j]
  rw [le_div_iff₀ (mul_pos (by linarith) (hp i))]
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < Δ + 1))]
  nlinarith only [hnum]
theorem adjacency_positive_eigenvector_diagonal_transition_lower
    (ρ Δ : ℝ) (hρ : 0 ≤ ρ) (hΔ : ρ ≤ Δ) :
    1 / (Δ + 1) ^ 2 ≤ 1 / (ρ + 1) := by
  have hΔ0 : 0 ≤ Δ := hρ.trans hΔ
  apply one_div_le_one_div_of_le (by linarith : 0 < ρ + 1)
  nlinarith
noncomputable def multiplicityTransition
    {ι : Type*} (B : Matrix ι ι ℝ) (q : ℝ) (p : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => B i j * p j / (q * p i)
theorem multiplicityTransition_normalization
    {ι : Type*} (B : Matrix ι ι ℝ) (q : ℝ) (hq : q ≠ 0)
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) (i j : ι) :
    q * p i * multiplicityTransition B q p i j = B i j * p j := by
  dsimp only [multiplicityTransition]
  exact mul_div_cancel₀ _ (mul_ne_zero hq (hp i))
noncomputable def multiplicityKilled
    {ι : Type*} (P : Matrix ι ι ℝ) (s : Set ι) : Matrix ι ι ℝ := by
  classical
  exact fun i j => if j ∈ s then 0 else P i j
theorem multiplicityKilled_power_dead_column
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (s : Set ι) (r : ℕ) (hr : 0 < r)
    (i d : ι) (hd : d ∈ s) :
    (multiplicityKilled P s ^ r) i d = 0 := by
  classical
  have hcol : (multiplicityKilled P s ^ 1).col d = 0 := by
    ext j
    simp [multiplicityKilled, hd]
  exact congrFun (Matrix.pow_col_eq_zero_of_le hcol hr) i
theorem connected_graph_sparse_walk_net
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (hG : G.Connected) (r : ℕ) (hr : 0 < r) :
    ∃ s : Finset ι, s.card ≤ Fintype.card ι / r + 1 ∧
      ∀ v, ∃ d ∈ s, ∃ w : G.Walk v d, w.length ≤ r := by
  classical
  let u : ι := Classical.choice hG.nonempty
  obtain ⟨k, hk, hcard⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul
    (s := (Finset.univ : Finset ι)) (t := Finset.range r)
    (f := fun v => G.dist u v % r)
    (by simpa using Nat.lt_mul_div_succ (Fintype.card ι) hr)
  have hkr : k < r := Finset.mem_range.mp hk
  let s : Finset ι := insert u (Finset.univ.filter fun v => G.dist u v % r = k)
  refine ⟨s, ?_, ?_⟩
  · exact (Finset.card_insert_le _ _).trans (by simpa using hcard)
  · intro v
    obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist u v
    by_cases hv : G.dist u v < k
    · refine ⟨u, Finset.mem_insert_self _ _, w.reverse, ?_⟩
      rw [w.length_reverse, hw]
      omega
    · let t := G.dist u v - (G.dist u v - k) % r
      have ht : t ≤ w.length := by dsimp only [t]; omega
      have htmod : t % r = k := by
        have hmod := Nat.mod_lt (G.dist u v - k) hr
        have hdiv := Nat.mod_add_div (G.dist u v - k) r
        have he : t = k + r * ((G.dist u v - k) / r) := by dsimp only [t]; omega
        rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkr]
      have hdist : G.dist u (w.getVert t) = t := by
        have h := G.length_eq_dist_of_subwalk hw (w.isSubwalk_take t)
        rw [w.take_length, Nat.min_eq_left ht] at h
        exact h.symm
      refine ⟨w.getVert t, Finset.mem_insert_of_mem (by simp [hdist, htmod]),
        (w.drop t).reverse, ?_⟩
      rw [(w.drop t).length_reverse, w.drop_length, hw]
      have hmod := Nat.mod_lt (G.dist u v - k) hr
      dsimp only [t]
      omega
theorem connected_graph_closed_ball_connected
    {ι : Type*} (G : SimpleGraph ι) (hG : G.Connected) (o : ι) (R : ℕ) :
    (G.induce {v | G.dist o v ≤ R}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨o, by simp⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist o v
  have hsupport : ∀ u ∈ w.support, G.dist o u ≤ R := by
    intro u hu
    obtain ⟨t, he, ht⟩ := (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hu
    have hdist := G.dist_le (w.take t)
    rw [w.take_length, he] at hdist
    exact hdist.trans ((Nat.min_le_right _ _).trans (hw ▸ hv))
  exact ⟨w.induce _ hsupport⟩
theorem adjacency_add_one_nonnegative
    {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] :
    ∀ i j, 0 ≤ (G.adjMatrix ℝ + 1) i j := by
  intro i j
  exact add_nonneg (by simp [SimpleGraph.adjMatrix_apply]; split <;> norm_num)
    (by simp [Matrix.one_apply]; split <;> norm_num)
theorem adjacency_add_one_rowsum_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (Δ : ℕ)
    (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ) :
    ∀ i, (∑ j, (G.adjMatrix ℝ + 1) i j) ≤ (Δ : ℝ) + 1 := by
  intro i
  simp only [Matrix.add_apply, Finset.sum_add_distrib]
  have hcard : (Finset.univ.filter (G.Adj i)).card ≤ Δ := by
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] using hΔ i
  have hsum : (∑ j, G.adjMatrix ℝ i j) =
      ((Finset.univ.filter (G.Adj i)).card : ℝ) := by
    simp [SimpleGraph.adjMatrix_apply, Finset.sum_boole]
  rw [hsum]
  simpa [Matrix.one_apply] using (by exact_mod_cast Nat.add_le_add_right hcard 1 :
    ((Finset.univ.filter (G.Adj i)).card : ℝ) + 1 ≤ (Δ : ℝ) + 1)
theorem connected_graph_closed_ball_card_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (hG : G.Connected) (Δ : ℕ)
    (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ) (o : ι) (R : ℕ) :
    ({v | G.dist o v ≤ R} : Set ι).ncard ≤ (Δ + 1) ^ R := by
  classical
  let B := G.adjMatrix ℝ + 1
  have hn : ∀ i j, 0 ≤ B i j := adjacency_add_one_nonnegative G
  have hrow := nonnegative_matrix_power_rowsum_bound B hn ((Δ : ℝ) + 1)
    (by positivity) (adjacency_add_one_rowsum_bound G Δ hΔ) R o
  have he : ∀ v, G.dist o v ≤ R → 1 ≤ (B ^ R) o v := by
    intro v hv
    obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist o v
    simpa only [one_pow] using walk_power_entry_lower G B hn 1 (by norm_num)
      (by intro i; simp [B])
      (by intro i j hij; simp [B, SimpleGraph.adjMatrix_apply, hij, Matrix.one_apply]; split <;> norm_num) w R (hw ▸ hv)
  have hcard : ((Finset.univ.filter fun v => G.dist o v ≤ R).card : ℝ) ≤
      ((Δ : ℝ) + 1) ^ R := by
    calc
      _ = ∑ v ∈ Finset.univ.filter (fun v => G.dist o v ≤ R), (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v => G.dist o v ≤ R), (B ^ R) o v :=
        Finset.sum_le_sum fun v hv => he v (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v, (B ^ R) o v := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun v _ _ => Matrix.pow_apply_nonneg hn R o v)
      _ ≤ _ := hrow
  have hnat : (Finset.univ.filter fun v => G.dist o v ≤ R).card ≤ (Δ + 1) ^ R := by
    exact_mod_cast hcard
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf] using hnat
noncomputable def multiplicityExtend
    {ι : Type*} (s : Set ι) (x : s → ℝ) : ι → ℝ := by
  classical
  exact fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 0
theorem multiplicityExtend_sum
    {ι : Type*} [Fintype ι] (s : Set ι) [Fintype s] (f : ι → ℝ)
    (hf : ∀ i, i ∉ s → f i = 0) :
    (∑ i, f i) = ∑ i : s, f i.val := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => i ∈ s)
    (by intro i; simp) f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [hi, hf]
theorem multiplicityExtend_dotProduct
    {ι : Type*} [Fintype ι] (s : Set ι) [Fintype s] (x y : s → ℝ) :
    dotProduct (multiplicityExtend s x) (multiplicityExtend s y) = dotProduct x y := by
  classical
  rw [dotProduct, multiplicityExtend_sum s _ (by
    intro i hi; simp [multiplicityExtend, hi])]
  simp [multiplicityExtend, dotProduct]
theorem multiplicityExtend_quadratic
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (s : Set ι) [Fintype s] (x : s → ℝ) :
    dotProduct (multiplicityExtend s x) (A.mulVec (multiplicityExtend s x)) =
      dotProduct x ((A.submatrix Subtype.val Subtype.val).mulVec x) := by
  classical
  rw [dotProduct, multiplicityExtend_sum s _ (by
    intro i hi; simp [multiplicityExtend, hi])]
  apply Finset.sum_congr rfl
  intro i _
  simp only [multiplicityExtend, dif_pos i.property]
  congr 1
  rw [Matrix.mulVec, dotProduct, multiplicityExtend_sum s _ (by
    intro j hj; simp [multiplicityExtend, hj])]
  simp [multiplicityExtend, Matrix.mulVec, dotProduct, Matrix.submatrix]
theorem multiplicityExtend_cross_zero
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (s t : Set ι)
    (x : s → ℝ) (y : t → ℝ)
    (hcross : ∀ i ∈ s, ∀ j ∈ t, A i j = 0) :
    dotProduct (multiplicityExtend s x) (A.mulVec (multiplicityExtend t y)) = 0 := by
  classical
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ s
  · have hinner : A.mulVec (multiplicityExtend t y) i = 0 := by
      rw [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ t
      · simp [hcross i hi j hj]
      · simp [multiplicityExtend, hj]
    simp [hinner]
  · simp [multiplicityExtend, hi]
theorem real_matrix_separated_supercritical_principal_impossible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (μ : ℝ) (j : ι)
    (hμ : ∀ i, i ≠ j → hA.eigenvalues i ≤ μ)
    (s t : Set ι) [Fintype s] [Fintype t] (hst : Disjoint s t)
    (hcross : ∀ i ∈ s, ∀ j ∈ t, A i j = 0)
    (x : s → ℝ) (y : t → ℝ)
    (hx : μ * dotProduct x x <
      dotProduct x ((A.submatrix Subtype.val Subtype.val).mulVec x))
    (hy : μ * dotProduct y y <
      dotProduct y ((A.submatrix Subtype.val Subtype.val).mulVec y)) : False := by
  classical
  apply real_matrix_no_two_orthogonal_supercritical_vectors A hA μ j hμ
    (multiplicityExtend s x) (multiplicityExtend t y)
  · rw [dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · have ht : i ∉ t := fun ht => Set.disjoint_left.mp hst hi ht
      simp [multiplicityExtend, ht]
    · simp [multiplicityExtend, hi]
  · exact multiplicityExtend_cross_zero A s t x y hcross
  · simpa only [multiplicityExtend_dotProduct, multiplicityExtend_quadratic] using hx
  · simpa only [multiplicityExtend_dotProduct, multiplicityExtend_quadratic] using hy
theorem induced_graph_degree_bound
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) (s : Set ι) (Δ : ℕ)
    (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ) :
    ∀ i : s, ({j | (G.induce s).Adj i j} : Set s).ncard ≤ Δ := by
  intro i
  apply le_trans _ (hΔ i.val)
  exact Set.ncard_le_ncard_of_injOn Subtype.val (fun j hj => hj)
    (fun x _ y _ h => Subtype.ext h)
theorem graph_separated_supported_vectors_cross_zero
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (s t : Set ι) (x y : ι → ℝ)
    (hx : ∀ i, i ∉ s → x i = 0) (hy : ∀ j, j ∉ t → y j = 0)
    (hst : Disjoint s t) (hcross : ∀ i ∈ s, ∀ j ∈ t, ¬ G.Adj i j) :
    dotProduct x y = 0 ∧ dotProduct x ((G.adjMatrix ℝ).mulVec y) = 0 := by
  classical
  constructor
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · simp [hy i (fun ht => Set.disjoint_left.mp hst hi ht)]
    · simp [hx i hi]
  · apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · have hz : (G.adjMatrix ℝ).mulVec y i = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : j ∈ t
        · simp [SimpleGraph.adjMatrix_apply, hcross i hi j hj]
        · simp [hy j hj]
      simp [hz]
    · simp [hx i hi]
theorem graph_uniform_local_rayleigh_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected)
    (Δ : ℕ) (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ)
    (μ : ℝ) (hA : (G.adjMatrix ℝ).IsHermitian)
    (j : ι) (hμ : ∀ i, i ≠ j → hA.eigenvalues i ≤ μ) (R : ℕ) :
    ∃ b : Finset ι, b.card ≤ (Δ + 1) ^ (2 * R + 1) ∧
      ∀ v ∉ b, ∀ x : ι → ℝ,
        (∀ i, R < G.dist v i → x i = 0) →
        dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ μ * dotProduct x x := by
  classical
  by_cases hex : ∃ o, ∃ x : ι → ℝ,
      (∀ i, R < G.dist o i → x i = 0) ∧
      μ * dotProduct x x < dotProduct x ((G.adjMatrix ℝ).mulVec x)
  · obtain ⟨o, x, hx, hxq⟩ := hex
    let b := Finset.univ.filter fun v => G.dist o v ≤ 2 * R + 1
    refine ⟨b, ?_, ?_⟩
    · simpa only [b, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using
        connected_graph_closed_ball_card_bound G hG Δ hΔ o (2 * R + 1)
    · intro v hv y hy
      by_contra! hyq
      have hd : 2 * R + 1 < G.dist o v := by simpa [b] using hv
      have hst : Disjoint {i | G.dist o i ≤ R} {i | G.dist v i ≤ R} := by
        apply Set.disjoint_left.mpr
        intro i hi hj
        change G.dist o i ≤ R at hi
        change G.dist v i ≤ R at hj
        have ht := hG.dist_triangle (u := o) (v := i) (w := v)
        rw [G.dist_comm (u := i) (v := v)] at ht
        omega
      have hcross : ∀ i ∈ ({i | G.dist o i ≤ R} : Set ι),
          ∀ l ∈ ({l | G.dist v l ≤ R} : Set ι), ¬ G.Adj i l := by
        intro i hi l hl hil
        change G.dist o i ≤ R at hi
        change G.dist v l ≤ R at hl
        have h1 := hG.dist_triangle (u := o) (v := i) (w := l)
        have h2 := hG.dist_triangle (u := o) (v := l) (w := v)
        rw [G.dist_comm (u := l) (v := v)] at h2
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hil] at h1
        omega
      obtain ⟨hxy, hxyA⟩ := graph_separated_supported_vectors_cross_zero G
        {i | G.dist o i ≤ R} {i | G.dist v i ≤ R} x y
        (by intro i hi; exact hx i (by simpa using hi))
        (by intro i hi; exact hy i (by simpa using hi)) hst hcross
      exact real_matrix_no_two_orthogonal_supercritical_vectors
        (G.adjMatrix ℝ) hA μ j hμ x y hxy hxyA hxq hyq
  · refine ⟨∅, by simp, ?_⟩
    intro v _ x hx
    exact le_of_not_gt fun h => hex ⟨v, x, hx, h⟩
theorem graph_matrix_power_support_distance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (hG : G.Connected) (M : Matrix ι ι ℝ)
    (hs : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j) (k : ℕ) :
    ∀ i j, (M ^ k) i j ≠ 0 → G.dist i j ≤ k := by
  induction k with
  | zero =>
    intro i j hij
    have he : i = j := by
      by_contra hne
      exact hij (by simp [Matrix.one_apply, hne])
    subst j
    simp
  | succ k ih =>
    intro i j hij
    have hex : ∃ l, (M ^ k) i l ≠ 0 ∧ M l j ≠ 0 := by
      by_contra! h
      apply hij
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_eq_zero fun l _ => by
        by_cases hl : (M ^ k) i l = 0
        · simp [hl]
        · simp [h l hl]
    obtain ⟨l, hl, hlj⟩ := hex
    have hd := ih i l hl
    rcases hs l j hlj with he | he
    · subst j; omega
    · have ht := hG.dist_triangle (u := i) (v := l) (w := j)
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr he] at ht
      omega
theorem graph_matrix_power_closed_ball_locality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (hG : G.Connected) (M : Matrix ι ι ℝ)
    (hs : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j)
    (o : ι) (R : ℕ) [Fintype {v // G.dist o v ≤ R}]
    [DecidableEq {v // G.dist o v ≤ R}] (k : ℕ) :
    ∀ (i j : {v // G.dist o v ≤ R}), G.dist o i.val + k ≤ R →
      (M ^ k) i.val j.val =
      ((M.submatrix (fun v : {v // G.dist o v ≤ R} => v.val) Subtype.val) ^ k) i j := by
  classical
  induction k with
  | zero =>
    intro i j _
    by_cases he : i = j
    · subst j; simp
    · have hval : i.val ≠ j.val := fun h => he (Subtype.ext h)
      simp [Matrix.one_apply, he, hval]
  | succ k ih =>
    intro i j hi
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    have hz : ∀ v, v ∉ ({v | G.dist o v ≤ R} : Set ι) →
        M i.val v * (M ^ k) v j.val = 0 := by
      intro v hv
      have hzero : M i.val v = 0 := by
        by_contra hz
        have hdist : G.dist o v ≤ G.dist o i.val + 1 := by
          rcases hs i.val v hz with he | he
          · rw [← he]; omega
          · have ht := hG.dist_triangle (u := o) (v := i.val) (w := v)
            rw [SimpleGraph.dist_eq_one_iff_adj.mpr he] at ht
            exact ht
        have hvr : R < G.dist o v := by simpa using hv
        omega
      simp [hzero]
    rw [@multiplicityExtend_sum ι _ {v | G.dist o v ≤ R}
      (inferInstance : Fintype {v // G.dist o v ≤ R}) _ hz]
    change (∑ l : {v // G.dist o v ≤ R}, M i.val l.val * (M ^ k) l.val j.val) =
      ∑ l : {v // G.dist o v ≤ R}, M i.val l.val *
        ((M.submatrix (fun v : {v // G.dist o v ≤ R} => v.val) Subtype.val) ^ k) l j
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : M i.val l.val = 0
    · simp [Matrix.submatrix, hl]
    · have hdist : G.dist o l.val ≤ G.dist o i.val + 1 := by
        rcases hs i.val l.val hl with he | he
        · rw [← he]; omega
        · have ht := hG.dist_triangle (u := o) (v := i.val) (w := l.val)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr he] at ht
          exact ht
      rw [ih l j (by omega)]
theorem multiplicityKilled_principal_power
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (s : Set ι) [Fintype {i // i ∉ s}]
    [DecidableEq {i // i ∉ s}] (k : ℕ) :
    ∀ (i j : {i // i ∉ s}),
      (multiplicityKilled B s ^ k) i.val j.val =
      ((B.submatrix (fun i : {i // i ∉ s} => i.val) Subtype.val) ^ k) i j := by
  classical
  induction k with
  | zero =>
    intro i j
    by_cases he : i = j
    · subst j; simp
    · have hval : i.val ≠ j.val := fun h => he (Subtype.ext h)
      simp [Matrix.one_apply, he, hval]
  | succ k ih =>
    intro i j
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    rw [@multiplicityExtend_sum ι _ {i | i ∉ s}
      (inferInstance : Fintype {i // i ∉ s}) _ (by
      intro l hl
      have hls : l ∈ s := by simpa using hl
      simp [multiplicityKilled, hls])]
    change (∑ l : {i // i ∉ s}, multiplicityKilled B s i.val l.val *
      (multiplicityKilled B s ^ k) l.val j.val) =
      ∑ l : {i // i ∉ s}, B i.val l.val *
        ((B.submatrix (fun i : {i // i ∉ s} => i.val) Subtype.val) ^ k) l j
    apply Finset.sum_congr rfl
    intro l _
    simp only [multiplicityKilled, if_neg l.property, Matrix.submatrix_apply, ih]
theorem real_matrix_eigenspace_shift_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (μ : ℝ) :
    Module.End.eigenspace (A + 1).mulVecLin (μ + 1) =
      Module.End.eigenspace A.mulVecLin μ := by
  ext x
  simp only [Module.End.mem_eigenspace_iff]
  change (A + 1).mulVec x = (μ + 1) • x ↔ A.mulVec x = μ • x
  rw [Matrix.add_mulVec, Matrix.one_mulVec, add_smul, one_smul]
  exact add_left_inj x
theorem graph_killed_shifted_diagonal_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected)
    (ρ : ℝ) (Δ : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (he : (G.adjMatrix ℝ).mulVec p = ρ • p) (hρ : 0 ≤ ρ) (hΔ : ρ ≤ Δ)
    (s : Set ι) (r k : ℕ) (hr : 0 < r) (o : ι)
    (hnet : ∀ a, a < k → ∀ j, G.dist o j ≤ r * a →
      ∃ d ∈ s, ∃ w : G.Walk j d, w.length ≤ r) :
    (multiplicityKilled (G.adjMatrix ℝ + 1) s ^ (r * k)) o o ≤
      (ρ + 1) ^ (r * k) * (1 - (1 / ((Δ : ℝ) + 1) ^ 2) ^ r) ^ k := by
  classical
  let B := G.adjMatrix ℝ + 1
  let P := multiplicityTransition B (ρ + 1) p
  let K := multiplicityKilled P s
  let δ : ℝ := 1 / ((Δ : ℝ) + 1) ^ 2
  have hδ : 0 ≤ δ ∧ δ ≤ 1 := by
    dsimp only [δ]
    constructor
    · positivity
    · rw [div_le_one (by positivity : 0 < ((Δ : ℝ) + 1) ^ 2)]
      nlinarith [Nat.cast_nonneg (α := ℝ) Δ]
  have hnB : ∀ i j, 0 ≤ B i j := adjacency_add_one_nonnegative G
  have hnP : ∀ i j, 0 ≤ P i j := fun i j => div_nonneg
    (mul_nonneg (hnB i j) (le_of_lt (hp j)))
    (le_of_lt (mul_pos (by linarith : 0 < ρ + 1) (hp i)))
  have hnK : ∀ i j, 0 ≤ K i j := by
    intro i j; dsimp only [K, multiplicityKilled]; split <;> simp_all
  have hKP : ∀ i j, K i j ≤ P i j := by
    intro i j; dsimp only [K, multiplicityKilled]; split <;> simp_all
  have hP := multiplicityTransition_normalization B (ρ + 1) (by linarith) p
    (fun i => ne_of_gt (hp i))
  have heB : B.mulVec p = (ρ + 1) • p := by
    simp only [B, Matrix.add_mulVec, Matrix.one_mulVec, he, add_smul, one_smul]
  have hrow : ∀ i, (∑ j, P i j) ≤ 1 := by
    intro i
    exact le_of_eq (real_matrix_normalization_rowsum B P (ρ + 1) (by linarith) p
      (fun i => ne_of_gt (hp i)) heB hP i)
  have hedge : ∀ i j, G.Adj i j → δ ≤ P i j := by
    intro i j hij
    have hne : i ≠ j := hij.ne
    simpa [P, multiplicityTransition, B, Matrix.one_apply, hne,
      SimpleGraph.adjMatrix_apply, hij, δ] using
      adjacency_positive_eigenvector_edge_transition_lower G ρ Δ p hp he hρ hΔ
        (Nat.cast_nonneg Δ) hij
  have hdiag : ∀ i, δ ≤ P i i := by
    intro i
    simpa [P, multiplicityTransition, B, δ, mul_comm,
      div_mul_eq_div_mul_one_div, ne_of_gt (hp i)] using
      adjacency_positive_eigenvector_diagonal_transition_lower ρ Δ hρ hΔ
  have hstep : ∀ i j, K i j ≠ 0 → i = j ∨ G.Adj i j := by
    intro i j hij
    by_contra! h
    apply hij
    simp [K, multiplicityKilled, P, multiplicityTransition, B,
      SimpleGraph.adjMatrix_apply, Matrix.one_apply, h.1, h.2]
  have hescape : ∀ a, a < k → ∀ j, (K ^ (r * a)) o j ≠ 0 →
      ∃ d, (K ^ r) j d = 0 ∧ δ ^ r ≤ (P ^ r) j d := by
    intro a ha j hj
    have hd := graph_matrix_power_support_distance G hG K hstep (r * a) o j hj
    obtain ⟨d, hds, w, hw⟩ := hnet a ha j hd
    exact ⟨d, multiplicityKilled_power_dead_column P s r hr j d hds,
      walk_power_entry_lower G P hnP δ hδ.1 hdiag hedge w r hw⟩
  have hbound := real_matrix_local_survival_diagonal_bound P K hnK hKP hrow
    (δ ^ r) (sub_nonneg.mpr (pow_le_one₀ hδ.1 hδ.2)) r k 0 o hescape
  have hnorm : ∀ i j, (ρ + 1) * p i * K i j =
      multiplicityKilled B s i j * p j := by
    intro i j
    by_cases hj : j ∈ s
    · simp [K, multiplicityKilled, hj]
    · simpa only [K, multiplicityKilled, if_neg hj] using hP i j
  rw [← real_matrix_normalization_power_diagonal (multiplicityKilled B s) K
    (ρ + 1) p (fun i => ne_of_gt (hp i)) hnorm (r * k) o]
  exact mul_le_mul_of_nonneg_left (by simpa only [δ, Nat.add_zero] using hbound) (by positivity)
theorem graph_walk_support_distance_bound
    {ι : Type*} (G : SimpleGraph ι) (hG : G.Connected) (o : ι)
    {i j : ι} (w : G.Walk i j) :
    ∀ u ∈ w.support, G.dist o u ≤ G.dist o i + w.length := by
  intro u hu
  obtain ⟨t, he, ht⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu
  have hdist := G.dist_le (w.take t)
  rw [w.take_length, he] at hdist
  exact (hG.dist_triangle (u := o) (v := i) (w := u)).trans
    (Nat.add_le_add_left (hdist.trans (Nat.min_le_right _ _)) _)
theorem graph_walk_induce_length
    {ι : Type*} (G : SimpleGraph ι) (s : Set ι)
    {i j : ι} (w : G.Walk i j) (hw : ∀ u ∈ w.support, u ∈ s) :
    (w.induce s hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih => simp only [SimpleGraph.Walk.induce_cons,
      SimpleGraph.Walk.length_cons, ih]
theorem induced_graph_distance_ge
    {ι : Type*} (G : SimpleGraph ι) (hG : G.Connected) (s : Set ι)
    (hH : (G.induce s).Connected) (i j : s) :
    G.dist i.val j.val ≤ (G.induce s).dist i j := by
  obtain ⟨w, hw⟩ := hH.exists_walk_length_eq_dist i j
  have h := G.dist_le (w.map ({toFun := Subtype.val, map_rel' := fun h => h} : G.induce s →g G))
  change G.dist i.val j.val ≤ (w.map
    ({toFun := Subtype.val, map_rel' := fun h => h} : G.induce s →g G)).length at h
  simpa only [SimpleGraph.Walk.length_map, hw] using h
theorem graph_local_killed_diagonal_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected)
    (Δ : ℕ) (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ)
    (μ : ℝ) (hμ : 0 ≤ μ) (s : Set ι) (r k : ℕ) (hr : 0 < r)
    (hnet : ∀ j, ∃ d ∈ s, ∃ w : G.Walk j d, w.length ≤ r)
    (o : ι)
    (hgood : ∀ x : ι → ℝ,
      (∀ i, r * k + r < G.dist o i → x i = 0) →
      dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ μ * dotProduct x x) :
    (multiplicityKilled (G.adjMatrix ℝ + 1) s ^ (r * k)) o o ≤
      (μ + 1) ^ (r * k) * (1 - (1 / ((Δ : ℝ) + 1) ^ 2) ^ r) ^ k := by
  classical
  let T : Set ι := {v | G.dist o v ≤ r * k + r}
  let H := G.induce T
  let c : T := ⟨o, by simp [T]⟩
  have hH : H.Connected := connected_graph_closed_ball_connected G hG o _
  letI : Nonempty T := hH.nonempty
  obtain ⟨ρ, p, hp, he, hb⟩ := multiplicity_connected_positive_eigenpair H hH
  have hdeg : ∀ i : T, ((Finset.univ.filter (H.Adj i)).card : ℝ) ≤ (Δ : ℝ) := by
    intro i
    have hh := induced_graph_degree_bound G T Δ hΔ i
    have hnat : (Finset.univ.filter (H.Adj i)).card ≤ Δ := by
      simpa only [H, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred] using hh
    exact_mod_cast hnat
  obtain ⟨hρ, hρΔ⟩ := adjacency_positive_eigenvalue_bounds H ρ Δ p hp he hdeg
  have hρμ : ρ ≤ μ := by
    have hbound := hgood (multiplicityExtend T p) (by
      intro i hi
      simp [multiplicityExtend, T, not_le.mpr hi])
    have hmat : (G.adjMatrix ℝ).submatrix (fun v : T => v.val) Subtype.val =
        H.adjMatrix ℝ := by ext i j; rfl
    rw [multiplicityExtend_dotProduct, multiplicityExtend_quadratic, hmat, he,
      dotProduct_smul, smul_eq_mul] at hbound
    have hnorm : 0 < dotProduct p p := by
      apply lt_of_lt_of_le (sq_pos_of_pos (hp c))
      simpa only [pow_two, dotProduct] using
        Finset.single_le_sum (fun i _ => mul_self_nonneg (p i)) (Finset.mem_univ c)
    exact (mul_le_mul_iff_left₀ hnorm).mp (by simpa only [mul_comm] using hbound)
  have hnetH : ∀ a, a < k → ∀ j : T, H.dist c j ≤ r * a →
      ∃ d ∈ (Subtype.val ⁻¹' s : Set T), ∃ w : H.Walk j d, w.length ≤ r := by
    intro a ha j hj
    have hd : G.dist o j.val ≤ r * a :=
      (induced_graph_distance_ge G hG T hH c j).trans hj
    obtain ⟨d, hds, w, hw⟩ := hnet j.val
    have hsupport : ∀ u ∈ w.support, u ∈ T := by
      intro u hu
      have hdist := graph_walk_support_distance_bound G hG o w u hu
      change G.dist o u ≤ r * k + r
      exact hdist.trans (Nat.add_le_add
        (hd.trans (Nat.mul_le_mul_left r (Nat.le_of_lt ha))) hw)
    refine ⟨⟨d, hsupport d w.end_mem_support⟩, hds, w.induce T hsupport, ?_⟩
    simpa only [graph_walk_induce_length] using hw
  have hlocal := graph_killed_shifted_diagonal_bound H hH ρ Δ p hp he hρ hρΔ
    (Subtype.val ⁻¹' s) r k hr c hnetH
  let M := multiplicityKilled (G.adjMatrix ℝ + 1) s
  have hsM : ∀ i j, M i j ≠ 0 → i = j ∨ G.Adj i j := by
    intro i j hij
    by_contra! h
    apply hij
    simp [M, multiplicityKilled, SimpleGraph.adjMatrix_apply, Matrix.one_apply, h.1, h.2]
  have hpow := @graph_matrix_power_closed_ball_locality ι _ _ G hG M hsM o
    (r * k + r) (inferInstance : Fintype T) (inferInstance : DecidableEq T) (r * k) c c (by simp [c])
  have hrestrict : M.submatrix (fun i : T => i.val) Subtype.val =
      multiplicityKilled (H.adjMatrix ℝ + 1) (Subtype.val ⁻¹' s) := by
    ext i j
    simp only [M, multiplicityKilled, Matrix.submatrix_apply, Set.mem_preimage,
      Matrix.add_apply]
    congr 1
    by_cases hij : i = j
    · subst j; simp
    · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [Matrix.one_apply, hij, hval, H, SimpleGraph.adjMatrix_apply]
  have heq := congrArg (fun Z : Matrix T T ℝ => (Z ^ (r * k)) c c) hrestrict
  have hfull := hpow.trans heq
  rw [hfull]
  apply hlocal.trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by linarith : 0 ≤ ρ + 1) (by linarith : ρ + 1 ≤ μ + 1) _)
    (pow_nonneg (sub_nonneg.mpr (pow_le_one₀ (by positivity)
      (by rw [div_le_one (by positivity : 0 < ((Δ : ℝ) + 1) ^ 2)];
          nlinarith [Nat.cast_nonneg (α := ℝ) Δ]))) k)
theorem graph_second_eigenvalue_multiplicity_finite_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected)
    (Δ : ℕ) (hΔ : ∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ)
    (μ : ℝ) (hμ : 0 ≤ μ) (hA : (G.adjMatrix ℝ).IsHermitian)
    (j : ι) (heig : ∀ i, i ≠ j → hA.eigenvalues i ≤ μ)
    (r k : ℕ) (hr : 0 < r) :
    (Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin μ) : ℝ) ≤
      (Fintype.card ι : ℝ) / (r : ℝ) + 1 +
      (Fintype.card ι : ℝ) * (1 - (1 / ((Δ : ℝ) + 1) ^ 2) ^ r) ^ (2 * k) +
      ((Δ : ℝ) + 1) ^ (2 * (r * (2 * k) + r) + 1 + r * (2 * k)) := by
  classical
  let L := r * (2 * k)
  let R := L + r
  let D : ℝ := (Δ : ℝ) + 1
  let a : ℝ := (1 - (1 / D ^ 2) ^ r) ^ (2 * k)
  let q : ℝ := (μ + 1) ^ L
  let C : ℝ := D ^ (2 * R + 1 + L)
  let B := G.adjMatrix ℝ + 1
  have hnB : ∀ i j, 0 ≤ B i j := adjacency_add_one_nonnegative G
  have hq : 1 ≤ q := one_le_pow₀ (by linarith : 1 ≤ μ + 1)
  have ha : 0 ≤ a := by dsimp only [a]; rw [mul_comm 2 k, pow_mul]; exact sq_nonneg _
  have hC : 0 ≤ C := by dsimp only [C, D]; positivity
  obtain ⟨s, hscard, hnet⟩ := connected_graph_sparse_walk_net G hG r hr
  obtain ⟨b, hbcard, hgood⟩ := graph_uniform_local_rayleigh_bound G hG Δ hΔ μ hA j heig R
  let K := multiplicityKilled B (s : Set ι)
  have hnK : ∀ i j, 0 ≤ K i j := by
    intro i j; dsimp only [K, multiplicityKilled]; split <;> simp_all
  have hKB : ∀ i j, K i j ≤ B i j := by
    intro i j; dsimp only [K, multiplicityKilled]; split <;> simp_all
  have hdiag : ∀ i, (K ^ L) i i ≤ q * a + (if i ∈ b then D ^ L else 0) := by
    intro i
    by_cases hi : i ∈ b
    · have hrow := nonnegative_matrix_power_rowsum_bound B hnB D
        (by dsimp only [D]; positivity) (adjacency_add_one_rowsum_bound G Δ hΔ) L i
      have hbound : (K ^ L) i i ≤ D ^ L :=
        (real_matrix_power_entry_mono K B hnK hKB L i i).trans
          ((Finset.single_le_sum (fun l _ => Matrix.pow_apply_nonneg hnB L i l)
            (Finset.mem_univ i)).trans hrow)
      simp only [if_pos hi]
      exact hbound.trans (le_add_of_nonneg_left (mul_nonneg (by linarith) ha))
    · have hlocal := graph_local_killed_diagonal_bound G hG Δ hΔ μ hμ
        (s : Set ι) r (2 * k) hr
        (by intro v; obtain ⟨d, hd, w, hw⟩ := hnet v; exact ⟨d, hd, w, hw⟩) i
        (hgood i hi)
      simpa only [K, B, L, q, a, D, if_neg hi, add_zero] using hlocal
  have hsum : (∑ i, (K ^ L) i i) ≤ (Fintype.card ι : ℝ) * q * a + C := by
    apply (Finset.sum_le_sum (fun i _ => hdiag i)).trans
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hb : (b.card : ℝ) ≤ D ^ (2 * R + 1) := by
      dsimp only [D]; exact_mod_cast hbcard
    have hsumB : (∑ i, if i ∈ b then D ^ L else 0) = (b.card : ℝ) * D ^ L := by
      rw [← Finset.sum_filter]
      simp
    rw [hsumB]
    have hmul := mul_le_mul_of_nonneg_right hb (by dsimp only [D]; positivity : 0 ≤ D ^ L)
    dsimp only [C]
    rw [pow_add]
    nlinarith only [hmul]
  let U := {i : ι // i ∉ s}
  let B' : Matrix U U ℝ := B.submatrix Subtype.val Subtype.val
  have hB' : B'.IsHermitian := (hA.add Matrix.isHermitian_one).submatrix Subtype.val
  have htrace : (B' ^ L).trace ≤ ∑ i, (K ^ L) i i := by
    have hp : ∀ i : U, (B' ^ L) i i = (K ^ L) i.val i.val := by
      intro i
      exact (multiplicityKilled_principal_power B (s : Set ι) L i i).symm
    simp only [Matrix.trace, Matrix.diag, hp]
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => i ∉ s)
      (by intro i; simp) (fun i => (K ^ L) i i)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => Matrix.pow_apply_nonneg hnK L i i)
  let m := Module.finrank ℝ (Module.End.eigenspace B'.mulVecLin (μ + 1))
  have hm : (m : ℝ) * q ≤ (Fintype.card ι : ℝ) * q * a + C := by
    have hh := real_matrix_eigenspace_multiplicity_trace_bound B' hB' (μ + 1) (r * k)
    have hL : 2 * (r * k) = L := by dsimp only [L]; ring
    rw [hL] at hh
    exact hh.trans (htrace.trans hsum)
  have hm' : (m : ℝ) ≤ (Fintype.card ι : ℝ) * a + C := by
    have hmul : C ≤ C * q := by nlinarith only [hq, hC]
    have hh : (m : ℝ) * q ≤ ((Fintype.card ι : ℝ) * a + C) * q := by
      nlinarith only [hm, hmul]
    exact (mul_le_mul_iff_left₀ (lt_of_lt_of_le zero_lt_one hq)).mp
      (by simpa only [mul_comm] using hh)
  have hdel := real_matrix_eigenspace_deletion_bound B (μ + 1) s
  rw [real_matrix_eigenspace_shift_one] at hdel
  have hdel' : (Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin μ) : ℝ) ≤
      (s.card : ℝ) + (m : ℝ) := by exact_mod_cast hdel
  have hscard' : (s.card : ℝ) ≤ (Fintype.card ι : ℝ) / (r : ℝ) + 1 := by
    have hnat : (s.card : ℝ) ≤ ((Fintype.card ι / r : ℕ) : ℝ) + 1 := by
      exact_mod_cast hscard
    have hdiv := Nat.cast_div_le (α := ℝ) (m := Fintype.card ι) (n := r)
    linarith
  change _ ≤ (Fintype.card ι : ℝ) / (r : ℝ) + 1 + (Fintype.card ι : ℝ) * a + C
  linarith
theorem uniform_second_eigenvalue_multiplicity :
    ∀ (Δ : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ),
        N ≤ n → 0 < lambda → G.Connected →
        (∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) →
        let A : Matrix (Fin n) (Fin n) ℝ :=
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
        ∀ hA : A.IsHermitian,
          (∃ j : Fin n, ∀ i : Fin n, i ≠ j → hA.eigenvalues i ≤ lambda) →
          (Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) : ℝ) ≤
            ε * (n : ℝ) := by
  classical
  intro Δ ε hε
  obtain ⟨r, hrlarge⟩ := exists_nat_gt (4 / ε)
  have hrreal : 0 < (r : ℝ) := (div_pos (by norm_num) hε).trans hrlarge
  have hr : 0 < r := by exact_mod_cast hrreal
  have hrinv : 1 / (r : ℝ) ≤ ε / 4 := by
    apply (div_le_iff₀ hrreal).mpr
    have hh := (div_lt_iff₀ hε).mp hrlarge
    nlinarith
  let δ : ℝ := 1 / ((Δ : ℝ) + 1) ^ 2
  have hδ : 0 < δ ∧ δ ≤ 1 := by
    dsimp only [δ]
    constructor
    · positivity
    · rw [div_le_one (by positivity : 0 < ((Δ : ℝ) + 1) ^ 2)]
      nlinarith [Nat.cast_nonneg (α := ℝ) Δ]
  let b : ℝ := 1 - δ ^ r
  have hb : 0 ≤ b ∧ b < 1 := by
    exact ⟨sub_nonneg.mpr (pow_le_one₀ hδ.1.le hδ.2), by
      dsimp only [b]; exact sub_lt_self _ (pow_pos hδ.1 r)⟩
  have hb2 : b ^ 2 < 1 := by nlinarith [sq_nonneg b]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 4 by positivity) hb2
  have hk' : b ^ (2 * k) ≤ ε / 4 := by simpa only [pow_mul] using hk.le
  let C : ℝ := ((Δ : ℝ) + 1) ^ (2 * (r * (2 * k) + r) + 1 + r * (2 * k))
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (1 + C) / ε)
  refine ⟨N, ?_⟩
  intro n G lambda hn hlam hG hΔ
  dsimp only
  intro hA heig
  obtain ⟨j, hj⟩ := heig
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hconstant : 1 + C ≤ ε / 4 * (n : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (hN.trans_le hnreal)
    nlinarith
  have hmain := graph_second_eigenvalue_multiplicity_finite_bound G hG Δ hΔ
    lambda hlam.le hA j hj r k hr
  have hfirst : (n : ℝ) / (r : ℝ) ≤ ε / 4 * (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hrinv (Nat.cast_nonneg (α := ℝ) n)
    simpa only [mul_one_div, mul_comm] using hh
  have hsecond : (n : ℝ) * b ^ (2 * k) ≤ ε / 4 * (n : ℝ) := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hk'
      (Nat.cast_nonneg (α := ℝ) n)
  have hbound :
      (Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) : ℝ) ≤
      (n : ℝ) / (r : ℝ) + 1 + (n : ℝ) * b ^ (2 * k) + C := by
    simpa only [Fintype.card_fin, b, δ, C] using hmain
  have hnonneg : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg n)
  linarith
def perron_revised_type_probe : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected → let A : Matrix (Fin n) (Fin n) ℝ := (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ); ∃ (rho : ℝ) (p : Fin n → ℝ), 0 ≤ rho ∧ spectralRadius ℝ A = ENNReal.ofReal rho ∧ (∀ i, 0 < p i) ∧ A.mulVec p = rho • p ∧ Module.finrank ℝ (Module.End.eigenspace A.mulVecLin rho) = 1 ∧ (∀ x : Fin n → ℝ, dotProduct x (A.mulVec x) ≤ rho * dotProduct x x)
theorem perron_abs_quadratic_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) :
    |dotProduct x ((G.adjMatrix ℝ).mulVec x)| ≤
      dotProduct (fun i => |x i|) ((G.adjMatrix ℝ).mulVec (fun i => |x i|)) := by
  classical
  calc
    |dotProduct x ((G.adjMatrix ℝ).mulVec x)| =
        |∑ i, ∑ j, x i * (G.adjMatrix ℝ i j * x j)| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |x i * (G.adjMatrix ℝ i j * x j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = dotProduct (fun i => |x i|)
        ((G.adjMatrix ℝ).mulVec (fun i => |x i|)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : G.Adj i j <;> simp [G.adjMatrix_apply, h, abs_mul]
theorem perron_nonnegative_eigenvector_positive {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) (rho : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp0 : p ≠ 0)
    (heig : (G.adjMatrix ℝ).mulVec p = rho • p) : ∀ i, 0 < p i := by
  classical
  have hstep : ∀ {i j}, G.Adj i j → p i = 0 → p j = 0 := by
    intro i j hij hi
    have hrow : (∑ k, G.adjMatrix ℝ i k * p k) = 0 := by
      have h := congrFun heig i
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hi, mul_zero] using h
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ) =>
        mul_nonneg (by simp only [G.adjMatrix_apply]; split_ifs <;> positivity) (hp k))).mp hrow
    have h := hterms j (Finset.mem_univ j)
    simpa only [G.adjMatrix_apply, if_pos hij, one_mul] using h
  have hprop : ∀ {i j}, G.Reachable i j → p i = 0 → p j = 0 := by
    intro i j hr
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact id
    | cons hij w ih => exact fun hi => ih (hstep hij hi)
  intro i
  by_contra h
  have hi : p i = 0 := le_antisymm (le_of_not_gt h) (hp i)
  apply hp0
  funext j
  exact hprop (hG i j) hi
theorem perron_nonnegative_top_eigenvector {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [Nonempty (Fin n)] :
    ∃ (rho : ℝ) (p : Fin n → ℝ), 0 ≤ rho ∧ (∀ i, 0 ≤ p i) ∧ p ≠ 0 ∧
      (G.adjMatrix ℝ).mulVec p = rho • p ∧
      (∀ x : Fin n → ℝ,
        dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ rho * dotProduct x x) := by
  classical
  let A := G.adjMatrix ℝ
  have hA : A.IsHermitian := by
    ext i j
    simp [A, Matrix.conjTranspose_apply, G.adj_comm]
  let T := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).toSelfAdjoint
  have hT : ∀ x : EuclideanSpace ℝ (Fin n),
      T.val.reApplyInnerSelf x = dotProduct x.ofLp (A.mulVec x.ofLp) := by
    intro x
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have heq : T.val x = Matrix.toEuclideanLin A x := by
      exact congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => f x)
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).coe_toSelfAdjoint
    rw [heq, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      star_trivial, RCLike.re_to_real]
  let i : Fin n := Classical.choice inferInstance
  let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i
  have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  obtain ⟨q, hq, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
    ⟨u, by simpa using hu⟩ T.val.reApplyInnerSelf_continuous.continuousOn
  have hqn : ‖q‖ = 1 := by simpa using hq
  let p : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => |q i|)
  have hpn : ‖p‖ = 1 := by
    rw [EuclideanSpace.norm_eq] at hqn ⊢
    simpa only [p, WithLp.ofLp_toLp, Real.norm_eq_abs, abs_abs] using hqn
  have hpq : T.val.reApplyInnerSelf q ≤ T.val.reApplyInnerSelf p := by
    rw [hT, hT]
    exact (le_abs_self _).trans (perron_abs_quadratic_bound G q.ofLp)
  have hpmax : IsMaxOn T.val.reApplyInnerSelf (Metric.sphere 0 1) p := by
    intro x hx
    exact (hmax hx).trans hpq
  let rho := T.val.reApplyInnerSelf p
  have hp0 : p ≠ 0 := by
    intro h
    have := hpn
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have heig : A.mulVec p.ofLp = rho • p.ofLp := by
    have h := T.prop.eq_smul_self_of_isLocalExtrOn
      (Or.inr (show IsMaxOn T.val.reApplyInnerSelf (Metric.sphere 0 ‖p‖) p by
        simpa only [hpn] using hpmax).localize)
    have heq : T.val p = Matrix.toEuclideanLin A p :=
      congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => f p)
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).coe_toSelfAdjoint
    rw [heq] at h
    have h' := congrArg (WithLp.ofLp) h
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      WithLp.ofLp_smul, ContinuousLinearMap.rayleighQuotient, hpn, one_pow, div_one,
      RCLike.ofReal_real_eq_id, id_eq, rho] using h'
  have hrho : 0 ≤ rho := by
    dsimp only [rho]
    rw [hT]
    change 0 ≤ ∑ i, |q i| * ∑ j, A i j * |q j|
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (abs_nonneg _)
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg _ (abs_nonneg _)
    simp only [A, G.adjMatrix_apply]
    split_ifs <;> positivity
  refine ⟨rho, p.ofLp, hrho, fun i => abs_nonneg _, ?_, heig, ?_⟩
  · exact fun h => hp0 ((WithLp.ofLp_eq_zero _).mp h)
  · intro x
    let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
    by_cases hz : z = 0
    · have hx : x = 0 := by exact congrArg WithLp.ofLp hz
      simp [hx, dotProduct]
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      have hyn : ‖‖z‖⁻¹ • z‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ hn]
      have hy := hpmax (show ‖z‖⁻¹ • z ∈ Metric.sphere 0 1 by simpa using hyn)
      change T.val.reApplyInnerSelf (‖z‖⁻¹ • z) ≤ T.val.reApplyInnerSelf p at hy
      rw [ContinuousLinearMap.reApplyInnerSelf_smul] at hy
      simp only [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z)] at hy
      have hmul := mul_le_mul_of_nonneg_left hy (sq_nonneg ‖z‖)
      have hcancel : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * T.val.reApplyInnerSelf z) = T.val.reApplyInnerSelf z := by
        field_simp
      rw [hcancel, hT] at hmul
      have hnorm : ‖z‖ ^ 2 = dotProduct x x := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [z, WithLp.ofLp_toLp, dotProduct, pow_two]
      simpa only [z, WithLp.ofLp_toLp, hnorm, rho, mul_comm] using hmul
theorem perron_eigenvector_proportional {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) (rho : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (heig : (G.adjMatrix ℝ).mulVec p = rho • p)
    (x : Fin n → ℝ) (hx : (G.adjMatrix ℝ).mulVec x = rho • x) :
    ∃ c : ℝ, c • p = x := by
  classical
  letI : Nonempty (Fin n) := hG.nonempty
  obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image (fun i => x i / p i) Finset.univ_nonempty
  let c := x j / p j
  let z := x - c • p
  have hznonneg : ∀ i, 0 ≤ z i := by
    intro i
    have hmin : c ≤ x i / p i := hj i (Finset.mem_univ i)
    have h := (le_div_iff₀ (hp i)).mp hmin
    change 0 ≤ x i - c * p i
    linarith
  have hzj : z j = 0 := by
    change x j - (x j / p j) * p j = 0
    rw [div_mul_cancel₀ _ (ne_of_gt (hp j)), sub_self]
  have hzeig : (G.adjMatrix ℝ).mulVec z = rho • z := by
    dsimp only [z]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hx, heig, smul_sub, smul_comm]
  have hz : z = 0 := by
    by_contra h
    have hpos := perron_nonnegative_eigenvector_positive G hG rho z hznonneg h hzeig j
    rw [hzj] at hpos
    exact (lt_irrefl 0) hpos
  exact ⟨c, (sub_eq_zero.mp hz).symm⟩
theorem perron_eigenspace_finrank_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) (rho : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (heig : (G.adjMatrix ℝ).mulVec p = rho • p) :
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin rho) = 1 := by
  classical
  letI : Nonempty (Fin n) := hG.nonempty
  have hp0 : p ≠ 0 := by
    intro h
    have hh := hp (Classical.choice inferInstance)
    rw [h, Pi.zero_apply] at hh
    exact (lt_irrefl 0) hh
  have hspace : Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin rho =
      Submodule.span ℝ {p} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hc⟩ := perron_eigenvector_proportional G hG rho p hp heig x
        (Module.End.mem_eigenspace_iff.mp hx)
      exact Submodule.mem_span_singleton.mpr ⟨c, hc⟩
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact Module.End.mem_eigenspace_iff.mpr heig
  rw [hspace]
  exact finrank_span_singleton hp0
theorem perron_spectralRadius_eq {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (rho : ℝ) (hrho : 0 ≤ rho) (p : Fin n → ℝ)
    (hp0 : p ≠ 0) (heig : (G.adjMatrix ℝ).mulVec p = rho • p)
    (hbound : ∀ x : Fin n → ℝ,
      dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ rho * dotProduct x x) :
    spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal rho := by
  classical
  let A := G.adjMatrix ℝ
  have hA : A.IsHermitian := by
    ext i j
    simp [A, Matrix.conjTranspose_apply, G.adj_comm]
  have heigs : ∀ i, |hA.eigenvalues i| ≤ rho := by
    intro i
    let q := hA.eigenvectorBasis i
    have hnorm : dotProduct (fun j => |q j|) (fun j => |q j|) = 1 := by
      calc
        dotProduct (fun j => |q j|) (fun j => |q j|) = ∑ j, (q j) ^ 2 := by
          simp only [dotProduct, ← pow_two, sq_abs]
        _ = ‖q‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq q).symm
        _ = 1 := by rw [hA.eigenvectorBasis.norm_eq_one]; norm_num
    have hb := (perron_abs_quadratic_bound G q.ofLp).trans (hbound (fun j => |q j|))
    rw [hnorm, mul_one] at hb
    simpa only [Matrix.IsHermitian.eigenvalues_eq, star_trivial, RCLike.re_to_real, q] using hb
  have hpv : Module.End.HasEigenvector (Matrix.toEuclideanLin A) rho (WithLp.toLp 2 p) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change WithLp.toLp 2 (A.mulVec p) = rho • WithLp.toLp 2 p
      rw [heig, WithLp.toLp_smul]
    · intro h
      exact hp0 (congrArg WithLp.ofLp h)
  have hmem : rho ∈ spectrum ℝ A := by
    simpa only [Matrix.toEuclideanLin, Matrix.spectrum_toLpLin] using
      (Module.End.hasEigenvalue_of_hasEigenvector hpv).mem_spectrum
  apply le_antisymm
  · rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun t ht => ?_
    change t ∈ spectrum ℝ A at ht
    rw [hA.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    have hnorm : ‖hA.eigenvalues i‖ ≤ rho := by
      simpa only [Real.norm_eq_abs] using heigs i
    calc
      (↑‖hA.eigenvalues i‖₊ : ENNReal) = ENNReal.ofReal ‖hA.eigenvalues i‖ :=
        ENNReal.coe_nnreal_eq ‖hA.eigenvalues i‖₊
      _ ≤ ENNReal.ofReal rho := ENNReal.ofReal_le_ofReal hnorm
  · calc
      ENNReal.ofReal rho = (↑‖rho‖₊ : ENNReal) := by
        calc
          ENNReal.ofReal rho = ENNReal.ofReal ‖rho‖ := by rw [Real.norm_of_nonneg hrho]
          _ = (↑‖rho‖₊ : ENNReal) := (ENNReal.coe_nnreal_eq ‖rho‖₊).symm
      _ ≤ spectralRadius ℝ A := by
        rw [spectralRadius_eq_of_unital]
        exact le_iSup_of_le rho (le_iSup_of_le hmem le_rfl)
theorem connected_perron_frobenius :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
      let A : Matrix (Fin n) (Fin n) ℝ :=
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
      ∃ (rho : ℝ) (p : Fin n → ℝ),
        0 ≤ rho ∧ spectralRadius ℝ A = ENNReal.ofReal rho ∧
        (∀ i, 0 < p i) ∧ A.mulVec p = rho • p ∧
        Module.finrank ℝ (Module.End.eigenspace A.mulVecLin rho) = 1 ∧
        (∀ x : Fin n → ℝ, dotProduct x (A.mulVec x) ≤ rho * dotProduct x x) := by
  classical
  intro n G hG
  letI : Nonempty (Fin n) := hG.nonempty
  obtain ⟨rho, p, hrho, hp, hp0, heig, hbound⟩ := perron_nonnegative_top_eigenvector G
  have hpos := perron_nonnegative_eigenvector_positive G hG rho p hp hp0 heig
  exact ⟨rho, p, hrho, perron_spectralRadius_eq G rho hrho p hp0 heig hbound,
    hpos, heig, perron_eigenspace_finrank_one G hG rho p hpos heig, hbound⟩
def component_rank_one_runtime_type_probe : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ), 0 < lambda →
    let A : Matrix (Fin n) (Fin n) ℝ :=
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
    let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => 1)
    let P := lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - A + (1 / 2 : ℝ) • J
    let r : G.ConnectedComponent → ENNReal := fun C =>
      (letI : Fintype C.supp := Fintype.ofFinite C.supp;
       letI : DecidableEq C.supp := Classical.decEq C.supp;
       letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj;
       spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ))
    P.PosSemidef →
      ((¬ ∃ C, ENNReal.ofReal lambda < r C) →
        let t := ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda}).ncard
        P.rank = if t = 0 then n else n + 1 - t) ∧
      ((∃ C, ENNReal.ofReal lambda < r C) →
        ∃ C, ENNReal.ofReal lambda < r C ∧
          (∀ D, D ≠ C → r D < ENNReal.ofReal lambda) ∧
          let mC : ℕ :=
            (letI : Fintype C.supp := Fintype.ofFinite C.supp;
             letI : DecidableEq C.supp := Classical.decEq C.supp;
             letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj;
             Module.finrank ℝ (Module.End.eigenspace
               (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda))
          Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) = mC ∧
          n ≤ P.rank + 1 + mC)
theorem component_abs_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (x : ι → ℝ) :
    |dotProduct x ((G.adjMatrix ℝ).mulVec x)| ≤
      dotProduct (fun i => |x i|) ((G.adjMatrix ℝ).mulVec (fun i => |x i|)) := by
  classical
  calc
    |dotProduct x ((G.adjMatrix ℝ).mulVec x)| =
        |∑ i, ∑ j, x i * (G.adjMatrix ℝ i j * x j)| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |x i * (G.adjMatrix ℝ i j * x j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = dotProduct (fun i => |x i|)
        ((G.adjMatrix ℝ).mulVec (fun i => |x i|)) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : G.Adj i j <;> simp [G.adjMatrix_apply, h, abs_mul]
theorem component_spectralRadius_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (rho : ℝ) (hrho : 0 ≤ rho) (p : ι → ℝ)
    (hp0 : p ≠ 0) (heig : (G.adjMatrix ℝ).mulVec p = rho • p)
    (hbound : ∀ x : ι → ℝ,
      dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ rho * dotProduct x x) :
    spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal rho := by
  classical
  let A := G.adjMatrix ℝ
  have hA : A.IsHermitian := by
    ext i j
    simp [A, Matrix.conjTranspose_apply, G.adj_comm]
  have heigs : ∀ i, |hA.eigenvalues i| ≤ rho := by
    intro i
    let q := hA.eigenvectorBasis i
    have hnorm : dotProduct (fun j => |q j|) (fun j => |q j|) = 1 := by
      calc
        dotProduct (fun j => |q j|) (fun j => |q j|) = ∑ j, (q j) ^ 2 := by
          simp only [dotProduct, ← pow_two, sq_abs]
        _ = ‖q‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq q).symm
        _ = 1 := by rw [hA.eigenvectorBasis.norm_eq_one]; norm_num
    have hb := (component_abs_quadratic_bound G q.ofLp).trans (hbound (fun j => |q j|))
    rw [hnorm, mul_one] at hb
    simpa only [Matrix.IsHermitian.eigenvalues_eq, star_trivial, RCLike.re_to_real, q] using hb
  have hpv : Module.End.HasEigenvector (Matrix.toEuclideanLin A) rho (WithLp.toLp 2 p) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      change WithLp.toLp 2 (A.mulVec p) = rho • WithLp.toLp 2 p
      rw [heig, WithLp.toLp_smul]
    · intro h
      exact hp0 (congrArg WithLp.ofLp h)
  have hmem : rho ∈ spectrum ℝ A := by
    simpa only [Matrix.toEuclideanLin, Matrix.spectrum_toLpLin] using
      (Module.End.hasEigenvalue_of_hasEigenvector hpv).mem_spectrum
  apply le_antisymm
  · rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun t ht => ?_
    change t ∈ spectrum ℝ A at ht
    rw [hA.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i, rfl⟩ := ht
    have hnorm : ‖hA.eigenvalues i‖ ≤ rho := by
      simpa only [Real.norm_eq_abs] using heigs i
    calc
      (↑‖hA.eigenvalues i‖₊ : ENNReal) = ENNReal.ofReal ‖hA.eigenvalues i‖ :=
        ENNReal.coe_nnreal_eq ‖hA.eigenvalues i‖₊
      _ ≤ ENNReal.ofReal rho := ENNReal.ofReal_le_ofReal hnorm
  · calc
      ENNReal.ofReal rho = (↑‖rho‖₊ : ENNReal) := by
        calc
          ENNReal.ofReal rho = ENNReal.ofReal ‖rho‖ := by rw [Real.norm_of_nonneg hrho]
          _ = (↑‖rho‖₊ : ENNReal) := (ENNReal.coe_nnreal_eq ‖rho‖₊).symm
      _ ≤ spectralRadius ℝ A := by
        rw [spectralRadius_eq_of_unital]
        exact le_iSup_of_le rho (le_iSup_of_le hmem le_rfl)
theorem component_connected_perron
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ (rho : ℝ) (p : ι → ℝ),
      0 ≤ rho ∧ spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal rho ∧
      (∀ i, 0 < p i) ∧ (G.adjMatrix ℝ).mulVec p = rho • p ∧
      Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin rho) = 1 ∧
      (∀ x, dotProduct x ((G.adjMatrix ℝ).mulVec x) ≤ rho * dotProduct x x) := by
  classical
  letI : Nonempty ι := hG.nonempty
  obtain ⟨rho, p, hp, he, hb⟩ := multiplicity_connected_positive_eigenpair G hG
  let i : ι := Classical.choice hG.nonempty
  have hp0 : p ≠ 0 := by
    intro h
    have hh := hp i
    rw [h, Pi.zero_apply] at hh
    exact (lt_irrefl 0) hh
  have hrho : 0 ≤ rho := by
    have hh := congrFun he i
    change (∑ j, G.adjMatrix ℝ i j * p j) = rho * p i at hh
    have hn : 0 ≤ ∑ j, G.adjMatrix ℝ i j * p j := by
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg _ (hp j).le
      simp only [G.adjMatrix_apply]
      split_ifs <;> norm_num
    rw [hh] at hn
    exact (mul_nonneg_iff_of_pos_right (hp i)).mp hn
  exact ⟨rho, p, hrho, component_spectralRadius_eq G rho hrho p hp0 he hb,
    hp, he, adjacency_positive_eigenvector_eigenspace_finrank G hG rho p hp he, hb⟩
theorem component_adj_mulVec_restrict
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (x : ι → ℝ) (i : C.supp) :
    (C.toSimpleGraph.adjMatrix ℝ).mulVec (fun j => x j.val) i =
      (G.adjMatrix ℝ).mulVec x i.val := by
  classical
  have hs := multiplicityExtend_sum C.supp
    (fun j => G.adjMatrix ℝ i.val j * x j) (by
      intro j hj
      have hnot : ¬ G.Adj i.val j := fun h =>
        hj ((C.mem_supp_congr_adj h).mp i.property)
      simp [SimpleGraph.adjMatrix_apply, hnot])
  calc
    _ = ∑ j : C.supp, G.adjMatrix ℝ i.val j.val * x j.val := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simp only [SimpleGraph.adjMatrix_apply,
        show C.toSimpleGraph.Adj i j ↔ G.Adj i.val j.val from Iff.rfl]
    _ = _ := hs.symm
theorem component_adj_mulVec_extend
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (x : C.supp → ℝ) :
    (G.adjMatrix ℝ).mulVec (multiplicityExtend C.supp x) =
      multiplicityExtend C.supp ((C.toSimpleGraph.adjMatrix ℝ).mulVec x) := by
  classical
  funext i
  by_cases hi : i ∈ C.supp
  · have h := component_adj_mulVec_restrict G C (multiplicityExtend C.supp x) ⟨i, hi⟩
    have hx : (fun j : C.supp => multiplicityExtend C.supp x j.val) = x := by
      funext j
      exact dif_pos j.property
    have hh := congrArg (fun z => (C.toSimpleGraph.adjMatrix ℝ).mulVec z ⟨i, hi⟩) hx
    exact h.symm.trans (hh.trans (by simp only [multiplicityExtend, dif_pos hi]))
  · change (∑ j, G.adjMatrix ℝ i j * multiplicityExtend C.supp x j) = _
    rw [multiplicityExtend, dif_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ C.supp
    · have hnot : ¬ G.Adj i j := fun h => hi ((C.mem_supp_congr_adj h).mpr hj)
      simp [SimpleGraph.adjMatrix_apply, hnot]
    · simp [multiplicityExtend, hj]
theorem component_eigenspace_finrank_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent]
    [∀ C : G.ConnectedComponent, Fintype C.supp]
    [∀ C : G.ConnectedComponent, DecidableRel C.toSimpleGraph.Adj]
    (lambda : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) =
      ∑ C : G.ConnectedComponent,
        Module.finrank ℝ (Module.End.eigenspace
          (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) := by
  classical
  let E := Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda
  let F := fun C : G.ConnectedComponent =>
    Module.End.eigenspace (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda
  let f : E →ₗ[ℝ] ((C : G.ConnectedComponent) → F C) :=
    { toFun := fun x C => ⟨fun i => x.val i.val, by
        apply Module.End.mem_eigenspace_iff.mpr
        funext i
        change (C.toSimpleGraph.adjMatrix ℝ).mulVec (fun i => x.val i.val) i =
          lambda * x.val i.val
        rw [component_adj_mulVec_restrict]
        exact congrFun (Module.End.mem_eigenspace_iff.mp x.property) i.val⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrFun (congrArg Subtype.val (congrFun h (G.connectedComponentMk i))) ⟨i, rfl⟩
  have hfs : Function.Surjective f := by
    intro y
    let x : ι → ℝ := fun i => (y (G.connectedComponentMk i)).val ⟨i, rfl⟩
    have hx (C : G.ConnectedComponent) (i : C.supp) : x i.val = (y C).val i := by
      rcases i with ⟨i, hi⟩
      change G.connectedComponentMk i = C at hi
      subst C
      rfl
    refine ⟨⟨x, ?_⟩, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      funext i
      let C := G.connectedComponentMk i
      let j : C.supp := ⟨i, rfl⟩
      have hy := congrFun (Module.End.mem_eigenspace_iff.mp (y C).property) j
      change (C.toSimpleGraph.adjMatrix ℝ).mulVec (y C).val j = lambda * (y C).val j at hy
      have hh : (fun k : C.supp => x k.val) = (y C).val := funext (hx C)
      have hrestrict := component_adj_mulVec_restrict G C x j
      have heq := congrArg (fun z => (C.toSimpleGraph.adjMatrix ℝ).mulVec z j) hh
      exact hrestrict.symm.trans (heq.trans hy)
    · funext C
      apply Subtype.ext
      funext i
      exact hx C i
  exact (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).finrank_eq.trans
    (Module.finrank_pi_fintype ℝ)
theorem component_rank_add_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
theorem component_rank_smul_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ℝ)
    (A : Matrix ι κ ℝ) : (a • A).rank ≤ A.rank := by
  rw [Matrix.rank, Matrix.rank]
  apply Submodule.finrank_mono
  rintro x ⟨c, rfl⟩
  refine ⟨a • c, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.smul_mulVec]
theorem component_rank_one_general_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lambda : ℝ) :
    Fintype.card ι ≤
      (lambda • (1 : Matrix ι ι ℝ) - A +
        (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).rank + 1 +
      Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) := by
  let Q := lambda • (1 : Matrix ι ι ℝ) - A
  let J : Matrix ι ι ℝ := Matrix.of (fun _ _ => 1)
  let P := Q + (1 / 2 : ℝ) • J
  have hker : LinearMap.ker Q.mulVecLin = Module.End.eigenspace A.mulVecLin lambda := by
    ext x
    simp only [LinearMap.mem_ker, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Q, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero, eq_comm]
  have hn := Q.mulVecLin.finrank_range_add_finrank_ker
  rw [hker, Module.finrank_pi] at hn
  change Q.rank + Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) =
    Fintype.card ι at hn
  have hJ : J.rank ≤ 1 := by
    simpa only [Matrix.vecMulVec, one_mul, J, Matrix.of_apply] using
      Matrix.rank_vecMulVec_le (fun _ : ι => (1 : ℝ)) (fun _ : ι => (1 : ℝ))
  have heq : Q = P + (- (1 / 2 : ℝ)) • J := by
    dsimp only [P]
    rw [add_assoc, ← add_smul]
    norm_num
  have hr : Q.rank ≤ P.rank + 1 := by
    rw [heq]
    exact (component_rank_add_le _ _).trans
      (Nat.add_le_add_left ((component_rank_smul_le _ _).trans hJ) _)
  change _ ≤ P.rank + 1 + _
  omega
theorem component_allones_mulVec
    {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (Matrix.of (fun _ _ : ι => (1 : ℝ))).mulVec x = fun _ => ∑ i, x i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul]
theorem component_rank_one_quadratic
    {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (x : ι → ℝ) :
    dotProduct x ((Q + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).mulVec x) =
      dotProduct x (Q.mulVec x) + (1 / 2 : ℝ) * (∑ i, x i) ^ 2 := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    component_allones_mulVec]
  simp only [dotProduct, Finset.sum_mul, smul_eq_mul, pow_two]
theorem component_rank_one_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ)
    (hQ : Q.PosSemidef) (x : ι → ℝ) :
    (Q + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).mulVec x = 0 ↔
      Q.mulVec x = 0 ∧ ∑ i, x i = 0 := by
  constructor
  · intro hx
    have hzero := congrArg (dotProduct x) hx
    rw [component_rank_one_quadratic, dotProduct_zero] at hzero
    have hn : 0 ≤ dotProduct x (Q.mulVec x) := by
      simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg x
    have hs : ∑ i, x i = 0 := by nlinarith [sq_nonneg (∑ i, x i)]
    refine ⟨?_, hs⟩
    apply hQ.dotProduct_mulVec_zero_iff.mp
    simp only [star_trivial]
    nlinarith [hs]
  · rintro ⟨hx, hs⟩
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, component_allones_mulVec, hs, hx]
    simp
    rfl
theorem component_eigenspace_eq_bot_of_rayleigh_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (rho lambda : ℝ) (hlt : rho < lambda)
    (hb : ∀ x, dotProduct x (A.mulVec x) ≤ rho * dotProduct x x) :
    Module.End.eigenspace A.mulVecLin lambda = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : A.mulVec x = lambda • x := Module.End.mem_eigenspace_iff.mp hx
  have hh := hb x
  rw [he, dotProduct_smul, smul_eq_mul] at hh
  have hn : 0 ≤ dotProduct x x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have hz : dotProduct x x = 0 := by nlinarith
  exact (dotProduct_self_eq_zero.mp hz)
theorem component_rank_one_positive_pair_impossible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lambda rho tau : ℝ)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef)
    (x y : ι → ℝ) (hx : A.mulVec x = rho • x) (hy : A.mulVec y = tau • y)
    (hxy : dotProduct x y = 0) (hsx : 0 < ∑ i, x i) (hsy : 0 < ∑ i, y i)
    (hrho : lambda < rho) (htau : lambda ≤ tau) : False := by
  let a := ∑ i, x i
  let b := ∑ i, y i
  let z := b • x - a • y
  have hyx : dotProduct y x = 0 := by rw [dotProduct_comm, hxy]
  have hzsum : ∑ i, z i = 0 := by
    simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [a, b]
    ring
  have hzq : dotProduct z (A.mulVec z) =
      b ^ 2 * rho * dotProduct x x + a ^ 2 * tau * dotProduct y y := by
    simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, hx, hy,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hxy, hyx]
    ring
  have hzn : dotProduct z z = b ^ 2 * dotProduct x x + a ^ 2 * dotProduct y y := by
    simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hxy, hyx]
    ring
  have hnonneg := hP.dotProduct_mulVec_nonneg z
  simp only [star_trivial] at hnonneg
  rw [component_rank_one_quadratic, hzsum, zero_pow (by decide : 2 ≠ 0), mul_zero,
    add_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hzq, hzn] at hnonneg
  have hxne : x ≠ 0 := by
    intro h
    have hh := hsx
    simp only [h, Pi.zero_apply, Finset.sum_const_zero] at hh
    exact (lt_irrefl 0) hh
  have hxpos : 0 < dotProduct x x := lt_of_le_of_ne
    (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))
    (fun h => hxne (dotProduct_self_eq_zero.mp h.symm))
  have hynonneg : 0 ≤ dotProduct y y := Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))
  have hstrict := mul_pos (sq_pos_of_pos hsy) (mul_pos (sub_pos.mpr hrho) hxpos)
  have hweak := mul_nonneg (sq_nonneg a) (mul_nonneg (sub_nonneg.mpr htau) hynonneg)
  dsimp only [b] at hnonneg
  nlinarith only [hnonneg, hstrict, hweak]
theorem component_psd_rank_one_rank
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosSemidef)
    (hw : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) ≠ 0 →
      ∃ x : ι → ℝ, Q.mulVec x = 0 ∧ (∑ i, x i) ≠ 0) :
    (Q + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).rank =
      if Module.finrank ℝ (LinearMap.ker Q.mulVecLin) = 0 then Fintype.card ι
      else Fintype.card ι + 1 - Module.finrank ℝ (LinearMap.ker Q.mulVecLin) := by
  let K := LinearMap.ker Q.mulVecLin
  let P := Q + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))
  let f : K →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ i, x.val i
      map_add' := by intro x y; simp [Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum] }
  have hker : LinearMap.ker P.mulVecLin = (LinearMap.ker f).map K.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hqx, hs⟩ := (component_rank_one_kernel Q hQ x).mp hx
      exact ⟨⟨x, hqx⟩, hs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (component_rank_one_kernel Q hQ x.val).mpr ⟨x.property, hx⟩
  have hdimker : Module.finrank ℝ (LinearMap.ker P.mulVecLin) =
      Module.finrank ℝ (LinearMap.ker f) := by
    rw [hker]
    exact Submodule.finrank_map_subtype_eq K (LinearMap.ker f)
  have hP := P.mulVecLin.finrank_range_add_finrank_ker
  rw [hdimker, Module.finrank_pi] at hP
  change P.rank + Module.finrank ℝ (LinearMap.ker f) = Fintype.card ι at hP
  have hf := f.finrank_range_add_finrank_ker
  change Module.finrank ℝ (LinearMap.range f) + Module.finrank ℝ (LinearMap.ker f) =
    Module.finrank ℝ K at hf
  change P.rank = if Module.finrank ℝ K = 0 then _ else _
  by_cases ht : Module.finrank ℝ K = 0
  · rw [if_pos ht]
    omega
  · rw [if_neg ht]
    change P.rank = Fintype.card ι + 1 - Module.finrank ℝ K
    obtain ⟨x, hx, hs⟩ := hw ht
    have hfs : Function.Surjective f := by
      intro c
      refine ⟨(c / ∑ i, x i) • (⟨x, hx⟩ : K), ?_⟩
      change ∑ i, (c / ∑ i, x i) * x i = c
      rw [← Finset.mul_sum, div_mul_cancel₀ _ hs]
    have hr : Module.finrank ℝ (LinearMap.range f) = 1 := by
      rw [LinearMap.range_eq_top.mpr hfs, finrank_top, Module.finrank_self]
    omega
theorem component_sum_by_components
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    [Fintype G.ConnectedComponent] [∀ C : G.ConnectedComponent, Fintype C.supp]
    (x : ι → ℝ) :
    (∑ C : G.ConnectedComponent, ∑ i : C.supp, x i.val) = ∑ i, x i := by
  classical
  convert Fintype.sum_fiberwise G.connectedComponentMk x using 1
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr (congrArg (fun e : Fintype C.supp => @Finset.univ C.supp e)
    (Subsingleton.elim _ _))
  intro i _
  rfl
theorem component_shift_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent]
    [∀ C : G.ConnectedComponent, Fintype C.supp]
    [∀ C : G.ConnectedComponent, DecidableRel C.toSimpleGraph.Adj]
    (lambda : ℝ)
    (hb : ∀ C : G.ConnectedComponent, ∀ x : C.supp → ℝ,
      dotProduct x ((C.toSimpleGraph.adjMatrix ℝ).mulVec x) ≤ lambda * dotProduct x x) :
    (lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint lambda)).sub
      (by
        change (G.adjMatrix ℝ).conjTranspose = G.adjMatrix ℝ
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, G.transpose_adjMatrix]))
  intro x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg]
  have hc := Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) =>
    hb C (fun i => x i.val))
  have hq : (∑ C : G.ConnectedComponent,
      dotProduct (fun i : C.supp => x i.val)
        ((C.toSimpleGraph.adjMatrix ℝ).mulVec (fun i => x i.val))) =
      dotProduct x ((G.adjMatrix ℝ).mulVec x) := by
    simp only [dotProduct]
    simp_rw [component_adj_mulVec_restrict]
    convert component_sum_by_components G
      (fun i => x i * (G.adjMatrix ℝ).mulVec x i) using 1
  have hn : (∑ C : G.ConnectedComponent,
      lambda * dotProduct (fun i : C.supp => x i.val) (fun i => x i.val)) =
      lambda * dotProduct x x := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [dotProduct]
    convert component_sum_by_components G (fun i => x i * x i) using 1
  calc
    _ = _ := hq.symm
    _ ≤ _ := hc
    _ = _ := hn
theorem component_extend_sum_pos
    {ι : Type*} [Fintype ι] (C : Set ι) [Fintype C] [Nonempty C]
    (p : C → ℝ) (hp : ∀ i, 0 < p i) :
    0 < ∑ i, multiplicityExtend C p i := by
  have hs := multiplicityExtend_sum C (multiplicityExtend C p)
    (by intro i hi; simp [multiplicityExtend, hi])
  have hh : ∑ i : C, multiplicityExtend C p i.val = ∑ i : C, p i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dif_pos i.property
  rw [hs, hh]
  exact Finset.sum_pos (fun i _ => hp i) Finset.univ_nonempty
theorem component_extend_eigenpair
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C.supp] [DecidableRel C.toSimpleGraph.Adj]
    (p : C.supp → ℝ) (rho : ℝ)
    (hp : (C.toSimpleGraph.adjMatrix ℝ).mulVec p = rho • p) :
    (G.adjMatrix ℝ).mulVec (multiplicityExtend C.supp p) =
      rho • multiplicityExtend C.supp p := by
  rw [component_adj_mulVec_extend, hp]
  funext i
  by_cases hi : i ∈ C.supp <;> simp [multiplicityExtend, hi]
theorem component_extend_orthogonal
    {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (C D : G.ConnectedComponent) (hCD : C ≠ D)
    (p : C.supp → ℝ) (q : D.supp → ℝ) :
    dotProduct (multiplicityExtend C.supp p) (multiplicityExtend D.supp q) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ C.supp
  · have hd : i ∉ D.supp := fun hd =>
      hCD (SimpleGraph.ConnectedComponent.eq_of_common_vertex hi hd)
    simp [multiplicityExtend, hd]
  · simp [multiplicityExtend, hi]
theorem component_accounting_of_perron_data
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent]
    [∀ C : G.ConnectedComponent, Fintype C.supp]
    [∀ C : G.ConnectedComponent, DecidableRel C.toSimpleGraph.Adj]
    (lambda : ℝ) (rho : G.ConnectedComponent → ℝ)
    (p : (C : G.ConnectedComponent) → C.supp → ℝ)
    (hp : ∀ C i, 0 < p C i)
    (he : ∀ C, (C.toSimpleGraph.adjMatrix ℝ).mulVec (p C) = rho C • p C)
    (hm : ∀ C, Module.finrank ℝ
      (Module.End.eigenspace (C.toSimpleGraph.adjMatrix ℝ).mulVecLin (rho C)) = 1)
    (hb : ∀ C x, dotProduct x ((C.toSimpleGraph.adjMatrix ℝ).mulVec x) ≤
      rho C * dotProduct x x)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef) :
    ((∀ C, rho C ≤ lambda) →
      let t := (Finset.univ.filter fun C => rho C = lambda).card
      (lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ +
        (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).rank =
        if t = 0 then Fintype.card ι else Fintype.card ι + 1 - t) ∧
    ((∃ C, lambda < rho C) → ∃ C, lambda < rho C ∧
      (∀ D, D ≠ C → rho D < lambda) ∧
      Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) =
        Module.finrank ℝ (Module.End.eigenspace (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) ∧
      Fintype.card ι ≤
        (lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ +
          (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).rank + 1 +
        Module.finrank ℝ (Module.End.eigenspace (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda)) := by
  classical
  let Q := lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ
  let P := Q + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))
  let m := fun C : G.ConnectedComponent => Module.finrank ℝ
    (Module.End.eigenspace (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda)
  have hker : LinearMap.ker Q.mulVecLin =
      Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda := by
    ext x
    simp only [LinearMap.mem_ker, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Q, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero, eq_comm]
  constructor
  · intro hle
    let t := (Finset.univ.filter fun C => rho C = lambda).card
    have hdim : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) = t := by
      rw [hker, component_eigenspace_finrank_sum]
      have hC : ∀ C, m C = if rho C = lambda then 1 else 0 := by
        intro C
        by_cases h : rho C = lambda
        · rw [if_pos h]
          dsimp only [m]
          have hh := hm C
          rw [h] at hh
          convert hh using 1
        · have hz := component_eigenspace_eq_bot_of_rayleigh_lt
            (C.toSimpleGraph.adjMatrix ℝ) (rho C) lambda (lt_of_le_of_ne (hle C) h)
            (hb C)
          rw [if_neg h]
          dsimp only [m]
          convert (congrArg (fun S : Submodule ℝ (C.supp → ℝ) => Module.finrank ℝ S) hz).trans
            (finrank_bot ℝ (C.supp → ℝ)) using 1
      calc
        _ = ∑ C, if rho C = lambda then 1 else 0 := Finset.sum_congr rfl (fun C _ => hC C)
        _ = t := by simp only [t, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hQ : Q.PosSemidef := component_shift_posSemidef G lambda (by
      intro C x
      exact (hb C x).trans (mul_le_mul_of_nonneg_right (hle C)
        (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))))
    have hw : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) ≠ 0 →
        ∃ x : ι → ℝ, Q.mulVec x = 0 ∧ (∑ i, x i) ≠ 0 := by
      intro hn
      have ht : t ≠ 0 := fun h => hn (hdim.trans h)
      obtain ⟨C, hC⟩ := Finset.card_ne_zero.mp ht
      have hcrit : rho C = lambda := (Finset.mem_filter.mp hC).2
      letI : Nonempty C.supp := C.connected_toSimpleGraph.nonempty
      refine ⟨multiplicityExtend C.supp (p C), ?_, ne_of_gt (component_extend_sum_pos
        C.supp (p C) (hp C))⟩
      have hext := component_extend_eigenpair G C (p C) (rho C) (he C)
      rw [hcrit] at hext
      simp only [Q, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hext, sub_self]
    have hr := component_psd_rank_one_rank Q hQ hw
    rw [hdim] at hr
    exact hr
  · rintro ⟨C, hC⟩
    have hless : ∀ D, D ≠ C → rho D < lambda := by
      intro D hDC
      by_contra hD
      have hD' : lambda ≤ rho D := le_of_not_gt hD
      letI : Nonempty C.supp := C.connected_toSimpleGraph.nonempty
      letI : Nonempty D.supp := D.connected_toSimpleGraph.nonempty
      exact component_rank_one_positive_pair_impossible (G.adjMatrix ℝ) lambda (rho C) (rho D)
        hP (multiplicityExtend C.supp (p C)) (multiplicityExtend D.supp (p D))
        (component_extend_eigenpair G C (p C) (rho C) (he C))
        (component_extend_eigenpair G D (p D) (rho D) (he D))
        (component_extend_orthogonal G C D (Ne.symm hDC) (p C) (p D))
        (component_extend_sum_pos C.supp (p C) (hp C))
        (component_extend_sum_pos D.supp (p D) (hp D)) hC hD'
    have hdim : Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) = m C := by
      rw [component_eigenspace_finrank_sum]
      apply Finset.sum_eq_single C
      · intro D _ hDC
        have hz := component_eigenspace_eq_bot_of_rayleigh_lt
          (D.toSimpleGraph.adjMatrix ℝ) (rho D) lambda (hless D hDC) (hb D)
        convert (congrArg (fun S : Submodule ℝ (D.supp → ℝ) => Module.finrank ℝ S) hz).trans
          (finrank_bot ℝ (D.supp → ℝ)) using 1
      · simp
    refine ⟨C, hC, hless, hdim, ?_⟩
    have hr := component_rank_one_general_bound (G.adjMatrix ℝ) lambda
    rw [hdim] at hr
    exact hr
theorem component_rank_one_accounting :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ), 0 < lambda →
    let A : Matrix (Fin n) (Fin n) ℝ :=
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
    let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => 1)
    let P := lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - A + (1 / 2 : ℝ) • J
    let r : G.ConnectedComponent → ENNReal := fun C =>
      (letI : Fintype C.supp := Fintype.ofFinite C.supp;
       letI : DecidableEq C.supp := Classical.decEq C.supp;
       letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj;
       spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ))
    P.PosSemidef →
      ((¬ ∃ C, ENNReal.ofReal lambda < r C) →
        let t := ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda}).ncard
        P.rank = if t = 0 then n else n + 1 - t) ∧
      ((∃ C, ENNReal.ofReal lambda < r C) →
        ∃ C, ENNReal.ofReal lambda < r C ∧
          (∀ D, D ≠ C → r D < ENNReal.ofReal lambda) ∧
          let mC : ℕ :=
            (letI : Fintype C.supp := Fintype.ofFinite C.supp;
             letI : DecidableEq C.supp := Classical.decEq C.supp;
             letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj;
             Module.finrank ℝ (Module.End.eigenspace
               (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda))
          Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) = mC ∧
          n ≤ P.rank + 1 + mC) := by
  classical
  intro n G lambda hlam
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent
  letI (C : G.ConnectedComponent) : Fintype C.supp := Fintype.ofFinite C.supp
  letI (C : G.ConnectedComponent) : DecidableEq C.supp := Classical.decEq C.supp
  letI (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
    Classical.decRel C.toSimpleGraph.Adj
  dsimp only
  intro hP
  choose rho p hnonneg hradius hpos heig hdim hbound using
    (fun C : G.ConnectedComponent =>
      component_connected_perron C.toSimpleGraph C.connected_toSimpleGraph)
  let r : G.ConnectedComponent → ENNReal :=
    fun C => spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ)
  have hr (C : G.ConnectedComponent) : r C = ENNReal.ofReal (rho C) := by
    convert hradius C using 1
  have heq (C : G.ConnectedComponent) :
      r C = ENNReal.ofReal lambda ↔ rho C = lambda := by
    rw [hr C]
    exact ENNReal.ofReal_eq_ofReal_iff (hnonneg C) hlam.le
  have hgt (C : G.ConnectedComponent) :
      ENNReal.ofReal lambda < r C ↔ lambda < rho C := by
    rw [hr C]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hlam.le
  have hlt (C : G.ConnectedComponent) :
      r C < ENNReal.ofReal lambda ↔ rho C < lambda := by
    rw [hr C]
    exact ENNReal.ofReal_lt_ofReal_iff hlam
  have hcase := component_accounting_of_perron_data G lambda rho p hpos heig hdim hbound hP
  constructor
  · intro hnone
    have hle : ∀ C, rho C ≤ lambda := by
      intro C
      apply le_of_not_gt
      intro h
      exact hnone ⟨C, (hgt C).mpr h⟩
    have hs : ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda} : Set _) =
        {C : G.ConnectedComponent | rho C = lambda} := by
      ext C
      exact heq C
    have ht : ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda} : Set _).ncard =
        (Finset.univ.filter fun C => rho C = lambda).card := by
      rw [hs]
      simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    have hh := hcase.1 hle
    dsimp only at hh
    change _ = if ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda} : Set _).ncard = 0
      then n else n + 1 - ({C : G.ConnectedComponent | r C = ENNReal.ofReal lambda} : Set _).ncard
    rw [ht]
    simpa only [Fintype.card_fin] using hh
  · intro hex
    have hex' : ∃ C, lambda < rho C := by
      obtain ⟨C, hC⟩ := hex
      exact ⟨C, (hgt C).mp hC⟩
    obtain ⟨C, hC, hD, hm, hn⟩ := hcase.2 hex'
    refine ⟨C, (hgt C).mpr hC, ?_, ?_⟩
    · intro D hDC
      exact (hlt D).mpr (hD D hDC)
    · constructor
      · convert hm using 1
      · simpa only [Fintype.card_fin] using hn
theorem supercritical_graph_rank_bound :
    ∀ (Δ : ℕ) (ε : ℝ), 0 < ε → ∃ M : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ), 0 < lambda →
        (∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) →
        let A : Matrix (Fin n) (Fin n) ℝ :=
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
        let P := lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
          (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))
        let r : G.ConnectedComponent → ENNReal := fun C =>
          (letI : Fintype C.supp := Fintype.ofFinite C.supp;
           letI : DecidableEq C.supp := Classical.decEq C.supp;
           letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj;
           spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ))
        P.PosSemidef → (∃ C, ENNReal.ofReal lambda < r C) →
          n ≤ P.rank + 1 + M ∨
            (n : ℝ) ≤ (P.rank : ℝ) + 1 + ε * (n : ℝ) := by
  classical
  intro Δ ε hε
  obtain ⟨M, hM⟩ := uniform_second_eigenvalue_multiplicity Δ ε hε
  refine ⟨M, ?_⟩
  intro n G lambda hlam hdegree
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI (C : G.ConnectedComponent) : Fintype C.supp := Fintype.ofFinite C.supp
  letI (C : G.ConnectedComponent) : DecidableEq C.supp := Classical.decEq C.supp
  letI (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
    Classical.decRel C.toSimpleGraph.Adj
  dsimp only
  intro hP hex
  obtain ⟨C, _, _, _, hn⟩ :=
    (component_rank_one_accounting n G lambda hlam hP).2 hex
  have hcard : Nat.card C = Nat.card C.supp := Nat.card_congr
    { toFun := fun i => ⟨i.val, i.property⟩
      invFun := fun i => ⟨i.val, i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  by_cases hsize : M ≤ Fintype.card C.supp
  · right
    obtain ⟨H, f, hH, hf, hdeg, hA, hdim⟩ :=
      supercritical_component_overFin_data n G C Δ hdegree
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    letI : Nonempty (Fin (Fintype.card C.supp)) := hH.nonempty
    have hPH : (lambda •
        (1 : Matrix (Fin (Fintype.card C.supp)) (Fin (Fintype.card C.supp)) ℝ) -
        H.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef := by
      rw [← hA]
      exact upper_rank_one_principal_psd (G.adjMatrix ℝ) lambda f hf hP
    have hHerm : (H.adjMatrix ℝ).IsHermitian := by
      change (H.adjMatrix ℝ).conjTranspose = H.adjMatrix ℝ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, H.transpose_adjMatrix]
    have hm := hM (Fintype.card C.supp) H lambda hsize hlam hH hdeg hHerm
      (upper_psd_eigenvalues_except_one (H.adjMatrix ℝ) hHerm lambda hPH)
    rw [hdim lambda] at hm
    have hCn : Fintype.card C.supp ≤ n := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective (Subtype.val : C.supp → Fin n) Subtype.val_injective
    have hCnR : (Fintype.card C.supp : ℝ) ≤ (n : ℝ) := by exact_mod_cast hCn
    have hmul := mul_le_mul_of_nonneg_left hCnR hε.le
    have hnR : (n : ℝ) ≤
        ((lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ +
          (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).rank : ℝ) + 1 +
          Module.finrank ℝ (Module.End.eigenspace
            (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) := by exact_mod_cast hn
    linarith only [hnR, hm, hmul]
  · left
    have hm := upper_small_eigenspace_bound (C.toSimpleGraph.adjMatrix ℝ) lambda
    simp only [← Nat.card_eq_fintype_card] at hm hsize
    rw [hcard] at hm
    exact hn.trans (Nat.add_le_add_left (by omega :
      Module.finrank ℝ (Module.End.eigenspace
        (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) ≤ M) _)
theorem lower_floor_count_real_subtraction (q d : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ =
      q * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) := by
  have hq1 : 1 ≤ q := by omega
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have heq : (q * (d - 1) : ℝ) / (q - 1 : ℝ) =
      ((d - 1 : ℕ) : ℝ) / ((q - 1 : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd, Nat.cast_sub hq1]
    push_cast
    field_simp [ne_of_gt hqpos]
    ring
  rw [heq, Nat.floor_add_natCast (by positivity), Nat.floor_div_eq_div]
  have hdiv := Nat.div_add_mod (d - 1) (q - 1)
  calc
    (d - 1) / (q - 1) + (d - 1) =
        (d - 1) / (q - 1) + ((q - 1) * ((d - 1) / (q - 1)) +
          (d - 1) % (q - 1)) := congrArg (fun a => (d - 1) / (q - 1) + a) hdiv.symm
    _ = ((q - 1) + 1) * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) := by ring
    _ = q * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) := by
      rw [Nat.sub_add_cancel hq1]
theorem floor_lower_bound_from_copies (q d : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    (q - 1) * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) + 1 = d := by
  rw [Nat.div_add_mod, Nat.sub_add_cancel hd]
theorem gram_bridge_rank_add_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
theorem gram_bridge_rank_smul_le {m n : ℕ} (a : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : (a • A).rank ≤ A.rank := by
  rw [Matrix.rank, Matrix.rank]
  apply Submodule.finrank_mono
  rintro x ⟨c, rfl⟩
  refine ⟨a • c, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.smul_mulVec]
theorem gram_spectral_bridge_of_unit_vectors
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ)
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hnorm : ∀ i, ‖v i‖ = 1)
    (hangle : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) :
    ∃ G : SimpleGraph (Fin n),
      let A : Matrix (Fin n) (Fin n) ℝ :=
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
      Matrix.gram ℝ v = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A ∧
      (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank ≤ d + 1 ∧
      n ≤ d + 1 + Module.finrank ℝ
        (Module.End.eigenspace A.mulVecLin ((1 - α) / (2 * α))) := by
  classical
  let G := SimpleGraph.fromRel (fun i j => inner ℝ (v i) (v j) < 0)
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
  have hadj : ∀ i j, G.Adj i j ↔ i ≠ j ∧ inner ℝ (v i) (v j) < 0 := by
    intro i j
    simp only [G, SimpleGraph.fromRel_adj, real_inner_comm (v j) (v i), or_self]
  have hgram : Matrix.gram ℝ v = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.gram_apply, hnorm, A]
    · rcases (abs_eq hα.1.le).mp (hangle i j hij) with hpos | hneg
      · have hnot : ¬α < 0 := not_lt.mpr hα.1.le
        simp [Matrix.gram_apply, hij, A, hadj, hpos, hnot]
      · simp [Matrix.gram_apply, hij, A, hadj, hneg, hα.1]
        ring
  have hgramrank : (Matrix.gram ℝ v).rank ≤ d := by
    let b := EuclideanSpace.basisFun (Fin d) ℝ
    let M : Matrix (Fin d) (Fin n) ℝ := Matrix.of (fun i j => b.repr (v j) i)
    have hg : Matrix.gram ℝ v = M.conjTranspose * M :=
      Matrix.gram_eq_conjTranspose_mul b v
    calc
      (Matrix.gram ℝ v).rank = (M.conjTranspose * M).rank := congrArg Matrix.rank hg
      _ ≤ M.rank := Matrix.rank_mul_le_right _ _
      _ ≤ d := by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height M
  let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => (1 : ℝ))
  let B : Matrix (Fin n) (Fin n) ℝ := ((1 - α) / (2 * α)) • 1 - A
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have heq : B = (1 / (2 * α)) • Matrix.gram ℝ v + (-1 / 2 : ℝ) • J := by
    rw [hgram]
    ext i j
    simp only [B, J, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hα0] <;> ring
  have hJ : J.rank ≤ 1 := by
    have hones : J = Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ))
        (fun _ : Fin n => (1 : ℝ)) := by
      ext i j
      simp [J, Matrix.vecMulVec]
    rw [hones]
    exact Matrix.rank_vecMulVec_le _ _
  have hrank : B.rank ≤ d + 1 := by
    rw [heq]
    calc
      ((1 / (2 * α)) • Matrix.gram ℝ v + (-1 / 2 : ℝ) • J).rank ≤
          ((1 / (2 * α)) • Matrix.gram ℝ v).rank + ((-1 / 2 : ℝ) • J).rank :=
        gram_bridge_rank_add_le _ _
      _ ≤ (Matrix.gram ℝ v).rank + J.rank :=
        Nat.add_le_add (gram_bridge_rank_smul_le _ _) (gram_bridge_rank_smul_le _ _)
      _ ≤ d + 1 := Nat.add_le_add hgramrank hJ
  have hker : LinearMap.ker B.mulVecLin =
      Module.End.eigenspace A.mulVecLin ((1 - α) / (2 * α)) := by
    ext c
    rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
    simp only [Matrix.mulVecLin_apply, B, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    exact eq_comm
  have hdim : B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker] at hdim
  refine ⟨G, hgram, hrank, ?_⟩
  exact hdim.symm.trans_le (Nat.add_le_add_right hrank _)
theorem switching_inner_weighted_sum
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (a : ℝ) (c : ι → ℝ)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = a) :
    (inner ℝ (∑ i ∈ s, c i • v i) (∑ i ∈ s, c i • v i)) =
      (1 - a) * (∑ i ∈ s, c i ^ 2) + a * (∑ i ∈ s, c i) ^ 2 := by
  have hrow : ∀ i ∈ s, (inner ℝ (v i) (∑ j ∈ s, c j • v j)) =
      (1 - a) * c i + a * ∑ j ∈ s, c j := by
    intro i hi
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    calc
      ∑ j ∈ s, c j * (inner ℝ (v i) (v j)) =
          ∑ j ∈ s, (a * c j + if j = i then (1 - a) * c j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : j = i
        · subst j
          rw [hdiag i hi, if_pos rfl]
          ring
        · rw [hoff i hi j hj (Ne.symm hij), if_neg hij]
          ring
      _ = (1 - a) * c i + a * ∑ j ∈ s, c j := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi,
          ← Finset.mul_sum]
        ring
  rw [sum_inner]
  simp_rw [real_inner_smul_left]
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => c i * x) (hrow i hi))]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ i ∈ s, c i * ((1 - a) * c i)) =
      (1 - a) * ∑ i ∈ s, c i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsecond : (∑ i ∈ s, c i * (a * ∑ j ∈ s, c j)) =
      a * (∑ i ∈ s, c i) ^ 2 := by
    rw [← Finset.sum_mul]
    ring
  rw [hfirst, hsecond]
theorem switching_negative_clique_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (α : ℝ) (hα : 0 < α)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = -α) :
    (s.card : ℝ) ≤ 1 + 1 / α := by
  have hs := switching_inner_weighted_sum s v (-α) (fun _ => 1) hdiag hoff
  simp only [one_smul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hn := real_inner_self_nonneg (x := ∑ i ∈ s, v i)
  have hc : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  by_cases hz : s.card = 0
  · rw [hz, Nat.cast_zero]
    positivity
  · have hcpos : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    have hb : α * (s.card : ℝ) ≤ 1 + α := by
      nlinarith [hs]
    calc
      (s.card : ℝ) ≤ (1 + α) / α := (le_div_iff₀ hα).mpr (by
        simpa only [mul_comm] using hb)
      _ = 1 + 1 / α := by field_simp; ring
theorem switching_residual_class_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (z : H) (α a : ℝ) (hα : α ≤ 1) (ha : α < a)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) ≤ α)
    (hvz : ∀ i ∈ s, (inner ℝ (v i) (z)) = a) (hzz : (inner ℝ (z) (z)) = a) :
    (s.card : ℝ) ≤ (1 - α) / (a - α) := by
  have hsum : (inner ℝ (∑ i ∈ s, (v i - z)) (∑ i ∈ s, (v i - z))) ≤
      (1 - α) * (s.card : ℝ) - (a - α) * (s.card : ℝ) ^ 2 := by
    rw [sum_inner]
    simp_rw [inner_sum]
    calc
      ∑ i ∈ s, ∑ j ∈ s, (inner ℝ (v i - z) (v j - z)) ≤
          ∑ i ∈ s, ∑ j ∈ s, ((α - a) + if j = i then 1 - α else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          hvz i hi, ← real_inner_comm z (v j), hvz j hj, hzz]
        by_cases hij : j = i
        · subst j
          rw [hdiag i hi, if_pos rfl]
          linarith
        · rw [if_neg hij]
          linarith [hoff i hi j hj (Ne.symm hij)]
      _ = (1 - α) * (s.card : ℝ) - (a - α) * (s.card : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_ite_eq']
        have he : ∀ i ∈ s, (if i ∈ s then 1 - α else 0) = 1 - α := by
          intro i hi
          rw [if_pos hi]
        rw [Finset.sum_congr rfl he]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hn := real_inner_self_nonneg (x := ∑ i ∈ s, (v i - z))
  by_cases hz : s.card = 0
  · rw [hz, Nat.cast_zero]
    apply div_nonneg ?_ (sub_pos.mpr ha).le
    exact sub_nonneg.mpr hα
  · have hcpos : 0 < (s.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
    nlinarith
theorem switching_mixed_sign_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : Finset ι) (v : ι → H) (w : H) (α : ℝ)
    (hdis : Disjoint p q) (hp : p.Nonempty) (hq : q.Nonempty)
    (hw : (inner ℝ (w) (w)) = 1)
    (hdiag : ∀ i ∈ p ∪ q, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ p ∪ q, ∀ j ∈ p ∪ q, i ≠ j → (inner ℝ (v i) (v j)) = α)
    (hneg : ∀ i ∈ p, (inner ℝ (w) (v i)) = -α)
    (hpos : ∀ i ∈ q, (inner ℝ (w) (v i)) = α) :
    4 * α ^ 2 * (p.card : ℝ) * (q.card : ℝ) ≤
      (1 - α) * ((p.card : ℝ) + (q.card : ℝ)) := by
  let c : ι → ℝ := fun i => if i ∈ p then (q.card : ℝ) else -(p.card : ℝ)
  have hc_p : ∀ i ∈ p, c i = (q.card : ℝ) := by
    intro i hi
    simp only [c, if_pos hi]
  have hc_q : ∀ i ∈ q, c i = -(p.card : ℝ) := by
    intro i hi
    have hn : i ∉ p := fun h => Finset.disjoint_left.mp hdis h hi
    simp only [c, if_neg hn]
  have hsum : (∑ i ∈ p ∪ q, c i) = 0 := by
    rw [Finset.sum_union hdis, Finset.sum_congr rfl hc_p, Finset.sum_congr rfl hc_q]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hsq : (∑ i ∈ p ∪ q, c i ^ 2) =
      (p.card : ℝ) * (q.card : ℝ) * ((p.card : ℝ) + (q.card : ℝ)) := by
    rw [Finset.sum_union hdis,
      Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hc_p i hi)),
      Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hc_q i hi))]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hiw : (inner ℝ (w) (∑ i ∈ p ∪ q, c i • v i)) =
      -2 * α * (p.card : ℝ) * (q.card : ℝ) := by
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    rw [Finset.sum_union hdis]
    have hp' : (∑ i ∈ p, c i * (inner ℝ (w) (v i))) = ∑ i ∈ p, (q.card : ℝ) * -α := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc_p i hi, hneg i hi]
    have hq' : (∑ i ∈ q, c i * (inner ℝ (w) (v i))) = ∑ i ∈ q, -(p.card : ℝ) * α := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc_q i hi, hpos i hi]
    rw [hp', hq']
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hcs := real_inner_mul_inner_self_le w (∑ i ∈ p ∪ q, c i • v i)
  rw [hw, switching_inner_weighted_sum (p ∪ q) v α c hdiag hoff,
    hiw, hsum, hsq] at hcs
  have hpq : 0 < (p.card : ℝ) * (q.card : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hp))
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hq))
  by_contra hnot
  have hgt := mul_pos hpq (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hcs, hgt]
theorem switching_seed_projection
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s p : Finset ι) (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hp : p ⊆ s) (hs : s.Nonempty)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = α) :
    let t : ℝ := s.card
    let k : ℝ := p.card
    let b : ι → ℝ := fun i => if i ∈ p then -1 else 1
    let c : ι → ℝ := fun i => α / (1 - α) *
      (b i - α * (t - 2 * k) / (1 + (t - 1) * α))
    let z : H := ∑ i ∈ s, c i • v i
    let a : ℝ := α ^ 2 / (1 - α) *
      (t - α * (t - 2 * k) ^ 2 / (1 + (t - 1) * α))
    (inner ℝ (z) (z)) = a ∧
      (∀ w : H, (∀ i ∈ s, (inner ℝ (w) (v i)) = α * b i) → (inner ℝ (w) (z)) = a) ∧
      a - α = α * (4 * α ^ 2 * k * (t - k) - (1 - α) ^ 2) /
        ((1 - α) * (1 + (t - 1) * α)) := by
  dsimp only
  let t : ℝ := s.card
  let k : ℝ := p.card
  let b : ι → ℝ := fun i => if i ∈ p then -1 else 1
  let L : ℝ := 1 + (t - 1) * α
  have h0 : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα.2)
  have ht : 1 ≤ t := by
    change (1 : ℝ) ≤ (s.card : ℝ)
    have ht_nat : 1 ≤ s.card := Finset.card_pos.mpr hs
    exact_mod_cast ht_nat
  have hL : L ≠ 0 := by
    dsimp [L]
    have hprod : 0 ≤ (t - 1) * α := mul_nonneg (sub_nonneg.mpr ht) hα.1.le
    linarith
  have hbsum : (∑ i ∈ s, b i) = t - 2 * k := by
    have hsplit : s = p ∪ (s \ p) := (Finset.union_sdiff_of_subset hp).symm
    have hdis : Disjoint p (s \ p) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_sdiff.mp hj).2 hi
    rw [hsplit, Finset.sum_union hdis]
    have hp' : (∑ i ∈ p, b i) = -(p.card : ℝ) := by
      simp only [b]
      rw [Finset.sum_congr rfl (fun i hi => if_pos hi)]
      simp
    have hq' : (∑ i ∈ s \ p, b i) = ((s \ p).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_sdiff.mp hi).2)]
      simp
    rw [hp', hq', Finset.card_sdiff_of_subset hp, Nat.cast_sub (Finset.card_le_card hp)]
    dsimp [t, k]
    ring
  have hbsq : (∑ i ∈ s, b i ^ 2) = t := by
    have hb : ∀ i ∈ s, b i ^ 2 = 1 := by
      intro i hi
      dsimp [b]
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl hb]
    simp [t]
  let c : ι → ℝ := fun i => α / (1 - α) * (b i - α * (t - 2 * k) / L)
  have hcsum : (∑ i ∈ s, c i) = α * (t - 2 * k) / L := by
    simp only [c, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hbsum]
    change α / (1 - α) * ((t - 2 * k) - t * (α * (t - 2 * k) / L)) = _
    field_simp [h0, hL]
    dsimp [L]
    ring
  have hcsq : (∑ i ∈ s, c i ^ 2) = (α / (1 - α)) ^ 2 *
      (t - 2 * (α * (t - 2 * k) / L) * (t - 2 * k) +
        t * (α * (t - 2 * k) / L) ^ 2) := by
    have hc : ∀ i ∈ s, c i ^ 2 = (α / (1 - α)) ^ 2 *
        (b i ^ 2 - 2 * (α * (t - 2 * k) / L) * b i +
          (α * (t - 2 * k) / L) ^ 2) := by
      intro i hi
      dsimp [c]
      ring
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hbsq, hbsum]
    rfl
  change (inner ℝ (∑ i ∈ s, c i • v i) (∑ i ∈ s, c i • v i)) =
    α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L) ∧
    (∀ w : H, (∀ i ∈ s, (inner ℝ (w) (v i)) = α * b i) →
      (inner ℝ (w) (∑ i ∈ s, c i • v i)) =
        α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L)) ∧
    α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L) - α =
      α * (4 * α ^ 2 * k * (t - k) - (1 - α) ^ 2) / ((1 - α) * L)
  refine ⟨?_, ?_, ?_⟩
  · rw [switching_inner_weighted_sum s v α c hdiag hoff, hcsum, hcsq]
    field_simp [h0, hL]
    dsimp [L]
    ring
  · intro w hw
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => c i * x) (hw i hi))]
    have hc : ∀ i ∈ s, c i * (α * b i) =
        α ^ 2 / (1 - α) * (b i ^ 2 - (α * (t - 2 * k) / L) * b i) := by
      intro i hi
      dsimp [c]
      ring
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hbsq, hbsum]
    ring
  · field_simp [h0, hL]
    dsimp [L]
    ring
theorem switching_finite_ramsey (p q : ℕ) :
    ∃ N : ℕ, ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (R : ι → ι → Prop),
      Symmetric R → N ≤ s.card →
      (∃ u : Finset ι, u ⊆ s ∧ u.card = p ∧
        ∀ i ∈ u, ∀ j ∈ u, i ≠ j → R i j) ∨
      (∃ u : Finset ι, u ⊆ s ∧ u.card = q ∧
        ∀ i ∈ u, ∀ j ∈ u, i ≠ j → ¬R i j) := by
  classical
  induction p generalizing q with
  | zero =>
    refine ⟨0, ?_⟩
    intro ι _ s R hR hcard
    exact Or.inl ⟨∅, Finset.empty_subset s, rfl, by simp⟩
  | succ p ihp =>
    induction q with
    | zero =>
      refine ⟨0, ?_⟩
      intro ι _ s R hR hcard
      exact Or.inr ⟨∅, Finset.empty_subset s, rfl, by simp⟩
    | succ q ihq =>
      obtain ⟨N₁, hN₁⟩ := ihp (q + 1)
      obtain ⟨N₂, hN₂⟩ := ihq
      refine ⟨N₁ + N₂ + 1, ?_⟩
      intro ι _ s R hR hcard
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hs
      let a := (s.erase x).filter (R x)
      let b := (s.erase x).filter (fun i => ¬R x i)
      have hsplit : a.card + b.card = s.card - 1 := by
        dsimp [a, b]
        rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hx]
      have hsuba : a ⊆ s := fun i hi =>
        (Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).2
      have hsubb : b ⊆ s := fun i hi =>
        (Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).2
      by_cases ha : N₁ ≤ a.card
      · rcases hN₁ a R hR ha with ⟨u, hua, hu, hRu⟩ | ⟨u, hua, hu, hRu⟩
        · left
          have hxu : x ∉ u := by
            intro h
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hua h)).1).1 rfl
          refine ⟨insert x u, Finset.insert_subset hx (Finset.Subset.trans hua hsuba),
            by rw [Finset.card_insert_of_notMem hxu, hu], ?_⟩
          intro i hi j hj hij
          rcases Finset.mem_insert.mp hi with rfl | hiu
          · rcases Finset.mem_insert.mp hj with rfl | hju
            · exact False.elim (hij rfl)
            · exact (Finset.mem_filter.mp (hua hju)).2
          · rcases Finset.mem_insert.mp hj with rfl | hju
            · exact hR ((Finset.mem_filter.mp (hua hiu)).2)
            · exact hRu i hiu j hju hij
        · exact Or.inr ⟨u, Finset.Subset.trans hua hsuba, hu, hRu⟩
      · have hb : N₂ ≤ b.card := by omega
        rcases hN₂ b R hR hb with ⟨u, hub, hu, hRu⟩ | ⟨u, hub, hu, hRu⟩
        · exact Or.inl ⟨u, Finset.Subset.trans hub hsubb, hu, hRu⟩
        · right
          have hxu : x ∉ u := by
            intro h
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp (hub h)).1).1 rfl
          refine ⟨insert x u, Finset.insert_subset hx (Finset.Subset.trans hub hsubb),
            by rw [Finset.card_insert_of_notMem hxu, hu], ?_⟩
          intro i hi j hj hij
          rcases Finset.mem_insert.mp hi with rfl | hiu
          · rcases Finset.mem_insert.mp hj with rfl | hju
            · exact False.elim (hij rfl)
            · exact (Finset.mem_filter.mp (hub hju)).2
          · rcases Finset.mem_insert.mp hj with rfl | hju
            · intro h
              exact (Finset.mem_filter.mp (hub hiu)).2 (hR h)
            · exact hRu i hiu j hju hij
theorem switching_large_groups_impossible (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D : ℕ) (hD : 1 - α < 2 * α ^ 2 * (D : ℝ))
    (p q : ℕ) (hp : D ≤ p) (hq : D ≤ q) (hDp : 0 < D)
    (hbound : 4 * α ^ 2 * (p : ℝ) * (q : ℝ) ≤
      (1 - α) * ((p : ℝ) + (q : ℝ))) : False := by
  have hp' : (D : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
  have hq' : (D : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hq
  have hpp : 0 < (p : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hDp hp)
  have hqp : 0 < (q : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hDp hq)
  have h1 := mul_lt_mul_of_pos_right hD hpp
  have h2 := mul_lt_mul_of_pos_right hD hqp
  have h3 := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 2 * α ^ 2 * (p : ℝ) by positivity)
  have h4 := mul_le_mul_of_nonneg_left hp' (show 0 ≤ 2 * α ^ 2 * (q : ℝ) by positivity)
  nlinarith only [h1, h2, h3, h4, hbound]
theorem switching_orient_to_seed
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (w : H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D : ℕ) (hDp : 0 < D) (hD : 1 - α < 2 * α ^ 2 * (D : ℝ))
    (hw : (inner ℝ (w) (w)) = 1)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = α)
    (hwv : ∀ i ∈ s, |(inner ℝ (w) (v i))| = α) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (s.filter (fun i => (inner ℝ (σ • w) (v i)) < 0)).card < D := by
  classical
  let p := s.filter (fun i => (inner ℝ (w) (v i)) < 0)
  let q := s.filter (fun i => ¬(inner ℝ (w) (v i)) < 0)
  have hdis : Disjoint p q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  have hsplit : p ∪ q = s := by
    ext i
    by_cases h : (inner ℝ (w) (v i)) < 0
    · simp [p, q, h]
    · have h' : 0 ≤ (inner ℝ (w) (v i)) := le_of_not_gt h
      simp [p, q, h, h']
  have hneg : ∀ i ∈ p, (inner ℝ (w) (v i)) = -α := by
    intro i hi
    have h := hwv i (Finset.mem_filter.mp hi).1
    rw [abs_of_neg (Finset.mem_filter.mp hi).2] at h
    linarith
  have hpos : ∀ i ∈ q, (inner ℝ (w) (v i)) = α := by
    intro i hi
    have h := hwv i (Finset.mem_filter.mp hi).1
    rw [abs_of_nonneg (le_of_not_gt (Finset.mem_filter.mp hi).2)] at h
    exact h
  by_cases hp : p.card < D
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa only [one_smul] using hp
  · have hq : q.card < D := by
      by_contra hq
      have hpp : p.Nonempty := Finset.card_pos.mp (by omega)
      have hqp : q.Nonempty := Finset.card_pos.mp (by omega)
      have hb := switching_mixed_sign_bound p q v w α hdis hpp hqp hw
        (by simpa only [hsplit] using hdiag) (by simpa only [hsplit] using hoff) hneg hpos
      exact switching_large_groups_impossible α hα D hD p.card q.card
        (by omega) (by omega) hDp hb
    refine ⟨-1, Or.inr rfl, ?_⟩
    have he : s.filter (fun i => (inner ℝ ((-1 : ℝ) • w) (v i)) < 0) = q := by
      ext i
      simp only [Finset.mem_filter, real_inner_smul_left, neg_mul, one_mul, q]
      constructor
      · rintro ⟨hi, h⟩
        exact ⟨hi, by linarith⟩
      · rintro ⟨hi, h⟩
        have hh := hpos i (Finset.mem_filter.mpr ⟨hi, h⟩)
        exact ⟨hi, by linarith [hα.1]⟩
    rw [he]
    exact hq
theorem switching_seed_pattern_class
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s p r : Finset ι) (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D : ℕ) (hp : p ⊆ s) (hpn : p.Nonempty) (hpD : p.card ≤ D)
    (hsD : D < s.card)
    (hdiag : ∀ i ∈ s, (inner ℝ (v i) (v i)) = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = α)
    (hrdiag : ∀ i ∈ r, (inner ℝ (v i) (v i)) = 1)
    (hroff : ∀ i ∈ r, ∀ j ∈ r, i ≠ j → (inner ℝ (v i) (v j)) ≤ α)
    (hrangle : ∀ i ∈ r, ∀ j ∈ s, |(inner ℝ (v i) (v j))| = α)
    (hpattern : ∀ i ∈ r, s.filter (fun j => (inner ℝ (v i) (v j)) < 0) = p) :
    let δ := α * (4 * α ^ 2 * ((s.card : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
      ((1 - α) * (1 + ((s.card : ℝ) - 1) * α))
    0 < δ → (r.card : ℝ) ≤ (1 - α) / δ := by
  intro δ hδ
  let t : ℝ := s.card
  let k : ℝ := p.card
  let b : ι → ℝ := fun j => if j ∈ p then -1 else 1
  let c : ι → ℝ := fun j => α / (1 - α) *
    (b j - α * (t - 2 * k) / (1 + (t - 1) * α))
  let z : H := ∑ j ∈ s, c j • v j
  let a : ℝ := α ^ 2 / (1 - α) *
    (t - α * (t - 2 * k) ^ 2 / (1 + (t - 1) * α))
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  have hproj := switching_seed_projection s p v α hα hp hs hdiag hoff
  change (inner ℝ (z) (z)) = a ∧
    (∀ w : H, (∀ j ∈ s, (inner ℝ (w) (v j)) = α * b j) → (inner ℝ (w) (z)) = a) ∧
    a - α = α * (4 * α ^ 2 * k * (t - k) - (1 - α) ^ 2) /
      ((1 - α) * (1 + (t - 1) * α)) at hproj
  have hden : 0 < (1 - α) * (1 + (t - 1) * α) := by
    have ht : 1 ≤ t := by
      change (1 : ℝ) ≤ (s.card : ℝ)
      have ht_nat : 1 ≤ s.card := Finset.card_pos.mpr hs
      exact_mod_cast ht_nat
    apply mul_pos (sub_pos.mpr hα.2)
    have hh := mul_nonneg (sub_nonneg.mpr ht) hα.1.le
    linarith
  have hδa : δ ≤ a - α := by
    rw [hproj.2.2]
    change α * (4 * α ^ 2 * (t - (D : ℝ)) - (1 - α) ^ 2) / _ ≤ _
    apply (div_le_div_iff_of_pos_right hden).mpr
    have hk1 : 1 ≤ k := by
      change (1 : ℝ) ≤ (p.card : ℝ)
      have hk_nat : 1 ≤ p.card := Finset.card_pos.mpr hpn
      exact_mod_cast hk_nat
    have hkD : k ≤ (D : ℝ) := Nat.cast_le.mpr hpD
    have hDt : (D : ℝ) < t := Nat.cast_lt.mpr hsD
    have htk : 0 ≤ t - k := by linarith
    have hkp := mul_le_mul_of_nonneg_right hk1 htk
    have hh : t - (D : ℝ) ≤ k * (t - k) := by nlinarith only [hkp, hkD]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * α ^ 2 by positivity)
    have hm' := mul_le_mul_of_nonneg_left hm hα.1.le
    nlinarith only [hm']
  have ha : α < a := by linarith only [hδa, hδ]
  have hvz : ∀ i ∈ r, (inner ℝ (v i) (z)) = a := by
    intro i hi
    apply hproj.2.1 (v i)
    intro j hj
    dsimp [b]
    by_cases hjp : j ∈ p
    · rw [if_pos hjp]
      have hneg : (inner ℝ (v i) (v j)) < 0 := by
        rw [← hpattern i hi] at hjp
        exact (Finset.mem_filter.mp hjp).2
      have hh := hrangle i hi j hj
      rw [abs_of_neg hneg] at hh
      linarith
    · rw [if_neg hjp]
      have hnon : 0 ≤ (inner ℝ (v i) (v j)) := by
        by_contra h
        apply hjp
        rw [← hpattern i hi]
        exact Finset.mem_filter.mpr ⟨hj, by linarith⟩
      have hh := hrangle i hi j hj
      rw [abs_of_nonneg hnon] at hh
      linarith
  have hr := switching_residual_class_bound r v z α a hα.2.le ha
    hrdiag hroff hvz hproj.1
  apply (le_div_iff₀ hδ).mpr
  have hrr : 0 ≤ (r.card : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hδa hrr
  have hb := (le_div_iff₀ (sub_pos.mpr ha)).mp hr
  linarith only [hh, hb]
theorem switching_seeded_degree
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D C R B : ℕ) (hDp : 0 < D) (hD : 1 - α < 2 * α ^ 2 * (D : ℝ))
    (hC : 1 + 1 / α < (C : ℝ))
    (hR : ∀ u : Finset ι, R ≤ u.card →
      (∃ p : Finset ι, p ⊆ u ∧ p.card = D ∧
        ∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (v i) (v j)) = α) ∨
      (∃ p : Finset ι, p ⊆ u ∧ p.card = C ∧
        ∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (v i) (v j)) ≠ α))
    (s : Finset ι) (hsD : 2 * D < s.card)
    (hdiag : ∀ i, (inner ℝ (v i) (v i)) = 1)
    (hangle : ∀ i j, i ≠ j → |(inner ℝ (v i) (v j))| = α)
    (hseed : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = α)
    (hsmall : ∀ i, (s.filter (fun j => (inner ℝ (v i) (v j)) < 0)).card < D)
    (hδ : 0 < α * (4 * α ^ 2 * ((s.card : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
      ((1 - α) * (1 + ((s.card : ℝ) - 1) * α)))
    (hB : (1 - α) /
      (α * (4 * α ^ 2 * ((s.card : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
        ((1 - α) * (1 + ((s.card : ℝ) - 1) * α))) ≤ (B : ℝ)) :
    ∀ i, (Finset.univ.filter (fun j => (inner ℝ (v i) (v j)) < 0)).card ≤
      s.card + 2 ^ s.card * B + R := by
  classical
  let f : ι → Finset ι := fun i => s.filter (fun j => (inner ℝ (v i) (v j)) < 0)
  let X : Finset ι := Finset.univ.filter (fun i => i ∉ s ∧ (f i).Nonempty)
  let U : Finset ι := Finset.univ.filter (fun i => i ∉ s ∧ f i = ∅)
  have hXp : X.card ≤ 2 ^ s.card * B := by
    have hf : Set.MapsTo f (X : Set ι) (s.powerset : Set (Finset ι)) := by
      intro i hi
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    rw [Finset.card_eq_sum_card_fiberwise hf]
    have hclass : ∀ p ∈ s.powerset, (X.filter (fun i => f i = p)).card ≤ B := by
      intro p hp
      let r := X.filter (fun i => f i = p)
      by_cases hr : r.Nonempty
      · obtain ⟨i, hi⟩ := hr
        have hiX := Finset.mem_filter.mp hi
        have hiXX := (Finset.mem_filter.mp hiX.1).2
        have hpnon : p.Nonempty := hiX.2 ▸ hiXX.2
        have hpD : p.card ≤ D := by
          have hh := hsmall i
          change (f i).card < D at hh
          rw [hiX.2] at hh
          omega
        have hrr := switching_seed_pattern_class s p r v α hα D
          (Finset.mem_powerset.mp hp) hpnon hpD (by omega)
          (fun i hi => hdiag i) hseed (fun i hi => hdiag i)
          (fun i hi j hj hij => (le_abs_self _).trans (hangle i j hij).le)
          (fun i hi j hj => hangle i j (by
            intro hij
            subst j
            exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.1 hj))
          (fun i hi => (Finset.mem_filter.mp hi).2) hδ
        have hh : (r.card : ℝ) ≤ (B : ℝ) := hrr.trans hB
        exact_mod_cast hh
      · have hz : r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
        change r.card ≤ B
        rw [hz, Finset.card_empty]
        exact Nat.zero_le _
    have hh := Finset.sum_le_sum hclass
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset, Nat.cast_id] using hh
  have hUpos : ∀ i ∈ U, ∀ j ∈ s, (inner ℝ (v i) (v j)) = α := by
    intro i hi j hj
    have hiU := (Finset.mem_filter.mp hi).2
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hiU.1 hj
    have hnon : 0 ≤ (inner ℝ (v i) (v j)) := by
      by_contra h
      have hh : j ∈ f i := Finset.mem_filter.mpr ⟨hj, by linarith⟩
      rw [hiU.2] at hh
      exact Finset.notMem_empty j hh
    have hh := hangle i j hij
    rwa [abs_of_nonneg hnon] at hh
  have hnegative : ∀ p : Finset ι,
      (∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (v i) (v j)) ≠ α) → p.card ≠ C := by
    intro p hp hpc
    have hh := switching_negative_clique_bound p v α hα.1
      (fun i hi => hdiag i) (by
        intro i hi j hj hij
        have h := hangle i j hij
        have hn : (inner ℝ (v i) (v j)) < 0 := by
          by_contra hn
          have hh := abs_of_nonneg (le_of_not_gt hn)
          exact hp i hi j hj hij (by rwa [hh] at h)
        rw [abs_of_neg hn] at h
        linarith)
    rw [hpc] at hh
    linarith only [hh, hC]
  intro i
  let V : Finset ι := U.filter (fun j => (inner ℝ (v i) (v j)) < 0)
  have hV : V.card ≤ R := by
    by_contra hnot
    have hrv : R ≤ V.card := by omega
    rcases hR V hrv with ⟨p, hpV, hpD, hpp⟩ | ⟨p, hpV, hpC, hpp⟩
    · have hiout : i ∉ s := by
        intro his
        have hpn : p.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨j, hj⟩ := hpn
        have hjV := Finset.mem_filter.mp (hpV hj)
        have hh := hUpos j hjV.1 i his
        have hh' : (inner ℝ (v i) (v j)) = α := by rw [real_inner_comm (v j) (v i)]; exact hh
        linarith only [hjV.2, hh', hα.1]
      let q := s \ f i
      have hdis : Disjoint p q := by
        apply Finset.disjoint_left.mpr
        intro j hj hjq
        have hjU := (Finset.mem_filter.mp (hpV hj)).1
        exact (Finset.mem_filter.mp hjU).2.1 (Finset.mem_sdiff.mp hjq).1
      have hqcard : D ≤ q.card := by
        have hs := hsmall i
        change (f i).card < D at hs
        have hfsub : f i ⊆ s := Finset.filter_subset _ _
        dsimp only [q]
        rw [Finset.card_sdiff_of_subset hfsub]
        omega
      have hpn : p.Nonempty := Finset.card_pos.mp (by omega)
      have hqn : q.Nonempty := Finset.card_pos.mp (by omega)
      have hposq : ∀ j ∈ q, (inner ℝ (v i) (v j)) = α := by
        intro j hj
        have hjs := (Finset.mem_sdiff.mp hj).1
        have hjf := (Finset.mem_sdiff.mp hj).2
        have hnon : 0 ≤ (inner ℝ (v i) (v j)) := by
          by_contra h
          exact hjf (Finset.mem_filter.mpr ⟨hjs, by linarith⟩)
        have hh := hangle i j (by intro h; subst j; exact hiout hjs)
        rwa [abs_of_nonneg hnon] at hh
      have hclique : ∀ j ∈ p ∪ q, ∀ k ∈ p ∪ q, j ≠ k → (inner ℝ (v j) (v k)) = α := by
        intro j hj k hk hjk
        rcases Finset.mem_union.mp hj with hj | hj
        · rcases Finset.mem_union.mp hk with hk | hk
          · exact hpp j hj k hk hjk
          · exact hUpos j (Finset.mem_filter.mp (hpV hj)).1 k
              (Finset.mem_sdiff.mp hk).1
        · rcases Finset.mem_union.mp hk with hk | hk
          · rw [real_inner_comm (v k) (v j)]
            exact hUpos k (Finset.mem_filter.mp (hpV hk)).1 j
              (Finset.mem_sdiff.mp hj).1
          · exact hseed j (Finset.mem_sdiff.mp hj).1 k (Finset.mem_sdiff.mp hk).1 hjk
      have hb := switching_mixed_sign_bound p q v (v i) α hdis hpn hqn
        (hdiag i) (fun j hj => hdiag j) hclique
        (fun j hj => by
          have hn := (Finset.mem_filter.mp (hpV hj)).2
          have hh := hangle i j (by
            intro h
            subst j
            rw [hdiag i] at hn
            linarith)
          rw [abs_of_neg hn] at hh
          linarith) hposq
      exact switching_large_groups_impossible α hα D hD p.card q.card
        (by omega) hqcard hDp hb
    · exact hnegative p hpp hpC
  let W : Finset ι := Finset.univ.filter (fun j => (inner ℝ (v i) (v j)) < 0)
  have hsub : W ⊆ (s ∪ X) ∪ V := by
    intro j hj
    by_cases hjs : j ∈ s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hjs)
    · by_cases hjf : (f j).Nonempty
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjs, hjf⟩))
      · have hjU : j ∈ U := Finset.mem_filter.mpr
          ⟨Finset.mem_univ j, hjs, Finset.not_nonempty_iff_eq_empty.mp hjf⟩
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hjU, (Finset.mem_filter.mp hj).2⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (s ∪ X) V
  have h3 := Finset.card_union_le s X
  change W.card ≤ _
  omega
theorem switching_graph_of_degree_bound
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (σ : ι → ℝ) (Δ : ℕ)
    (hdegree : ∀ i, (Finset.univ.filter (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)).card ≤ Δ) :
    ∃ G : SimpleGraph ι,
      (∀ i j, G.Adj i j ↔ i ≠ j ∧ (inner ℝ (σ i • v i) (σ j • v j)) < 0) ∧
      (∀ i, ({j : ι | G.Adj i j} : Set ι).ncard ≤ Δ) := by
  classical
  let G : SimpleGraph ι := {
    Adj := fun i j => i ≠ j ∧ (inner ℝ (σ i • v i) (σ j • v j)) < 0
    symm := ⟨fun i j h => ⟨h.1.symm, by
      rw [real_inner_comm (σ i • v i) (σ j • v j)]
      exact h.2⟩⟩
    loopless := ⟨fun i h => h.1 rfl⟩ }
  refine ⟨G, fun i j => Iff.rfl, ?_⟩
  intro i
  let s := Finset.univ.filter (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)
  have hsub : {j : ι | G.Adj i j} ⊆ (s : Set ι) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.2⟩
  calc
    ({j : ι | G.Adj i j} : Set ι).ncard ≤ (s : Set ι).ncard := Set.ncard_le_ncard hsub
    _ = s.card := Set.ncard_coe_finset s
    _ ≤ Δ := hdegree i
theorem uniform_switching_of_unit_vectors :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 → ∃ Δ : ℕ,
      ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, inner ℝ (v i) (v i) = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∃ (σ : Fin n → ℝ) (G : SimpleGraph (Fin n)),
          (∀ i, σ i = 1 ∨ σ i = -1) ∧
          (∀ i j, G.Adj i j ↔ i ≠ j ∧ inner ℝ (σ i • v i) (σ j • v j) < 0) ∧
          (∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) := by
  classical
  intro α hα
  have hαpos : 0 < α := hα.1
  have hαlt : α < 1 := hα.2
  have hαsq : 0 < 2 * α ^ 2 := by positivity
  have hαsq4 : 0 < 4 * α ^ 2 := by positivity
  obtain ⟨D, hDlarge⟩ := exists_nat_gt ((1 - α) / (2 * α ^ 2) + 1)
  have hDp : 0 < D := by
    have hn : 0 ≤ (1 - α) / (2 * α ^ 2) := by positivity
    have hh : 0 < (D : ℝ) := by linarith
    exact Nat.cast_pos.mp hh
  have hD : 1 - α < 2 * α ^ 2 * (D : ℝ) := by
    have hh : (1 - α) / (2 * α ^ 2) < (D : ℝ) := by linarith
    have hh' := (div_lt_iff₀ hαsq).mp hh
    nlinarith only [hh']
  obtain ⟨C, hC⟩ := exists_nat_gt (1 + 1 / α)
  obtain ⟨T, hT⟩ := exists_nat_gt
    (max (2 * (D : ℝ)) ((D : ℝ) + (1 - α) ^ 2 / (4 * α ^ 2)))
  have hT1 : 2 * D < T := by
    have hh : 2 * (D : ℝ) < (T : ℝ) := lt_of_le_of_lt (le_max_left _ _) hT
    exact_mod_cast hh
  have hT2 : (1 - α) ^ 2 < 4 * α ^ 2 * ((T : ℝ) - (D : ℝ)) := by
    have hh := lt_of_le_of_lt (le_max_right _ _) hT
    have hh' : (1 - α) ^ 2 / (4 * α ^ 2) < (T : ℝ) - (D : ℝ) := by linarith
    have hh'' := (div_lt_iff₀ hαsq4).mp hh'
    nlinarith only [hh'']
  let δ := α * (4 * α ^ 2 * ((T : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
    ((1 - α) * (1 + ((T : ℝ) - 1) * α))
  have hδ : 0 < δ := by
    have hTp : 1 ≤ T := by omega
    have hTp' : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTp
    have hnum : 0 < α * (4 * α ^ 2 * ((T : ℝ) - (D : ℝ)) - (1 - α) ^ 2) :=
      mul_pos hα.1 (sub_pos.mpr hT2)
    have hprod : 0 ≤ ((T : ℝ) - 1) * α := mul_nonneg (sub_nonneg.mpr hTp') hα.1.le
    exact div_pos hnum (mul_pos (sub_pos.mpr hα.2) (by linarith))
  obtain ⟨B, hB⟩ := exists_nat_ge ((1 - α) / δ)
  obtain ⟨N, hN⟩ := switching_finite_ramsey T C
  obtain ⟨R, hR⟩ := switching_finite_ramsey D C
  let Δ := max N (T + 2 ^ T * B + R)
  refine ⟨Δ, ?_⟩
  intro d n v hdiag hangle
  by_cases hn : N ≤ n
  · have hs := hN (Finset.univ : Finset (Fin n)) (fun i j => (inner ℝ (v i) (v j)) = α)
      (fun i j h => by
        change (inner ℝ (v j) (v i)) = α
        rw [real_inner_comm (v i) (v j)]
        exact h)
      (by simpa using hn)
    have hnegative : ∀ p : Finset (Fin n), p.card = C →
        (∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (v i) (v j)) ≠ α) → False := by
      intro p hp hnot
      have hh := switching_negative_clique_bound p v α hα.1
        (fun i hi => hdiag i) (by
          intro i hi j hj hij
          have hab := hangle i j hij
          have hneg : (inner ℝ (v i) (v j)) < 0 := by
            by_contra h
            rw [abs_of_nonneg (le_of_not_gt h)] at hab
            exact hnot i hi j hj hij hab
          rw [abs_of_neg hneg] at hab
          linarith)
      rw [hp] at hh
      linarith only [hh, hC]
    obtain ⟨s, hssub, hsT, hseed⟩ : ∃ s : Finset (Fin n),
        s ⊆ Finset.univ ∧ s.card = T ∧
        ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (v i) (v j)) = α := by
      rcases hs with h | ⟨p, hp, hpC, hnot⟩
      · exact h
      · exact False.elim (hnegative p hpC hnot)
    have horient : ∀ i : Fin n, ∃ a : ℝ,
        (a = 1 ∨ a = -1) ∧ (i ∈ s → a = 1) ∧
        (s.filter (fun j => (inner ℝ (a • v i) (v j)) < 0)).card < D := by
      intro i
      by_cases his : i ∈ s
      · refine ⟨1, Or.inl rfl, fun _ => rfl, ?_⟩
        have he : s.filter (fun j => (inner ℝ ((1 : ℝ) • v i) (v j)) < 0) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro j hj
          have h := Finset.mem_filter.mp hj
          rw [one_smul] at h
          by_cases hij : i = j
          · subst j
            rw [hdiag i] at h
            linarith only [h.2]
          · rw [hseed i his j h.1 hij] at h
            linarith only [h.2, hα.1]
        rw [he, Finset.card_empty]
        exact hDp
      · obtain ⟨a, ha, hsmall⟩ := switching_orient_to_seed s v (v i) α hα
          D hDp hD (hdiag i) (fun j hj => hdiag j) hseed
          (fun j hj => hangle i j (by intro h; subst j; exact his hj))
        exact ⟨a, ha, fun h => False.elim (his h), hsmall⟩
    choose σ hσ using horient
    let w : Fin n → EuclideanSpace ℝ (Fin d) := fun i => σ i • v i
    have hwdiag : ∀ i, (inner ℝ (w i) (w i)) = 1 := by
      intro i
      rcases (hσ i).1 with hi | hi
      · simp only [w, hi, one_smul, hdiag]
      · simp only [w, hi, neg_one_smul, inner_neg_left, inner_neg_right, neg_neg, hdiag]
    have hwangle : ∀ i j, i ≠ j → |(inner ℝ (w i) (w j))| = α := by
      intro i j hij
      rcases (hσ i).1 with hi | hi <;> rcases (hσ j).1 with hj | hj <;>
        simp only [w, hi, hj, one_smul, neg_one_smul, inner_neg_left,
          inner_neg_right, neg_neg, abs_neg, hangle i j hij]
    have hwseed : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (inner ℝ (w i) (w j)) = α := by
      intro i hi j hj hij
      simp only [w, (hσ i).2.1 hi, (hσ j).2.1 hj, one_smul, hseed i hi j hj hij]
    have hwsmall : ∀ i, (s.filter (fun j => (inner ℝ (w i) (w j)) < 0)).card < D := by
      intro i
      have he : s.filter (fun j => (inner ℝ (w i) (w j)) < 0) =
          s.filter (fun j => (inner ℝ (σ i • v i) (v j)) < 0) := by
        apply Finset.filter_congr
        intro j hj
        simp only [w, (hσ j).2.1 hj, one_smul]
      rw [he]
      exact (hσ i).2.2
    have hRamsey : ∀ u : Finset (Fin n), R ≤ u.card →
        (∃ p : Finset (Fin n), p ⊆ u ∧ p.card = D ∧
          ∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (w i) (w j)) = α) ∨
        (∃ p : Finset (Fin n), p ⊆ u ∧ p.card = C ∧
          ∀ i ∈ p, ∀ j ∈ p, i ≠ j → (inner ℝ (w i) (w j)) ≠ α) := by
      intro u hu
      exact hR u (fun i j => (inner ℝ (w i) (w j)) = α)
        (fun i j h => by
          change (inner ℝ (w j) (w i)) = α
          rw [real_inner_comm (w i) (w j)]
          exact h) hu
    have hdegree := switching_seeded_degree w α hα D C R B hDp hD hC
      hRamsey s (by omega) hwdiag hwangle hwseed hwsmall
      (by simpa only [hsT] using hδ) (by simpa only [hsT] using hB)
    have hb : ∀ i, (Finset.univ.filter (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)).card ≤ Δ := by
      intro i
      have hh := hdegree i
      rw [hsT] at hh
      exact hh.trans (le_max_right _ _)
    obtain ⟨G, hG, hdeg⟩ := switching_graph_of_degree_bound v σ Δ hb
    exact ⟨σ, G, fun i => (hσ i).1, hG, hdeg⟩
  · let σ : Fin n → ℝ := fun _ => 1
    have hb : ∀ i, (Finset.univ.filter (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)).card ≤ Δ := by
      intro i
      have hh := Finset.card_filter_le (Finset.univ : Finset (Fin n))
        (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)
      have hn' : n ≤ N := by omega
      have hh' : (Finset.univ.filter
          (fun j => (inner ℝ (σ i • v i) (σ j • v j)) < 0)).card ≤ n := by
        simpa only [Finset.card_univ, Fintype.card_fin] using hh
      exact hh'.trans (hn'.trans (le_max_left _ _))
    obtain ⟨G, hG, hdeg⟩ := switching_graph_of_degree_bound v σ Δ hb
    exact ⟨σ, G, fun _ => Or.inl rfl, hG, hdeg⟩
theorem switching_norm_eq
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (σ : ι → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (i : ι) :
    ‖σ i • v i‖ = ‖v i‖ := by
  rcases hσ i with hi | hi <;> simp [hi]
theorem switching_abs_inner_eq
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (σ : ι → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (i j : ι) :
    |inner ℝ (σ i • v i) (σ j • v j)| = |inner ℝ (v i) (v j)| := by
  rcases hσ i with hi | hi <;> rcases hσ j with hj | hj <;>
    simp [hi, hj]
theorem switching_injective_of_unit_angles
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (σ : ι → ℝ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (α : ℝ) (hα : α < 1) (hnorm : ∀ i, ‖v i‖ = 1)
    (hangle : ∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) :
    Function.Injective (fun i => σ i • v i) := by
  intro i j hij
  change σ i • v i = σ j • v j at hij
  by_contra hne
  have ha : |inner ℝ (σ i • v i) (σ j • v j)| = α :=
    (switching_abs_inner_eq v σ hσ i j).trans (hangle i j hne)
  rw [hij, real_inner_self_eq_norm_sq, switching_norm_eq v σ hσ j, hnorm j] at ha
  norm_num at ha
  exact (ne_of_lt hα) ha.symm
theorem switching_negative_graph_eq
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (w : ι → H) (G : SimpleGraph ι)
    (hG : ∀ i j, G.Adj i j ↔ i ≠ j ∧ inner ℝ (w i) (w j) < 0) :
    G = SimpleGraph.fromRel (fun i j => inner ℝ (w i) (w j) < 0) := by
  ext i j
  simp only [hG, SimpleGraph.fromRel_adj, real_inner_comm (w j) (w i), or_self]
theorem switching_gram_eq_of_negative_graph
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ)
    (w : Fin n → EuclideanSpace ℝ (Fin d))
    (hnorm : ∀ i, ‖w i‖ = 1)
    (hangle : ∀ i j, i ≠ j → |inner ℝ (w i) (w j)| = α)
    (G : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j ↔ i ≠ j ∧ inner ℝ (w i) (w j) < 0) :
    let A : Matrix (Fin n) (Fin n) ℝ :=
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
    Matrix.gram ℝ w = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A := by
  classical
  dsimp only
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply, hnorm]
  · rcases (abs_eq hα.1.le).mp (hangle i j hij) with hpos | hneg
    · have hnot : ¬α < 0 := not_lt.mpr hα.1.le
      simp [Matrix.gram_apply, hij, SimpleGraph.adjMatrix_apply, hG, hpos, hnot]
    · simp [Matrix.gram_apply, hij, SimpleGraph.adjMatrix_apply, hG, hneg, hα.1]
      ring
theorem uniform_switching_with_gram_data :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 → ∃ Δ : ℕ,
      ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖v i‖ = 1) →
        (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
        ∃ (σ : Fin n → ℝ) (G : SimpleGraph (Fin n)),
          (∀ i, σ i = 1 ∨ σ i = -1) ∧
          (∀ i, ‖σ i • v i‖ = 1) ∧
          (∀ i j, i ≠ j → |inner ℝ (σ i • v i) (σ j • v j)| = α) ∧
          Function.Injective (fun i => σ i • v i) ∧
          G = SimpleGraph.fromRel (fun i j => inner ℝ (σ i • v i) (σ j • v j) < 0) ∧
          (∀ i j, G.Adj i j ↔ i ≠ j ∧ inner ℝ (σ i • v i) (σ j • v j) < 0) ∧
          (∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) ∧
          (let A : Matrix (Fin n) (Fin n) ℝ :=
            (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
           Matrix.gram ℝ (fun i => σ i • v i) =
             (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
               α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A) := by
  intro α hα
  obtain ⟨Δ, hΔ⟩ := uniform_switching_of_unit_vectors α hα
  refine ⟨Δ, ?_⟩
  intro d n v hnorm hangle
  have hdiag : ∀ i, inner ℝ (v i) (v i) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hnorm i]
    norm_num
  obtain ⟨σ, G, hσ, hG, hdegree⟩ := hΔ d n v hdiag hangle
  have hwnorm : ∀ i, ‖σ i • v i‖ = 1 := fun i =>
    (switching_norm_eq v σ hσ i).trans (hnorm i)
  have hwangle : ∀ i j, i ≠ j → |inner ℝ (σ i • v i) (σ j • v j)| = α :=
    fun i j hij => (switching_abs_inner_eq v σ hσ i j).trans (hangle i j hij)
  exact ⟨σ, G, hσ, hwnorm, hwangle,
    switching_injective_of_unit_angles v σ hσ α hα.2 hnorm hangle,
    switching_negative_graph_eq (fun i => σ i • v i) G hG,
    hG, hdegree,
    switching_gram_eq_of_negative_graph α hα d n (fun i => σ i • v i)
      hwnorm hwangle G hG⟩
end Submission.Helpers
