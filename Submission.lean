import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.ENat.Lattice
import ChallengeDeps
import Submission.Helpers

open EquiangularLinesFixedAngle
open Filter
open scoped RealInnerProductSpace

set_option autoImplicit false

namespace Submission

theorem spectral_order_attained (lambda : ℝ) (hfinite : spectralRadiusOrder lambda < ⊤) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (n : ℕ∞) = spectralRadiusOrder lambda ∧
        (show ENNReal from by
          classical
          exact spectralRadius ℝ (G.adjMatrix ℝ)) = ENNReal.ofReal lambda := by
  classical
  obtain ⟨n, hn⟩ := ENat.exists_eq_iInf (fun n : ℕ =>
    ⨅ (_ : ∃ G : SimpleGraph (Fin n),
      spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda), (n : ℕ∞))
  have hn' :
      (⨅ (_ : ∃ G : SimpleGraph (Fin n),
        spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda), (n : ℕ∞)) =
        spectralRadiusOrder lambda := hn
  by_cases hG : ∃ G : SimpleGraph (Fin n),
      spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda
  · have horder : (n : ℕ∞) = spectralRadiusOrder lambda := by
      simpa only [iInf_pos hG] using hn'
    obtain ⟨G, hG⟩ := hG
    exact ⟨n, G, horder, hG⟩
  · have htop : spectralRadiusOrder lambda = ⊤ := by
      simpa only [iInf_neg hG] using hn'.symm
    exact False.elim ((ne_of_lt hfinite) htop)
theorem configuration_dist_separated (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (d : ℕ) (E : EquiangularLines α d)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ E.carrier) (hy : y ∈ E.carrier)
    (hxy : x ≠ y) : 1 - α < dist x y := by
  have hi : ⟪x, y⟫ ≤ α := by
    calc
      ⟪x, y⟫ ≤ |⟪x, y⟫| := le_abs_self _
      _ = α := E.angle hx hy hxy
  have hs := norm_sub_sq_real x y
  rw [E.norm x hx, E.norm y hy, ← dist_eq_norm] at hs
  have hn := dist_nonneg (x := x) (y := y)
  have hsq : (1 - α) ^ 2 < 2 * (1 - α) := by
    have hp : 0 < (1 - α) * (1 + α) :=
      mul_pos (sub_pos.mpr hα.2) (by linarith only [hα.1])
    nlinarith only [hp]
  apply (sq_lt_sq₀ (sub_nonneg.mpr hα.2.le) hn).mp
  linarith only [hs, hi, hsq]
theorem configuration_cardinality_bounded :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 → ∀ d : ℕ,
      ∃ B : ℕ, ∀ E : EquiangularLines α d, E.carrier.ncard ≤ B := by
  classical
  intro α hα d
  obtain ⟨t, _, ht, hcover⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).finite_cover_balls
      (show 0 < (1 - α) / 2 by linarith [hα.2])
  refine ⟨t.ncard, ?_⟩
  intro E
  have hball : ∀ x ∈ E.carrier, ∃ c ∈ t, dist x c < (1 - α) / 2 := by
    intro x hx
    have hs : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using E.norm x hx
    rcases Set.mem_iUnion₂.mp (hcover hs) with ⟨c, hc, hxc⟩
    exact ⟨c, hc, hxc⟩
  let f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x =>
    if hx : x ∈ E.carrier then (hball x hx).choose else 0
  have hf : ∀ x ∈ E.carrier, f x ∈ t ∧ dist x (f x) < (1 - α) / 2 := by
    intro x hx
    dsimp only [f]
    rw [dif_pos hx]
    exact (hball x hx).choose_spec
  apply Set.ncard_le_ncard_of_injOn f (fun x hx => (hf x hx).1) ?_ ht
  intro x hx y hy hfxy
  by_contra hxy
  have hsep := configuration_dist_separated α hα d E hx hy hxy
  have htri := dist_triangle x (f x) y
  have hfx := (hf x hx).2
  have hfy := (hf y hy).2
  rw [← hfxy, dist_comm y (f x)] at hfy
  linarith only [hsep, htri, hfx, hfy]
theorem configuration_cardinality_le_N :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      ∀ (d : ℕ) (E : EquiangularLinesFixedAngle.EquiangularLines α d),
        E.carrier.ncard ≤ EquiangularLinesFixedAngle.N α d := by
  intro α hα d E
  obtain ⟨B, hB⟩ := configuration_cardinality_bounded α hα d
  have hbounded : BddAbove (Set.range
      (fun F : EquiangularLinesFixedAngle.EquiangularLines α d => F.carrier.ncard)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨F, rfl⟩
    exact hB F
  exact le_ciSup hbounded E
theorem euclidean_gram_rank_le {d n : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : (Matrix.gram ℝ v).rank ≤ d := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let M : Matrix (Fin d) (Fin n) ℝ := Matrix.of (fun i j => b.repr (v j) i)
  have hg : Matrix.gram ℝ v = M.conjTranspose * M :=
    Matrix.gram_eq_conjTranspose_mul b v
  calc
    (Matrix.gram ℝ v).rank = (M.conjTranspose * M).rank := congrArg Matrix.rank hg
    _ ≤ M.rank := Matrix.rank_mul_le_right _ _
    _ ≤ d := by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height M
theorem real_matrix_rank_smul_le {m n : ℕ} (a : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : (a • A).rank ≤ A.rank := by
  rw [Matrix.rank, Matrix.rank]
  apply Submodule.finrank_mono
  rintro x ⟨c, rfl⟩
  refine ⟨a • c, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.smul_mulVec]
theorem upper_spectralRadius_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℝ) (e : κ ≃ ι) :
    spectralRadius ℝ (A.submatrix e e) = spectralRadius ℝ A := by
  have hs : spectrum ℝ (A.submatrix e e) = spectrum ℝ A :=
    AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ e.symm) A
  simp only [spectralRadius_eq_of_unital, hs]
theorem upper_spectral_order_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (lambda : ℝ)
    (hG : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda) :
    spectralRadiusOrder lambda ≤ (Fintype.card ι : ℕ∞) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let H := G.comap e
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hA : H.adjMatrix ℝ = (G.adjMatrix ℝ).submatrix e e := by
    ext i j
    simp [H, SimpleGraph.adjMatrix_apply]
  have hH : spectralRadius ℝ (H.adjMatrix ℝ) = ENNReal.ofReal lambda := by
    rw [hA, upper_spectralRadius_relabel]
    exact hG
  unfold spectralRadiusOrder
  exact iInf_le_of_le (Fintype.card ι) (iInf_le_of_le ⟨H, hH⟩ le_rfl)
theorem upper_eigenspace_add_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lambda : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) +
      (lambda • (1 : Matrix ι ι ℝ) - A).rank = Fintype.card ι := by
  have hker : LinearMap.ker (lambda • (1 : Matrix ι ι ℝ) - A).mulVecLin =
      Module.End.eigenspace A.mulVecLin lambda := by
    ext x
    rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    exact eq_comm
  have h := LinearMap.finrank_range_add_finrank_ker
    (lambda • (1 : Matrix ι ι ℝ) - A).mulVecLin
  rw [hker, ← Matrix.rank, Module.finrank_fintype_fun_eq_card] at h
  omega
theorem upper_eigenspace_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℝ) (e : κ ≃ ι) (lambda : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (A.submatrix e e).mulVecLin lambda) =
      Module.finrank ℝ (Module.End.eigenspace A.mulVecLin lambda) := by
  have h1 := upper_eigenspace_add_rank (A.submatrix e e) lambda
  have h2 := upper_eigenspace_add_rank A lambda
  have heq : lambda • (1 : Matrix κ κ ℝ) - A.submatrix e e =
      (lambda • (1 : Matrix ι ι ℝ) - A).submatrix e e := by
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [heq, Matrix.rank_submatrix, Fintype.card_congr e] at h1
  omega
theorem upper_gram_psd_rank (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d n : ℕ)
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hgram : Matrix.gram ℝ v = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A) :
    let P := ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ : Fin n => (1 : ℝ))
    P.PosSemidef ∧ P.rank ≤ d := by
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have heq : ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) =
      (1 / (2 * α)) • Matrix.gram ℝ v := by
    rw [hgram]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hα0]
    ring
  dsimp only
  rw [heq]
  exact ⟨(Matrix.posSemidef_gram ℝ v).smul (by
      have hp := hα.1
      positivity),
    (real_matrix_rank_smul_le _ _).trans (euclidean_gram_rank_le v)⟩
theorem upper_psd_eigenvalue_exception {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (lambda : ℝ)
    (hP : (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef) :
    ∃ j : ι, ∀ i : ι, i ≠ j → hA.eigenvalues i ≤ lambda := by
  classical
  have hone (i : ι) : dotProduct (hA.eigenvectorBasis i).ofLp
      (hA.eigenvectorBasis i).ofLp = 1 := by
    have h := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      if_pos rfl, ite_true] using h
  have hsum (i : ι) (hi : lambda < hA.eigenvalues i) :
      (∑ k, (hA.eigenvectorBasis i).ofLp k) ≠ 0 := by
    intro hz
    have h := hP.dotProduct_mulVec_nonneg (hA.eigenvectorBasis i).ofLp
    simp only [star_trivial] at h
    rw [Helpers.component_rank_one_quadratic, hz, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hA.mulVec_eigenvectorBasis, dotProduct_smul,
      hone, smul_eq_mul] at h
    simp only [smul_eq_mul, mul_one] at h
    linarith
  by_cases hex : ∃ j, lambda < hA.eigenvalues j
  · obtain ⟨j, hj⟩ := hex
    refine ⟨j, ?_⟩
    intro i hij
    by_contra hi
    have hi' : lambda < hA.eigenvalues i := lt_of_not_ge hi
    let x := (hA.eigenvectorBasis j).ofLp
    let y := (hA.eigenvectorBasis i).ofLp
    let a := ∑ k, x k
    let b := ∑ k, y k
    let z := b • x - a • y
    have hx : A.mulVec x = hA.eigenvalues j • x := hA.mulVec_eigenvectorBasis j
    have hy : A.mulVec y = hA.eigenvalues i • y := hA.mulVec_eigenvectorBasis i
    have hxy : dotProduct x y = 0 := by
      have h := hA.eigenvectorBasis.orthonormal.inner_eq_zero hij.symm
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct_comm] using h
    have hyx : dotProduct y x = 0 := by rw [dotProduct_comm, hxy]
    have hzsum : ∑ k, z k = 0 := by
      simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
      change b * a - a * b = 0
      ring
    have hzn : dotProduct z z = b ^ 2 + a ^ 2 := by
      simp only [z, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, hxy, hyx, smul_eq_mul]
      rw [hone j, hone i]
      ring
    have hzq : dotProduct z (A.mulVec z) =
        b ^ 2 * hA.eigenvalues j + a ^ 2 * hA.eigenvalues i := by
      simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul,
        hx, hy, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hxy, hyx]
      rw [hone j, hone i]
      ring
    have h := hP.dotProduct_mulVec_nonneg z
    simp only [star_trivial] at h
    rw [Helpers.component_rank_one_quadratic, hzsum, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hzn, hzq] at h
    have h1 := mul_pos (sq_pos_of_ne_zero (hsum i hi')) (sub_pos.mpr hj)
    have h2 := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hi'.le)
    change 0 < b ^ 2 * (hA.eigenvalues j - lambda) at h1
    nlinarith only [h, h1, h2]
  · exact ⟨Classical.choice ‹Nonempty ι›, fun i _ => le_of_not_gt (fun hi => hex ⟨i, hi⟩)⟩
theorem upper_rank_one_submatrix {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (lambda : ℝ) (e : κ → ι) (he : Function.Injective e) :
    (lambda • (1 : Matrix ι ι ℝ) - A +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).submatrix e e =
    lambda • (1 : Matrix κ κ ℝ) - A.submatrix e e +
      (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext i j
  simp [Matrix.one_apply, he.eq_iff]
theorem upper_uniform_connected_multiplicity (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (G : SimpleGraph ι) [DecidableRel G.Adj] (lambda : ℝ),
      M ≤ Fintype.card ι → 0 < lambda → G.Connected →
      (∀ i, ({j | G.Adj i j} : Set ι).ncard ≤ Δ) →
      (lambda • (1 : Matrix ι ι ℝ) - G.adjMatrix ℝ +
        (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef →
      (Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) : ℝ) ≤
        ε * (Fintype.card ι : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := Helpers.uniform_second_eigenvalue_multiplicity Δ ε hε
  refine ⟨M, ?_⟩
  intro ι _ _ G _ lambda hsize hlam hG hdegree hP
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let H := G.comap e
  let : DecidableRel H.Adj := Classical.decRel H.Adj
  have hA : H.adjMatrix ℝ = (G.adjMatrix ℝ).submatrix e e := by
    ext i j
    simp [H, SimpleGraph.adjMatrix_apply]
  have hH : H.Connected := (SimpleGraph.Iso.comap e G).connected_iff.mpr hG
  let : Nonempty (Fin (Fintype.card ι)) := hH.nonempty
  have hdeg : ∀ i, ({j | H.Adj i j} : Set (Fin (Fintype.card ι))).ncard ≤ Δ := by
    intro i
    apply le_trans _ (hdegree (e i))
    exact Set.ncard_le_ncard_of_injOn e (fun j hj => hj)
      (fun _ _ _ _ he => e.injective he)
  have hPH : (lambda • (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ) -
      H.adjMatrix ℝ + (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef := by
    rw [hA, ← upper_rank_one_submatrix _ _ e e.injective]
    exact hP.submatrix e
  have hHerm : (H.adjMatrix ℝ).IsHermitian := by
    change (H.adjMatrix ℝ).conjTranspose = H.adjMatrix ℝ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, H.transpose_adjMatrix]
  have hb := hM (Fintype.card ι) H lambda hsize hlam hH hdeg hHerm
    (upper_psd_eigenvalue_exception _ hHerm lambda hPH)
  rw [hA, upper_eigenspace_relabel] at hb
  exact hb
noncomputable def upperComponentRadius {n : ℕ} (G : SimpleGraph (Fin n))
    (C : G.ConnectedComponent) : ENNReal := by
  classical
  letI : Fintype C.supp := Fintype.ofFinite C.supp
  letI : DecidableEq C.supp := Classical.decEq C.supp
  letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel C.toSimpleGraph.Adj
  exact spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ)
theorem upper_graph_bound_cases (Δ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (n d : ℕ) (G : SimpleGraph (Fin n))
      (lambda : ℝ), 0 < lambda →
      (∀ i, ({j | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) →
      let A : Matrix (Fin n) (Fin n) ℝ :=
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
      let P := lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - A +
        (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))
      P.PosSemidef → P.rank ≤ d →
      ((¬ ∃ C, ENNReal.ofReal lambda < upperComponentRadius G C) ∧
        P.rank = if ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
          Set G.ConnectedComponent).ncard = 0 then n else
            n + 1 - ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
              Set G.ConnectedComponent).ncard) ∨
      (n : ℝ) ≤ (d : ℝ) + 1 + M + ε * n := by
  classical
  obtain ⟨M, hM⟩ := upper_uniform_connected_multiplicity Δ ε hε
  refine ⟨M, ?_⟩
  intro n d G lambda hlam hdeg
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  dsimp only
  let P := lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ +
    (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))
  intro hP hrank
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let (C : G.ConnectedComponent) : Fintype C.supp := Fintype.ofFinite _
  let (C : G.ConnectedComponent) : DecidableEq C.supp := Classical.decEq _
  let (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hc := Helpers.component_rank_one_accounting n G lambda hlam hP
  change
    ((¬ ∃ C, ENNReal.ofReal lambda < upperComponentRadius G C) →
      P.rank = if ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
        Set G.ConnectedComponent).ncard = 0 then n else
          n + 1 - ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
            Set G.ConnectedComponent).ncard) ∧
    ((∃ C, ENNReal.ofReal lambda < upperComponentRadius G C) →
      ∃ C, ENNReal.ofReal lambda < upperComponentRadius G C ∧
        (∀ D, D ≠ C → upperComponentRadius G D < ENNReal.ofReal lambda) ∧
        Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin lambda) =
          Module.finrank ℝ (Module.End.eigenspace
            (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) ∧
        n ≤ P.rank + 1 + Module.finrank ℝ (Module.End.eigenspace
          (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda)) at hc
  by_cases hex : ∃ C, ENNReal.ofReal lambda < upperComponentRadius G C
  · right
    obtain ⟨C, _, _, _, hn⟩ := hc.2 hex
    have hcard : Nat.card C = Nat.card C.supp := Nat.card_congr
      { toFun := fun i => ⟨i.val, i.property⟩
        invFun := fun i => ⟨i.val, i.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hCn : Fintype.card C.supp ≤ n := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective (Subtype.val : C.supp → Fin n) Subtype.val_injective
    have hm : (Module.finrank ℝ (Module.End.eigenspace
        (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) : ℝ) ≤ M + ε * n := by
      by_cases hsize : M ≤ Fintype.card C.supp
      · have hsub : (G.adjMatrix ℝ).submatrix (Subtype.val : C.supp → Fin n)
            Subtype.val = C.toSimpleGraph.adjMatrix ℝ := by
          ext i j
          change (G.adjMatrix ℝ) i.val j.val = (G.induce C.supp).adjMatrix ℝ i j
          simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.induce_adj]
        have hPC : (lambda • (1 : Matrix C.supp C.supp ℝ) -
            C.toSimpleGraph.adjMatrix ℝ +
            (1 / 2 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))).PosSemidef := by
          have hh := hP.submatrix (Subtype.val : C.supp → Fin n)
          rw [upper_rank_one_submatrix _ _ _ Subtype.val_injective] at hh
          convert hh using 1
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
            Matrix.smul_apply, smul_eq_mul]
          congr 2
        have hh := hM C.toSimpleGraph lambda hsize hlam C.connected_toSimpleGraph
          (Helpers.induced_graph_degree_bound G C.supp Δ hdeg) hPC
        simp only [← Nat.card_eq_fintype_card] at hh
        rw [hcard] at hh
        have hcast : (Fintype.card C.supp : ℝ) ≤ n := by exact_mod_cast hCn
        simp only [← Nat.card_eq_fintype_card] at hcast
        have hmul := mul_le_mul_of_nonneg_left hcast hε.le
        have hMn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
        linarith
      · have hsmall : Module.finrank ℝ (Module.End.eigenspace
            (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) ≤ M := by
          have hh := Submodule.finrank_le (Module.End.eigenspace
            (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda)
          rw [Module.finrank_fintype_fun_eq_card] at hh
          simp only [← Nat.card_eq_fintype_card] at hh hsize
          rw [hcard] at hh
          omega
        have hh : (Module.finrank ℝ (Module.End.eigenspace
            (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) : ℝ) ≤ M := by
          exact_mod_cast hsmall
        have hprod : 0 ≤ ε * (n : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
        linarith
    have hn' : (n : ℝ) ≤ (d : ℝ) + 1 + Module.finrank ℝ (Module.End.eigenspace
        (C.toSimpleGraph.adjMatrix ℝ).mulVecLin lambda) := by
      exact_mod_cast hn.trans (Nat.add_le_add_right (Nat.add_le_add_right hrank 1) _)
    linarith
  · exact Or.inl ⟨hex, hc.1 hex⟩
theorem upper_critical_count_mul_le (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ)
    (q : ℕ) (hq : (q : ℕ∞) ≤ spectralRadiusOrder lambda) :
    q * ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
      Set G.ConnectedComponent).ncard ≤ n := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let (C : G.ConnectedComponent) : Fintype C.supp := Fintype.ofFinite _
  let (C : G.ConnectedComponent) : DecidableEq C.supp := Classical.decEq _
  let (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let S := Finset.univ.filter (fun C => upperComponentRadius G C = ENNReal.ofReal lambda)
  have ht : ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
      Set G.ConnectedComponent).ncard = S.card := by
    simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, S]
  have hsize (C : G.ConnectedComponent) (hC : C ∈ S) : q ≤ Fintype.card C.supp := by
    have hr : spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ) = ENNReal.ofReal lambda := by
      exact (Finset.mem_filter.mp hC).2
    have hh := hq.trans (upper_spectral_order_le C.toSimpleGraph lambda hr)
    have hcard : Fintype.card C = Fintype.card C.supp := Fintype.card_congr
      { toFun := fun i => ⟨i.val, i.property⟩
        invFun := fun i => ⟨i.val, i.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [hcard] at hh
    exact_mod_cast hh
  have htotal : (∑ C : G.ConnectedComponent, Fintype.card C.supp) = n := by
    have hh := Helpers.component_sum_by_components G (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fin] at hh
    exact_mod_cast hh
  rw [ht]
  calc
    q * S.card = ∑ C ∈ S, q := by simp [mul_comm]
    _ ≤ ∑ C ∈ S, Fintype.card C.supp := Finset.sum_le_sum hsize
    _ ≤ ∑ C : G.ConnectedComponent, Fintype.card C.supp :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = n := htotal
theorem upper_no_critical_of_infinite (n : ℕ) (G : SimpleGraph (Fin n)) (lambda : ℝ)
    (htop : spectralRadiusOrder lambda = ⊤) :
    ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
      Set G.ConnectedComponent).ncard = 0 := by
  classical
  have hempty : ({C | upperComponentRadius G C = ENNReal.ofReal lambda} :
      Set G.ConnectedComponent) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro C hC
    let : Fintype C.supp := Fintype.ofFinite _
    let : DecidableEq C.supp := Classical.decEq _
    let : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
    have hr : spectralRadius ℝ (C.toSimpleGraph.adjMatrix ℝ) = ENNReal.ofReal lambda := hC
    have hh := upper_spectral_order_le C.toSimpleGraph lambda hr
    rw [htop] at hh
    exact (not_le_of_gt (ENat.natCast_lt_top (Fintype.card C))) hh
  rw [hempty, Set.ncard_empty]
theorem upper_rank_count_floor (n d q t r : ℕ) (hq : 2 ≤ q) (hd : q ≤ d)
    (ht : q * t ≤ n) (hr : r = if t = 0 then n else n + 1 - t) (hrd : r ≤ d) :
    n ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hdR : (q : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < (q : ℝ) - 1 := by linarith
  apply Nat.le_floor
  apply (le_div_iff₀ hden).mpr
  by_cases hz : t = 0
  · rw [hz, if_pos rfl] at hr
    have hnd : n ≤ d := by omega
    have hnR : (n : ℝ) ≤ d := by exact_mod_cast hnd
    nlinarith
  · rw [if_neg hz] at hr
    have htn : t ≤ n := by nlinarith
    have hn : n + 1 ≤ d + t := by omega
    have hnR : (n : ℝ) + 1 ≤ (d : ℝ) + t := by exact_mod_cast hn
    have htR : (q : ℝ) * t ≤ (n : ℝ) := by exact_mod_cast ht
    nlinarith
theorem upper_N_le_of_unit_bound (α : ℝ) (d B : ℕ)
    (hB : ∀ (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) → n ≤ B) : N α d ≤ B := by
  classical
  apply ciSup_le'
  intro E
  by_cases hz : E.carrier.ncard = 0
  · rw [hz]
    exact Nat.zero_le _
  · have hfin := Set.finite_of_ncard_ne_zero hz
    let : Fintype E.carrier := hfin.fintype
    let e : Fin (Fintype.card E.carrier) ≃ E.carrier := (Fintype.equivFin _).symm
    have hh := hB (Fintype.card E.carrier) (fun i => (e i).val)
      (fun i => E.norm (e i).val (e i).property)
      (fun i j hij => E.angle (e i).property (e j).property (by
        intro he
        exact hij (e.injective (Subtype.ext he))))
    rwa [Set.fintypeCard_eq_ncard] at hh
theorem upper_unit_vector_bound_cases (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ (d n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → |inner ℝ (v i) (v j)| = α) →
      (∃ G : SimpleGraph (Fin n),
        (if ({C | upperComponentRadius G C = ENNReal.ofReal ((1 - α) / (2 * α))} :
          Set G.ConnectedComponent).ncard = 0 then n else
          n + 1 - ({C | upperComponentRadius G C = ENNReal.ofReal ((1 - α) / (2 * α))} :
            Set G.ConnectedComponent).ncard) ≤ d) ∨
      (n : ℝ) ≤ (d : ℝ) + 1 + M + ε * n := by
  classical
  obtain ⟨Δ, hΔ⟩ := Helpers.uniform_switching_with_gram_data α hα
  obtain ⟨M, hM⟩ := upper_graph_bound_cases Δ ε hε
  refine ⟨M, ?_⟩
  intro d n v hnorm hangle
  obtain ⟨σ, G, _, _, _, _, _, _, hdegree, hgram⟩ := hΔ d n v hnorm hangle
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hP := upper_gram_psd_rank α hα d n (fun i => σ i • v i) (G.adjMatrix ℝ) hgram
  have hlam : 0 < (1 - α) / (2 * α) :=
    div_pos (sub_pos.mpr hα.2) (mul_pos (by norm_num) hα.1)
  rcases hM n d G _ hlam hdegree hP.1 hP.2 with hc | hb
  · left
    refine ⟨G, ?_⟩
    rw [← hc.2]
    exact hP.2
  · exact Or.inr hb
theorem upper_absorb_finite (n d q M : ℕ) (hq : 2 ≤ q)
    (hd : 2 * q * (M + 2) ≤ d)
    (hb : (n : ℝ) ≤ (d : ℝ) + 1 + M + (1 / (2 * (q : ℝ))) * n) :
    n ≤ ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := by linarith
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hdR : 2 * (q : ℝ) * ((M : ℝ) + 2) ≤ d := by exact_mod_cast hd
  have hcancel : (2 * (q : ℝ)) * ((1 / (2 * (q : ℝ))) * n) = n := by
    field_simp
    <;> ring
  have hbase : (n : ℝ) * (2 * (q : ℝ) - 1) ≤
      2 * (q : ℝ) * ((d : ℝ) + (M : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (q : ℝ) by positivity)
    simp only [mul_add, hcancel] at hh
    nlinarith only [hh]
  have hthreshold := mul_le_mul_of_nonneg_left hdR hqpos.le
  have hcompare : 2 * (q : ℝ) * ((d : ℝ) + (M : ℝ) + 1) * ((q : ℝ) - 1) ≤
      (q : ℝ) * ((d : ℝ) - 1) * (2 * (q : ℝ) - 1) := by
    nlinarith [mul_nonneg hqpos.le hM]
  apply Nat.le_floor
  apply (le_div_iff₀ (show 0 < (q : ℝ) - 1 by linarith)).mpr
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * (q : ℝ) - 1 by linarith)).mp
  calc
    (n : ℝ) * ((q : ℝ) - 1) * (2 * (q : ℝ) - 1) =
        ((n : ℝ) * (2 * (q : ℝ) - 1)) * ((q : ℝ) - 1) := by ring
    _ ≤ (2 * (q : ℝ) * ((d : ℝ) + (M : ℝ) + 1)) * ((q : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hbase (by linarith)
    _ ≤ (q : ℝ) * ((d : ℝ) - 1) * (2 * (q : ℝ) - 1) := hcompare
theorem upper_absorb_infinite (n d M : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hd : 2 * ((M : ℝ) + 1) / ε ≤ (d : ℝ))
    (hb : (n : ℝ) ≤ (d : ℝ) + 1 + M + (ε / (2 * (1 + ε))) * n) :
    (n : ℝ) ≤ (1 + ε) * d := by
  let δ := ε / (2 * (1 + ε))
  have hden : 0 < 2 * (1 + ε) := by positivity
  have hδ : δ < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hcoef : (1 - δ) * (1 + ε) = 1 + ε / 2 := by
    dsimp [δ]
    field_simp
    <;> ring
  have hconst : (M : ℝ) + 1 ≤ ε * (d : ℝ) / 2 := by
    have hh := (div_le_iff₀ hε).mp hd
    linarith
  apply (mul_le_mul_iff_right₀ (sub_pos.mpr hδ)).mp
  calc
    (1 - δ) * (n : ℝ) ≤ (d : ℝ) + 1 + M := by
      change (n : ℝ) ≤ (d : ℝ) + 1 + M + δ * n at hb
      linarith
    _ ≤ (1 + ε / 2) * (d : ℝ) := by nlinarith only [hconst]
    _ = (1 - δ) * ((1 + ε) * (d : ℝ)) := by rw [← mul_assoc, hcoef]
theorem lower_gram_configuration (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (n d : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (hrank : M.rank ≤ d) (hdiag : ∀ i, M i i = 1)
    (hoff : ∀ i j, i ≠ j → |M i j| = α) : n ≤ N α d := by
  classical
  obtain ⟨v, hv⟩ := Helpers.positive_semidefinite_gram_realization n d M hM hrank
  have hinner : ∀ i j, ⟪v i, v j⟫ = M i j := by
    intro i j
    exact congrFun (congrFun hv i) j
  have hnorm : ∀ i, ‖v i‖ = 1 := by
    intro i
    have h := hinner i i
    rw [hdiag, inner_self_eq_norm_sq_to_K] at h
    change ‖v i‖ ^ 2 = 1 at h
    nlinarith [norm_nonneg (v i)]
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have h := hoff i j hne
    rw [← hinner, hij, inner_self_eq_norm_sq_to_K, hnorm] at h
    norm_num at h
    exact (ne_of_lt hα.2) h.symm
  let E : EquiangularLines α d :=
    { carrier := Set.range v
      norm := by rintro x ⟨i, rfl⟩; exact hnorm i
      angle := by
        rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hxy
        rw [hinner]
        exact hoff i j (fun hij => hxy (congrArg v hij)) }
  have hc : E.carrier.ncard = n := by
    exact (Set.ncard_range_of_injective hinj).trans (by simp)
  rw [← hc]
  exact configuration_cardinality_le_N α hα d E
theorem lower_all_ones_posSemidef {ι : Type*} [Fintype ι] :
    (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
  classical
  simpa [Matrix.vecMulVec] using
    Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ))
theorem configuration_dimension_lower_bound (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (d : ℕ) : d ≤ N α d := by
  classical
  let M : Matrix (Fin d) (Fin d) ℝ :=
    (1 - α) • 1 + α • Matrix.of (fun _ _ => (1 : ℝ))
  apply lower_gram_configuration α hα d d M
  · exact (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hα.2.le)).add
      (lower_all_ones_posSemidef.smul hα.1.le)
  · simpa using Matrix.rank_le_card_height M
  · intro i
    simp [M]
  · intro i j hij
    simp [M, Matrix.one_apply, hij, abs_of_pos hα.1]
theorem lower_perron_abs_quadratic_bound {n : ℕ} (G : SimpleGraph (Fin n))
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
theorem lower_perron_nonnegative_top_eigenvector {n : ℕ} (G : SimpleGraph (Fin n))
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
    exact (le_abs_self _).trans (lower_perron_abs_quadratic_bound G q.ofLp)
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
theorem lower_perron_spectralRadius_eq {n : ℕ} (G : SimpleGraph (Fin n))
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
    have hb := (lower_perron_abs_quadratic_bound G q.ofLp).trans (hbound (fun j => |q j|))
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
theorem lower_graph_order_ge_two (lambda : ℝ) (hlambda : 0 < lambda)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hradius : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda) : 2 ≤ n := by
  classical
  by_contra hn
  have hsmall : n ≤ 1 := by omega
  letI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hsmall
  have hzero : G.adjMatrix ℝ = 0 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp
  rw [hzero, spectrum.spectralRadius_zero] at hradius
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr hlambda)) hradius.symm
theorem lower_graph_shift_psd_rank (lambda : ℝ) (hlambda : 0 < lambda)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hradius : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lambda) :
    (lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ).PosSemidef ∧
    (lambda • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ).rank ≤ n - 1 := by
  classical
  have hn := lower_graph_order_ge_two lambda hlambda n G hradius
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨rho, p, hrho, _, hp0, heig, hbound⟩ := lower_perron_nonnegative_top_eigenvector G
  have hr := lower_perron_spectralRadius_eq G rho hrho p hp0 heig hbound
  have heq : rho = lambda := by
    have h := congrArg ENNReal.toReal (hr.symm.trans hradius)
    simpa only [ENNReal.toReal_ofReal hrho, ENNReal.toReal_ofReal hlambda.le] using h
  subst rho
  let B : Matrix (Fin n) (Fin n) ℝ := lambda • 1 - G.adjMatrix ℝ
  have hA : (G.adjMatrix ℝ).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, G.adj_comm]
  have hB : B.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_one.smul (show IsSelfAdjoint lambda from rfl)).sub hA)
    intro x
    simp only [B, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul]
    exact sub_nonneg.mpr (hbound x)
  refine ⟨hB, ?_⟩
  have hpker : p ∈ LinearMap.ker B.mulVecLin := by
    rw [LinearMap.mem_ker]
    simp only [B, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, heig, sub_self]
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker B.mulVecLin) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hzero
    rw [hzero, Submodule.mem_bot] at hpker
    exact hp0 hpker
  have hdim := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hdim' : B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim
  change B.rank ≤ n - 1
  omega
theorem lower_graph_factor (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hradius : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal ((1 - α) / (2 * α))) :
    ∃ B : Matrix (Fin (n - 1)) (Fin n) ℝ,
      B.conjTranspose * B = (1 - α) • 1 - (2 * α) • G.adjMatrix ℝ := by
  classical
  have hαpos : 0 < α := hα.1
  have hlambda : 0 < (1 - α) / (2 * α) :=
    div_pos (sub_pos.mpr hα.2) (by positivity)
  obtain ⟨hpsd, hrank⟩ := lower_graph_shift_psd_rank _ hlambda n G hradius
  have heq : (2 * α) • (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      G.adjMatrix ℝ) = (1 - α) • 1 - (2 * α) • G.adjMatrix ℝ := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ (show 2 * α ≠ 0 by positivity)]
  obtain ⟨v, hv⟩ := Helpers.positive_semidefinite_gram_realization n (n - 1)
    _ (hpsd.smul (show 0 ≤ 2 * α by positivity))
    ((real_matrix_rank_smul_le _ _).trans hrank)
  let b := EuclideanSpace.basisFun (Fin (n - 1)) ℝ
  refine ⟨Matrix.of (fun i j => b.repr (v j) i), ?_⟩
  exact (Matrix.gram_eq_conjTranspose_mul b v).symm.trans (hv.trans heq)
theorem lower_gram_configuration_fintype {ι : Type*} [Fintype ι]
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (d : ℕ) (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) (hrank : M.rank ≤ d) (hdiag : ∀ i, M i i = 1)
    (hoff : ∀ i j, i ≠ j → |M i j| = α) : Fintype.card ι ≤ N α d := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  apply lower_gram_configuration α hα _ d (M.submatrix e e) (hM.submatrix e)
  · simpa only [Matrix.rank_submatrix] using hrank
  · intro i; exact hdiag (e i)
  · intro i j hij; exact hoff (e i) (e j) (e.injective.ne hij)
theorem lower_matrix_rank_add_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  classical
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
theorem lower_graph_copies_configuration (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hradius : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal ((1 - α) / (2 * α)))
    (t r : ℕ) : n * t + r ≤ N α ((n - 1) * t + r + 1) := by
  classical
  obtain ⟨B, hB⟩ := lower_graph_factor α hα n G hradius
  let S : Matrix (Fin r) (Fin r) ℝ := Real.sqrt (1 - α) • 1
  have hS : S.conjTranspose * S = (1 - α) • 1 := by
    simp only [S, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [Real.mul_self_sqrt (sub_nonneg.mpr hα.2.le)]
  let C : Matrix ((Fin (n - 1) × Fin t) ⊕ Fin r) ((Fin n × Fin t) ⊕ Fin r) ℝ :=
    Matrix.fromBlocks (Matrix.blockDiagonal (fun _ : Fin t => B)) 0 0 S
  let D : Matrix ((Fin n × Fin t) ⊕ Fin r) ((Fin n × Fin t) ⊕ Fin r) ℝ :=
    Matrix.fromBlocks
      (Matrix.blockDiagonal (fun _ : Fin t => (1 - α) • 1 - (2 * α) • G.adjMatrix ℝ))
      0 0 ((1 - α) • 1)
  have hC : C.conjTranspose * C = D := by
    dsimp only [C, D]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, hB, hS]
  let J : Matrix ((Fin n × Fin t) ⊕ Fin r) ((Fin n × Fin t) ⊕ Fin r) ℝ :=
    Matrix.of (fun _ _ => 1)
  let M := C.conjTranspose * C + α • J
  have hM : M.PosSemidef :=
    (Matrix.posSemidef_conjTranspose_mul_self C).add
      (lower_all_ones_posSemidef.smul hα.1.le)
  have hrank : M.rank ≤ (n - 1) * t + r + 1 := by
    have hJ : (α • J).rank ≤ 1 := by
      have heq : α • J = Matrix.vecMulVec (fun _ => α) (fun _ => (1 : ℝ)) := by
        ext i j; simp [J, Matrix.vecMulVec]
      rw [heq]
      exact Matrix.rank_vecMulVec_le _ _
    calc
      M.rank ≤ (C.conjTranspose * C).rank + (α • J).rank := lower_matrix_rank_add_le _ _
      _ ≤ C.rank + 1 := Nat.add_le_add (Matrix.rank_mul_le_right _ _) hJ
      _ ≤ (n - 1) * t + r + 1 := by
        have hc := Matrix.rank_le_card_height C
        simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hc
        omega
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    rw [show M = D + α • J from congrArg (fun X => X + α • J) hC]
    rcases i with ⟨i, a⟩ | i <;>
      simp [D, J, Matrix.blockDiagonal_apply, Matrix.one_apply] <;> ring
  have hoff : ∀ i j, i ≠ j → |M i j| = α := by
    intro i j hij
    rw [show M = D + α • J from congrArg (fun X => X + α • J) hC]
    rcases i with ⟨i, a⟩ | i <;> rcases j with ⟨j, b⟩ | j
    · by_cases hab : a = b
      · have hne : i ≠ j := by intro h; subst j; subst b; exact hij rfl
        by_cases hadj : G.Adj i j
        · simp [D, J, Matrix.blockDiagonal_apply, hab, hne, hadj]
          simpa only [show -(2 * α) + α = -α by ring, abs_neg, abs_of_pos hα.1]
        · simp [D, J, Matrix.blockDiagonal_apply, hab, hne, hadj, abs_of_pos hα.1]
      · simp [D, J, Matrix.blockDiagonal_apply, hab, abs_of_pos hα.1]
    · simp [D, J, abs_of_pos hα.1]
    · simp [D, J, abs_of_pos hα.1]
    · have hne : i ≠ j := by intro h; subst j; exact hij rfl
      simp [D, J, hne, abs_of_pos hα.1]
  have h := lower_gram_configuration_fintype α hα _ M hM hrank hdiag hoff
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using h
theorem lower_floor_count (q d : ℕ) (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ⌊(q * (d - 1) : ℝ) / (q - 1 : ℝ)⌋₊ =
      q * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) := by
  exact Helpers.lower_floor_count_real_subtraction q d hq hd
theorem configuration_lower_bounds :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      let k := spectralRadiusOrder ((1 - α) / (2 * α))
      (∀ d : ℕ, d ≤ N α d) ∧
      (k < ⊤ → ∀ᶠ (d : ℕ) in Filter.atTop,
        ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊ ≤ N α d) := by
  classical
  intro α hα
  refine ⟨configuration_dimension_lower_bound α hα, ?_⟩
  intro hfinite
  obtain ⟨q, G, hq, hradius⟩ := spectral_order_attained _ hfinite
  have hαpos : 0 < α := hα.1
  have hlambda : 0 < (1 - α) / (2 * α) :=
    div_pos (sub_pos.mpr hα.2) (by positivity)
  have hqge := lower_graph_order_ge_two _ hlambda q G hradius
  have hqn : (spectralRadiusOrder ((1 - α) / (2 * α))).toNat = q := by
    rw [← hq, ENat.toNat_natCast]
  apply Filter.eventually_atTop.mpr
  refine ⟨1, ?_⟩
  intro d hd
  rw [hqn, lower_floor_count q d hqge hd]
  have hc := lower_graph_copies_configuration α hα q G hradius
    ((d - 1) / (q - 1)) ((d - 1) % (q - 1))
  have hdim : (q - 1) * ((d - 1) / (q - 1)) + (d - 1) % (q - 1) + 1 = d := by
    rw [Nat.div_add_mod]
    omega
  rwa [hdim] at hc
theorem configuration_upper_bounds :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      let k := spectralRadiusOrder ((1 - α) / (2 * α))
      (k < ⊤ → ∀ᶠ (d : ℕ) in Filter.atTop,
        N α d ≤ ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
      (k = ⊤ → ∀ ε : ℝ, 0 < ε → ∀ᶠ (d : ℕ) in Filter.atTop,
        (N α d : ℝ) ≤ (1 + ε) * (d : ℝ)) := by
  classical
  intro α hα
  have hlam : 0 < (1 - α) / (2 * α) :=
    div_pos (sub_pos.mpr hα.2) (mul_pos (by norm_num) hα.1)
  constructor
  · intro hfinite
    obtain ⟨q, H, hqorder, hradius⟩ := spectral_order_attained _ hfinite
    have hqge : 2 ≤ q := lower_graph_order_ge_two _ hlam q H hradius
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hqnat : (spectralRadiusOrder ((1 - α) / (2 * α))).toNat = q := by
      rw [← hqorder, ENat.toNat_natCast]
    obtain ⟨M, hM⟩ := upper_unit_vector_bound_cases α hα
      (1 / (2 * (q : ℝ))) (by positivity)
    apply Filter.eventually_atTop.mpr
    refine ⟨max q (2 * q * (M + 2)), ?_⟩
    intro d hd
    have hdq : q ≤ d := (le_max_left _ _).trans hd
    have hdM : 2 * q * (M + 2) ≤ d := (le_max_right _ _).trans hd
    rw [hqnat]
    apply upper_N_le_of_unit_bound
    intro n v hnorm hangle
    rcases hM d n v hnorm hangle with ⟨G, hc⟩ | hb
    · let t := ({C | upperComponentRadius G C = ENNReal.ofReal ((1 - α) / (2 * α))} :
        Set G.ConnectedComponent).ncard
      have ht : q * t ≤ n := upper_critical_count_mul_le n G _ q hqorder.le
      exact upper_rank_count_floor n d q t (if t = 0 then n else n + 1 - t)
        hqge hdq ht rfl hc
    · exact upper_absorb_finite n d q M hqge hdM hb
  · intro htop ε hε
    have hδ : 0 < ε / (2 * (1 + ε)) := div_pos hε (by positivity)
    obtain ⟨M, hM⟩ := upper_unit_vector_bound_cases α hα _ hδ
    obtain ⟨L, hL⟩ := exists_nat_gt (2 * ((M : ℝ) + 1) / ε)
    apply Filter.eventually_atTop.mpr
    refine ⟨L, ?_⟩
    intro d hd
    have hdR : 2 * ((M : ℝ) + 1) / ε ≤ (d : ℝ) := by
      have hcast : (L : ℝ) ≤ d := by exact_mod_cast hd
      exact hL.le.trans hcast
    have hbound : N α d ≤ ⌊(1 + ε) * (d : ℝ)⌋₊ := by
      apply upper_N_le_of_unit_bound
      intro n v hnorm hangle
      apply Nat.le_floor
      rcases hM d n v hnorm hangle with ⟨G, hc⟩ | hb
      · rw [upper_no_critical_of_infinite n G _ htop, if_pos rfl] at hc
        have hnR : (n : ℝ) ≤ d := by exact_mod_cast hc
        have hprod : 0 ≤ ε * (d : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
        nlinarith
      · exact upper_absorb_infinite n d M ε hε hdR hb
    exact (show (N α d : ℝ) ≤ (⌊(1 + ε) * (d : ℝ)⌋₊ : ℝ) by
      exact_mod_cast hbound).trans (Nat.floor_le (by positivity))
theorem theorem_1_2 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    let k := spectralRadiusOrder ((1 - α) / (2 * α))
    (k < ⊤ → ∀ᶠ d in atTop, N α d = ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
    (k = ⊤ → ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d) := by
  have hlower := configuration_lower_bounds α hα
  have hupper := configuration_upper_bounds α hα
  dsimp only
  constructor
  · intro hk
    filter_upwards [hlower.2 hk, hupper.1 hk] with d hlow hupp
    exact Nat.le_antisymm hupp hlow
  · intro hk
    exact Helpers.error_term_of_bounds (N α) hlower.1 (hupper.2 hk)
theorem sign_reduction_inner_weighted_sum
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (a : ℝ) (c : ι → ℝ)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = a) :
    ⟪∑ i ∈ s, c i • v i, ∑ i ∈ s, c i • v i⟫ =
      (1 - a) * (∑ i ∈ s, c i ^ 2) + a * (∑ i ∈ s, c i) ^ 2 := by
  have hrow : ∀ i ∈ s, ⟪v i, ∑ j ∈ s, c j • v j⟫ =
      (1 - a) * c i + a * ∑ j ∈ s, c j := by
    intro i hi
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    calc
      ∑ j ∈ s, c j * ⟪v i, v j⟫ =
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
theorem sign_reduction_negative_clique_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (α : ℝ) (hα : 0 < α)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = -α) :
    (s.card : ℝ) ≤ 1 + 1 / α := by
  have hs := sign_reduction_inner_weighted_sum s v (-α) (fun _ => 1) hdiag hoff
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
theorem sign_reduction_residual_class_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (z : H) (α a : ℝ) (hα : α ≤ 1) (ha : α < a)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ ≤ α)
    (hvz : ∀ i ∈ s, ⟪v i, z⟫ = a) (hzz : ⟪z, z⟫ = a) :
    (s.card : ℝ) ≤ (1 - α) / (a - α) := by
  have hsum : ⟪∑ i ∈ s, (v i - z), ∑ i ∈ s, (v i - z)⟫ ≤
      (1 - α) * (s.card : ℝ) - (a - α) * (s.card : ℝ) ^ 2 := by
    rw [sum_inner]
    simp_rw [inner_sum]
    calc
      ∑ i ∈ s, ∑ j ∈ s, ⟪v i - z, v j - z⟫ ≤
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
theorem sign_reduction_mixed_sign_bound
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : Finset ι) (v : ι → H) (w : H) (α : ℝ)
    (hdis : Disjoint p q) (hp : p.Nonempty) (hq : q.Nonempty)
    (hw : ⟪w, w⟫ = 1)
    (hdiag : ∀ i ∈ p ∪ q, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ p ∪ q, ∀ j ∈ p ∪ q, i ≠ j → ⟪v i, v j⟫ = α)
    (hneg : ∀ i ∈ p, ⟪w, v i⟫ = -α)
    (hpos : ∀ i ∈ q, ⟪w, v i⟫ = α) :
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
  have hiw : ⟪w, ∑ i ∈ p ∪ q, c i • v i⟫ =
      -2 * α * (p.card : ℝ) * (q.card : ℝ) := by
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
    rw [Finset.sum_union hdis]
    have hp' : (∑ i ∈ p, c i * ⟪w, v i⟫) = ∑ i ∈ p, (q.card : ℝ) * -α := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc_p i hi, hneg i hi]
    have hq' : (∑ i ∈ q, c i * ⟪w, v i⟫) = ∑ i ∈ q, -(p.card : ℝ) * α := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc_q i hi, hpos i hi]
    rw [hp', hq']
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hcs := real_inner_mul_inner_self_le w (∑ i ∈ p ∪ q, c i • v i)
  rw [hw, sign_reduction_inner_weighted_sum (p ∪ q) v α c hdiag hoff,
    hiw, hsum, hsq] at hcs
  have hpq : 0 < (p.card : ℝ) * (q.card : ℝ) :=
    mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hp))
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hq))
  by_contra hnot
  have hgt := mul_pos hpq (sub_pos.mpr (lt_of_not_ge hnot))
  nlinarith only [hcs, hgt]
theorem sign_reduction_seed_projection
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s p : Finset ι) (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (hp : p ⊆ s) (hs : s.Nonempty)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = α) :
    let t : ℝ := s.card
    let k : ℝ := p.card
    let b : ι → ℝ := fun i => if i ∈ p then -1 else 1
    let c : ι → ℝ := fun i => α / (1 - α) *
      (b i - α * (t - 2 * k) / (1 + (t - 1) * α))
    let z : H := ∑ i ∈ s, c i • v i
    let a : ℝ := α ^ 2 / (1 - α) *
      (t - α * (t - 2 * k) ^ 2 / (1 + (t - 1) * α))
    ⟪z, z⟫ = a ∧
      (∀ w : H, (∀ i ∈ s, ⟪w, v i⟫ = α * b i) → ⟪w, z⟫ = a) ∧
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
  change ⟪∑ i ∈ s, c i • v i, ∑ i ∈ s, c i • v i⟫ =
    α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L) ∧
    (∀ w : H, (∀ i ∈ s, ⟪w, v i⟫ = α * b i) →
      ⟪w, ∑ i ∈ s, c i • v i⟫ =
        α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L)) ∧
    α ^ 2 / (1 - α) * (t - α * (t - 2 * k) ^ 2 / L) - α =
      α * (4 * α ^ 2 * k * (t - k) - (1 - α) ^ 2) / ((1 - α) * L)
  refine ⟨?_, ?_, ?_⟩
  · rw [sign_reduction_inner_weighted_sum s v α c hdiag hoff, hcsum, hcsq]
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
theorem sign_reduction_finite_ramsey (p q : ℕ) :
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
theorem sign_reduction_large_groups_impossible (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
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
theorem sign_reduction_orient_to_seed
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : Finset ι) (v : ι → H) (w : H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D : ℕ) (hDp : 0 < D) (hD : 1 - α < 2 * α ^ 2 * (D : ℝ))
    (hw : ⟪w, w⟫ = 1)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = α)
    (hwv : ∀ i ∈ s, |⟪w, v i⟫| = α) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (s.filter (fun i => ⟪σ • w, v i⟫ < 0)).card < D := by
  classical
  let p := s.filter (fun i => ⟪w, v i⟫ < 0)
  let q := s.filter (fun i => ¬⟪w, v i⟫ < 0)
  have hdis : Disjoint p q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  have hsplit : p ∪ q = s := by
    ext i
    by_cases h : ⟪w, v i⟫ < 0
    · simp [p, q, h]
    · have h' : 0 ≤ ⟪w, v i⟫ := le_of_not_gt h
      simp [p, q, h, h']
  have hneg : ∀ i ∈ p, ⟪w, v i⟫ = -α := by
    intro i hi
    have h := hwv i (Finset.mem_filter.mp hi).1
    rw [abs_of_neg (Finset.mem_filter.mp hi).2] at h
    linarith
  have hpos : ∀ i ∈ q, ⟪w, v i⟫ = α := by
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
      have hb := sign_reduction_mixed_sign_bound p q v w α hdis hpp hqp hw
        (by simpa only [hsplit] using hdiag) (by simpa only [hsplit] using hoff) hneg hpos
      exact sign_reduction_large_groups_impossible α hα D hD p.card q.card
        (by omega) (by omega) hDp hb
    refine ⟨-1, Or.inr rfl, ?_⟩
    have he : s.filter (fun i => ⟪(-1 : ℝ) • w, v i⟫ < 0) = q := by
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
theorem sign_reduction_seed_pattern_class
    {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s p r : Finset ι) (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D : ℕ) (hp : p ⊆ s) (hpn : p.Nonempty) (hpD : p.card ≤ D)
    (hsD : D < s.card)
    (hdiag : ∀ i ∈ s, ⟪v i, v i⟫ = 1)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = α)
    (hrdiag : ∀ i ∈ r, ⟪v i, v i⟫ = 1)
    (hroff : ∀ i ∈ r, ∀ j ∈ r, i ≠ j → ⟪v i, v j⟫ ≤ α)
    (hrangle : ∀ i ∈ r, ∀ j ∈ s, |⟪v i, v j⟫| = α)
    (hpattern : ∀ i ∈ r, s.filter (fun j => ⟪v i, v j⟫ < 0) = p) :
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
  have hproj := sign_reduction_seed_projection s p v α hα hp hs hdiag hoff
  change ⟪z, z⟫ = a ∧
    (∀ w : H, (∀ j ∈ s, ⟪w, v j⟫ = α * b j) → ⟪w, z⟫ = a) ∧
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
  have hvz : ∀ i ∈ r, ⟪v i, z⟫ = a := by
    intro i hi
    apply hproj.2.1 (v i)
    intro j hj
    dsimp [b]
    by_cases hjp : j ∈ p
    · rw [if_pos hjp]
      have hneg : ⟪v i, v j⟫ < 0 := by
        rw [← hpattern i hi] at hjp
        exact (Finset.mem_filter.mp hjp).2
      have hh := hrangle i hi j hj
      rw [abs_of_neg hneg] at hh
      linarith
    · rw [if_neg hjp]
      have hnon : 0 ≤ ⟪v i, v j⟫ := by
        by_contra h
        apply hjp
        rw [← hpattern i hi]
        exact Finset.mem_filter.mpr ⟨hj, by linarith⟩
      have hh := hrangle i hi j hj
      rw [abs_of_nonneg hnon] at hh
      linarith
  have hr := sign_reduction_residual_class_bound r v z α a hα.2.le ha
    hrdiag hroff hvz hproj.1
  apply (le_div_iff₀ hδ).mpr
  have hrr : 0 ≤ (r.card : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hδa hrr
  have hb := (le_div_iff₀ (sub_pos.mpr ha)).mp hr
  linarith only [hh, hb]
theorem sign_reduction_seeded_degree
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (D C R B : ℕ) (hDp : 0 < D) (hD : 1 - α < 2 * α ^ 2 * (D : ℝ))
    (hC : 1 + 1 / α < (C : ℝ))
    (hR : ∀ u : Finset ι, R ≤ u.card →
      (∃ p : Finset ι, p ⊆ u ∧ p.card = D ∧
        ∀ i ∈ p, ∀ j ∈ p, i ≠ j → ⟪v i, v j⟫ = α) ∨
      (∃ p : Finset ι, p ⊆ u ∧ p.card = C ∧
        ∀ i ∈ p, ∀ j ∈ p, i ≠ j → ⟪v i, v j⟫ ≠ α))
    (s : Finset ι) (hsD : 2 * D < s.card)
    (hdiag : ∀ i, ⟪v i, v i⟫ = 1)
    (hangle : ∀ i j, i ≠ j → |⟪v i, v j⟫| = α)
    (hseed : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫ = α)
    (hsmall : ∀ i, (s.filter (fun j => ⟪v i, v j⟫ < 0)).card < D)
    (hδ : 0 < α * (4 * α ^ 2 * ((s.card : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
      ((1 - α) * (1 + ((s.card : ℝ) - 1) * α)))
    (hB : (1 - α) /
      (α * (4 * α ^ 2 * ((s.card : ℝ) - (D : ℝ)) - (1 - α) ^ 2) /
        ((1 - α) * (1 + ((s.card : ℝ) - 1) * α))) ≤ (B : ℝ)) :
    ∀ i, (Finset.univ.filter (fun j => ⟪v i, v j⟫ < 0)).card ≤
      s.card + 2 ^ s.card * B + R := by
  classical
  let f : ι → Finset ι := fun i => s.filter (fun j => ⟪v i, v j⟫ < 0)
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
        have hrr := sign_reduction_seed_pattern_class s p r v α hα D
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
  have hUpos : ∀ i ∈ U, ∀ j ∈ s, ⟪v i, v j⟫ = α := by
    intro i hi j hj
    have hiU := (Finset.mem_filter.mp hi).2
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hiU.1 hj
    have hnon : 0 ≤ ⟪v i, v j⟫ := by
      by_contra h
      have hh : j ∈ f i := Finset.mem_filter.mpr ⟨hj, by linarith⟩
      rw [hiU.2] at hh
      exact Finset.notMem_empty j hh
    have hh := hangle i j hij
    rwa [abs_of_nonneg hnon] at hh
  have hnegative : ∀ p : Finset ι,
      (∀ i ∈ p, ∀ j ∈ p, i ≠ j → ⟪v i, v j⟫ ≠ α) → p.card ≠ C := by
    intro p hp hpc
    have hh := sign_reduction_negative_clique_bound p v α hα.1
      (fun i hi => hdiag i) (by
        intro i hi j hj hij
        have h := hangle i j hij
        have hn : ⟪v i, v j⟫ < 0 := by
          by_contra hn
          have hh := abs_of_nonneg (le_of_not_gt hn)
          exact hp i hi j hj hij (by rwa [hh] at h)
        rw [abs_of_neg hn] at h
        linarith)
    rw [hpc] at hh
    linarith only [hh, hC]
  intro i
  let V : Finset ι := U.filter (fun j => ⟪v i, v j⟫ < 0)
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
        have hh' : ⟪v i, v j⟫ = α := by rw [real_inner_comm (v j) (v i)]; exact hh
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
      have hposq : ∀ j ∈ q, ⟪v i, v j⟫ = α := by
        intro j hj
        have hjs := (Finset.mem_sdiff.mp hj).1
        have hjf := (Finset.mem_sdiff.mp hj).2
        have hnon : 0 ≤ ⟪v i, v j⟫ := by
          by_contra h
          exact hjf (Finset.mem_filter.mpr ⟨hjs, by linarith⟩)
        have hh := hangle i j (by intro h; subst j; exact hiout hjs)
        rwa [abs_of_nonneg hnon] at hh
      have hclique : ∀ j ∈ p ∪ q, ∀ k ∈ p ∪ q, j ≠ k → ⟪v j, v k⟫ = α := by
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
      have hb := sign_reduction_mixed_sign_bound p q v (v i) α hdis hpn hqn
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
      exact sign_reduction_large_groups_impossible α hα D hD p.card q.card
        (by omega) hqcard hDp hb
    · exact hnegative p hpp hpC
  let W : Finset ι := Finset.univ.filter (fun j => ⟪v i, v j⟫ < 0)
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
theorem sign_reduction_graph_of_degree_bound
    {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ι → H) (σ : ι → ℝ) (Δ : ℕ)
    (hdegree : ∀ i, (Finset.univ.filter (fun j => ⟪σ i • v i, σ j • v j⟫ < 0)).card ≤ Δ) :
    ∃ G : SimpleGraph ι,
      (∀ i j, G.Adj i j ↔ i ≠ j ∧ ⟪σ i • v i, σ j • v j⟫ < 0) ∧
      (∀ i, ({j : ι | G.Adj i j} : Set ι).ncard ≤ Δ) := by
  classical
  let G : SimpleGraph ι := {
    Adj := fun i j => i ≠ j ∧ ⟪σ i • v i, σ j • v j⟫ < 0
    symm := ⟨fun i j h => ⟨h.1.symm, by
      rw [real_inner_comm (σ i • v i) (σ j • v j)]
      exact h.2⟩⟩
    loopless := ⟨fun i h => h.1 rfl⟩ }
  refine ⟨G, fun i j => Iff.rfl, ?_⟩
  intro i
  let s := Finset.univ.filter (fun j => ⟪σ i • v i, σ j • v j⟫ < 0)
  have hsub : {j : ι | G.Adj i j} ⊆ (s : Set ι) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.2⟩
  calc
    ({j : ι | G.Adj i j} : Set ι).ncard ≤ (s : Set ι).ncard := Set.ncard_le_ncard hsub
    _ = s.card := Set.ncard_coe_finset s
    _ ≤ Δ := hdegree i
theorem uniform_sign_reduction :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 → ∃ Δ : ℕ,
      ∀ (d n : ℕ) (E : EquiangularLinesFixedAngle.EquiangularLines α d)
        (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, v i ∈ E.carrier) → Function.Injective v →
        ∃ (σ : Fin n → ℝ) (G : SimpleGraph (Fin n)),
          (∀ i, σ i = 1 ∨ σ i = -1) ∧
          (∀ i j, G.Adj i j ↔ i ≠ j ∧ ⟪σ i • v i, σ j • v j⟫ < 0) ∧
          (∀ i, ({j : Fin n | G.Adj i j} : Set (Fin n)).ncard ≤ Δ) := by
  classical
  intro α hα
  obtain ⟨Δ, hΔ⟩ := Helpers.uniform_switching_with_gram_data α hα
  refine ⟨Δ, ?_⟩
  intro d n E v hv hinj
  obtain ⟨σ, G, hσ, _, _, _, _, hG, hdegree, _⟩ := hΔ d n v
    (fun i => E.norm (v i) (hv i))
    (fun i j hij => E.angle (hv i) (hv j) (hinj.ne hij))
  exact ⟨σ, G, hσ, hG, hdegree⟩
noncomputable def negativeInnerGraph {d n : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => ⟪v i, v j⟫ < 0)
theorem negativeInnerGraph_adj {d n : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    (negativeInnerGraph v).Adj i j ↔ i ≠ j ∧ ⟪v i, v j⟫ < 0 := by
  simp only [negativeInnerGraph, SimpleGraph.fromRel_adj, real_inner_comm (v j) (v i),
    or_self]
noncomputable def negativeInnerAdjMatrix {d n : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact (negativeInnerGraph v).adjMatrix ℝ
theorem configuration_gram_eq_adjacency (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    {d n : ℕ} (E : EquiangularLines α d)
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, v i ∈ E.carrier) (hinj : Function.Injective v) :
    Matrix.gram ℝ v =
      (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) -
        (2 * α) • negativeInnerAdjMatrix v := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply, E.norm _ (hv i), negativeInnerAdjMatrix]
  · have hangle := E.angle (hv i) (hv j) (hinj.ne hij)
    rcases (abs_eq hα.1.le).mp hangle with hpos | hneg
    · have hnot : ¬α < 0 := not_lt.mpr hα.1.le
      simp [Matrix.gram_apply, hij, negativeInnerAdjMatrix,
        negativeInnerGraph_adj, hpos, hnot]
    · simp [Matrix.gram_apply, hij, negativeInnerAdjMatrix,
        negativeInnerGraph_adj, hneg, hα.1]
      ring
theorem real_matrix_rank_add_le {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
theorem configuration_shifted_adjacency_rank_le (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    {d n : ℕ} (E : EquiangularLines α d)
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, v i ∈ E.carrier) (hinj : Function.Injective v) :
    (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      negativeInnerAdjMatrix v).rank ≤ d + 1 := by
  classical
  let J : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun _ _ => (1 : ℝ))
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have heq : ((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
      negativeInnerAdjMatrix v =
      (1 / (2 * α)) • Matrix.gram ℝ v + (-1 / 2 : ℝ) • J := by
    rw [configuration_gram_eq_adjacency α hα E v hv hinj]
    ext i j
    simp only [J, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp [hα0] <;> ring
  have hJ : J.rank ≤ 1 := by
    have hones : J = Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ))
        (fun _ : Fin n => (1 : ℝ)) := by
      ext i j
      simp [J, Matrix.vecMulVec]
    rw [hones]
    exact Matrix.rank_vecMulVec_le _ _
  rw [heq]
  calc
    ((1 / (2 * α)) • Matrix.gram ℝ v + (-1 / 2 : ℝ) • J).rank ≤
        ((1 / (2 * α)) • Matrix.gram ℝ v).rank + ((-1 / 2 : ℝ) • J).rank :=
      real_matrix_rank_add_le _ _
    _ ≤ (Matrix.gram ℝ v).rank + J.rank :=
      Nat.add_le_add (real_matrix_rank_smul_le _ _) (real_matrix_rank_smul_le _ _)
    _ ≤ d + 1 := Nat.add_le_add (euclidean_gram_rank_le v) hJ
theorem configuration_eigenspace_dimension_bound (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    {d n : ℕ} (E : EquiangularLines α d)
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, v i ∈ E.carrier) (hinj : Function.Injective v) :
    n ≤ d + 1 + Module.finrank ℝ
      (Module.End.eigenspace (negativeInnerAdjMatrix v).mulVecLin ((1 - α) / (2 * α))) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ :=
    ((1 - α) / (2 * α)) • 1 - negativeInnerAdjMatrix v
  have hker : LinearMap.ker B.mulVecLin =
      Module.End.eigenspace (negativeInnerAdjMatrix v).mulVecLin ((1 - α) / (2 * α)) := by
    ext c
    rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
    simp only [Matrix.mulVecLin_apply, B, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero]
    exact eq_comm
  have hdim : B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker] at hdim
  have hrank : B.rank ≤ d + 1 :=
    configuration_shifted_adjacency_rank_le α hα E v hv hinj
  omega
theorem configuration_gram_spectral_bridge :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      ∀ (d n : ℕ) (E : EquiangularLinesFixedAngle.EquiangularLines α d)
        (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, v i ∈ E.carrier) → Function.Injective v →
        ∃ G : SimpleGraph (Fin n),
          let A : Matrix (Fin n) (Fin n) ℝ :=
            (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
          Matrix.gram ℝ v = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
            α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A ∧
          (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank ≤ d + 1 ∧
          n ≤ d + 1 + Module.finrank ℝ
            (Module.End.eigenspace A.mulVecLin ((1 - α) / (2 * α))) := by
  classical
  intro α hα d n E v hv hinj
  refine ⟨negativeInnerGraph v, ?_⟩
  exact ⟨configuration_gram_eq_adjacency α hα E v hv hinj,
    configuration_shifted_adjacency_rank_le α hα E v hv hinj,
    configuration_eigenspace_dimension_bound α hα E v hv hinj⟩
theorem configuration_gram_spectral_bridge_from_units :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      ∀ (d n : ℕ) (E : EquiangularLinesFixedAngle.EquiangularLines α d)
        (v : Fin n → EuclideanSpace ℝ (Fin d)),
        (∀ i, v i ∈ E.carrier) → Function.Injective v →
        ∃ G : SimpleGraph (Fin n),
          let A : Matrix (Fin n) (Fin n) ℝ :=
            (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.adjMatrix ℝ)
          Matrix.gram ℝ v = (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) +
            α • Matrix.of (fun _ _ : Fin n => (1 : ℝ)) - (2 * α) • A ∧
          (((1 - α) / (2 * α)) • (1 : Matrix (Fin n) (Fin n) ℝ) - A).rank ≤ d + 1 ∧
          n ≤ d + 1 + Module.finrank ℝ
            (Module.End.eigenspace A.mulVecLin ((1 - α) / (2 * α))) := by
  intro α hα d n E v hv hinj
  exact Helpers.gram_spectral_bridge_of_unit_vectors α hα d n v
    (fun i => E.norm (v i) (hv i))
    (fun i j hij => E.angle (hv i) (hv j) (hinj.ne hij))
theorem configuration_lower_bounds_nat_index :
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
      let k := spectralRadiusOrder ((1 - α) / (2 * α))
      (∀ d : ℕ, d ≤ N α d) ∧
      (k < ⊤ → ∀ᶠ (d : ℕ) in Filter.atTop,
        ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊ ≤ N α d) := by
  classical
  intro α hα
  refine ⟨configuration_dimension_lower_bound α hα, ?_⟩
  intro hfinite
  obtain ⟨q, G, hq, hradius⟩ := spectral_order_attained _ hfinite
  have hαpos : 0 < α := hα.1
  have hlambda : 0 < (1 - α) / (2 * α) :=
    div_pos (sub_pos.mpr hα.2) (by positivity)
  have hqge := lower_graph_order_ge_two _ hlambda q G hradius
  have hqn : (spectralRadiusOrder ((1 - α) / (2 * α))).toNat = q := by
    rw [← hq, ENat.toNat_natCast]
  apply Filter.eventually_atTop.mpr
  refine ⟨1, ?_⟩
  intro d hd
  rw [hqn, Helpers.lower_floor_count_real_subtraction q d hqge hd]
  have hc := lower_graph_copies_configuration α hα q G hradius
    ((d - 1) / (q - 1)) ((d - 1) % (q - 1))
  rwa [Helpers.floor_lower_bound_from_copies q d hqge hd] at hc
end Submission
