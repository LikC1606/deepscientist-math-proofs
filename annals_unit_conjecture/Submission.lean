import ChallengeDeps
import Mathlib.Tactic

open UnitConjecture

set_option autoImplicit false

namespace Submission

noncomputable section

private structure Point where
  i : ℤ
  j : ℤ
  k : ℤ
deriving DecidableEq

private def affineA : Equiv.Perm Point where
  toFun v := ⟨v.i + 1, -v.j, 1 - v.k⟩
  invFun v := ⟨v.i - 1, -v.j, 1 - v.k⟩
  left_inv := by rintro ⟨i, j, k⟩; simp
  right_inv := by rintro ⟨i, j, k⟩; simp

private def affineB : Equiv.Perm Point where
  toFun v := ⟨-v.i, v.j + 1, -v.k⟩
  invFun v := ⟨-v.i, v.j - 1, -v.k⟩
  left_inv := by rintro ⟨i, j, k⟩; simp
  right_inv := by rintro ⟨i, j, k⟩; simp

private def affineGenerator : generators → Equiv.Perm Point
  | .a => affineA
  | .b => affineB

private lemma affine_relations (w : FreeGroup generators) (hw : w ∈ relations) :
    FreeGroup.lift affineGenerator w = 1 := by
  simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · ext v
    rcases v with ⟨i, j, k⟩
    simp [UnitConjecture.a, UnitConjecture.b, affineGenerator, affineA, affineB, pow_two]
  · ext v
    rcases v with ⟨i, j, k⟩
    simp [UnitConjecture.a, UnitConjecture.b, affineGenerator, affineA, affineB, pow_two]

private def affineRepresentation : P →* Equiv.Perm Point :=
  PresentedGroup.toGroup affine_relations

@[simp] private lemma affineRepresentation_a : affineRepresentation (a : P) = affineA := by
  rfl

@[simp] private lemma affineRepresentation_b : affineRepresentation (b : P) = affineB := by
  rfl

@[simp] private lemma affineRepresentation_x : affineRepresentation x = affineA ^ 2 := by
  simp [x]

@[simp] private lemma affineRepresentation_y : affineRepresentation y = affineB ^ 2 := by
  simp [y]

@[simp] private lemma affineRepresentation_z :
    affineRepresentation z = (affineA * affineB) ^ 2 := by
  simp [z]

private lemma affineX_zpow_apply (m : ℤ) : ∀ v : Point,
    ((affineA ^ 2) ^ m) v = ⟨v.i + 2 * m, v.j, v.k⟩ := by
  refine Int.inductionOn' m 0 ?_ ?_ ?_
  · intro v
    simp
  · intro n _ ih v
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineA, pow_two, Point.mk.injEq]
    omega
  · intro n _ ih v
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineA, pow_two, Point.mk.injEq]
    omega

private lemma affineY_zpow_apply (m : ℤ) : ∀ v : Point,
    ((affineB ^ 2) ^ m) v = ⟨v.i, v.j + 2 * m, v.k⟩ := by
  refine Int.inductionOn' m 0 ?_ ?_ ?_
  · intro v
    simp
  · intro n _ ih v
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineB, pow_two, Point.mk.injEq]
    omega
  · intro n _ ih v
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineB, pow_two, Point.mk.injEq]
    omega

private lemma affineZ_zpow_apply (m : ℤ) : ∀ v : Point,
    (((affineA * affineB) ^ 2) ^ m) v = ⟨v.i, v.j, v.k + 2 * m⟩ := by
  refine Int.inductionOn' m 0 ?_ ?_ ?_
  · intro v
    simp
  · intro n _ ih v
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineA, affineB, pow_two, Point.mk.injEq]
    omega
  · intro n _ ih v
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    rcases v with ⟨i, j, k⟩
    simp [affineA, affineB, pow_two, Point.mk.injEq]
    omega

private lemma relation_a : (b : P)⁻¹ * (a : P) ^ 2 * b * a ^ 2 = 1 := by
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

private lemma relation_b : (a : P)⁻¹ * (b : P) ^ 2 * a * b ^ 2 = 1 := by
  exact PresentedGroup.one_of_mem (by simp [UnitConjecture.relations])

private lemma conjugate_x_by_b : (b : P)⁻¹ * x * b = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa [x, mul_assoc] using relation_a

private lemma conjugate_y_by_a : (a : P)⁻¹ * y * a = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa [y, mul_assoc] using relation_b

private lemma conjugate_x_inv_by_b : (b : P)⁻¹ * x⁻¹ * b = x := by
  have h := congrArg Inv.inv conjugate_x_by_b
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

private lemma conjugate_y_inv_by_a : (a : P)⁻¹ * y⁻¹ * a = y := by
  have h := congrArg Inv.inv conjugate_y_by_a
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

private lemma commute_x_y : x * y = y * x := by
  calc
    x * y = b * ((b : P)⁻¹ * x * b) * b := by simp [y, pow_two, mul_assoc]
    _ = b * x⁻¹ * b := by rw [conjugate_x_by_b]
    _ = y * ((b : P)⁻¹ * x⁻¹ * b) := by simp [y, pow_two, mul_assoc]
    _ = y * x := by rw [conjugate_x_inv_by_b]

private lemma commute_a_x : (a : P) * x = x * a := by
  simp [x, pow_two, mul_assoc]

private lemma commute_b_y : (b : P) * y = y * b := by
  simp [y, pow_two, mul_assoc]

private lemma a_mul_y : (a : P) * y = y⁻¹ * a := by
  calc
    (a : P) * y = x * ((a : P)⁻¹ * y * a) * (a : P)⁻¹ := by
      simp [x, pow_two, mul_assoc]
    _ = x * y⁻¹ * (a : P)⁻¹ := by rw [conjugate_y_by_a]
    _ = y⁻¹ * a := by
      rw [(show Commute x y⁻¹ from (show Commute x y from commute_x_y).inv_right).eq]
      simp [x, pow_two, mul_assoc]

private lemma b_mul_x : (b : P) * x = x⁻¹ * b := by
  calc
    (b : P) * x = y * ((b : P)⁻¹ * x * b) * (b : P)⁻¹ := by
      simp [y, pow_two, mul_assoc]
    _ = y * x⁻¹ * (b : P)⁻¹ := by rw [conjugate_x_by_b]
    _ = x⁻¹ * b := by
      rw [(show Commute y x⁻¹ from (show Commute y x from commute_x_y.symm).inv_right).eq]
      simp [y, pow_two, mul_assoc]

private lemma conjugate_z_by_a : (a : P)⁻¹ * z * a = z⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    ((a : P)⁻¹ * z * a) * z =
        (b : P) * a * b * x * b * a * b := by
      simp only [z, x, pow_two]
      group
    _ = (b : P) * a * (b * x) * b * a * b := by group
    _ = (b : P) * a * (x⁻¹ * b) * b * a * b := by rw [b_mul_x]
    _ = (b : P) * (a * x⁻¹) * b * b * a * b := by group
    _ = (b : P) * (x⁻¹ * a) * b * b * a * b := by
      rw [(show Commute (a : P) x⁻¹ from
        (show Commute (a : P) x from commute_a_x).inv_right).eq]
    _ = (b : P) * x⁻¹ * a * y * a * b := by
      simp only [y, pow_two]
      group
    _ = (b : P) * x⁻¹ * (a * y) * a * b := by group
    _ = (b : P) * x⁻¹ * (y⁻¹ * a) * a * b := by rw [a_mul_y]
    _ = (b : P) * x⁻¹ * y⁻¹ * x * b := by
      simp only [x, pow_two]
      group
    _ = (b : P) * (x⁻¹ * y⁻¹) * x * b := by group
    _ = (b : P) * y⁻¹ * b := by
      rw [(show Commute x⁻¹ y⁻¹ from
        (show Commute x y from commute_x_y).inv_left.inv_right).eq]
      simp [mul_assoc]
    _ = 1 := by
      rw [(show Commute (b : P) y⁻¹ from
        (show Commute (b : P) y from commute_b_y).inv_right).eq]
      simp [y, pow_two, mul_assoc]

private lemma conjugate_z_inv_by_a : (a : P)⁻¹ * z⁻¹ * a = z := by
  have h := congrArg Inv.inv conjugate_z_by_a
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

private lemma conjugate_z_inv_by_b : (b : P)⁻¹ * z⁻¹ * b = z := by
  calc
    (b : P)⁻¹ * z⁻¹ * b =
        (b : P)⁻¹ * ((a : P)⁻¹ * z * a) * b := by rw [conjugate_z_by_a]
    _ = ((a : P) * b)⁻¹ * z * (a * b) := by group
    _ = z := by simp [z, pow_two, mul_assoc]

private lemma conjugate_z_by_b : (b : P)⁻¹ * z * b = z⁻¹ := by
  have h := congrArg Inv.inv conjugate_z_inv_by_b
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

private lemma commute_x_z : x * z = z * x := by
  symm
  calc
    z * x = (a : P) * ((a : P)⁻¹ * z * a) * a := by simp [x, pow_two, mul_assoc]
    _ = (a : P) * z⁻¹ * a := by rw [conjugate_z_by_a]
    _ = x * ((a : P)⁻¹ * z⁻¹ * a) := by simp [x, pow_two, mul_assoc]
    _ = x * z := by rw [conjugate_z_inv_by_a]

private lemma commute_y_z : y * z = z * y := by
  symm
  calc
    z * y = (b : P) * ((b : P)⁻¹ * z * b) * b := by simp [y, pow_two, mul_assoc]
    _ = (b : P) * z⁻¹ * b := by rw [conjugate_z_by_b]
    _ = y * ((b : P)⁻¹ * z⁻¹ * b) := by simp [y, pow_two, mul_assoc]
    _ = y * z := by rw [conjugate_z_inv_by_b]

private def translations : Subgroup P where
  carrier := {g | ∃ i j k : ℤ, g = x ^ i * y ^ j * z ^ k}
  one_mem' := ⟨0, 0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨l, m, n, rfl⟩
    refine ⟨i + l, j + m, k + n, ?_⟩
    simp only [zpow_add]
    calc
      (x ^ i * y ^ j * z ^ k) * (x ^ l * y ^ m * z ^ n) =
          x ^ i * y ^ j * (z ^ k * x ^ l) * y ^ m * z ^ n := by group
      _ = x ^ i * y ^ j * (x ^ l * z ^ k) * y ^ m * z ^ n := by
        rw [(show Commute (z ^ k) (x ^ l) from
          (show Commute z x from commute_x_z.symm).zpow_zpow k l).eq]
      _ = x ^ i * (y ^ j * x ^ l) * z ^ k * y ^ m * z ^ n := by group
      _ = x ^ i * (x ^ l * y ^ j) * z ^ k * y ^ m * z ^ n := by
        rw [(show Commute (y ^ j) (x ^ l) from
          (show Commute y x from commute_x_y.symm).zpow_zpow j l).eq]
      _ = x ^ i * x ^ l * y ^ j * (z ^ k * y ^ m) * z ^ n := by group
      _ = x ^ i * x ^ l * y ^ j * (y ^ m * z ^ k) * z ^ n := by
        rw [(show Commute (z ^ k) (y ^ m) from
          (show Commute z y from commute_y_z.symm).zpow_zpow k m).eq]
      _ = (x ^ i * x ^ l) * (y ^ j * y ^ m) * (z ^ k * z ^ n) := by group
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    refine ⟨-i, -j, -k, ?_⟩
    simp only [zpow_neg]
    calc
      (x ^ i * y ^ j * z ^ k)⁻¹ = (z ^ k)⁻¹ * (y ^ j)⁻¹ * (x ^ i)⁻¹ := by group
      _ = (y ^ j)⁻¹ * (z ^ k)⁻¹ * (x ^ i)⁻¹ := by
        rw [(show Commute (z ^ k)⁻¹ (y ^ j)⁻¹ from
          (show Commute (z ^ k) (y ^ j) from
            (show Commute z y from commute_y_z.symm).zpow_zpow k j).inv_left.inv_right).eq]
      _ = (y ^ j)⁻¹ * ((z ^ k)⁻¹ * (x ^ i)⁻¹) := by group
      _ = (y ^ j)⁻¹ * (x ^ i)⁻¹ * (z ^ k)⁻¹ := by
        rw [(show Commute (z ^ k)⁻¹ (x ^ i)⁻¹ from
          (show Commute (z ^ k) (x ^ i) from
            (show Commute z x from commute_x_z.symm).zpow_zpow k i).inv_left.inv_right).eq]
        group
      _ = (x ^ i)⁻¹ * (y ^ j)⁻¹ * (z ^ k)⁻¹ := by
        rw [(show Commute (y ^ j)⁻¹ (x ^ i)⁻¹ from
          (show Commute (y ^ j) (x ^ i) from
            (show Commute y x from commute_x_y.symm).zpow_zpow j i).inv_left.inv_right).eq]

private lemma conjugate_x_by_a : (a : P)⁻¹ * x * a = x := by
  calc
    (a : P)⁻¹ * x * a = (a : P)⁻¹ * (a * x) := by rw [commute_a_x]; group
    _ = x := by simp

private lemma conjugate_y_by_b : (b : P)⁻¹ * y * b = y := by
  calc
    (b : P)⁻¹ * y * b = (b : P)⁻¹ * (b * y) := by rw [commute_b_y]; group
    _ = y := by simp

private lemma conjugate_left_x_by_a : (a : P) * x * (a : P)⁻¹ = x := by
  rw [commute_a_x]
  simp [mul_assoc]

private lemma conjugate_left_y_by_a : (a : P) * y * (a : P)⁻¹ = y⁻¹ := by
  rw [a_mul_y]
  simp [mul_assoc]

private lemma conjugate_left_z_by_a : (a : P) * z * (a : P)⁻¹ = z⁻¹ := by
  calc
    (a : P) * z * (a : P)⁻¹ = x * ((a : P)⁻¹ * z * a) * x⁻¹ := by
      simp [x, pow_two, mul_assoc]
    _ = x * z⁻¹ * x⁻¹ := by rw [conjugate_z_by_a]
    _ = z⁻¹ := by
      rw [(show Commute x z⁻¹ from
        (show Commute x z from commute_x_z).inv_right).eq]
      simp [mul_assoc]

private lemma conjugate_left_x_by_b : (b : P) * x * (b : P)⁻¹ = x⁻¹ := by
  calc
    (b : P) * x * (b : P)⁻¹ = y * ((b : P)⁻¹ * x * b) * y⁻¹ := by
      simp [y, pow_two, mul_assoc]
    _ = y * x⁻¹ * y⁻¹ := by rw [conjugate_x_by_b]
    _ = x⁻¹ := by
      rw [(show Commute y x⁻¹ from
        (show Commute y x from commute_x_y.symm).inv_right).eq]
      simp [mul_assoc]

private lemma conjugate_left_y_by_b : (b : P) * y * (b : P)⁻¹ = y := by
  rw [commute_b_y]
  simp [mul_assoc]

private lemma conjugate_left_z_by_b : (b : P) * z * (b : P)⁻¹ = z⁻¹ := by
  calc
    (b : P) * z * (b : P)⁻¹ = y * ((b : P)⁻¹ * z * b) * y⁻¹ := by
      simp [y, pow_two, mul_assoc]
    _ = y * z⁻¹ * y⁻¹ := by rw [conjugate_z_by_b]
    _ = z⁻¹ := by
      rw [(show Commute y z⁻¹ from
        (show Commute y z from commute_y_z).inv_right).eq]
      simp [mul_assoc]

private lemma conjugate_inv_zpow (g h : P) (i : ℤ) :
    g⁻¹ * h ^ i * g = (g⁻¹ * h * g) ^ i := by
  simpa only [inv_inv] using (conj_zpow (a := g⁻¹) (b := h) (i := i)).symm

private lemma conjugate_translation_by_a (i j k : ℤ) :
    (a : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * a = x ^ i * y ^ (-j) * z ^ (-k) := by
  calc
    (a : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * a =
        ((a : P)⁻¹ * x ^ i * a) * ((a : P)⁻¹ * y ^ j * a) *
          ((a : P)⁻¹ * z ^ k * a) := by group
    _ = ((a : P)⁻¹ * x * a) ^ i * ((a : P)⁻¹ * y * a) ^ j *
          ((a : P)⁻¹ * z * a) ^ k := by simp only [conjugate_inv_zpow]
    _ = x ^ i * (y⁻¹) ^ j * (z⁻¹) ^ k := by
      rw [conjugate_x_by_a, conjugate_y_by_a, conjugate_z_by_a]
    _ = x ^ i * y ^ (-j) * z ^ (-k) := by simp only [inv_zpow']

private lemma conjugate_translation_left_by_a (i j k : ℤ) :
    (a : P) * (x ^ i * y ^ j * z ^ k) * (a : P)⁻¹ =
      x ^ i * y ^ (-j) * z ^ (-k) := by
  calc
    (a : P) * (x ^ i * y ^ j * z ^ k) * (a : P)⁻¹ =
        ((a : P) * x ^ i * (a : P)⁻¹) * ((a : P) * y ^ j * (a : P)⁻¹) *
          ((a : P) * z ^ k * (a : P)⁻¹) := by group
    _ = ((a : P) * x * (a : P)⁻¹) ^ i * ((a : P) * y * (a : P)⁻¹) ^ j *
          ((a : P) * z * (a : P)⁻¹) ^ k := by simp only [conj_zpow]
    _ = x ^ i * (y⁻¹) ^ j * (z⁻¹) ^ k := by
      rw [conjugate_left_x_by_a, conjugate_left_y_by_a, conjugate_left_z_by_a]
    _ = x ^ i * y ^ (-j) * z ^ (-k) := by simp only [inv_zpow']

private lemma conjugate_translation_by_b (i j k : ℤ) :
    (b : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * b = x ^ (-i) * y ^ j * z ^ (-k) := by
  calc
    (b : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * b =
        ((b : P)⁻¹ * x ^ i * b) * ((b : P)⁻¹ * y ^ j * b) *
          ((b : P)⁻¹ * z ^ k * b) := by group
    _ = ((b : P)⁻¹ * x * b) ^ i * ((b : P)⁻¹ * y * b) ^ j *
          ((b : P)⁻¹ * z * b) ^ k := by simp only [conjugate_inv_zpow]
    _ = (x⁻¹) ^ i * y ^ j * (z⁻¹) ^ k := by
      rw [conjugate_x_by_b, conjugate_y_by_b, conjugate_z_by_b]
    _ = x ^ (-i) * y ^ j * z ^ (-k) := by simp only [inv_zpow']

private lemma conjugate_translation_left_by_b (i j k : ℤ) :
    (b : P) * (x ^ i * y ^ j * z ^ k) * (b : P)⁻¹ =
      x ^ (-i) * y ^ j * z ^ (-k) := by
  calc
    (b : P) * (x ^ i * y ^ j * z ^ k) * (b : P)⁻¹ =
        ((b : P) * x ^ i * (b : P)⁻¹) * ((b : P) * y ^ j * (b : P)⁻¹) *
          ((b : P) * z ^ k * (b : P)⁻¹) := by group
    _ = ((b : P) * x * (b : P)⁻¹) ^ i * ((b : P) * y * (b : P)⁻¹) ^ j *
          ((b : P) * z * (b : P)⁻¹) ^ k := by simp only [conj_zpow]
    _ = (x⁻¹) ^ i * y ^ j * (z⁻¹) ^ k := by
      rw [conjugate_left_x_by_b, conjugate_left_y_by_b, conjugate_left_z_by_b]
    _ = x ^ (-i) * y ^ j * z ^ (-k) := by simp only [inv_zpow']

private lemma a_mem_translations_normalizer :
    (a : P) ∈ Subgroup.normalizer (translations : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨i, -j, -k, conjugate_translation_left_by_a i j k⟩
  · rintro ⟨i, j, k, hh⟩
    refine ⟨i, -j, -k, ?_⟩
    calc
      h = (a : P)⁻¹ * ((a : P) * h * (a : P)⁻¹) * a := by group
      _ = (a : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * a := by rw [hh]
      _ = x ^ i * y ^ (-j) * z ^ (-k) := conjugate_translation_by_a i j k

private lemma b_mem_translations_normalizer :
    (b : P) ∈ Subgroup.normalizer (translations : Set P) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨i, j, k, rfl⟩
    exact ⟨-i, j, -k, conjugate_translation_left_by_b i j k⟩
  · rintro ⟨i, j, k, hh⟩
    refine ⟨-i, j, -k, ?_⟩
    calc
      h = (b : P)⁻¹ * ((b : P) * h * (b : P)⁻¹) * b := by group
      _ = (b : P)⁻¹ * (x ^ i * y ^ j * z ^ k) * b := by rw [hh]
      _ = x ^ (-i) * y ^ j * z ^ (-k) := conjugate_translation_by_b i j k

private lemma translations_normal : translations.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by relations (Subgroup.normalizer (translations : Set P))
  intro c
  cases c with
  | a => exact a_mem_translations_normalizer
  | b => exact b_mem_translations_normalizer

private instance : translations.Normal := translations_normal

private abbrev TranslationQuotient := P ⧸ translations

private abbrev quotientA : TranslationQuotient := (a : P)

private abbrev quotientB : TranslationQuotient := (b : P)

private lemma quotientA_sq : quotientA ^ 2 = 1 := by
  apply (QuotientGroup.eq_one_iff ((a : P) ^ 2)).mpr
  exact ⟨1, 0, 0, by simp [x]⟩

private lemma quotientB_sq : quotientB ^ 2 = 1 := by
  apply (QuotientGroup.eq_one_iff ((b : P) ^ 2)).mpr
  exact ⟨0, 1, 0, by simp [y]⟩

private lemma quotientAB_sq : (quotientA * quotientB) ^ 2 = 1 := by
  apply (QuotientGroup.eq_one_iff (((a : P) * b) ^ 2)).mpr
  exact ⟨0, 0, 1, by simp [z]⟩

private lemma quotientA_inv : quotientA⁻¹ = quotientA := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using quotientA_sq

private lemma quotientB_inv : quotientB⁻¹ = quotientB := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using quotientB_sq

private lemma quotientAB_inv : (quotientA * quotientB)⁻¹ = quotientA * quotientB := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using quotientAB_sq

private lemma quotientA_commute_quotientB : quotientA * quotientB = quotientB * quotientA := by
  calc
    quotientA * quotientB = (quotientA * quotientB)⁻¹ := quotientAB_inv.symm
    _ = quotientB⁻¹ * quotientA⁻¹ := mul_inv_rev _ _
    _ = quotientB * quotientA := by rw [quotientA_inv, quotientB_inv]

private lemma quotientA_mul_self : quotientA * quotientA = 1 := by
  simpa only [pow_two] using quotientA_sq

private lemma quotientB_mul_self : quotientB * quotientB = 1 := by
  simpa only [pow_two] using quotientB_sq

private lemma quotientAB_mul_self :
    (quotientA * quotientB) * (quotientA * quotientB) = 1 := by
  simpa only [pow_two] using quotientAB_sq

private lemma quotientB_mul_quotientA : quotientB * quotientA = quotientA * quotientB :=
  quotientA_commute_quotientB.symm

private lemma quotientA_mul_quotientAB :
    quotientA * (quotientA * quotientB) = quotientB := by
  rw [← mul_assoc, quotientA_mul_self, one_mul]

private lemma quotientAB_mul_quotientA :
    (quotientA * quotientB) * quotientA = quotientB := by
  rw [quotientA_commute_quotientB, mul_assoc, quotientA_mul_self, mul_one]

private lemma quotientB_mul_quotientAB :
    quotientB * (quotientA * quotientB) = quotientA := by
  calc
    quotientB * (quotientA * quotientB) = (quotientB * quotientA) * quotientB := by group
    _ = (quotientA * quotientB) * quotientB := by rw [quotientB_mul_quotientA]
    _ = quotientA := by rw [mul_assoc, quotientB_mul_self, mul_one]

private lemma quotientAB_mul_quotientB :
    (quotientA * quotientB) * quotientB = quotientA := by
  rw [mul_assoc, quotientB_mul_self, mul_one]

private def quotientFour : Subgroup TranslationQuotient where
  carrier := {1, quotientA, quotientB, quotientA * quotientB}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh ⊢
    rcases hg with rfl | rfl | rfl | rfl <;>
      rcases hh with rfl | rfl | rfl | rfl
    all_goals simp only [one_mul, mul_one, quotientA_mul_self, quotientB_mul_self,
      quotientAB_mul_self, quotientB_mul_quotientA, quotientA_mul_quotientAB,
      quotientAB_mul_quotientA, quotientB_mul_quotientAB, quotientAB_mul_quotientB]
    all_goals aesop
  inv_mem' := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl quotientA_inv)
    · exact Or.inr (Or.inr (Or.inl quotientB_inv))
    · exact Or.inr (Or.inr (Or.inr quotientAB_inv))

private lemma quotientFour_eq_top : quotientFour = ⊤ := by
  apply top_unique
  intro q _
  refine Quotient.inductionOn' q ?_
  intro g
  apply PresentedGroup.generated_by relations
    (quotientFour.comap (QuotientGroup.mk' translations))
  intro c
  cases c with
  | a =>
      change quotientA ∈ quotientFour
      exact Or.inr (Or.inl rfl)
  | b =>
      change quotientB ∈ quotientFour
      exact Or.inr (Or.inr (Or.inl rfl))

private lemma exists_normal_form (g : P) :
    ∃ i j k : ℤ,
      g = x ^ i * y ^ j * z ^ k ∨
      g = x ^ i * y ^ j * z ^ k * a ∨
      g = x ^ i * y ^ j * z ^ k * b ∨
      g = x ^ i * y ^ j * z ^ k * (a * b) := by
  have hq : (g : TranslationQuotient) ∈ quotientFour := by
    rw [quotientFour_eq_top]
    trivial
  simp only [quotientFour] at hq
  rcases hq with hq | hq | hq | hq
  · obtain ⟨i, j, k, hg⟩ := (QuotientGroup.eq_one_iff g).mp hq
    exact ⟨i, j, k, Or.inl hg⟩
  · obtain ⟨i, j, k, hg⟩ := (QuotientGroup.eq_iff_div_mem.mp hq)
    refine ⟨i, j, k, Or.inr (Or.inl ?_)⟩
    calc
      g = g / (a : P) * (a : P) := by simp
      _ = x ^ i * y ^ j * z ^ k * (a : P) := by rw [hg]
  · obtain ⟨i, j, k, hg⟩ := (QuotientGroup.eq_iff_div_mem.mp hq)
    refine ⟨i, j, k, Or.inr (Or.inr (Or.inl ?_))⟩
    calc
      g = g / (b : P) * (b : P) := by simp
      _ = x ^ i * y ^ j * z ^ k * (b : P) := by rw [hg]
  · obtain ⟨i, j, k, hg⟩ := (QuotientGroup.eq_iff_div_mem.mp hq)
    refine ⟨i, j, k, Or.inr (Or.inr (Or.inr ?_))⟩
    calc
      g = g / ((a : P) * (b : P)) * ((a : P) * (b : P)) := by simp
      _ = x ^ i * y ^ j * z ^ k * ((a : P) * (b : P)) := by rw [hg]

private lemma affineTranslation_apply (i j k : ℤ) (v : Point) :
    affineRepresentation (x ^ i * y ^ j * z ^ k) v =
      ⟨v.i + 2 * i, v.j + 2 * j, v.k + 2 * k⟩ := by
  simp only [map_mul, map_zpow, affineRepresentation_x, affineRepresentation_y,
    affineRepresentation_z, Equiv.Perm.mul_apply]
  rw [affineZ_zpow_apply, affineY_zpow_apply, affineX_zpow_apply]

private lemma affineTranslationA_i (i j k : ℤ) (v : Point) :
    (affineRepresentation (x ^ i * y ^ j * z ^ k * a) v).i =
      v.i + (2 * i + 1) := by
  calc
    (affineRepresentation (x ^ i * y ^ j * z ^ k * a) v).i =
        (affineRepresentation (x ^ i * y ^ j * z ^ k) (affineA v)).i := by
      simp only [map_mul, affineRepresentation_a, Equiv.Perm.mul_apply]
    _ = (affineA v).i + 2 * i := by rw [affineTranslation_apply]
    _ = v.i + (2 * i + 1) := by simp [affineA]; omega

private lemma affineTranslationB_j (i j k : ℤ) (v : Point) :
    (affineRepresentation (x ^ i * y ^ j * z ^ k * b) v).j =
      v.j + (2 * j + 1) := by
  calc
    (affineRepresentation (x ^ i * y ^ j * z ^ k * b) v).j =
        (affineRepresentation (x ^ i * y ^ j * z ^ k) (affineB v)).j := by
      simp only [map_mul, affineRepresentation_b, Equiv.Perm.mul_apply]
    _ = (affineB v).j + 2 * j := by rw [affineTranslation_apply]
    _ = v.j + (2 * j + 1) := by simp [affineB]; omega

private lemma affineTranslationAB_k (i j k : ℤ) (v : Point) :
    (affineRepresentation (x ^ i * y ^ j * z ^ k * (a * b)) v).k =
      v.k + (2 * k + 1) := by
  calc
    (affineRepresentation (x ^ i * y ^ j * z ^ k * (a * b)) v).k =
        (affineRepresentation (x ^ i * y ^ j * z ^ k) (affineA (affineB v))).k := by
      simp only [map_mul, affineRepresentation_a, affineRepresentation_b, Equiv.Perm.mul_apply]
    _ = (affineA (affineB v)).k + 2 * k := by rw [affineTranslation_apply]
    _ = v.k + (2 * k + 1) := by simp [affineA, affineB]; omega

private lemma perm_pow_i_of_shift (f : Equiv.Perm Point) (d : ℤ)
    (h : ∀ v, (f v).i = v.i + d) (n : ℕ) (v : Point) :
    ((f ^ n) v).i = v.i + n * d := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih (f v), h]
      push_cast
      ring

private lemma perm_pow_j_of_shift (f : Equiv.Perm Point) (d : ℤ)
    (h : ∀ v, (f v).j = v.j + d) (n : ℕ) (v : Point) :
    ((f ^ n) v).j = v.j + n * d := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih (f v), h]
      push_cast
      ring

private lemma perm_pow_k_of_shift (f : Equiv.Perm Point) (d : ℤ)
    (h : ∀ v, (f v).k = v.k + d) (n : ℕ) (v : Point) :
    ((f ^ n) v).k = v.k + n * d := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih (f v), h]
      push_cast
      ring

private lemma torsion_free_P : ∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1 := by
  intro g n hn hpow
  obtain ⟨i, j, k, hg | hg | hg | hg⟩ := exists_normal_form g
  · subst g
    have hp : (affineRepresentation (x ^ i * y ^ j * z ^ k)) ^ n = 1 := by
      simpa only [map_pow, map_one] using congrArg affineRepresentation hpow
    have happ := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hp
    have hi := congrArg Point.i happ
    have hj := congrArg Point.j happ
    have hk := congrArg Point.k happ
    rw [perm_pow_i_of_shift _ (2 * i) (fun v => by rw [affineTranslation_apply]) n] at hi
    rw [perm_pow_j_of_shift _ (2 * j) (fun v => by rw [affineTranslation_apply]) n] at hj
    rw [perm_pow_k_of_shift _ (2 * k) (fun v => by rw [affineTranslation_apply]) n] at hk
    simp only [zero_add] at hi hj hk
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have hi' : 2 * i = 0 := (mul_eq_zero.mp hi).resolve_left hn'
    have hj' : 2 * j = 0 := (mul_eq_zero.mp hj).resolve_left hn'
    have hk' : 2 * k = 0 := (mul_eq_zero.mp hk).resolve_left hn'
    have : i = 0 ∧ j = 0 ∧ k = 0 := by omega
    rcases this with ⟨rfl, rfl, rfl⟩
    simp
  · subst g
    have hp : (affineRepresentation (x ^ i * y ^ j * z ^ k * a)) ^ n = 1 := by
      simpa only [map_pow, map_one] using congrArg affineRepresentation hpow
    have happ := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hp
    have hi := congrArg Point.i happ
    rw [perm_pow_i_of_shift _ (2 * i + 1) (affineTranslationA_i i j k) n] at hi
    simp only [zero_add] at hi
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have : 2 * i + 1 = 0 := (mul_eq_zero.mp hi).resolve_left hn'
    omega
  · subst g
    have hp : (affineRepresentation (x ^ i * y ^ j * z ^ k * b)) ^ n = 1 := by
      simpa only [map_pow, map_one] using congrArg affineRepresentation hpow
    have happ := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hp
    have hj := congrArg Point.j happ
    rw [perm_pow_j_of_shift _ (2 * j + 1) (affineTranslationB_j i j k) n] at hj
    simp only [zero_add] at hj
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have : 2 * j + 1 = 0 := (mul_eq_zero.mp hj).resolve_left hn'
    omega
  · subst g
    have hp : (affineRepresentation (x ^ i * y ^ j * z ^ k * (a * b))) ^ n = 1 := by
      simpa only [map_pow, map_one] using congrArg affineRepresentation hpow
    have happ := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hp
    have hk := congrArg Point.k happ
    rw [perm_pow_k_of_shift _ (2 * k + 1) (affineTranslationAB_k i j k) n] at hk
    simp only [zero_add] at hk
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
    have : 2 * k + 1 = 0 := (mul_eq_zero.mp hk).resolve_left hn'
    omega

private lemma affineRepresentation_eq_one (g : P) (hg : affineRepresentation g = 1) : g = 1 := by
  obtain ⟨i, j, k, h | h | h | h⟩ := exists_normal_form g
  · subst g
    have hv := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hg
    rw [affineTranslation_apply] at hv
    have hi := congrArg Point.i hv
    have hj := congrArg Point.j hv
    have hk := congrArg Point.k hv
    simp at hi hj hk
    have : i = 0 ∧ j = 0 ∧ k = 0 := by omega
    rcases this with ⟨rfl, rfl, rfl⟩
    simp
  · subst g
    have hv := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hg
    have hi := congrArg Point.i hv
    rw [affineTranslationA_i] at hi
    simp at hi
    omega
  · subst g
    have hv := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hg
    have hj := congrArg Point.j hv
    rw [affineTranslationB_j] at hj
    simp at hj
    omega
  · subst g
    have hv := congrArg (fun f : Equiv.Perm Point => f ⟨0, 0, 0⟩) hg
    have hk := congrArg Point.k hv
    rw [affineTranslationAB_k] at hk
    simp at hk
    omega

private lemma affineRepresentation_injective : Function.Injective affineRepresentation := by
  intro g h hgh
  apply eq_of_mul_inv_eq_one
  apply affineRepresentation_eq_one
  simp [hgh]

private def T (i j k : ℤ) : P := x ^ i * y ^ j * z ^ k

private def TA (i j k : ℤ) : P := T i j k * a

private def TB (i j k : ℤ) : P := T i j k * b

private def TAB (i j k : ℤ) : P := T i j k * (a * b)

private lemma affineT_apply (i j k : ℤ) (v : Point) :
    affineRepresentation (T i j k) v = ⟨v.i + 2 * i, v.j + 2 * j, v.k + 2 * k⟩ := by
  simpa only [T] using affineTranslation_apply i j k v

private lemma T_mul_T (i j k l m n : ℤ) :
    T i j k * T l m n = T (i + l) (j + m) (k + n) := by
  apply affineRepresentation_injective
  ext v
  simp only [map_mul, Equiv.Perm.mul_apply]
  rw [affineT_apply, affineT_apply, affineT_apply]
  rcases v with ⟨vi, vj, vk⟩
  simp [Point.mk.injEq]
  constructor <;> omega

private lemma T_zero : T 0 0 0 = 1 := by
  simp [T]

private lemma a_mul_T (i j k : ℤ) : (a : P) * T i j k = T i (-j) (-k) * a := by
  simp only [T]
  calc
    (a : P) * (x ^ i * y ^ j * z ^ k) =
        ((a : P) * (x ^ i * y ^ j * z ^ k) * (a : P)⁻¹) * a := by group
    _ = (x ^ i * y ^ (-j) * z ^ (-k)) * a := by rw [conjugate_translation_left_by_a]

private lemma b_mul_T (i j k : ℤ) : (b : P) * T i j k = T (-i) j (-k) * b := by
  simp only [T]
  calc
    (b : P) * (x ^ i * y ^ j * z ^ k) =
        ((b : P) * (x ^ i * y ^ j * z ^ k) * (b : P)⁻¹) * b := by group
    _ = (x ^ (-i) * y ^ j * z ^ (-k)) * b := by rw [conjugate_translation_left_by_b]

private lemma ab_mul_T (i j k : ℤ) :
    ((a : P) * b) * T i j k = T (-i) (-j) k * (a * b) := by
  calc
    ((a : P) * b) * T i j k = (a : P) * (b * T i j k) := by group
    _ = (a : P) * (T (-i) j (-k) * b) := by rw [b_mul_T]
    _ = ((a : P) * T (-i) j (-k)) * b := by group
    _ = (T (-i) (-j) (- -k) * a) * b := by rw [a_mul_T]
    _ = (T (-i) (-j) k * a) * b := by simp
    _ = T (-i) (-j) k * (a * b) := by group

private lemma b_mul_a : (b : P) * a = T (-1) 1 (-1) * (a * b) := by
  apply affineRepresentation_injective
  ext v
  rcases v with ⟨vi, vj, vk⟩
  simp only [map_mul, affineRepresentation_a, affineRepresentation_b, Equiv.Perm.mul_apply]
  rw [affineT_apply]
  simp [affineA, affineB, Point.mk.injEq]
  omega

private lemma b_mul_ab : (b : P) * (a * b) = T (-1) 0 (-1) * a := by
  apply affineRepresentation_injective
  ext v
  rcases v with ⟨vi, vj, vk⟩
  simp only [map_mul, affineRepresentation_a, affineRepresentation_b, Equiv.Perm.mul_apply]
  rw [affineT_apply]
  simp [affineA, affineB, Point.mk.injEq]
  omega

private lemma ab_mul_a : ((a : P) * b) * a = T 0 (-1) 1 * b := by
  apply affineRepresentation_injective
  ext v
  rcases v with ⟨vi, vj, vk⟩
  simp only [map_mul, affineRepresentation_a, affineRepresentation_b, Equiv.Perm.mul_apply]
  rw [affineT_apply]
  simp [affineA, affineB, Point.mk.injEq]
  omega

private lemma ab_mul_b : ((a : P) * b) * b = T 0 (-1) 0 * a := by
  apply affineRepresentation_injective
  ext v
  rcases v with ⟨vi, vj, vk⟩
  simp only [map_mul, affineRepresentation_a, affineRepresentation_b, Equiv.Perm.mul_apply]
  rw [affineT_apply]
  simp [affineA, affineB, Point.mk.injEq]
  omega

private lemma a_mul_a : (a : P) * a = T 1 0 0 := by
  simp [T, x, pow_two]

private lemma b_mul_b : (b : P) * b = T 0 1 0 := by
  simp [T, y, pow_two]

private lemma ab_mul_ab : ((a : P) * b) * (a * b) = T 0 0 1 := by
  simp [T, z, pow_two]

private lemma T_mul_TA (i j k l m n : ℤ) :
    T i j k * TA l m n = TA (i + l) (j + m) (k + n) := by
  unfold TA
  calc
    T i j k * (T l m n * a) = (T i j k * T l m n) * a := by group
    _ = T (i + l) (j + m) (k + n) * a := by rw [T_mul_T]

private lemma T_mul_TB (i j k l m n : ℤ) :
    T i j k * TB l m n = TB (i + l) (j + m) (k + n) := by
  unfold TB
  calc
    T i j k * (T l m n * b) = (T i j k * T l m n) * b := by group
    _ = T (i + l) (j + m) (k + n) * b := by rw [T_mul_T]

private lemma T_mul_TAB (i j k l m n : ℤ) :
    T i j k * TAB l m n = TAB (i + l) (j + m) (k + n) := by
  unfold TAB
  calc
    T i j k * (T l m n * (a * b)) = (T i j k * T l m n) * (a * b) := by group
    _ = T (i + l) (j + m) (k + n) * (a * b) := by rw [T_mul_T]

private lemma TA_mul_T (i j k l m n : ℤ) :
    TA i j k * T l m n = TA (i + l) (j - m) (k - n) := by
  unfold TA
  calc
    (T i j k * a) * T l m n = T i j k * (a * T l m n) := by group
    _ = T i j k * (T l (-m) (-n) * a) := by rw [a_mul_T]
    _ = (T i j k * T l (-m) (-n)) * a := by group
    _ = T (i + l) (j + -m) (k + -n) * a := by rw [T_mul_T]
    _ = T (i + l) (j - m) (k - n) * a := by rfl

private lemma TA_mul_TA (i j k l m n : ℤ) :
    TA i j k * TA l m n = T (i + l + 1) (j - m) (k - n) := by
  unfold TA
  calc
    (T i j k * a) * (T l m n * a) =
        T i j k * (a * T l m n) * a := by group
    _ = T i j k * (T l (-m) (-n) * a) * a := by rw [a_mul_T]
    _ = (T i j k * T l (-m) (-n)) * (a * a) := by group
    _ = T (i + l) (j + -m) (k + -n) * (a * a) := by rw [T_mul_T]
    _ = T (i + l) (j + -m) (k + -n) * T 1 0 0 := by rw [a_mul_a]
    _ = T (i + l + 1) (j - m) (k - n) := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TA_mul_TB (i j k l m n : ℤ) :
    TA i j k * TB l m n = TAB (i + l) (j - m) (k - n) := by
  unfold TA TB TAB
  calc
    (T i j k * a) * (T l m n * b) =
        T i j k * (a * T l m n) * b := by group
    _ = T i j k * (T l (-m) (-n) * a) * b := by rw [a_mul_T]
    _ = (T i j k * T l (-m) (-n)) * (a * b) := by group
    _ = T (i + l) (j + -m) (k + -n) * (a * b) := by rw [T_mul_T]
    _ = T (i + l) (j - m) (k - n) * (a * b) := by rfl

private lemma TA_mul_TAB (i j k l m n : ℤ) :
    TA i j k * TAB l m n = TB (i + l + 1) (j - m) (k - n) := by
  unfold TA TAB TB
  calc
    (T i j k * a) * (T l m n * (a * b)) =
        T i j k * (a * T l m n) * (a * b) := by group
    _ = T i j k * (T l (-m) (-n) * a) * (a * b) := by rw [a_mul_T]
    _ = (T i j k * T l (-m) (-n)) * (a * a) * b := by group
    _ = T (i + l) (j + -m) (k + -n) * (a * a) * b := by rw [T_mul_T]
    _ = (T (i + l) (j + -m) (k + -n) * T 1 0 0) * b := by rw [a_mul_a]
    _ = T (i + l + 1) (j - m) (k - n) * b := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TB_mul_T (i j k l m n : ℤ) :
    TB i j k * T l m n = TB (i - l) (j + m) (k - n) := by
  unfold TB
  calc
    (T i j k * b) * T l m n = T i j k * (b * T l m n) := by group
    _ = T i j k * (T (-l) m (-n) * b) := by rw [b_mul_T]
    _ = (T i j k * T (-l) m (-n)) * b := by group
    _ = T (i + -l) (j + m) (k + -n) * b := by rw [T_mul_T]
    _ = T (i - l) (j + m) (k - n) * b := by rfl

private lemma TB_mul_TA (i j k l m n : ℤ) :
    TB i j k * TA l m n = TAB (i - l - 1) (j + m + 1) (k - n - 1) := by
  unfold TB TA TAB
  calc
    (T i j k * b) * (T l m n * a) =
        T i j k * (b * T l m n) * a := by group
    _ = T i j k * (T (-l) m (-n) * b) * a := by rw [b_mul_T]
    _ = (T i j k * T (-l) m (-n)) * (b * a) := by group
    _ = T (i + -l) (j + m) (k + -n) * (b * a) := by rw [T_mul_T]
    _ = T (i + -l) (j + m) (k + -n) * (T (-1) 1 (-1) * (a * b)) := by rw [b_mul_a]
    _ = (T (i + -l) (j + m) (k + -n) * T (-1) 1 (-1)) * (a * b) := by group
    _ = T (i - l - 1) (j + m + 1) (k - n - 1) * (a * b) := by
      rw [T_mul_T]
      rfl

private lemma TB_mul_TB (i j k l m n : ℤ) :
    TB i j k * TB l m n = T (i - l) (j + m + 1) (k - n) := by
  unfold TB
  calc
    (T i j k * b) * (T l m n * b) =
        T i j k * (b * T l m n) * b := by group
    _ = T i j k * (T (-l) m (-n) * b) * b := by rw [b_mul_T]
    _ = (T i j k * T (-l) m (-n)) * (b * b) := by group
    _ = T (i + -l) (j + m) (k + -n) * (b * b) := by rw [T_mul_T]
    _ = T (i + -l) (j + m) (k + -n) * T 0 1 0 := by rw [b_mul_b]
    _ = T (i - l) (j + m + 1) (k - n) := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TB_mul_TAB (i j k l m n : ℤ) :
    TB i j k * TAB l m n = TA (i - l - 1) (j + m) (k - n - 1) := by
  unfold TB TAB TA
  calc
    (T i j k * b) * (T l m n * (a * b)) =
        T i j k * (b * T l m n) * (a * b) := by group
    _ = T i j k * (T (-l) m (-n) * b) * (a * b) := by rw [b_mul_T]
    _ = (T i j k * T (-l) m (-n)) * (b * (a * b)) := by group
    _ = T (i + -l) (j + m) (k + -n) * (b * (a * b)) := by rw [T_mul_T]
    _ = T (i + -l) (j + m) (k + -n) * (T (-1) 0 (-1) * a) := by rw [b_mul_ab]
    _ = (T (i + -l) (j + m) (k + -n) * T (-1) 0 (-1)) * a := by group
    _ = T (i - l - 1) (j + m) (k - n - 1) * a := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TAB_mul_T (i j k l m n : ℤ) :
    TAB i j k * T l m n = TAB (i - l) (j - m) (k + n) := by
  unfold TAB
  calc
    (T i j k * (a * b)) * T l m n = T i j k * ((a * b) * T l m n) := by group
    _ = T i j k * (T (-l) (-m) n * (a * b)) := by rw [ab_mul_T]
    _ = (T i j k * T (-l) (-m) n) * (a * b) := by group
    _ = T (i + -l) (j + -m) (k + n) * (a * b) := by rw [T_mul_T]
    _ = T (i - l) (j - m) (k + n) * (a * b) := by rfl

private lemma TAB_mul_TA (i j k l m n : ℤ) :
    TAB i j k * TA l m n = TB (i - l) (j - m - 1) (k + n + 1) := by
  unfold TAB TA TB
  calc
    (T i j k * (a * b)) * (T l m n * a) =
        T i j k * ((a * b) * T l m n) * a := by group
    _ = T i j k * (T (-l) (-m) n * (a * b)) * a := by rw [ab_mul_T]
    _ = (T i j k * T (-l) (-m) n) * ((a * b) * a) := by group
    _ = T (i + -l) (j + -m) (k + n) * ((a * b) * a) := by rw [T_mul_T]
    _ = T (i + -l) (j + -m) (k + n) * (T 0 (-1) 1 * b) := by rw [ab_mul_a]
    _ = (T (i + -l) (j + -m) (k + n) * T 0 (-1) 1) * b := by group
    _ = T (i - l) (j - m - 1) (k + n + 1) * b := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TAB_mul_TB (i j k l m n : ℤ) :
    TAB i j k * TB l m n = TA (i - l) (j - m - 1) (k + n) := by
  unfold TAB TB TA
  calc
    (T i j k * (a * b)) * (T l m n * b) =
        T i j k * ((a * b) * T l m n) * b := by group
    _ = T i j k * (T (-l) (-m) n * (a * b)) * b := by rw [ab_mul_T]
    _ = (T i j k * T (-l) (-m) n) * ((a * b) * b) := by group
    _ = T (i + -l) (j + -m) (k + n) * ((a * b) * b) := by rw [T_mul_T]
    _ = T (i + -l) (j + -m) (k + n) * (T 0 (-1) 0 * a) := by rw [ab_mul_b]
    _ = (T (i + -l) (j + -m) (k + n) * T 0 (-1) 0) * a := by group
    _ = T (i - l) (j - m - 1) (k + n) * a := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private lemma TAB_mul_TAB (i j k l m n : ℤ) :
    TAB i j k * TAB l m n = T (i - l) (j - m) (k + n + 1) := by
  unfold TAB
  calc
    (T i j k * (a * b)) * (T l m n * (a * b)) =
        T i j k * ((a * b) * T l m n) * (a * b) := by group
    _ = T i j k * (T (-l) (-m) n * (a * b)) * (a * b) := by rw [ab_mul_T]
    _ = (T i j k * T (-l) (-m) n) * ((a * b) * (a * b)) := by group
    _ = T (i + -l) (j + -m) (k + n) * ((a * b) * (a * b)) := by rw [T_mul_T]
    _ = T (i + -l) (j + -m) (k + n) * T 0 0 1 := by rw [ab_mul_ab]
    _ = T (i - l) (j - m) (k + n + 1) := by
      rw [T_mul_T]
      simp [sub_eq_add_neg]

private def U : R :=
  T 0 0 0 + T 1 0 0 + T 0 1 0 + T 1 1 0 +
  T 0 0 (-1) + T 1 0 (-1) + T 0 1 (-1) + T 1 1 (-1) +
  TA (-1) (-1) 0 + TA 1 0 0 + TA 0 (-1) 1 + TA 0 0 1 +
  TB 0 0 0 + TB 1 0 0 + TB 0 (-1) 1 + TB 1 1 1 +
  TAB 0 0 0 + TAB 1 0 (-1) + TAB (-1) 0 (-1) + TAB 0 1 (-1) + TAB 0 (-1) (-1)

private def V : R :=
  T 0 0 0 + T (-1) 0 0 + T 0 (-1) 0 + T (-1) (-1) 0 +
  T 0 0 1 + T (-1) 0 1 + T 0 (-1) 1 + T (-1) (-1) 1 +
  TA (-2) (-1) 0 + TA (-1) (-1) 1 + TA (-1) 0 1 + TA 0 0 0 +
  TB 0 (-2) 1 + TB 0 (-1) 0 + TB 1 (-1) 0 + TB 1 0 1 +
  TAB (-1) 0 0 + TAB 0 (-1) 0 + TAB 0 0 (-1) + TAB 0 1 0 + TAB 1 0 0

private lemma u_eq_U : u = U := by
  simp [u, p, q, r, s, U, T, TA, TB, TAB, add_mul, mul_add]
  module

private def oneCoeff : ZMod 2 := 1

private lemma oneCoeff_smul (w : R) : oneCoeff • w = w := by
  simp [oneCoeff]

private lemma U_mul_V : U * V = 1 := by
  simp [U, V, T_mul_T, T_mul_TA, T_mul_TB, T_mul_TAB,
    TA_mul_T, TA_mul_TA, TA_mul_TB, TA_mul_TAB,
    TB_mul_T, TB_mul_TA, TB_mul_TB, TB_mul_TAB,
    TAB_mul_T, TAB_mul_TA, TAB_mul_TB, TAB_mul_TAB,
    T_zero, add_mul, mul_add]
  rw [← oneCoeff_smul (1 : R)]
  match_scalars
  all_goals decide

private lemma V_mul_U : V * U = 1 := by
  simp [U, V, T_mul_T, T_mul_TA, T_mul_TB, T_mul_TAB,
    TA_mul_T, TA_mul_TA, TA_mul_TB, TA_mul_TAB,
    TB_mul_T, TB_mul_TA, TB_mul_TB, TB_mul_TAB,
    TAB_mul_T, TAB_mul_TA, TAB_mul_TB, TAB_mul_TAB,
    T_zero, add_mul, mul_add]
  rw [← oneCoeff_smul (1 : R)]
  match_scalars
  all_goals decide

private def unitU : Rˣ where
  val := U
  inv := V
  val_inv := U_mul_V
  inv_val := V_mul_U

private lemma isUnit_u : IsUnit u := by
  rw [u_eq_U]
  exact unitU.isUnit

@[simp] private lemma T_eq_T_iff (i j k l m n : ℤ) :
    T i j k = T l m n ↔ i = l ∧ j = m ∧ k = n := by
  constructor
  · intro h
    have hv := congrArg (fun g : P => affineRepresentation g ⟨0, 0, 0⟩) h
    rw [affineT_apply, affineT_apply] at hv
    have hi := congrArg Point.i hv
    have hj := congrArg Point.j hv
    have hk := congrArg Point.k hv
    simp at hi hj hk
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma affineTA_i (i j k : ℤ) (v : Point) :
    (affineRepresentation (TA i j k) v).i = v.i + (2 * i + 1) := by
  simpa only [TA, T] using affineTranslationA_i i j k v

private lemma affineTB_j (i j k : ℤ) (v : Point) :
    (affineRepresentation (TB i j k) v).j = v.j + (2 * j + 1) := by
  simpa only [TB, T] using affineTranslationB_j i j k v

private lemma affineTAB_k (i j k : ℤ) (v : Point) :
    (affineRepresentation (TAB i j k) v).k = v.k + (2 * k + 1) := by
  simpa only [TAB, T] using affineTranslationAB_k i j k v

@[simp] private lemma TA_ne_T (i j k l m n : ℤ) : TA i j k ≠ T l m n := by
  intro h
  have hv := congrArg (fun g : P => affineRepresentation g ⟨0, 0, 0⟩) h
  have hi := congrArg Point.i hv
  rw [affineTA_i, affineT_apply] at hi
  simp at hi
  omega

@[simp] private lemma TB_ne_T (i j k l m n : ℤ) : TB i j k ≠ T l m n := by
  intro h
  have hv := congrArg (fun g : P => affineRepresentation g ⟨0, 0, 0⟩) h
  have hj := congrArg Point.j hv
  rw [affineTB_j, affineT_apply] at hj
  simp at hj
  omega

@[simp] private lemma TAB_ne_T (i j k l m n : ℤ) : TAB i j k ≠ T l m n := by
  intro h
  have hv := congrArg (fun g : P => affineRepresentation g ⟨0, 0, 0⟩) h
  have hk := congrArg Point.k hv
  rw [affineTAB_k, affineT_apply] at hk
  simp at hk
  omega

private lemma U_apply_T_zero : U.coeff (T 0 0 0) = 1 := by
  simp [U, MonoidAlgebra.of_apply]

private lemma U_apply_T_x : U.coeff (T 1 0 0) = 1 := by
  simp [U, MonoidAlgebra.of_apply]

private lemma u_not_monomial : ¬ ∃ g : P, u = g := by
  rintro ⟨g, h⟩
  have hU : U = (g : R) := u_eq_U.symm.trans h
  have hzero := congrArg (fun w : R => w.coeff (T 0 0 0)) hU
  have hx := congrArg (fun w : R => w.coeff (T 1 0 0)) hU
  rw [U_apply_T_zero] at hzero
  rw [U_apply_T_x] at hx
  have hgzero : g = T 0 0 0 := by
    by_contra hne
    simp [MonoidAlgebra.of_apply, hne] at hzero
  have hgx : g = T 1 0 0 := by
    by_contra hne
    simp [MonoidAlgebra.of_apply, hne] at hx
  have htx : T 0 0 0 = T 1 0 0 := hgzero.symm.trans hgx
  have := (T_eq_T_iff 0 0 0 1 0 0).mp htx
  omega

theorem theorem_A : (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  exact ⟨torsion_free_P, isUnit_u, u_not_monomial⟩

end

end Submission
