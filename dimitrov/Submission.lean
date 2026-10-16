import Mathlib.NumberTheory.NumberField.House
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers

namespace Submission

theorem dimitrov {K : Type*} [Field K] [NumberField K]
    (α : K)
    (α_int : IsIntegral ℤ α)
    (α_ne_zero : α ≠ 0)
    (α_not_rootOfUnity : ¬ IsOfFinOrder α) :
    (2 : ℝ) ^ (1 / (4 * (Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg).card) : ℝ) ≤
      NumberField.house α := by
  exact Helpers.rpow_from_nat_power (NumberField.house α) _
    (NumberField.house_nonneg α) (Helpers.argument_card_pos α)
    (Helpers.house_power_lower_bound α α_int α_ne_zero α_not_rootOfUnity)
end Submission
