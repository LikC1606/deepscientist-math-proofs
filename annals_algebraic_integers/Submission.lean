import ChallengeDeps
import Submission.Helpers

open AlgebraicIntegers
open ComplexOrder

set_option autoImplicit false

namespace Submission

theorem theorem_1_1 : lambda_SSS < 1.89831 := by
  let : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨c, hc0, hc, hinfinite⟩ := Helpers.exists_small_trace_infinite_family
  exact lt_of_le_of_lt (Helpers.lambda_SSS_le_of_infinite c hc0 hinfinite) hc
end Submission
