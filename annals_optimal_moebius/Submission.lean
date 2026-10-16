import ChallengeDeps
import Submission.Helpers

open OptimalMoebius
open Topology ContDiff

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Submission

theorem theorem_1_1 (a : ℝ) (ha : a > 0) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) :
    a > √3 := by
  exact Helpers.aspect_ratio_of_ordered_straight_family_certificate a ha f hf
    (Helpers.orderedStraightFamily_of_embedding a ha f hf)
end Submission
