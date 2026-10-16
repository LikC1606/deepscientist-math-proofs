import ChallengeDeps
import Submission.Helpers

open LorentzianPolynomials
open Finsupp Matrix MvPolynomial UpperHalfPlane

set_option autoImplicit false

namespace Submission

theorem theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d := by
  exact Set.Subset.antisymm (Helpers.closure_strict_subset_lorentzian n d hn)
    (Helpers.lorentzian_subset_closure_strict n d hn)
end Submission
