# Polynomial Factor Matching Checkpoint

Task `help_f9e206b7fe0e41e49174596683c59e8c`, revision 0, digest
`69a477346b36b5e12d649fb0d1c2018b53397328287b890fc83c4396eef79ea5`.
The assigned polynomial factor matching question is proved over every field,
which includes the requested specialization to rational polynomials.

## Saved Helpers

`Submission.Helpers.polynomial_dvd_of_irreducible_mul_eq_sq`,
`Submission/Helpers.lean:3658`:

```lean
{k : Type*} [Field k] {P Q G : Polynomial k}
(hP : Irreducible P) (hsq : G ^ 2 = P * Q) : P ∣ Q
```

Primality of the irreducible polynomial gives `P ∣ G`. Substitute `G=P*H`,
cancel the nonzero factor `P`, and obtain `Q=P*H^2`.

`Submission.Helpers.polynomial_eq_of_monic_irreducible_mul_eq_sq`,
`Submission/Helpers.lean:3669`:

```lean
{k : Type*} [Field k] {P Q G : Polynomial k}
(hP : P.Monic) (hPirr : Irreducible P) (hQ : Q.Monic)
(hdegree : Q.natDegree = P.natDegree)
(hsq : G ^ 2 = P * Q) : Q = P
```

Apply the preceding divisibility lemma and the library theorem
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`. Irreducibility of `Q`
is not needed. All inherited declarations, proofs, imports, options and
namespace context are preserved. No probe commands remain.

## Validation

The frozen `check_lean` check of final saved `Submission.lean` passed:
exitCode 0, timedOut false. It compiled Helpers uncached in 31536 ms and
Submission uncached in 6117 ms. Helpers had no diagnostics. Submission
reported only its preserved original `dimitrov` sorry warning.
`git diff --check` passed.

Final Helpers SHA256:
`70fe5882f4b41086aa4ad07b7a19b28a75300b9d0cafae08834e3e4b0d51e178`.
Unchanged Submission SHA256:
`4ccc782999c50bb2bfb202882f675c6c2dc34fa54fbe1609796c781e9177b84e`.
No git commit was created; git metadata is managed by the host.

## Integration And Remaining Gaps

The host should independently check and integrate the two new named helpers,
then specialize the second to the monic reverses of the transform factors.
Their monicity, equal degrees and first-factor irreducibility must still be
established at that application site. No second-factor irreducibility is
required.

All recovered helpers, including argument positivity and exact argument
halving in the degree-drop case, remain in place and compiled in this run.
The original `Submission.dimitrov` remains unproved. Sharp arbitrary-ray
energy, quantitative contraction, reciprocal-minpoly identification and
final number-field/induction integration remain outside this assignment.
Original-target acceptance and independent official local evaluation are
not claimed.
