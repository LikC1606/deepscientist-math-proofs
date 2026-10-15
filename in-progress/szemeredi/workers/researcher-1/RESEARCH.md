# Current checkpoint: fixed-majority density obstruction

The assigned mathematical audit is complete. No Lean source was edited, no library search was performed, and no new wrapper or conditional engine was introduced. The argument below is a mathematical reduction using the lead's reported checked cyclic amplification and the previously checked modulo-unwrapping helpers. The exact finite-color theorem is stated explicitly; its Lean integration is not claimed here.

## Precise fixed-density premise

Fix a real `c` with `0 < c < 1`, independent of progression length. Let `M_c` denote:

```text
For every length L there exists B_c(L) such that, for every n >= B_c(L),
every U subset {0,...,n-1} with |U| > c*n contains
an ordinary AP a+d*i, i<L, with d>=1.
```

The cases c=1/2 and c=0.9 are instances of this same premise. A version with `|U| >= c*n` is stronger and also suffices. The ordinary AP must lie in the represented subset of `[0,n)`, not merely be a modular AP with uncontrolled total span.

## Exact finite-color input

Only the following ordinary finite van der Waerden statement is needed:

```text
For all integers m>=1 and r>=1, there exists L>=m such that,
for every coloring chi:{0,...,L-1}->{0,...,r-1},
there exist p>=0, q>=1 and a color i<r with
p+q*j<L and chi(p+q*j)=i for every j<m.
```

In particular the selected index progression has positive step and its last index is below L. No density hypothesis or specified color is needed. A coloring defined on the whole ambient interval can equivalently be pulled back to the L progression indices.

## Finite-bound quantifier chain

Given a requested length k and density epsilon>0, the case k=0 is vacuous. Assume k>=1. Input densities greater than one are impossible on nonempty intervals; thus it suffices to consider 0<epsilon<=1.

1. Choose **r=r(epsilon,c)>=1**, independent of n, S, and all progression lengths below, so every subset S of a nonempty finite cyclic group of density at least epsilon has a union of at most r translates of density **strictly greater than c**. Averaging gives uncovered density at most `(1-epsilon)^r`; choose r with `(1-epsilon)^r < 1-c`. The lead has checked uniform finite-translate majority amplification for c=1/2. For any other fixed c<1, the same finite amplification mechanism can be repeated a fixed number of times, or the averaging estimate gives the displayed choice directly.
2. Put **m=2*k-1** and choose **L=W(m,r)** by the exact finite-color statement above.
3. Request the majority bound **B=B_c(L)**. Set **N=max(1,L,B)**. All choices so far depend only on k, epsilon, and the fixed c.
4. Now take any **n>=N** and **S subset [0,n)** with `|S|>=epsilon*n`. Identify S with its injective residue image in Z/nZ (n>=1); cardinality is preserved. Obtain at most r shifts t_i whose union U has `|U|>c*n`.
5. Choose the ordinary representatives **V={x<n : x mod n belongs to U}**. The representative map is a bijection, so `|V|=|U|>c*n`. Apply M_c at length L to V. This gives an ordinary AP `x_h=a+d*h` for h<L with d>=1 and all x_h<n.
6. Assign to each index h<L a color i<r with `x_h mod n in S+t_i`. If there are fewer than r shifts, label them among r colors; the union is nonempty because c>0 and n>=1. Use the least available label, for example. The finite-color theorem gives indices `p+q*j`, j<m, all the same color, q>=1.
7. Set **A=a+d*p**, **Bstep=d*q>=1**. The monochromatic subprogression is `A+Bstep*j`, j<m, entirely below n. Its last point is `<n`, so **Bstep*(m-1)<n**, hence **Bstep*(2*k-2)<n**. This is the precise ordinary-span bound required for unwrapping.
8. Let w<n represent the inverse shift `-t_i` in Z/nZ. For every j<m, membership in S+t_i gives **(A+Bstep*j+w)%n in S**; this uses that S consists of the canonical representatives in `[0,n)`. Apply the checked `ap_of_shifted_mod_membership` with k, A, Bstep, w, n. It yields a positive-step **ordinary k-AP in S**. Its midpoint argument takes the first k unwrapped terms if the middle term has not wrapped, otherwise the last k terms after subtracting n.

Thus the final finite bound is `N(k,epsilon)=max(1,W(2*k-1,r(epsilon,c)), B_c(W(2*k-1,r(epsilon,c))))`. This is an existential finite bound; no numerical growth estimate for W or B_c is required. All n and S quantifiers occur after choosing N.

## Mathematical difficulty

This chain proves: **M_c plus finite van der Waerden and cyclic amplification implies general finite positive-density Szemeredi**, for every fixed c in (0,1). Conversely, general finite positive-density Szemeredi immediately gives M_c by taking epsilon=c. Therefore the fixed-majority problem is equivalent to the full finite theorem relative to these standard finite combinatorial reductions. The majority restriction does not remove the substantive difficulty.

No simpler elementary majority proof follows from the available ingredients, and none was found in this audit. The elementary union bound for the simultaneous k membership conditions loses at most k times the complement density. It guarantees a progression only when the density exceeds `1-1/k`, which depends on k. A fixed c<1 cannot meet this criterion for all k. Similarly, intersecting two translates gives lower density at least `2*c-1`, which does not preserve the original fixed majority threshold under indefinite iteration. A large union of translates has its progression in some color only after a further finite-color argument; proving that union has arbitrarily long progressions at a fixed majority density is exactly M_c, not routine arithmetic.

The earlier circular inequality `(1-epsilon)^r < 1/W(2*k-1,r)` arises only when trying to replace M_c by the available length-dependent high-density bound. Assuming an actual fixed-c arbitrary-length theorem removes that parameter circularity, but it supplies a theorem equivalent to the original density result.

## Cube obstruction to the recurrence bridge

The proposed finite-dimensional cube does not force even a nonconstant 3-term AP, regardless of its dimension. For any `m`, take `a=0` and generators `d_i=3^i` (`0≤i<m`), and let

```text
C_m = { Σ_{i<m} ε_i 3^i : ε_i ∈ {0,1} }.
```

The generators have unique subset sums, so `C_m` is an `m`-dimensional cube with `2^m` points. If `x,y,z∈C_m` satisfy `x+z=2*y`, write their least ternary digits as `ε,η,ζ∈{0,1}`. Reduction modulo `3` gives `ε+ζ ≡ 2η (mod 3)`; since `ε+ζ∈{0,1,2}` and `2η∈{0,2}`, this forces `ε=η=ζ`. Subtracting that common digit and dividing by `3` gives the same equation for the remaining digits. Induction on `m` yields `x=y=z`. Thus no `C_m` contains a nonconstant 3AP, for arbitrarily large `m`.

This is a sparse construction (density `(2/3)^m` in its enclosing interval), so it does not contradict Szemerédi. It does show that repeated recurrence producing an aligned subset-sum cube, even with arbitrarily many independent positive generators, cannot by itself supply the missing arbitrary-length positive-density argument; an additional density/alignment input is essential.

## Tensor/extremal-count audit

Let `r_k(n)` be the largest size of a `k`-AP-free subset of `range n`. The checked `k=3` facts include `r_3(3)=2` and `r_3(9)≥5`, witnessed by `{0,1,3,7,8}`; hence direct submultiplicativity `r_k(mn)≤r_k(m)r_k(n)` already fails (`5>2²`). The witness is AP-free by checking each ordered pair `x<y` and observing that `2*y-x` is absent.

The elementary grid slicing bound is only

```text
r_k(m*n) ≤ min (m * r_k(n), n * r_k(m)).
```

Indeed, partition `range (m*n)` into `m` consecutive fibers of width `n`, or into `n` fixed-residue columns; every fiber and every column is itself `k`-AP-free. There is no multiplication because the AP-free patterns in different fibers need not align. The 3-by-3 witness above exhibits exactly this misalignment.

The checked square-block estimate gives, for a fixed block size `B=q²`, `r_k(B)≤Q=q*(q−1)−1`. Tiling an interval gives `r_k(N)≤Q*floor(N/B)+(N % B)`, so the limiting normalized extremal density is at most `Q/B<1`; iterating this estimate does not make the density tend to zero.

A genuinely stronger statement would be an approximate product inequality with vanishing normalized error, for example

```text
r_k(m*n) ≤ r_k(m)*r_k(n) + E(m,n),   E(m,n)/(m*n) → 0
```

as `m,n→∞` (the diagonal form `r_k(n²)≤r_k(n)²+o(n²)` already suffices). Subadditivity `r_k(a+b)≤r_k(a)+r_k(b)` gives a limit `α=lim r_k(n)/n`; the approximate product then yields `α≤α²`. Since the square-block bound gives `α<1`, this forces `α=0`, which is the desired finite-density conclusion for that `k`. Establishing such an error term requires new control of cross-fiber alignment (a density-increment/removal-type argument); it does not follow from the existing one-block counting estimate or the slicing bound.

## Graph-regularity audit for four-term APs

The installed theorem `szemeredi_regularity` has the conclusion

```text
∃ P : Finpartition univ,
  P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ bound ε l ∧ P.IsUniform G ε.
```

Here `P.IsUniform` controls edge densities for pairs of partition classes (and only for all but an `ε` fraction of those pairs). This is enough for the usual tripartite triangle encoding of one equation `x₀−2x₁+x₂=0`, but it does not control simultaneous three-variable face constraints.

For a four-term progression, put four variables `x₀,…,x₃` in four classes and define

```text
Fᵢ(x) = Σⱼ (j−i) * xⱼ = S₁ − i*S₀,
S₀ = Σⱼ xⱼ,  S₁ = Σⱼ j*xⱼ.
```

The four values `F₀,F₁,F₂,F₃` form an arithmetic progression, and the coefficient of `xᵢ` in `Fᵢ` is zero. Thus the condition `Fᵢ(x) ∈ A` is a 3-variable face relation on the classes other than `i`. A 4-AP is a compatible choice satisfying all four such 3-uniform constraints. Pairwise graph regularity sees only two-variable shadows and does not control this four-way intersection.

The obstruction is already visible in the coefficient matrix for the two equations
`x₀−2x₁+x₂=0` and `x₁−2x₂+x₃=0`:

```text
[[ 1, -2,  1,  0 ],
 [ 0,  1, -2,  1 ]].
```

Over characteristic different from `2,3`, its four columns are pairwise nonparallel, so its rank-two column matroid is `U₂,₄`. This is not the cycle matroid of a simple graph: a graph of cycle rank two with four distinct edges would need three vertices, but a simple graph on three vertices has at most three edges. Therefore the direct scalar-edge/cycle encoding used for triangles cannot be extended to four AP variables by adding one graph class.

Pairwise shadows can even be complete while the 3-face constraints are inconsistent. Over `𝔽₅`, impose on face `i` the weighted equation `Fᵢ(x)=cᵢ`, with `c=(0,0,0,1)`. Every coefficient of a variable present in a face is nonzero, so every pair of coordinates extends to a face edge; all pairwise shadows are complete and hence maximally regular. But `F₀=F₁=F₂=0` forces `S₀=S₁=0`, hence `F₃=0`, contradicting `c₃=1`. The missing input is therefore 3-uniform hypergraph regularity/counting (equivalently, a suitable complexity-two linear-forms or `U³` condition), not the installed pairwise graph regularity lemma.

## Evidence and remaining obligation

The preceding turn's `ap_of_cyclic_mod_membership` and `ap_of_shifted_mod_membership` were checked in Lean (standalone and dependent-source checks exitCode 0, timedOut false); the lead reported selective integration and an independent saved-source check. The lead also reported checked uniform-r majority amplification. These prior receipts are not new checks in this notes-only assignment. This worktree's Lean sources were left byte-for-byte unchanged and no new compiler run was needed.

The original `Submission.szemeredi` and the arbitrary-k finite-density theorem remain unproved. The missing substantive statement can equivalently be taken to be M_(1/2) for all L, or M_0.9 for all L. Only the amplification, coloring, ordinary-span calculation, and unwrapping are routine parts of this proposed route. No original acceptance, majority proof, axiom, or new assumption in a frozen statement is claimed.
