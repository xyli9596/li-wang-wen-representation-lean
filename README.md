# Li–Wang–Wen exponential-sum representation: formalization and audit

Target: X.-Y. Li, J. Wang and Z.-T. Wen, *Representation of finite-order solutions
to linear differential equations with exponential-sum coefficients*,
J. Differential Equations **423 (2025)**, 118–132.
DOI: https://doi.org/10.1016/j.jde.2024.12.035
The supplied PDF's filename says 2024; the published volume is from 2025.

The main targets are Theorems 3.1, 3.2 and 3.5, Corollaries 3.3 and 3.4,
and Lemmas 5.1 and 5.2 of the Li–Wang–Wen paper. The current source adds
exact matrix substitution, normalized indicial roots, the logarithmic-degree
budget and extraction from arbitrary nontrivial finite-order solutions.
The coverage table below identifies the actual statements;
[statement-alignment.json](statement-alignment.json) records the paper pages,
hypotheses, conclusions and qualifications. Check
[verification/verification.json](verification/verification.json) for the
fresh compilation result and the exact checked source hashes.
The earlier CRG project's full Theorem 1.1 is a different theorem and is
not certified by this package.
The classical Wiman–Valiron derivative dependency is now proved in
[WimanValironTheorem.lean](WimanValironTheorem.lean) and
[WimanValironLimits.lean](WimanValironLimits.lean), with the quantitative
near-maximum error and a genuine finite-logarithmic-measure exceptional set.

## Coverage

| Paper item | Current scope | Entry point / remaining work |
| --- | --- | --- |
| Theorem 3.1 | Exact polynomial-lift substitution, including the displayed `Q M` matrices | `LiWangWenTheorem31.lean`, `LiWangWenMatrix31.lean`. The indicial-root implication uses `u(0) ≠ 0`; an arbitrary nonzero polynomial lift can be normalized by moving its zero order into the exponent. |
| Theorem 3.2 | Representation with indicial roots and the degree budget | `LiWangWen.theorem_3_2`, `theorem_3_2_recurrence`; polynomial-factor variants use `F_j,p = X^p`, whose degree is exactly `p`, and conclude `sum K_j ≤ n`. These conditions are conclusions, not hypotheses. |
| Corollary 3.3 | Equivalence for nontrivial solutions | `LiWangWen.corollary_3_3`, `corollary_3_3_recurrence`: from an arbitrary nonzero finite-order entire solution extract a polynomial solution with `u(0) ≠ 0` and an indicial root. The converse produces an actual nonzero solution. The `_matrix` and `_matrix_recurrence` wrappers use the literal equation (3.3). |
| Corollary 3.4 | Proved | `LiWangWen.corollary_3_4` includes the actual equation, entirety, finite order and nontriviality. A stronger statement allows a zero exponent; the paper's nonzero-exponent specialization follows. |
| Theorem 3.5 | Representation for every natural gamma and nonzero complex frequency, via two routes | `LiWangWen.frequency_finiteOrder_iff_isExponentialSum` and `frequency_finiteOrder_iff_isExponentialSum_direct`. Both use the actual pointwise ODE. |
| Lemma 5.1 | Three proved routes | `LiWangWen.lemma_5_1`: finite order implies exact order one and finite positive type for actual nonpolynomial entire solutions. `LiWangWen.lemma_5_1_direct` gives the independent direct WV proof via two-sided central-index bounds. `LiWangWen.lemma_5_1_via_single_branch` additionally proves the growth conclusion from the directly established global limit `nu(r)/r -> C > 0`. The general-gamma, nonzero-frequency growth result is also proved by representation. |
| Lemma 5.2 | Cancellation-safe polynomial coefficient extraction, including distinct-degree polynomial factors | `LiWangWen.lemma_5_2_mean_type` is the original mean-type entry; `LiWangWenLemma52.lean` extends `polynomial_coefficients_of_exp_bound` from monomials to nonzero polynomial factors with strictly increasing degrees. A finite exponential bound on the whole sum suffices; positive type is unnecessary. The paper assumes entire exp-coefficients, not arbitrary Laurent coefficients. |
| Supplementary Lemma 5.2′ | Complete punctured-plane coefficient theorem with finite Laurent conclusion | `LiWangWenLemma52Prime.lean`: `lemma_5_2_prime_of_representation_symmetric` accepts the whole sum `g` and proves each coefficient equals a Laurent sum over `[-N,N]` on `w≠0`. The only growth assumption is on the whole sum. `lemma_5_2_prime_holomorphic_at_zero` and `lemma_5_2_prime_entire` give ordinary polynomials on all of `ℂ`. |
| Examples 3.6–3.7 | Explicit solution substitutions checked | `LiWangWenExamples`. The finite-order space's dimension/classification is not proved by these examples. |
| Examples 3.8–3.9 | Open | Remaining identities and the nonexistence/classification arguments. |

Here `P : Fin (n+1) → Polynomial ℂ` includes the highest derivative coefficient.
The paper has `P n = 1` for gamma zero, and `P n = X^gamma` in general.
`Solves P f` is the actual pointwise differential equation with `iteratedDeriv`,
not an assumed residual. `shiftedEuler a u = X*u.derivative + C a*u`.
`IsExponentialSum` permits polynomial multipliers in `z`, and only linear
exponents, as in the paper. It is stronger than the older project's definition
of an exponential polynomial with arbitrary polynomial exponents.

## Ince dependencies

The general scalar Floquet decomposition for actual entire solutions is now
proved by `IncePeriodic.entire_solution_floquet`. Its hypotheses are entire
coefficients, a leading coefficient nonzero at the origin, a nonzero common
period, and the actual differential equation. It does not assume a solution
basis, finite dimensionality, generalized eigenvector decomposition, or a
periodic-coefficient representation.

The proof proceeds through these independently checked modules:

| Module | Proved scope |
| --- | --- |
| [IncePeriodic.lean](IncePeriodic.lean) | Periodic translation, scalar multipliers and the first Jordan step. |
| [InceSolutionSpace.lean](InceSolutionSpace.lean) | Uniqueness from the initial jet via Taylor series, dimension at most the differential order, and invertible translation on the actual entire solution space. |
| [InceExponentialConjugation.lean](InceExponentialConjugation.lean) | Exact conjugation of every power of a translation Jordan block to finite differences after exponential removal. |
| [InceDifferencePolynomial.lean](InceDifferencePolynomial.lean) | Explicit polynomial antidifferences from Bernoulli polynomials, including degree bounds. |
| [InceFiniteDifference.lean](InceFiniteDifference.lean) | `Delta_h^k g = 0` implies an actual sum of `z^j p_j(z)` with entire `h`-periodic coefficients. |
| [InceFloquet.lean](InceFloquet.lean) | Full finite scalar Floquet sums via generalized eigenspaces, for arbitrary block lengths. |
| [LiWangWenFloquet.lean](LiWangWenFloquet.lean) | Application to the paper's actual equation, every natural gamma and every nonzero complex frequency. |
| [LiWangWenDifferenceGrowth.lean](LiWangWenDifferenceGrowth.lean) | Global exponential bounds survive translations, finite differences, finite iteration, and exponential removal. |

The resulting representation is a finite sum of
`exp(a*z) * z^j * p(z)`, with actual entire periodic `p`.
The subsequent Fourier-recurrence modules now prove that the periodic
coefficients have finite Fourier support. The new normalization takes the lowest occupied Fourier index in each
solution block and incorporates it into the exponent. At that index the
highest occupied monomial degree forces the indicial equation.
The entire solution space has dimension **at most** the differential order;
the theorem does not claim a global fundamental system of that exact size
when the leading coefficient is allowed to vanish elsewhere.

Theorem 3.2 is an existential representation theorem for each given
finite-order solution. The proof constructs valid witnesses with `C_j=1`
and `F_j,p=X^p`, including the required exact factor degrees, indicial-root
exponents and `sum K_j ≤ n`. These choices are conclusions of the proof;
they impose no extra assumption on the input solution. The intermediate
sum of the participating block lengths is also at most the differential order.

The polynomial factors associated with a block satisfy the triangular
coefficient equations proved in `LiWangWenFloquetCoefficientEquations.lean`.
They are not all asserted to solve the same homogeneous equation (3.3).

Separate further tasks include the precise Helmrath–Nikolaus
maximum-modulus asymptotic and the complete classification arguments in
Examples 3.6–3.9. They are not prerequisites for the numbered main results
listed above. This package is not a formalization of every sentence in the
paper or of every classical theorem mentioned in its references.

## Wiman–Valiron and Helmrath–Nikolaus dependencies

**The classical Wiman–Valiron derivative theorem for transcendental entire
functions is proved**, including the exceptional set and the quantitative
relative error. The Helmrath–Nikolaus central-index single-branch asymptotic
is now proved; its precise maximum-modulus asymptotic remains unfinished.

| Module | Proved scope | Important inputs / remaining work |
| --- | --- | --- |
| [WimanValironMaximumTerm.lean](WimanValironMaximumTerm.lean) | Maximum term and last maximizing central index; existence, positivity and monotonicity; entire Taylor-series adapters; central index tends to infinity for nonpolynomial entire functions; Cauchy coefficient bounds. | Elementary foundations used by the completed derivative theorem. |
| [WimanValironCircleBounds.lean](WimanValironCircleBounds.lean) | Maximum-modulus bound from a maximum term at a larger radius; exact Taylor series for actual iterated derivatives and their falling-factorial weights. | Convergent identities used by the moment and derivative modules. |
| [WimanValironNormalRadii.lean](WimanValironNormalRadii.lean) | Actual auxiliary weighted series and normal radii; both coefficient comparisons in (1.4.1); agreement with the original central index. | The complete exceptional cover is supplied by `ExceptionalRadii`. |
| [WimanValironComparisonSequence.lean](WimanValironComparisonSequence.lean) | Positive, strictly increasing, bounded comparison factors and exponential coefficient decay on both sides of the central index. | The actual summation estimates are supplied by `WeightedMoments`. |
| [WimanValironLogarithmicMeasure.lean](WimanValironLogarithmicMeasure.lean) | Actual measure `dr/r`, telescoping gap bounds and null countable endpoints. | General covering corollaries are applied to a proved cover in `ExceptionalRadii`. |
| [WimanValironExceptionalRadii.lean](WimanValironExceptionalRadii.lean) | A genuine countable cover of all nonnormal positive radii and a measurable exceptional set of finite logarithmic measure. | No covering or jump-enumeration hypothesis remains. |
| [WimanValironWeightedMoments.lean](WimanValironWeightedMoments.lean) | Uniform bounds for every fixed absolute coefficient moment at normal radii, including the center and both full tails; summability. | Numerical bounds are derived from exponential decay, with no moment-bound hypothesis. |
| [WimanValironBookEstimates.lean](WimanValironBookEstimates.lean) | Unit-constant weighted estimates corresponding to Lemma 1.2, and `M(r) ≤ μ(r) ν(r)^(1/2+ε)`. | For each fixed moment order and exponent loss; this is not a claim that every statement in Section 1.4 is covered. |
| [WimanValironAngularEstimate.lean](WimanValironAngularEstimate.lean) | Global exponential remainder, finite and infinite angular estimates, and optimized first signed moment bound. | The actual Taylor application and circle bound are supplied by `TaylorMoments`. |
| [WimanValironTaylorMoments.lean](WimanValironTaylorMoments.lean) | Actual circle maximum, Taylor moment summability, angular rotation identity, optimized first moment and division at near-maximum points. | All analytic objects are actual function values and coefficients. |
| [WimanValironHigherDerivatives.lean](WimanValironHigherDerivatives.lean) | Centered falling-factorial expansion and exact connection to actual higher derivatives. | A reusable conditional algebraic bridge; its moment inputs are proved in the final theorem. |
| [WimanValironQuantitativeDerivatives.lean](WimanValironQuantitativeDerivatives.lean) | Explicit derivative-order constants bound the relative derivative error by finite signed moments plus `1/ν`. | The moment bounds are supplied by the completed analytic proof. |
| [WimanValironDerivativeAsymptotics.lean](WimanValironDerivativeAsymptotics.lean) | Falling-factorial limits, exact relative-error formula and normalization helpers. | Used to express the completed theorem in its customary form. |
| [WimanValironTheorem.lean](WimanValironTheorem.lean) | Complete quantitative theorem and derivative formula outside one measurable finite-logarithmic-measure set, common to all fixed derivative orders. | Final hypotheses are entirety, nonpolynomiality and `0 < δ < 1/8`; no unproved analytic bound is assumed. |
| [WimanValironGoodRadii.lean](WimanValironGoodRadii.lean) | The restricted-radius filter is nontrivial; arbitrarily distant good circles have nonzero maximum points satisfying the strict near-maximum condition. | Establishes nonvacuity. |
| [WimanValironLimits.lean](WimanValironLimits.lean) | The Big-O relative-error rate, the actual limit `η -> 0`, and an actual choice of maximum points for all fixed derivative orders. | Final asymptotic formulation. |
| [WimanValironCauchyTransfer.lean](WimanValironCauchyTransfer.lean) | A separate Cauchy-estimate route converts a local normalized monomial approximation into higher derivative error bounds. | Such a local approximation is not assumed to follow merely from a pointwise small error. This is an auxiliary route, not a replacement for the book's angular argument. |
| [HelmrathNewtonBalance.lean](HelmrathNewtonBalance.lean) | A finite vanishing asymptotic sum has at least two maximal weights; integer degrees force a rational power; equal degrees force power one; exact derivative-comparison substitution into the ODE. | The actual polynomial-ODE application is supplied by `HelmrathODEApplication`; the root-clustering and branch-selection modules below now supply a single asymptotic branch. |
| [HelmrathExceptionalSet.lean](HelmrathExceptionalSet.lean) | Actual finite logarithmic measure implies zero radial density; a positive power asymptotic of a monotone function extends from the complement of the exceptional set to all sufficiently large radii. | Requires an already established single power asymptotic outside the exceptional set. It does not establish or select the Newton branch. |
| [HelmrathNewtonBranches.lean](HelmrathNewtonBranches.lean) | Finite explicit rational candidates and two-sided power bands from comparable terms of a vanishing finite sum. | No single limiting branch or leading constant is asserted. |
| [HelmrathODECoefficients.lean](HelmrathODECoefficients.lean) | Polynomial leading-term limits along any unbounded complex path and uniform bounds for a finite family of nonzero limiting multipliers. | Used on the actual WV maximum points. |
| [HelmrathODEApplication.lean](HelmrathODEApplication.lean) | Entire nonpolynomial solutions of actual polynomial-coefficient ODEs satisfy finite positive rational power bands outside a constructed finite-logarithmic-measure set. Equal participating coefficient degrees give linear bands. | Derivative comparisons, maximum points, coefficient limits and the exceptional set are proved, not input hypotheses. |
| [WimanValironGrowthBridge.lean](WimanValironGrowthBridge.lean) | An eventual linear upper bound on the genuine Taylor central index implies a global exponential bound; finite-logarithmic-measure exceptions are allowed. | Still needs the central-index bound from the particular equation being studied. |
| [HelmrathODEGrowth.lean](HelmrathODEGrowth.lean) | Every entire solution of a common-degree polynomial-coefficient ODE has a global exponential bound. | This concerns polynomial coefficients in the independent variable, not `P_j(exp z)`; it does not prove Lemma 5.1. |
| [LiWangWenCoefficientExtraction.lean](LiWangWenCoefficientExtraction.lean) | Fixed-node Lagrange interpolation extracts each periodic coefficient with its exponential bound, despite cancellation in the whole finite monomial sum. Entire exp-coefficients are then polynomial. | Growth of the whole sum remains the input; this result does not manufacture that growth from finite order. |

In particular, excluding powers other than one does not by itself establish
exponential type: the existence of a power asymptotic must first be proved.
The finite rational Newton candidates, root clustering and selection of one
branch are now proved for actual polynomial-coefficient ODEs.
`HelmrathODE.polynomial_ode_single_branch` gives positive rational `rho`,
positive `c`, and the global limit `nu(r)/r^rho -> c`, with the exceptional
set removed. The corresponding precise maximum-modulus asymptotic remains
unfinished.
An upper-bound bridge from `nu(r) <= C*r` to global exponential type is proved
separately; it does not require the sharper limiting constant.

### Completed single-branch and independent representation developments

- `HelmrathRootClustering`, `HelmrathRootApplication`,
  `HelmrathBranchSelection`, and `HelmrathSingleBranch` refine the actual
  Newton bands to finitely many root moduli and select a single global
  central-index asymptotic. No branch asymptotic is an input hypothesis.
- `LiWangWenFiniteOrderBounds` and `LiWangWenFiniteOrderFloquet` preserve
  finite order through the actual Floquet decomposition and periodic
  coefficient extraction.
- `LiWangWenFourier`, `LiWangWenFourierDecay`, and
  `LiWangWenFiniteOrderRecurrence` establish actual vertical Fourier
  coefficients, decay faster than every factorial power, and vanishing
  tails of polynomial recurrences.
- `LiWangWenFourierRecurrence`, `LiWangWenFourierPolynomial`,
  `LiWangWenFourierLaurent`, `LiWangWenFourierSupport`, and
  `LiWangWenFloquetCoefficientEquations` derive the recurrence from the
  actual differential equation, including positive leading gamma and
  inhomogeneous descent through a Floquet block.
- `LiWangWenFourierReconstruction` uses Fourier uniqueness to recover the
  actual function from its finite support. `LiWangWenRepresentation` and
  `LiWangWenFrequencyRepresentation` assemble the representation for every
  natural gamma and every nonzero complex frequency.
- `LiWangWenExponentialSumGrowth` first combines equal frequencies, then
  proves positive exponential type on a strictly dominant ray.
  `LiWangWenLemma51` consequently proves the actual Lemma 5.1, with no
  assumption about a central-index asymptotic. This dependency order is
  acyclic: representation is proved before its growth corollary.

The English manuscripts are supplied separately as
[the updated direct repair](../lemma-5-1-type-only-proof.tex) and
[the independent proof](../finite-order-independent-proof.tex), with
corresponding PDFs. The independent manuscript uses a matrix logarithm to
package the same periodic reduction; the Lean implementation uses scalar
Floquet blocks and triangular coefficient descent instead.

### Direct Wiman–Valiron repair: scope of the formalization

The target is `c₁*r ≤ nu(r) ≤ c₂*r`, not convergence of `nu(r)/r`.
`WimanValironLinearType.order_and_type_of_centralIndex_linear_bounds`
proves that these bounds suffice for exact order one and finite positive
type, using maximum-term comparisons rather than a classification of `f`.

`LiWangWenVerticalGrowth` proves finite-order solutions have a bound
`exp(A*(1+|Re z|)^k+B*|Im z|)` using periodic finite-order coefficients;
no Fourier classification is used. `LiWangWenWimanValironStrip` proves
noncancellation after normalization of every exponential-frequency group.
`WimanValironLocalAngular` proves a same-circle near-maximum estimate from
actual Taylor moments. The Lean local estimate uses an angular step that
is a small power of the radius. The current type-only PDF instead presents
a first-contact argument on the shorter arc of angle `1/nu(r)` and rules
out zero type. These are versions of the same direct growth route, not a
claim that every line of that PDF is the Lean proof term. The Lean result
proves the stronger two-sided central-index bounds. The required local
estimate is proved from coefficient moments; the full classical local
theorem is not an axiom.

The actual equation-to-two-sided-bound assembly is complete:
`LiWangWen.lemma_5_1_centralIndex_linear_bounds` in
`LiWangWenLemma51Direct.lean` has only the actual monic equation, entirety,
nonpolynomiality and finite order as hypotheses. Both constants are positive
and the bounds hold at every sufficiently large radius. Its corollary
`LiWangWen.lemma_5_1_direct` proves exact order one and finite positive type.

The lower-bound module constructs the local rotation and the actual ODE
contradiction, then removes its constructed finite-logarithmic-measure set.
The upper-bound module derives the actual grouped coefficient strip and
compares maximum terms at two radii, using `WimanValironFiniteOrder` to
bound the central index by a polynomial. Neither half assumes a central-index
asymptotic. The direct proof's import closure contains no Fourier,
representation, Laurent or factorial-recurrence module, and no single-branch
selection module. The 58-module transitive local import closure is recorded
in [the direct-route dependency report](verification/direct-proof-dependencies.json).
The independent representation proof remains separately available as
`LiWangWen.lemma_5_1`.

### A stronger direct route: single linear asymptotic

An earlier separate single-branch manuscript
changes the contradiction assumption to failure of convergence of `nu(r)/r`.
It incorporates the auxiliary growth argument in the proof without a
separately numbered lemma. It is a different proof route, not a compression
of the old two-sided-bound argument.

After the already established upper bound `nu(r) <= K*r`, the local WV
estimate chooses a near-maximum point on the same circle with
`|Re z| >= r^(1/8)/8`. In the first and last exponential-frequency groups,
factor out the smallest nonzero derivative power. The resulting endpoint
polynomials `R0`, `RD` have nonzero constant terms. The actual ODE implies
`(R0*RD)(nu(r)/z) -> 0`, while `1/r <= |nu(r)/z| <= K`.
Consequently `nu(r)/r` approaches a finite set of **positive** root moduli.
Monotonicity and finite logarithmic measure exclude repeated switching
between candidates and select a single constant.

`LiWangWen.lemma_5_1_centralIndex_asymptotic` in
`LiWangWenWimanValironAsymptotic.lean` proves the actual global conclusion
`exists C > 0, nu(r)/r -> C`, from the monic equation, entirety,
nonpolynomiality and finite order. `LiWangWen.lemma_5_1_via_single_branch`
gives order one and finite positive type as a corollary.
The supporting modules are `LiWangWenWimanValironEndpoint` and
`WimanValironLargeAngular`. No independently proved linear lower bound is
used: positivity is supplied by the endpoint polynomials' nonzero constant
terms. No exponential-sum classification is used.

See [the single-branch dependency report](verification/single-branch-proof-dependencies.json).
The generic monotone finite-candidate selector is shared with the HN
single-branch development; the polynomial-ODE asymptotic theorem is not
applied to the different exponential-sum equation.

### Original gaps addressed by the completed proof routes

The following implications on the supplied paper's pp. 128–129 require
additional justification. The direct repair above addresses them without
claiming a counterexample or requiring a central-index ratio limit.

- Failure of `nu(r) ~ C*r` does not, from monotonicity and polynomial growth
  alone, produce an unbounded set with `nu(r) ~ C*r^rho` for a fixed
  `rho != 1`. The increasing function `r*log r` already shows why slowly
  varying factors at exponent one must be treated separately. This example
  is about the logical inference, not a solution of the paper's ODE.
- Bounded coefficients on the left half-plane alone cannot exclude
  `nu(r)/r -> 0`, since some coefficients can tend to zero. On the right
  half-plane, `Re z > 0` alone does not justify dominance of the largest
  exponential degree over radial powers: `Re z` may be comparable to
  `log r`. The near-maximum-point condition requires an additional argument.
- Helmrath–Nikolaus first refines the polynomial-ODE Newton bands to finitely
  many root asymptotics and selects one branch, then removes the exceptional
  set and derives `log M(r) ~ (c/rho)*r^rho`. Its exception-removal result
  cannot create the missing asymptotic for the different exponential-sum
  equation. The present upper-bound growth bridge avoids the exact leading
  constant when a linear central-index upper bound has actually been proved.

The derivative order `n` needed in the substitution is available from the
proved WV theorem; this minor indexing issue is distinct from the substantive
branch-selection and dominance questions above.

### Source mapping: He Yuzan, Chapter 1, Section 1.4

The supplied scan of *Algebroid Functions and Ordinary Differential Equations*
has been checked visually. Printed pages 23–32 correspond to PDF pages 25–34.
The Lean code, theorem documentation and this coverage description are in English.

| Book result | Role in the proof | Formalization status |
| --- | --- | --- |
| Lemma 1.1, pp. 23–24 | Normal-radius coefficient comparison outside a finite-logarithmic-measure set | Complete: `exists_exceptional_set_normal_radii` plus the coefficient comparisons. A monotone threshold argument proves the cover without enumerating jumps. |
| Theorem 1.14, pp. 24–26 | `M(r) ≤ μ(r) ν(r)^(1/2+ε)` | Proved: `book_maximum_modulus_bound`. |
| Lemma 1.2, pp. 26–28 | Weighted absolute coefficient moments about the central index | Proved: `book_weighted_moment_bound`, including an extra denominator exponent; the bound is uniform in the radius. |
| Theorem 1.15, pp. 28–30 | First derivative estimate by angular rotation | Proved by the `j = 1` specialization of `wimanValiron_derivative_formula`, with the actual Taylor rotation and second-moment estimate. |
| Theorem 1.16, pp. 30–32 | Every fixed derivative order with quantitative relative error | Proved: `wimanValiron_derivative_formula` and `wimanValiron_asymptotic_formula`. |

The proved final statement is for a **transcendental entire function** `f`.
Let `ν(r)` be the last maximizing Taylor index and `M(r)` the actual circle
maximum. For `0 < δ < 1/8`, there is one measurable radial exceptional set
`E` of finite logarithmic measure. For every fixed natural `j`, there are
constants `C_j > 0` and `R_j > 0` such that, for `r ≥ R_j`, `r ∉ E`, and
`|z| = r` with `|f(z)| > M(r) ν(r)^(-1/8+δ)`,

```text
f^(j)(z) / f(z) = (ν(r)/z)^j * (1 + η_j(z)),
|η_j(z)| ≤ C_j * ν(r)^(-1/8+δ).
```

Because `ν(r) -> infinity` and the exponent is negative, `η_j -> 0` on the
nontrivial filter of good radii. `wimanValiron_at_maximum_points` also produces
an actual choice of circle maxima for which all fixed derivative ratios tend
to one. The quantitative theorem permits the stronger non-strict near-maximum
inequality. The set `E` may depend on `f` and `δ`, but not on `j`.

Nonpolynomiality makes the central-index growth requirement explicit; the
formula is not asserted for arbitrary polynomials. The completed scope is
this classical derivative theorem and the estimates listed above. Stronger
WV variants, local monomial approximation, and other results in the book are
not asserted by this coverage table.

The relevant references have distinct scopes:

- Helmrath–Nikolaus (1984), *Ein elementarer Beweis bei der Anwendung der
  Zentralindexmethode auf Differentialgleichungen*, Complex Variables 3,
  387–396, DOI: https://doi.org/10.1080/17476938408814078. For transcendental
  entire solutions of polynomial-coefficient ODEs with nonzero zeroth and
  highest coefficients, it gives positive rational order, finite positive
  type and the corresponding growth asymptotics. Its proof uses an existing
  Wiman–Valiron derivative theorem.
- Gundersen–Steinbart–Wang (1998), *The Possible Orders of Solutions of Linear
  Differential Equations with Polynomial Coefficients*, TAMS 350, 1225–1247,
  describes possible orders explicitly in terms of the coefficient degrees.
  This is different from Gundersen–Steinbart (1994), *Subnormal Solutions of
  Second Order Linear Differential Equations With Periodic Coefficients*,
  which supplies an example used in the representation paper.

### Public implementation search (12 October 2026)

A search of the current mathlib sources, public GitHub projects and other
proof-assistant indexes did not locate a verified, reusable implementation of
the full Wiman–Valiron derivative theorem. This is a bounded search result,
not a claim that none exists.

The [Erdős 516 proof in plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos516.lean)
contains related maximum-term estimates. The
[formal-conjectures entry](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/516.lean)
links to that external proof. In particular, the proof includes a geometric
series bound equivalent to `M(r) <= maximumTerm(s) / (1 - r/s)` for `0 < r < s`.
The external project has been inspected, not built in this environment; none
of its source code is copied here. Its Fabry-gap theorem does not supply the
missing general Wiman–Valiron derivative estimate.

The notation in the search results needs care: the Erdős Problems commentary
notes that the 1961 formulation used `m` for the maximum term, for which the
logarithmic comparison follows from Wiman's inequality. The current problem
and the linked Lean theorem instead use the minimum modulus on a circle.
The linked proof uses maximum-term estimates together with Turán-type and
local minimum-modulus arguments; the historical maximum-term observation
is not evidence that it formalizes the general derivative theorem.
See [the problem commentary](https://www.erdosproblems.com/516) and
[Grosse-Erdmann's inequality overview](https://arxiv.org/html/2409.06499v1).

## Build and audit

**Fresh verification passed (14 October 2026): 100 modules, 716 distinct audited declarations, 0 warnings.** Every local module was recompiled. All audited declarations use only the three standard axioms listed in the report.

The fresh report linked below is authoritative for this source snapshot.
Do not use older counts or an earlier copy of the report for these new files.
See [the machine-readable report](verification/verification.json).

```sh
lake exe cache get
python3 verify.py --jobs 4
```

`lake build` also checks the entire local source set through `Audit.lean`.
Lean 4.33.0 and the exact mathlib revision are pinned. The verifier recompiles
all local modules, checks explicit axiom audits and records source hashes.
See `verification/verification.json`; its module/audit counts are not counts
of completed paper statements. No placeholders are accepted.

`SOURCE_PROVENANCE.json` records copied, unmodified dependencies from the
existing CRG project. No existing published Lean archive, manuscript or arXiv
version is changed by this separate development project.

Apache 2.0. ChatGPT and Codex assisted with formalization and documentation.
The PDF is not included in this project.

## Continuation checkpoint: 12 October 2026

This working copy resumes the interrupted chat named
"定理 1.1 的完整形式化与证明依赖审查". The latest substantive task in that
chat had advanced to the Li–Wang–Wen representation paper and requested the
Floquet and Helmrath–Nikolaus connections. The earlier source directory was
preserved. Only dependency caches are shared; local proof artifacts are
rebuilt in this working copy.

For a future continuation, start with the coverage table, the independent
representation entry points, and the direct-proof status below. Do not
reintroduce the completed scalar Floquet, classical WV, single-branch
central-index or generic exponential-sum representation results as open
assumptions. The 14 October continuation closes the displayed Theorem 3.2 conditions;
the original full CRG Theorem 1.1 belongs to its separate project.

## Continuation checkpoint: 14 October 2026

This copy continues “继续定理 1.1 形式化审查”, whose last turn was interrupted.
It was copied from `/Users/lxy/Documents/tex/HITW/1-1/outputs/` into this
chat's output directory before editing. At the user's subsequent request,
the updated document, sources and verification reports were synchronized
back to that original directory on 14 October 2026. The original files
changed by that synchronization were backed up in the continuation chat's
`work/before-original-overwrite/` directory.
The only shared resource is the pinned dependency cache. Local source and
local compiled proof artifacts are separate.

The direct route first proves a finite exponential bound by Wiman–Valiron
estimates, then uses periodic coefficient extraction and finite Fourier
support. The recurrence route derives finite Fourier support directly from
finite order and the actual polynomial recurrence. They share the algebraic
normalization, spectral dimension bound and substitution identities.
A statement about both routes does not mean that every supporting identity
has been reproved twice.

For a proof-body audit of the route separation, run after a successful full
verification:

```sh
python3 tools/verify_routes.py
```

[verification/proof-routes.json](verification/proof-routes.json) traverses
both types and bodies of all referenced Lean declarations. It checks that
the four direct endpoints use the quantitative Wiman–Valiron theorem and
not factorial-decay rigidity, while the four recurrence endpoints use
factorial-decay rigidity and not that Wiman–Valiron theorem. Four additional
shared endpoints cover Theorem 3.1, Corollary 3.4, Lemma 5.2 and the
standalone supplementary Lemma 5.2′.


## Standalone punctured-plane Lemma 5.2′

`LiWangWenLemma52Prime.lean` proves the complete statement, including the
passage from the periodic functions of `z` to the coefficient functions of
`w≠0`. It does not assume a Laurent representation or finite support.
Polynomial coefficient extraction first derives each composition's growth
bound from the growth bound on the whole sum. The proved periodic Fourier
theorems give tail vanishing and actual reconstruction. Evaluating at
`Complex.log w` yields integer powers of `w`; zero padding gives exactly
the symmetric integer interval used in the note.

The coefficient functions are only required to be holomorphic on `ℂ\{0}`.
Their value at zero is irrelevant to the Laurent theorem. Adding holomorphy
at zero gives the ordinary-polynomial conclusion, with equality on all of
`ℂ`. The public entry with a separately named `g` is
`LiWangWen.lemma_5_2_prime_of_representation_symmetric`.
