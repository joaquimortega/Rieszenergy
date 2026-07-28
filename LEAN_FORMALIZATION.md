# Lean formalization status: upper bound complete

The development is pinned to Lean 4.19.0 and mathlib 4.19.0.

Build it with:

```bash
lake build
```

The sole paper target is `BEMOCRieszEnergies.tex`.  Its canonical root module
is `BEMOCFormalization.lean`; the core development and analytic support are
split into checked modules under `BEMOCFormalization/`.

## Machine-checked now

- the unit sphere type in `EuclideanSpace ℝ (Fin 3)`;
- the parallel parametrization, equally spaced polygons with arbitrary phase,
  and their certified height coordinate;
- the exact squared chordal-distance formula for two parallel points and its
  same-parallel specialization;
- ordered-pair Riesz energy for finite spherical configurations;
- nonnegativity of this energy and the empty-configuration calculation;
- the continuous coefficient `2^(α+1)/(α+2)` and its `α = 1` value `4/3`;
- the BEMOC parameters `M`, ordinary populations, central population, and
  reflected band populations;
- the closed ordinary-population sum, `M^2 ≤ N/4`, automatic admissibility
  of the central population, and the exact reflected cardinality `N`;
- an explicit finite list of northern, central, and reflected BEMOC bands,
  with certified length and total population `N`;
- cumulative boundary heights from the band populations, their north/south
  endpoint values, and certified midpoint heights in `[-1,1]`;
- the exact BEMOC midpoint populations and combined shared-boundary
  populations, including a proof that their total is `N`;
- a concrete `bemocRingConstructionSequence` containing those rings;
- finite occupied-ring families, their cardinality, relabeling by `Fin N`,
  and conversion into configuration sequences;
- invariance of ordered-pair energy under arbitrary finite relabeling, and
  equality between the explicitly indexed ring energy and its `Fin N`
  relabeling;
- normalized angular Lebesgue measure, its measurable pushforward to every
  occupied parallel, and the population-weighted continuous BEMOC measure;
- the exact mass `N` of the continuous BEMOC ring measure;
- continuity and integrability of the distance-power kernel for `α > 0`,
  and the equality between the finite ring-pair energy and the double
  integral against the combined continuous ring measure;
- normalized spherical surface area constructed from mathlib's Haar-to-sphere
  measure, together with the mass-`N` reference measure;
- preservation of normalized surface area under every Householder reflection,
  and reduction of every spherical distance-power potential to the north pole;
- the exact north-pole chord/height identity and the complete one-dimensional
  integral evaluation `2^(α+1)/(α+2)`;
- the full uniform-height marginal for normalized surface area, proved through
  the Cartesian cone description `v₂ ≤ a‖v‖`, a volume-preserving
  `ℝ³ ≃ ℝ × ℝ²` split, Tonelli, exact planar disk integrals, central symmetry,
  and null boundary circles;
- the unconditional constant-potential formula
  `HasConstantSpherePotential α (continuousEnergy α)` for every `α > 0`;
- finite atomic point measures, their exact mass and integration formula,
  and identification of their distance-power energy with `rieszEnergy`;
- the exact within-ring/cross-ring partition of discrete energy;
- the exact telescoping trigonometric identity
  `circleChordSum w = 2 * cot (π / (2w))` for every `w ≥ 2`, which is the
  manuscript's independent `α = 1` check of the regular-polygon circle sum;
- the exact general-`α` statement of the endpoint Euler--Maclaurin limit,
  together with the real Riemann-zeta normalization used by the manuscript;
- the Riemann-zeta functional equation specialized to `-α`, including its
  reduction to the absolutely convergent positive series at `1+α`;
- a corrected finite power sum through the `B₂` term, a fourth-order local
  Taylor cancellation, the bound `O(n^(α-3))` for its increments, absolute
  summability for `0 < α < 2`, and convergence to a canonical finite-part
  constant;
- the exact reduction of equality between that finite-part constant and
  `ζ(-α)` to one equality between two explicit absolutely convergent series;
- the full complex Euler--Maclaurin continuation identifying that finite-part
  constant with `ζ(-α)`: complex-power Taylor bounds, the exact complex
  Peano-kernel increment formula, a locally uniform `O(n^{-Re(s)-3})` bound,
  holomorphy on a convex continuation domain, telescoping to the corrected
  finite sums, agreement with the Dirichlet series for `Re(s) > 1`, and the
  analytic identity theorem;
- a corrected composite-trapezoid Euler--Maclaurin formula with exact Peano
  kernel, both bounded-`C³` and `L¹`-third-derivative remainder estimates, and
  the resulting `o(w^-α)` smooth error for every `0 < α < 2`;
- the symmetric singular endpoint model for the circle profile, its exact
  mesh sum and integral, and the identity saying its mesh error is precisely
  twice the corrected power sum;
- the holomorphic removable sinc factor `sin(πx)/(πx)`, its positivity and
  evenness, smooth real powers near the endpoint, and the quantitative
  cancellation `|sinc(πx)^α - 1| ≤ Cx²` on a fixed half-interval;
- explicit first, second, and third derivative formulas for the endpoint
  correction, the bounds `q(x)-1 = O(x²)`, `q'(x) = O(x)`, and the decisive
  estimate `|g'''(x)| ≤ C x^(α-1)`; interval integrability at both endpoints
  for every `α > 0`; matching one-sided two-jets; and a checked quadratic-jet
  extension producing `EndpointResidualData α` unconditionally;
- the exact decomposition of the circle mesh error into that singular model
  and an explicit smooth residual, plus the unconditional endpoint
  Euler--Maclaurin theorem for every `0 < α < 2`;
- complete consistency checks at `α = 1`: the finite-part power constant is
  `-1/12`, Mathlib's zeta value is `-1/12`, and the general limit specializes
  to the independently proved cotangent limit;
- the associated `α = 1` regular-polygon self-deficit, including strict
  positivity for `w ≥ 2`, nonnegativity for every population, a uniform
  population-independent bound, and the sharp limit `π / 3` proved from a
  cubic l'Hôpital calculation for `sin x - x cos x`;
- the general-`α` scalar regular-polygon self-deficit, its normalized limit
  `-2(2π)^αζ(-α)` obtained from endpoint Euler--Maclaurin, and an eventual
  population-uniform domination bound;
- the exact radius-times-unit-chord formula on a spherical parallel; cyclic
  invariance of every polygon vertex; and the unconditional discrete
  one-ring identity `ρ^α w circleChordPowerSum α w`;
- periodic invariance of the continuous angular kernel, its reduction to a
  reference-vertex interval integral, and the unconditional continuous
  one-ring identity `ρ^α w² circleAngularMoment α`;
- the exact finite-family aggregation of the actual within-ring deficit as
  `Σ ρ_p^α circleSelfDeficit α w_p`, together with its uniform bound by a
  constant times `Σ ρ_p^α w_p^(1-α)`;
- the complete concrete BEMOC population--radius estimate: exact northern,
  central, and reflected southern population formulas; uniform positivity;
  polar-depth population bounds; north--south radius symmetry; and the
  ringwise comparison `M ρ_p ≤ 2 w_p` for every midpoint and shared-boundary
  ring, including polar and central exceptions;
- the unconditional weighted summation theorem
  `Σ ρ_p^α w_p^(1-α) ≤ C_α N^(1-α/2)` for `N ≥ 36`, with the explicit
  non-optimized choice `C_α = 20` for `α ≤ 1` and
  `C_α = 4(1/2)^(1-α)` for `α > 1`, and the resulting concrete bound
  `|B_{α,N}| ≤ C N^(1-α/2)`;
- the corrected sharp square-subsequence within-ring limit: exact
  `N = 4m²` northern, central, and reflected ring formulas; compact-uniform
  control of the polar triangular arrays; the midpoint and shared-boundary
  Riemann sums with their distinct population factors `8/3` and `4/3`;
  negligibility of the central and central-adjacent exceptions; the
  low-population transfer from the normalized circle limit; and the
  unconditional theorem
  `B_{α,4m²}/(4m²)^(1-α/2) → -κ_α(4π)^α ζ(-α)`;
- the exact gcd/lcm common-grid combinatorics for two polygon populations:
  surjectivity of the cyclic difference map, fiber cardinality equal to the
  gcd, and the resulting finite-sum multiplicity identity used by the
  cross-ring trapezoidal argument, both in coprime-factorized form and
  directly for arbitrary positive populations `q,r` on the `lcm q r` grid;
- a single cross-ring angular kernel with the exact point-distance,
  latitude-integral, population-weighted continuous-energy, periodicity, and
  `A - B cos θ` bridges, including `0 ≤ B ≤ A` and `B = 2ρ_pρ_q`;
- the cusp Fourier recurrence and uniform `n^(-1-α)` coefficient bound, the
  Bernstein-mixture smoothing domination, absolute Fourier summability, and
  the phase-uniform shifted trapezoid estimate with a constant independent of
  `A`, `B`, `L`, and the phase;
- the literal two-polygon reindexing onto the lcm grid and the phase-uniform
  pair estimate
  `C_α(ρ_pρ_q)^(α/2) gcd(w_p,w_q)^(1+α)/(w_pw_q)^α`;
- the concrete cross-ring arithmetic summation: every BEMOC population is
  at most `30M`, every population fiber has cardinality at most seven, the
  divisor majorization of the gcd double sum is `O(M²)`, and consequently
  `|C_{α,N}| ≤ C_α M^(2-α) ≤ C_α N^(1-α/2)` for `N ≥ 36`;
- continuous within-ring and cross-ring pair energies and their exact finite
  decomposition, specialized to the concrete BEMOC ring family;
- the algebraic identity that inserts continuous ring energy and produces
  the three deficit terms;
- concrete definitions of the manuscript quantities `A_{α,N}`, `B_{α,N}`,
  and `C_{α,N}`, their exact decomposition of the BEMOC deficit, and the
  final upper-bound assembly from explicit bounds on those three terms;
- unconditional nonnegativity of the total concrete BEMOC deficit for
  `0 < α < 2`;
- the finite-measure formulation of conditional negative definiteness and
  its formal implication that a constant-potential energy deficit is
  nonnegative;
- conditional negative definiteness of squared chordal distance in the full
  arbitrary-finite-measure interface, plus positive definiteness of the
  spherical inner-product kernel and every tensor power
  `(x · y)^n` via explicit finite-dimensional feature moments;
- positive definiteness of `exp (c * (x · y))` for `c ≥ 0`, proved by its
  factorial series and dominated convergence on product measures; positive
  definiteness of the Gaussian distance kernel `exp (-t * dist x y ^ 2)`;
  conditional negative definiteness of `1 - exp (-t * dist x y ^ 2)`; and a
  general dominated-limit closure theorem for continuous CND kernels;
- the complete Schoenberg argument for `0 < α < 2`: integrability and scaling
  of the fractional-power integral, strict positivity of its normalization,
  joint product-measure integrability, Fubini interchange, and the resulting
  theorem `distancePowerMeasureCND_of_pos_of_lt_two` in the full arbitrary
  finite-measure interface;
- reduction of discrete and continuous BEMOC deficit nonnegativity to CND
  and the explicit constant-potential formula, wired into
  `ConfigurationSequence.deficit`;
- the concrete latitude-band rule, including exact atomic/continuous masses,
  exact cancellation on constants and linear functions, endpoint-atom
  recombination into the BEMOC ring family, concatenation of all band
  integrals to `[-1,1]`, population/width scale comparisons, and localized
  total-variation bounds;
- the unconditional L2 latitude decomposition: every sphere point is put on
  its certified parallel, angular disintegration reduces the spherical
  potential to `latitudeKernel`, the uniform-height marginal evaluates its
  height integral, and consequently
  `bemocLatitudeDeficit = -∑ j, ∑ k, bandPairError ...`;
- reusable one- and two-variable two-moment Peano estimates, including the
  mixed-fourth-derivative block interface and the full bilinear Taylor
  nullspace (terms affine in either variable);
- the exact radial-gap/half-angle normal form of the latitude kernel and its
  scaling by the universal `reducedLatitudeCusp`; complete fourth-derivative
  chains for the nonresonant `|s-t|^(1+α)` model and the resonant
  `(s-t)^2 log |s-t|` model;
- the complete off-pole derivative chain for the height radius, angular
  coefficient, and normalized radial gap `q/p`, including the explicit
  mixed `(2,2)` derivative of `q/p` and a quantitative mixed `(2,2)` bound
  for the angular coefficient under a radius floor;
- the complete named mixed `(2,2)` product/composition derivative chain for
  the actual variable-coefficient latitude kernel off the diagonal;
- explicit radius-floor envelopes for every power, reduced-cusp, and
  normalized-gap jet entering that mixed derivative, and the resulting
  premise-free pointwise `4PH+36PHQ` bound for the full displayed formula;
- literal comparable same-hemisphere rectangle geometry: a common radius
  floor, a matching radius ceiling, an angular-scale floor, and the
  index-distance height separation used in equation (5.5);
- differentiation of the defining reduced-cusp angular integral through
  order four, together with a quadratic-cosine comparison and the sharp
  half-power moment bound
  `reducedCuspMoment γ x ≤ (π/(2√2)) x^(γ+1/2)` for `γ ≤ -1`;
- the exact fourth-order chain rule for the quadratic-gap model
  `reducedLatitudeCusp α (c(s-t)^2)`, with a quantitative bound reducing its
  fourth derivative to the checked second-, third-, and fourth-cusp moments;
- global and height-separated latitude-kernel bounds, physical-height
  clipping for band errors, a coarse unconditional finite block-row bound,
  and an exhaustive polar/central/same-hemisphere/opposite-hemisphere,
  comparable/unequal-scale classification of all ordered band pairs;
- the unconditional manuscript-scale polar L5 estimate for every comparable
  same-hemisphere polar pair,
  `|E_jk| ≤ 4 r_j r_k (144/M²)^(α/2)`, including north/south reflection and
  explicit polar-rectangle height-gap bounds;
- exact conversion of a comparable same-hemisphere local mixed remainder
  into the manuscript L5 weight
  `C d_j M^-α (1+|j-k|)^(α-3)`, and exact conversion of an unequal-scale
  same-hemisphere local remainder into
  `1024 C d_j³ M^-α d_k^(α-5)`;
- unconditional (non-sharp) central and smooth-opposite block bounds, plus
  the exact smooth-opposite `64 C r_j³ r_k³/N⁴` conversion from a local
  mixed remainder;
- fixed-square two-moment bounds for both the power cusp and the resonant
  quadratic-log cusp, including the quadratic reduced-variable substitution
  and exact cancellation of the apparent scale-dependent `a² log a` term;
- the resonant reduced-cusp principal subtraction, proved directly from the
  centered angular integral: exact integration of the quadratic model,
  near/away cosine comparison, the estimate
  `|h₁''(x)-c₁/x|=O(x⁻¹ᐟ²)`, two justified integrations, and the exact local
  decomposition
  `h₁(x)=C₀+A₁x+c₁x log x+x^(3/2)B(x)` with uniformly bounded `B`;
- the endpoint-safe algebraic core of the unequal-scale even-power series:
  `Q=(B/A)²`, degree-four polynomial/geometric normal summability, and the
  monomial bound `16 A^(β-4) Q^(m-2)` even when a squared radius vanishes;
- the real generalized-binomial theorem on `|q|<1`, sum--integral exchange
  for the angular average, exact cancellation of all odd cosine moments,
  and the resulting identity of the actual latitude kernel with the even
  series in equation (5.6);
- the complete derivative chain for every even-series summand through
  `Dsstt`, including its identification with Lean's iterated mixed `(2,2)`
  derivative;
- the literal unequal-scale rectangle geometry, including
  `2d_j<d_k ⇒ 5(1-s²)≤3(1-t²)`, two-sided control
  `A ≍ d_k²/N`, and the uniform endpoint-safe ratio `Q≤15/16`;
- a generic tensor Taylor theorem requiring only pointwise derivative
  chains, and its fully concrete specialization converting a bound on the
  actual `variableReducedLatitudeKernelDsstt` over a literal off-diagonal
  band rectangle into the sharp
  `64 C r_j³ r_k³/N⁴` band-pair estimate; all continuity, localization,
  derivative commutation, and interval-integrability obligations are
  discharged internally;
- the direct left-small Peano bridge: a pointwise derivative bound at scale
  `C M^(8-α)d_k^(α-8)` yields the final unequal block majorant with explicit
  constant `1024 C`;
- normal convergence of the unequal even-power series through all four
  derivative stages, equality of the summed `Dsstt` series with the actual
  latitude-kernel mixed derivative on the full closed band rectangle, an
  explicit nonnegative coefficient constant, conversion to the manuscript
  scale `Cα M^(8-α)d_k^(α-8)`, and the unconditional left-small
  same-hemisphere block estimate;
- explicit central and opposite-hemisphere gap geometry, including uniform
  `Q≤63/64` and `Q≤15/16` regions, together with a finite fallback which
  reduces all sharp analytic row estimates to `M≥15`;
- direct neighboring-band rescaling on the actual BEMOC rectangles,
  including the fixed-square power-cusp bound and the resonant
  `w² log |w|` bound with exact cancellation of the scale logarithm and no
  remaining integrability premise;
- Hölder continuity of `reducedLatitudeCusp` at zero, identification of the
  upper and lower integral-defined subtraction constants with the literal
  cusp value there, and endpoint-complete nonresonant local decompositions;
  these identities cover the atomic diagonal samples rather than only the
  positive-gap part of the rectangle;
- unconditional upper- and lower-nonresonant neighboring central-comparable
  block bounds, including Tietze extension and all pair-error linearity and
  integrability obligations, exported respectively as
  `centralComparable_neighboring_upper_block_bound` and
  `centralComparable_neighboring_lower_block_bound`;
- a classifier-free comparable radius chart and sharp four-term derivative
  estimate on the exceptional separated rectangles; in particular,
  `hasCentralComparableSeparatedDssttBound_generic` makes the separated
  central predicate unconditional, while
  `hasSmoothOppositeComparableLatitudeBlockBound_generic` closes the complete
  smooth-opposite comparable field;
- unconditional polar and regular same-hemisphere oriented unequal-scale
  block estimates, enlarged to one common positive constant and exported as
  the complete
  `HasUnequalLatitudeBlockBound` interface;
- the full four-term Leibniz expansion for the sharp off-diagonal
  comparable mixed derivative, with explicit graded power, cusp, and
  normalized-gap jets; its conversion to the manuscript
  `R^(-2-α)|s-t|^(α-3)` scale; and the unconditional separated regular
  comparable block estimate;
- endpoint completion of the resonant reduced cusp, exported as
  `reducedLatitudeCusp_one_zero_eq_resonantConstantCoefficient` and
  `latitudeKernel_one_eq_neighboringResonantModel_add_branch_on_unitChart`,
  so the `α = 1` decomposition includes the literal diagonal atoms;
- quantitative normalized-radius, quadratic-coefficient,
  angular-coefficient, amplitude, and logarithmic-amplitude oscillation
  bounds for the resonant principal term, together with exact cancellation
  of its frozen quadratic part and physical quadratic control of the
  freezing remainder;
- the full resonant neighboring comparable estimate, with fixed nonnegative
  constants `neighboringResonantPrincipalBlockConstant`,
  `neighboringResonantHigherBranchBlockConstant`, and
  `neighboringResonantFullBlockConstant`, exported at the predicate level as
  `hasLargeDepthNeighboringComparableLatitudeBlockBound_one` and
  `hasNeighboringComparableLatitudeBlockBound_one`;
- the central resonant closure at the fixed normalized radius `1/5`,
  including the principal, higher-branch, and model block bounds; the final
  nonnegative constant `centralResonantComparableBlockConstant`; and the
  all-distance export
  `hasCentralComparableLatitudeBlockBound_resonant`, which combines the
  neighboring estimate with the generic separated central theorem;
- exact logical assembly of the polar, central, opposite, comparable-same,
  and oriented unequal geometric cases into the two broad pointwise
  interfaces consumed by the row arithmetic;
- exact L7 row partitioning, symmetry of the two-band error, the summable
  comparable-distance convolution, multiplicity-two latitude-depth coding,
  both orientations of the unequal-scale sum, conversion from the two
  pointwise block estimates to scale- and population-weighted rows, absolute
  double-sum control, and the complete arithmetic implication to
  `|A_{α,N}| = O(N^(1-α/2))`;
- an explicit three-term interface for latitude, within-ring, and cross-ring
  contributions;
- unconditional assembly of all neighboring, central, opposite, unequal,
  and finite-depth latitude cases throughout `0 < α < 2`, including the
  resonant branch, exported as
  `veryLargeRemainingComparableLatitudeBounds`,
  `hasVeryLargeComparableLatitudeBlockBound`, and
  `exists_bemocLatitudeDeficit_concrete_bound`;
- unconditional construction of the three concrete component bounds
  (`exists_bemocComponentBounds`) and the final upper energy theorem
  `bemoc_deficit_bound`: for every `0 < α < 2`, the concrete BEMOC deficit is
  nonnegative and is at most `C N^(1-α/2)` for all sufficiently large `N`;
- an auxiliary interface for Wagner's lower bound, together with its
  specialization to arbitrary configuration sequences and the concrete
  BEMOC sequence; this lower-bound direction is outside the project scope;
- the conditional deduction of the full asymptotic theorem from the three
  upper estimates and Wagner's universal lower estimate.

The development contains no `sorry` and introduces no `axiom`.

## Completed upper-bound endpoint

The root module imports the unconditional comparable closure and
`BEMOCFormalization.MainTheorem`.  The final checked statement is
`BEMOC.bemoc_deficit_bound`:

```text
0 < α → α < 2 →
∃ C > 0, ∃ N₀, ∀ N ≥ N₀,
  0 ≤ continuousEnergy α * N^2 - bemocFiniteEnergy α N
    ∧ continuousEnergy α * N^2 - bemocFiniteEnergy α N
        ≤ C * N^(1 - α/2).
```

Thus no upper-bound analytic premise remains, including at the resonant
exponent `α = 1`.  `FORMALIZATION_BLUEPRINT.md` is retained as a historical
implementation plan rather than a list of outstanding completion gates.

## Optional and out-of-scope refinements

- The closed Gamma-form normalization of every positive-frequency cusp
  coefficient is optional.  The recurrence, uniform coefficient decay,
  smoothing domination, alias reindexing, summability, and concrete
  cross-ring bound no longer depend on it.
- Wagner's configuration-uniform lower bound and the matching lower
  asymptotic are outside the formalization scope.  Their interfaces remain
  available for possible future work, but they are not completion criteria
  for this project.
