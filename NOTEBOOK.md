# Formalization notebook

Source: `definitive.tex` copied into this repository with trailing whitespace
normalized; its mathematical content is unchanged. Entries
record errors, clarifications, and simplifications separately. An observation
is not evidence that its Lean proof has been completed. Source line numbers
refer to this snapshot; labels are the more stable locators.

## 2026-09-22 — recovery and scope

**N01 — Different old and new point sets (reuse limitation).** The old
`Core.lean` defines `ordinaryPopulation j = 4*j-1` and midpoint/shared-boundary
Simpson rings. The new `eq:rj` uses `4*j` and one polygon per midpoint. The
previous main theorem cannot certify the new theorem. Resolution: preserve
legacy at remote commit `2348f37`, extract only generic helpers, and rebuild
anything reused. Current reuse is the elementary sphere-membership proof.

**N02 — Local source recovery (environment).** At task start, the outer worktree
had empty proof-module and Git metadata directories despite completion claims
in its README. Those claims were not treated as verification. Recovered the
GitHub repository into `Rieszenergy/`, preserving its history. The outer files
were not overwritten.

**N03 — Range of N (clarification).** `thm:main` implicitly uses the construction
from Section 2, which exists for `N≥4`. Source line 274 explicitly restricts
the analytic proof to `N≥1024`, hence `M≥16`. This is a stated global assumption,
not a missing assumption in the paper. Lean interfaces repeat it on the block
bounds and separate finite-size closure. Target is all `N≥4`.

**N04 — Small N and varying phases (proof obligation/simplification).** For
`4≤N≤15`, `M=1` and the configuration is a single equatorial N-gon. To cover
`4≤N<1024`, a maximum over N alone is insufficient if one has arbitrary phases.
Use the phase-independent inequality `deficit ≤ Iα N²`, since energy is
nonnegative, and enlarge the constant over the finite N range. This avoids a
compactness argument over phase spaces. Status: planned proof.

**N05 — Cardinality and injectivity (clarification).** A dependent vertex label
type is not yet an N-element point set. Prove the population sum is N and the
point map injective (distinct interior heights, distinct regular polygon
vertices). `ConstructionFacts` explicitly demands these; no energy proof may
silently use N as the actual label count beforehand.

**N06 — Canonical versus arbitrary phases (generalization).** The source fixes
one vertex on the positive x meridian and explains arbitrary rotations are
allowed. The scaffold quantifies a phase per ring, outside N but inside the
uniform constant. Zero phases recover the named deterministic set. The
point definition has a total north-pole fallback; height-interiority must be
proved to show it is never used for `N≥4`.

## 2026-09-22 — energy and longitude audit

**N07 — Ordered pairs and diagonal (normalization).** The new paper sums all
ordered pairs. For `α>0` the diagonal is zero. The old code omits diagonal
terms, so an explicit equality is needed when reusing it. No factor 1/2 belongs
in the energy; normalized surface measure has total mass one.

**N08 — Latitude integration variables (confirmed typographical error).** In
`eq:latitude-decomposition` and the subsequent block displays (source
614–659), the measure variables are swapped relative to the band indices.
The correct binding is `s∈B_j`, `t∈B_k`, with `dμ_k(t) dμ_j(s)`.
`bandBlock N j k G` applies the j functional to s and the k functional to t.
Resolution: fixed in formal definitions; manuscript preserved.

**N09 — Negative type is not the full nonnegativity argument (clarification).**
CND gives nonpositive energy for zero-mass measure differences. To obtain the
stated deficit, also prove the mass identity and constant sphere potential
`Iα`. These are separate `ContinuousEnergy` obligations; B need not be
nonnegative. The proof of the two-term algebraic decomposition is complete.

**N10 — Closed-band overlaps (clarification/simplification).** Adjacent bands
share endpoints. Lebesgue endpoints are null and nodes lie in band interiors.
Use almost-everywhere additivity when summing continuous band measures.
The scaffold implements μ-integrals as differences of ordinary interval
integrals; linearity still requires integrability, and this representation
does not excuse a missing Fubini justification.

**N11 — Fourier endpoints (required cases).** Lemma `trap` includes B=0,
A=B (δ=0), L=1 and arbitrary phase. Smooth parameter differentiation is valid
only for δ>0. Reach δ=0 via uniform convergence and infinity via the zero
nonzero-frequency limit. The Gamma coefficient in `eq:f0-explicit` checks out.
The positive-frequency cosine normalization must be matched to the complex
Fourier/aliasing normalization. Status: all cases retained in contracts.

**N12 — gcd/lcm multiplicity (clarification).** Pair differences have lcm grid
size L and multiplicity d=gcd. Since r_j r_k=dL, the error contains
`d^(1+α)/(r_j r_k)^α`, not `d^α`. At most three rings have a given population,
so replacing the ring-pair sum by a population-pair sum costs at most 9.
This constant is harmless but must be explicit in a finite-sum proof.

**N13 — Longitude arithmetic simplification.** After u=da, v=db, the summand is
`d/(ab)^(α/2)`. Sum d up to T/max(a,b), drop coprimality, and use
`max(a,b)^2≥ab`; the remaining product of p-series has exponent `1+α/2>1`.
No analytic continuation of zeta or sharp asymptotic constant is needed.

## 2026-09-22 — latitude blocks

**N14 — Diagonal cusp (essential restriction).** Full Fα is not generally C⁴
on touching/identical band rectangles. For index gap at most 2, split angles
at 1/r: use a sup/total-variation estimate below the cutoff and mixed Taylor
only above it. Treat polar bands separately. No claim of global smoothness
of the full kernel is permitted in the scaffold or final proof.

**N15 — Polar derivative extension (clarification).** `sqrt(1-s²)` is singular
in height coordinates at a pole. The even angular series supplies a C⁴
extension of the averaged kernel on separated regions; this is the object
whose boundary derivatives are estimated. Terms m=0,1 must be handled
separately before bounding powers for m≥2. A local extension bound will also
need a compatible rectangle-level extension before applying `MixedTaylorBound`.

**N16 — Resonance α=1 (required case).** The integral of D^(α−2) has a
logarithm at α=1. Preserve the three cases α<1, α=1, α>1 and bound
`x² log(2+1/x)` uniformly for 0<x≤2. Dividing by α−1 uniformly would leave
the discrepancy corollary's essential exponent unproved.

**N17 — Same-side gap exercise (checked algebra).** In the far northern case,
write x=1−k²/N. The manuscript's expression expands as
`8(x−H_(k−1))−(1−x H_k) = (19k²−36k)/N + 4k³(k+1)/N² > 0`
for k≥9. Monotonicity gives the full-rectangle separation and V/U≤√63/8.
This is a concrete algebraic lemma for formalization.

**N18 — Central-band classification (clarification).** `SameSide` excludes the
central band. In noncomparable pairs the smaller band is away from the
central region; the central band is covered with opposite-side estimates.
The exhaustive ordered-pair partition must also use block exchange symmetry.
The comparable, same-side unequal, and opposite/central sums have orders
M^(2−α), 1, 1 respectively.

## 2026-09-22 — corollaries and tool scope

**N19 — Stolarsky normalization (checked).** The manuscript integrates dt,
not dt/2. Consequently `4 D² = I₁−E₁/N²`. For probability height measure the
factor would be 8. A useful one-point check is D²=1/3. The formal cap error
is defined by the actual cap indicator integral, independently of energy.

**N20 — Sobolev citation (clarification).** The citation BSSW14 equation (29)
is the general reproducing-kernel identity. The distance-kernel formula is
(42), with kernel (40); the coefficient comparison in (38)–(39) transfers it
to the paper's specified spectral norm. See the independent corollary review
and https://arxiv.org/pdf/1208.3267. A norm-comparison constant is necessary.
The manuscript is unchanged.

**N21 — Actual Sobolev unit ball (definition safeguard).** A distance-energy
square root cannot simply be renamed WCE. The scaffold uses restrictions of
homogeneous harmonic polynomials, an orthonormal complete harmonic system,
and the series with weights `(1+ℓ(ℓ+1))^s`. Summability is explicit because
Lean's default value for a divergent tsum would otherwise admit wrong
functions. Basis existence and spectral/continuous representative equivalence
remain obligations; the final target explicitly includes basis existence.

**N22 — Supremum and lower bounds (separate dependencies).** Nonempty unit
ball and bounded evaluation are needed for sSup to have its mathematical
meaning. The cap lower bound needs Beck (or Wagner plus Stolarsky). Sobolev
optimality needs a universal lower theorem or a reverse norm comparison plus
Wagner; the one-sided energy upper estimate cannot supply it.

**N23 — Comparator role (tool clarification).** Comparator verifies statement
and axiom agreement and replays proofs; it is not a source-flattening tool.
A separate generator must inline project definitions/proofs into a Mathlib-only
file, after which comparator can check agreement with the modular development.
Tool compatibility with Lean 4.19 must be verified. No comparator success is
claimed until an actual run succeeds.

**N24 — Verification boundary (status).** Successful elaboration of a `Prop`
definition is a checked statement, not its proof. Current public targets are
not completed theorems. `formalization.yaml` and the proof inventory must
track open obligations separately from the absence of proof shortcuts.

## 2026-09-22 — proof development

**N25 — Reuse actually checked.** Generic negative-type and geometric surface
measure proofs were extracted into current modules and re-elaborated against
the new definitions. This proves the constant potential and nonnegative
deficit for the new labelled family; no Simpson-specific bound was imported.

**N26 — Alternative angular proof (simplification).** The new `Angular/` chain
ports general circle cusp/Fourier smoothing arguments, proving the full
`TrapezoidBound` including δ=0 and arbitrary phases. This discharges the main
angular lemma without first inhabiting the optional Appendix-1 Gamma-formula
contracts. The distinction is explicit in the proof inventory.

**N27 — Gcd bound beyond required range (generalization).** The arithmetic
`gcd_sum_bound` holds for every α>0. The implemented proof treats 0<α<2 by
divisor majorization and p-series, then compares larger α to α=1 using
gcd(u,v)²≤uv. Only 0<α<2 is used in the Riesz theorem.

**N28 — Comparator backport still under verification.** A Lean4.19-compatible
exporter/comparator and real landrun were built. Initial modular/standalone
comparison reported an internal definition mismatch, and a diagnostic
self-comparison reached a replay/private-name failure. These are tool/export
integration issues, not evidence of a proved or disproved mathematical target.
The tool setup is being investigated; no certification is claimed.

**N29 — Latitude summation simplification.** The main theorem only requires
O(M^(2−α)). For an oriented unequal same-side pair, r_j≤r_k and α<2 imply
r_j³/r_k^(5−α)≤1. Thus crude O(M²) pair counting after M^(−α) suffices,
without reproducing the sharper O(1) intermediate sum. This is a valid
alternative proof route for the requested total bound; it must not be reported
as a proof of the manuscript's stronger intermediate estimate.


**N30 — Sobolev coefficient comparison without asymptotics (simplification).**
For 1<s<2, the positive distance coefficients satisfy
`a_(ℓ+1)/a_ℓ=(ℓ+1−s)/(ℓ+1+s)`. Bernoulli's inequality with
`t=ℓ+1−s>0` shows that `a_ℓ(ℓ+1−s)^(2s)` is increasing for ℓ≥1.
Consequently it is bounded below by `a_1(2−s)^(2s)>0`. Since
`(ℓ+1−s)²≤1+ℓ(ℓ+1)`, this gives the one-sided comparison
`(1+ℓ(ℓ+1))^(−s)≤C_s a_ℓ` needed for the upper WCE estimate.
The scalar inequality is checked in the developing `SobolevKernel` module;
the harmonic reconstruction and distance spectral identity remain separate
obligations. A full Gamma asymptotic is unnecessary for this direction.

**N31 — Center the polynomial test in the Sobolev lower proof (clarification).**
The averaged test `f(x)=n⁻¹∑ᵢ⟨Xᵢ,x⟩^(2n)` has mean `(2n+1)⁻¹`.
Its quadrature error is the even-moment gap, but its spectral norm includes
a nonzero degree-zero term. Subtracting that constant preserves quadrature
error and removes the term, allowing the positive-degree coefficient argument
to match the gap exactly. Omitting the constant from the uncentered norm
would be unjustified. This is a correction to the developing proof route,
not an error claimed in the manuscript.


**N32 — Beck lower bound without a black-box discrepancy theorem.** The
positive-binomial proof of Bilyk–Brauchart, §2, supplies an elementary route
from projection moments and Stolarsky to the actual cap discrepancy. The
checked `capDiscrepancy_lower_rpow` proves the explicit bound
`D(X) ≥ (1/16)n^(-3/4)` for every nonempty labelled configuration, allowing
repetitions. The proof uses interior regularization before taking the endpoint
limit, so convergence at the square-root cusp is not presumed. This supplies
the universal lower half of the cap corollary independently of the still-open
Diamond energy upper estimate.

**N33 — Comparator compatibility resolved for the initial scaffold.** The
strict comparison now passes for the conditional main theorem at `d621018`,
with real landrun, only standard axioms, and kernel replay. The exporter
resets the module-local auxiliary-lemma cache between inlined files. The
Lean 4.19 backport also incorporates a traversal tail-recursion fix and
uses the kernel environment directly during replay to avoid frontend private
name collisions. Illegal-axiom and unequal-statement controls are rejected.
Each larger proof checkpoint still needs its own exact comparison; the
unconditional mathematical targets do not follow from this tooling repair.


**N34 — Comparator validates the larger proof checkpoint.** The full check
now passes for five named results from the 40-module development: the main
assembly from block estimates, universal Beck lower bound, cap assembly
from the main theorem, longitude bound, and mixed Taylor bound. Both source
forms elaborate; matching definitions, permitted axioms and kernel replay
pass. This strengthens the tool evidence in N33 while retaining the explicit
conditional scope of the main and cap assemblies. See the recorded command,
standalone hash and actual log in `comparator/`.
