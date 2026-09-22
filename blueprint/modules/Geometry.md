# Geometry proof guide

Source anchors: `definitive.tex` `eq:geometry` near lines 359–367; polar geometry and chordal-distance comparisons in the latitude appendix, especially around lines 1286–1352 and the separated-band arguments around 1587–1731. The module converts exact Construction formulas into bounds with constants independent of `N`, ring index, and phase. `GeometryBounds` applies already for `N≥4`; `AngularGeometry` is deliberately restricted to `M≥16` and is for the analytic block lemmas.

Start from `0<h_j<1` on northern noncentral rings, `h_M=0`, and reflection. For `1≤j<M`, put `x=4j²/N`; then `h_j=1−x` and `ρ_j²=1−h_j²=x(2−x)`. The square bounds imply `j/M` and `sqrt x` are comparable by absolute constants; `x<1` for these rings. Therefore `ρ_j` is comparable to `j/M`, while `r_j=4j` is comparable to `Mρ_j`. The southern case follows by symmetry of the radius; the central case is `ρ_M=1` and `4M≤r_M≤12M+3`. Combine these to prove the two inequalities in `GeometryBounds` using one global pair of positive constants. Do not assume the central population is exactly `4M`; its residual `N−4M(M−1)` varies across the full permitted interval.

The `population≤15M` clause follows from `4j≤4M` on ordinary rings and `r_M≤12M+3≤15M` for `M≥1`. For each integer population `n`, an ordinary northern value `4j` appears at most once and has at most one reflected southern counterpart. The central ring can add one more occurrence, so the multiplicity is at most three. This fact is used in the longitude gcd double sum. Establish also `Σ_jρ_j≍M`: sum the inequalities `cMρ_j≤r_j≤CMρ_j` and use `Σr_j=N≍M²`. It is a consequence of the contract rather than a separate requested conjunct, but an exported theorem will prevent later duplication.

For `AngularGeometry`, write polar coordinate `φ=arccos z`. The band `polarBand N j` is `[arccos H_{j−1}, arccos H_j]` because `arccos` reverses height order. Its width is `arccos H_j−arccos H_{j−1}`. Express it as an integral of `1/sqrt(1−z²)` over a height interval of length `2r_j/N`. On ordinary bands, the radius throughout the band is comparable to `r_j/M`; for the two cap bands, evaluate endpoint behavior directly rather than invoking a positive lower radius at the pole. The result is a width between `c/M` and `C/M`, including the polar bands. Near a pole the height width is of order `M^{-2}`, yet the polar angular width remains order `M^{-1}`. This is why direct global Lipschitz estimates for `arccos` fail.

The second conjunct bounds `sin θ` on noncap bands by `r_j/M`. Check its current one-based exclusion: `j.val≠0` excludes the first ring, and `j.val+1≠2M−1` excludes the last. The central band is included and has `sin θ` bounded away from zero when `M≥16`. Derive the estimate from the endpoint heights, monotonicity on each hemisphere, and the population comparisons. At the equator, use central band symmetry rather than a formula that presumes a hemisphere. Explicitly prove `θ∈[0,π]` for valid bands.

The third conjunct handles ring offsets at least two. Ordered disjoint polar intervals imply their pointwise angular gap is at least the sum of intervening widths, hence at least a constant times `|j−k|/M`. The upper bound follows by summing the widths of all bands between the selected points, with at most two partial endpoint bands. Both directions are symmetric in `j,k`; avoid a proof that tacitly assumes `j<k`. Use `Int` absolute values for the discrete separation and real absolute values for the angle bound; cast lemmas should be kept separate from analytic estimates.

These bounds feed the appendix's angular-distance model `D²≍(φ−ψ)²+sinφ sinψ θ²`, comparable-block gap estimates, and smooth unequal-block estimates. They do not themselves establish the kernel's derivative bounds. In particular, they must be combined with special treatment when heights coincide and the angular kernel has a cusp, and with polar endpoint expansions where `sqrt(1−z²)` has singular derivatives.

Status: `GeometryBounds` is proved by `geometry_bounds` with constants `c=2` and `C=15`. The proof includes the population cap, threefold multiplicity, northern radius estimate, and equatorial reflection. `sum_radius_bounds` also gives `(4/15)M ≤ Σρ_j ≤ 8M`. `AngularGeometry` remains an explicit obligation; `polarBand` is defined. Any reused legacy bound should be checked against the new exact height `1−4j²/N` and central residual population.

<!-- LEAN_STATEMENTS -->

## Exact checked Lean source

```lean
import BEMOCFormalization.Construction

open scoped BigOperators
namespace BEMOC.Definitive

/-- Uniform geometric estimates; constants never depend on N or phases. -/
def GeometryBounds : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
    (∀ j : RingIndex N,
      c * bandParameter N * radius N (j.val + 1) ≤ population N (j.val + 1) ∧
      (population N (j.val + 1) : ℝ) ≤
        C * bandParameter N * radius N (j.val + 1)) ∧
    (∀ j : RingIndex N, population N (j.val + 1) ≤ 15 * bandParameter N) ∧
    (∀ n : ℕ, (Finset.univ.filter
      (fun j : RingIndex N => population N (j.val + 1) = n)).card ≤ 3)

/-- The central residual is the largest possible ring population. -/
theorem population_le_fifteen {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    population N j ≤ 15 * bandParameter N := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  rcases lt_trichotomy j M with hlt | heq | hgt
  · rw [north_population N j hlt]
    omega
  · subst j
    have hc := (central_population_bounds hN).2
    dsimp [M] at *
    omega
  · rw [south_population N j hgt]
    omega

/-- Any fixed population occurs on at most three occupied parallels. -/
theorem population_multiplicity_le_three (N n : ℕ) (hN : 4 ≤ N) :
    (Finset.univ.filter
      (fun j : RingIndex N => population N (j.val + 1) = n)).card ≤ 3 := by
  classical
  let M := bandParameter N
  let s : Finset (RingIndex N) := Finset.univ.filter
    (fun j => population N (j.val + 1) = n)
  have hM : 1 ≤ M := bandParameter_pos hN
  have hsubset : s.image (fun j => j.val) ⊆
      ({n / 4 - 1, M - 1, 2 * M - n / 4 - 1} : Finset ℕ) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hjv : j.val < 2 * M - 1 := j.isLt
    have hjpos : 1 ≤ j.val + 1 := by omega
    have hjmax : j.val + 1 < 2 * M := by omega
    have hpop : population N (j.val + 1) = n := Finset.mem_filter.mp hj |>.2
    rcases lt_trichotomy (j.val + 1) M with hlt | heq | hgt
    · rw [north_population N (j.val + 1) hlt] at hpop
      have hdiv : n / 4 = j.val + 1 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      left
      omega
    · rw [south_population N (j.val + 1) hgt] at hpop
      have hdiv : n / 4 = 2 * M - (j.val + 1) := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      right
      omega
  have hcard : s.card = (s.image (fun j => j.val)).card :=
    (Finset.card_image_of_injective s (fun a b h => Fin.ext h)).symm
  change s.card ≤ 3
  rw [hcard]
  exact (Finset.card_le_card hsubset).trans Finset.card_le_three

set_option maxHeartbeats 800000

/-- On northern ordinary rings, the radius is comparable to the ring label over `M`. -/
theorem north_radius_comparison {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hjM : j < bandParameter N) :
    (j : ℝ) ≤ 2 * bandParameter N * radius N j ∧
      (bandParameter N : ℝ) * radius N j ≤ 2 * j := by
  let M := bandParameter N
  let x : ℝ := 4 * (j : ℝ) ^ 2 / N
  let r := radius N j
  have hM : 1 ≤ M := bandParameter_pos hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlow : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hhigh0 : (N : ℝ) < 4 * ((M : ℝ) + 1) ^ 2 := by
    exact_mod_cast (bandParameter_bounds N).2
  have hhigh : (N : ℝ) ≤ 16 * (M : ℝ) ^ 2 := by
    have hmreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hm1 : (M : ℝ) + 1 ≤ 2 * M := by linarith
    have hsq : ((M : ℝ) + 1) ^ 2 ≤ (2 * M) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
        (show (0 : ℝ) ≤ (M : ℝ) - 1 by linarith)]
    nlinarith
  have hjlt : (j : ℝ) < M := by exact_mod_cast hjM
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ hNr).2
    nlinarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = x * (2 - x) := by
    dsimp [r, radius]
    rw [Real.sq_sqrt]
    · rw [north_height hN hj1 hjM]
      dsimp [x]
      ring
    · rw [north_height hN hj1 hjM]
      change 0 ≤ 1 - (1 - x) ^ 2
      nlinarith [sq_nonneg (1 - x)]
  have hrlo : (j : ℝ) ^ 2 ≤ 4 * (M : ℝ) ^ 2 * r ^ 2 := by
    have haux : (j : ℝ) ^ 2 / (4 * (M : ℝ) ^ 2) ≤ x := by
      dsimp [x]
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (M : ℝ) ^ 2) hNr).2
      nlinarith
    have hrr : x ≤ r ^ 2 := by nlinarith [hrsq]
    have hmul := mul_le_mul_of_nonneg_left (haux.trans hrr)
      (show (0 : ℝ) ≤ 4 * (M : ℝ) ^ 2 by positivity)
    field_simp at hmul
    nlinarith
  have hrhi : (M : ℝ) ^ 2 * r ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by
    have haux : x ≤ (j : ℝ) ^ 2 / (M : ℝ) ^ 2 := by
      dsimp [x]
      apply (div_le_div_iff₀ hNr (by positivity : (0 : ℝ) < (M : ℝ) ^ 2)).2
      nlinarith
    have hrr : r ^ 2 ≤ 2 * x := by nlinarith [hrsq]
    have hmul := mul_le_mul_of_nonneg_left (hrr.trans (by nlinarith : 2 * x ≤
      2 * ((j : ℝ) ^ 2 / (M : ℝ) ^ 2)))
      (show (0 : ℝ) ≤ (M : ℝ) ^ 2 by positivity)
    field_simp at hmul
    nlinarith
  change (j : ℝ) ≤ 2 * (M : ℝ) * r ∧ (M : ℝ) * r ≤ 2 * j
  constructor <;> nlinarith [mul_nonneg (show (0 : ℝ) ≤ M by positivity) hr0]

/-- Reflected occupied rings have the same radius. -/
theorem radius_reflect {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    radius N (2 * bandParameter N - j) = radius N j := by
  simp only [radius, height_reflect hN hj1 hj2, neg_sq]

/-- Radius and population comparisons for each occupied parallel. -/
theorem population_radius_comparison {N j : ℕ} (hN : 4 ≤ N)
    (hj1 : 1 ≤ j) (hj2 : j < 2 * bandParameter N) :
    2 * bandParameter N * radius N j ≤ population N j ∧
      (population N j : ℝ) ≤ 15 * bandParameter N * radius N j := by
  let M := bandParameter N
  have hM : 1 ≤ M := bandParameter_pos hN
  rcases lt_trichotomy j M with hlt | heq | hgt
  · obtain ⟨hlo, hhi⟩ := north_radius_comparison hN hj1 hlt
    rw [north_population N j hlt]
    push_cast
    constructor <;> nlinarith
  · subst j
    have hr : radius N M = 1 := by
      change radius N (bandParameter N) = 1
      simp [radius, central_height hN]
    have hc := central_population_bounds hN
    dsimp [M] at *
    rw [hr]
    constructor
    · norm_num
      exact_mod_cast (by omega :
        2 * bandParameter N ≤ population N (bandParameter N))
    · norm_num
      exact_mod_cast (by omega :
        population N (bandParameter N) ≤ 15 * bandParameter N)
  · let k := 2 * M - j
    have hk1 : 1 ≤ k := by dsimp [k]; omega
    have hkM : k < M := by dsimp [k]; omega
    have hkr := north_radius_comparison hN hk1 hkM
    have hpop : population N j = population N k := by
      have h := population_reflect hN hk1 (by dsimp [k]; omega : k < 2 * M)
      have hidx : 2 * M - k = j := by dsimp [k]; omega
      change 2 * bandParameter N - k = j at hidx
      rw [hidx] at h
      exact h
    have hrad : radius N j = radius N k := by
      have h := radius_reflect hN hk1 (by dsimp [k]; omega : k < 2 * M)
      have hidx : 2 * M - k = j := by dsimp [k]; omega
      change 2 * bandParameter N - k = j at hidx
      rw [hidx] at h
      exact h
    rw [hpop, hrad, north_population N k hkM]
    push_cast
    constructor <;> nlinarith [hkr.1, hkr.2]

/-- Uniform radius, population, and multiplicity bounds for the Diamond rings. -/
theorem geometry_bounds : GeometryBounds := by
  refine ⟨2, 15, by norm_num, by norm_num, ?_⟩
  intro N hN
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact population_radius_comparison hN (by omega) (by
      have hj := j.isLt
      have hM := bandParameter_pos hN
      omega)
  · intro j
    exact population_le_fifteen hN (by omega) (by
      have hj := j.isLt
      have hM := bandParameter_pos hN
      omega)
  · intro n
    exact population_multiplicity_le_three N n hN

/-- The total radius of the occupied parallels is of order `M`. -/
theorem sum_radius_bounds (N : ℕ) (hN : 4 ≤ N) :
    (4 / 15 : ℝ) * bandParameter N ≤
      ∑ j : RingIndex N, radius N (j.val + 1) ∧
    (∑ j : RingIndex N, radius N (j.val + 1)) ≤
      8 * bandParameter N := by
  let M := bandParameter N
  let R : ℝ := ∑ j : RingIndex N, radius N (j.val + 1)
  have hM : 1 ≤ M := bandParameter_pos hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlowN : 4 * (M : ℝ) ^ 2 ≤ N := by
    exact_mod_cast (bandParameter_bounds N).1
  have hhighN : (N : ℝ) ≤ 16 * (M : ℝ) ^ 2 := by
    have hmreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have htop : (N : ℝ) < 4 * ((M : ℝ) + 1) ^ 2 := by
      exact_mod_cast (bandParameter_bounds N).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
      (show (0 : ℝ) ≤ (M : ℝ) - 1 by linarith)]
  have hsum : (∑ j : RingIndex N, (population N (j.val + 1) : ℝ)) = N := by
    exact_mod_cast population_sum_eq N hN
  have hlo : 2 * (M : ℝ) * R ≤ N := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (j : RingIndex N) _ =>
      (population_radius_comparison hN (by omega) (by
        have hj := j.isLt
        omega : j.val + 1 < 2 * bandParameter N)).1)
    simp only [← Finset.mul_sum] at h
    dsimp [R] at *
    rw [hsum] at h
    exact h
  have hhi : (N : ℝ) ≤ 15 * (M : ℝ) * R := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (j : RingIndex N) _ =>
      (population_radius_comparison hN (by omega) (by
        have hj := j.isLt
        omega : j.val + 1 < 2 * bandParameter N)).2)
    simp only [← Finset.mul_sum] at h
    dsimp [R] at *
    rw [hsum] at h
    exact h
  change (4 / 15 : ℝ) * M ≤ R ∧ R ≤ 8 * M
  constructor <;> nlinarith

/-- Polar interval in increasing angular coordinates. -/
def polarBand (N j : ℕ) : Set ℝ :=
  Set.Icc (Real.arccos (boundary N (j - 1))) (Real.arccos (boundary N j))

/-- Polar geometry used for block estimates, after the explicit large-N cutoff. -/
def AngularGeometry : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N : ℕ, 16 ≤ bandParameter N →
    (∀ j : RingIndex N,
      c / bandParameter N ≤ Real.arccos (boundary N (j.val + 1)) -
        Real.arccos (boundary N j.val) ∧
      Real.arccos (boundary N (j.val + 1)) - Real.arccos (boundary N j.val)
        ≤ C / bandParameter N) ∧
    (∀ j : RingIndex N, j.val ≠ 0 → j.val + 1 ≠ 2 * bandParameter N - 1 →
      ∀ θ ∈ polarBand N (j.val + 1),
        c * population N (j.val + 1) / bandParameter N ≤ Real.sin θ ∧
        Real.sin θ ≤ C * population N (j.val + 1) / bandParameter N) ∧
    (∀ j k : RingIndex N, 2 ≤ |(j.val : ℤ) - k.val| →
      ∀ θ ∈ polarBand N (j.val + 1), ∀ ψ ∈ polarBand N (k.val + 1),
        c * |(j.val : ℝ) - k.val| / bandParameter N ≤ |θ - ψ| ∧
        |θ - ψ| ≤ C * |(j.val : ℝ) - k.val| / bandParameter N)

end BEMOC.Definitive
```

<!-- END_LEAN_STATEMENTS -->
