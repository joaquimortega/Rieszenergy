import BEMOCFormalization.LatitudeEstimate

/-!
# Geometric classification of latitude-band pairs

This module packages the finite case split used between the pointwise
comparable/unequal-scale estimates and the latitude row summation.  The
central and polar bands are given priority; every remaining pair is either
opposite-hemisphere, or is a same-hemisphere pair in exactly one of the
factor-two scale regimes.
-/

open scoped BigOperators

namespace BEMOC

/-- Bands strictly before the central band. -/
def IsNorthernLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Prop :=
  (j : ℕ) < bandCount N - 1

/-- The unique central band index. -/
def IsCentralLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Prop :=
  (j : ℕ) = bandCount N - 1

/-- Bands strictly after the central band. -/
def IsSouthernLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Prop :=
  bandCount N - 1 < (j : ℕ)

theorem latitudeBand_region_trichotomy (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    IsNorthernLatitudeBand N j ∨ IsCentralLatitudeBand N j ∨
      IsSouthernLatitudeBand N j := by
  unfold IsNorthernLatitudeBand IsCentralLatitudeBand IsSouthernLatitudeBand
  omega

theorem northern_not_central {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (h : IsNorthernLatitudeBand N j) : ¬ IsCentralLatitudeBand N j := by
  unfold IsNorthernLatitudeBand IsCentralLatitudeBand at *
  omega

theorem southern_not_central {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (h : IsSouthernLatitudeBand N j) : ¬ IsCentralLatitudeBand N j := by
  unfold IsSouthernLatitudeBand IsCentralLatitudeBand at *
  omega

theorem northern_not_southern {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (h : IsNorthernLatitudeBand N j) : ¬ IsSouthernLatitudeBand N j := by
  unfold IsNorthernLatitudeBand IsSouthernLatitudeBand at *
  omega

theorem latitudeBandScale_eq_north {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j) :
    latitudeBandScale N j = (j : ℕ) + 1 := by
  unfold IsNorthernLatitudeBand at hj
  unfold latitudeBandScale
  rw [Nat.min_eq_left]
  simp [bandTailCount]
  omega

theorem latitudeBandScale_eq_central {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (hM : 1 ≤ bandCount N)
    (hj : IsCentralLatitudeBand N j) :
    latitudeBandScale N j = bandCount N := by
  unfold IsCentralLatitudeBand at hj
  unfold latitudeBandScale
  rw [Nat.min_eq_left]
  · simp [bandTailCount]
    omega
  · simp [bandTailCount]
    omega

theorem latitudeBandScale_eq_south {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (hj : IsSouthernLatitudeBand N j) :
    latitudeBandScale N j = bandTailCount N + 1 - (j : ℕ) := by
  unfold IsSouthernLatitudeBand at hj
  unfold latitudeBandScale
  rw [Nat.min_eq_right]
  simp [bandTailCount]
  omega

@[simp] theorem latitudeBandScale_reflect (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    latitudeBandScale N (concreteReflectBandIndex N j) =
      latitudeBandScale N j := by
  unfold latitudeBandScale concreteReflectBandIndex
  simp only [Fin.val_mk]
  omega

theorem reflect_northern_is_southern {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (hj : IsNorthernLatitudeBand N j) :
    IsSouthernLatitudeBand N (concreteReflectBandIndex N j) := by
  unfold IsNorthernLatitudeBand IsSouthernLatitudeBand
    concreteReflectBandIndex at *
  simp only [Fin.val_mk]
  simp [bandTailCount] at *
  omega

theorem reflect_southern_is_northern {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (hj : IsSouthernLatitudeBand N j) :
    IsNorthernLatitudeBand N (concreteReflectBandIndex N j) := by
  unfold IsNorthernLatitudeBand IsSouthernLatitudeBand
    concreteReflectBandIndex at *
  simp only [Fin.val_mk]
  simp [bandTailCount] at *
  omega

/-- The fixed polar exception consists of the first two bands at either
end.  Equivalently, its manuscript scale is at most two. -/
def IsPolarLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Prop :=
  latitudeBandScale N j ≤ 2

/-- All nonpolar bands have scale at least three. -/
def IsRegularLatitudeBand (N : ℕ)
    (j : Fin (bandTailCount N + 1)) : Prop :=
  2 < latitudeBandScale N j

theorem polar_or_regular (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    IsPolarLatitudeBand N j ∨ IsRegularLatitudeBand N j := by
  unfold IsPolarLatitudeBand IsRegularLatitudeBand
  omega

theorem polar_not_regular {N : ℕ} {j : Fin (bandTailCount N + 1)}
    (h : IsPolarLatitudeBand N j) : ¬ IsRegularLatitudeBand N j := by
  unfold IsPolarLatitudeBand IsRegularLatitudeBand at *
  omega

/-- Literal endpoint-index description of the fixed polar exception. -/
theorem polar_iff_near_endpoint (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    IsPolarLatitudeBand N j ↔
      (j : ℕ) ≤ 1 ∨ bandTailCount N ≤ (j : ℕ) + 1 := by
  unfold IsPolarLatitudeBand latitudeBandScale
  omega

theorem regular_of_not_polar {N : ℕ}
    {j : Fin (bandTailCount N + 1)}
    (h : ¬ IsPolarLatitudeBand N j) :
    IsRegularLatitudeBand N j := by
  unfold IsPolarLatitudeBand IsRegularLatitudeBand at *
  omega

/-- A code for the two polar bands at each endpoint. -/
noncomputable def polarLatitudeBandCode (N : ℕ)
    (j : {j : Fin (bandTailCount N + 1) // IsPolarLatitudeBand N j}) :
    Fin 4 :=
  if h : (j.1 : ℕ) ≤ 1 then
    ⟨(j.1 : ℕ), by omega⟩
  else
    ⟨2 + (bandTailCount N - (j.1 : ℕ)), by
      have hp := (polar_iff_near_endpoint N j.1).mp j.2
      omega⟩

theorem polarLatitudeBandCode_injective (N : ℕ) :
    Function.Injective (polarLatitudeBandCode N) := by
  intro j k hcode
  apply Subtype.ext
  apply Fin.ext
  unfold polarLatitudeBandCode at hcode
  split_ifs at hcode with hj hk
  · simpa using congrArg Fin.val hcode
  · have hv := congrArg Fin.val hcode
    simp only [Fin.val_mk] at hv
    omega
  · have hv := congrArg Fin.val hcode
    simp only [Fin.val_mk] at hv
    omega
  · have hv := congrArg Fin.val hcode
    simp only [Fin.val_mk] at hv
    have hjle : (j.1 : ℕ) ≤ bandTailCount N := by omega
    have hkle : (k.1 : ℕ) ≤ bandTailCount N := by omega
    omega

/-- The finite set of polar exceptional bands. -/
noncomputable def polarLatitudeBands (N : ℕ) :
    Finset (Fin (bandTailCount N + 1)) := by
  classical
  exact Finset.univ.filter (IsPolarLatitudeBand N)

/-- There are at most four polar exceptional bands, uniformly in `N`. -/
theorem card_polarLatitudeBands_le_four (N : ℕ) :
    (polarLatitudeBands N).card ≤ 4 := by
  classical
  let f : polarLatitudeBands N → (Finset.univ : Finset (Fin 4)) :=
    fun j ↦ ⟨polarLatitudeBandCode N
      ⟨j.1, by
        simpa only [polarLatitudeBands, Finset.mem_filter, Finset.mem_univ,
          true_and] using j.2⟩, by simp⟩
  have hf : Function.Injective f := by
    intro j k h
    apply Subtype.ext
    apply Fin.ext
    have hcode : polarLatitudeBandCode N
          ⟨j.1, by
            simpa only [polarLatitudeBands, Finset.mem_filter,
              Finset.mem_univ, true_and] using j.2⟩ =
        polarLatitudeBandCode N
          ⟨k.1, by
            simpa only [polarLatitudeBands, Finset.mem_filter,
              Finset.mem_univ, true_and] using k.2⟩ := by
      exact congrArg Subtype.val h
    have hsub := polarLatitudeBandCode_injective N hcode
    exact congrArg (fun x ↦ (x.1 : ℕ)) hsub
  calc
    (polarLatitudeBands N).card ≤
        (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_le_card_of_injective hf
    _ = 4 := by simp

@[simp] theorem polar_reflect_iff (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    IsPolarLatitudeBand N (concreteReflectBandIndex N j) ↔
      IsPolarLatitudeBand N j := by
  simp [IsPolarLatitudeBand]

@[simp] theorem regular_reflect_iff (N : ℕ)
    (j : Fin (bandTailCount N + 1)) :
    IsRegularLatitudeBand N (concreteReflectBandIndex N j) ↔
      IsRegularLatitudeBand N j := by
  simp [IsRegularLatitudeBand]

/-- Same open hemisphere, with the central band deliberately excluded. -/
def SameLatitudeHemisphere (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  (IsNorthernLatitudeBand N j ∧ IsNorthernLatitudeBand N k) ∨
    (IsSouthernLatitudeBand N j ∧ IsSouthernLatitudeBand N k)

/-- Opposite open hemispheres, in either order. -/
def OppositeLatitudeHemispheres (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  (IsNorthernLatitudeBand N j ∧ IsSouthernLatitudeBand N k) ∨
    (IsSouthernLatitudeBand N j ∧ IsNorthernLatitudeBand N k)

theorem sameLatitudeHemisphere_comm {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} :
    SameLatitudeHemisphere N j k ↔ SameLatitudeHemisphere N k j := by
  simp only [SameLatitudeHemisphere, and_comm, or_comm]

theorem oppositeLatitudeHemispheres_comm {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} :
    OppositeLatitudeHemispheres N j k ↔
      OppositeLatitudeHemispheres N k j := by
  simp only [OppositeLatitudeHemispheres, and_comm, or_comm]

theorem same_not_opposite {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : SameLatitudeHemisphere N j k) :
    ¬ OppositeLatitudeHemispheres N j k := by
  unfold SameLatitudeHemisphere OppositeLatitudeHemispheres at *
  rcases h with hNN | hSS
  · rintro (hNS | hSN)
    · exact northern_not_southern hNN.2 hNS.2
    · exact northern_not_southern hNN.1 hSN.1
  · rintro (hNS | hSN)
    · exact northern_not_southern hNS.1 hSS.1
    · exact northern_not_southern hSN.2 hSS.2

theorem same_or_opposite_of_noncentral {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (hj : ¬ IsCentralLatitudeBand N j)
    (hk : ¬ IsCentralLatitudeBand N k) :
    SameLatitudeHemisphere N j k ∨
      OppositeLatitudeHemispheres N j k := by
  rcases latitudeBand_region_trichotomy N j with hjN | hjC | hjS
  · rcases latitudeBand_region_trichotomy N k with hkN | hkC | hkS
    · exact Or.inl (Or.inl ⟨hjN, hkN⟩)
    · exact (hk hkC).elim
    · exact Or.inr (Or.inl ⟨hjN, hkS⟩)
  · exact (hj hjC).elim
  · rcases latitudeBand_region_trichotomy N k with hkN | hkC | hkS
    · exact Or.inr (Or.inr ⟨hjS, hkN⟩)
    · exact (hk hkC).elim
    · exact Or.inl (Or.inr ⟨hjS, hkS⟩)

/-- At least one band is in the fixed polar exception. -/
def PolarLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  IsPolarLatitudeBand N j ∨ IsPolarLatitudeBand N k

/-- A central exception after the higher-priority polar cases are removed. -/
def CentralLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ¬ PolarLatitudePair N j k ∧
    (IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k)

/-- A smooth opposite-hemisphere pair after polar and central exceptions. -/
def SmoothOppositeLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ¬ PolarLatitudePair N j k ∧
    ¬ (IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k) ∧
      OppositeLatitudeHemispheres N j k

/-- A regular same-hemisphere pair with factor-two comparable scales. -/
def ComparableSameLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ¬ PolarLatitudePair N j k ∧
    ¬ (IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k) ∧
      SameLatitudeHemisphere N j k ∧ ComparableLatitudeScales N j k

/-- A regular same-hemisphere pair in which `j` is the smaller scale. -/
def LeftSmallSameLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ¬ PolarLatitudePair N j k ∧
    ¬ (IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k) ∧
      SameLatitudeHemisphere N j k ∧
        2 * latitudeBandScale N j < latitudeBandScale N k

/-- A regular same-hemisphere pair in which `k` is the smaller scale. -/
def RightSmallSameLatitudePair (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  ¬ PolarLatitudePair N j k ∧
    ¬ (IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k) ∧
      SameLatitudeHemisphere N j k ∧
        2 * latitudeBandScale N k < latitudeBandScale N j

/-- The disjoint-priority geometric partition used to route every ordered
band pair to its L5/L6 estimate. -/
theorem latitudePair_geometric_partition (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    PolarLatitudePair N j k ∨
      CentralLatitudePair N j k ∨
      SmoothOppositeLatitudePair N j k ∨
      ComparableSameLatitudePair N j k ∨
      LeftSmallSameLatitudePair N j k ∨
      RightSmallSameLatitudePair N j k := by
  by_cases hp : PolarLatitudePair N j k
  · exact Or.inl hp
  right
  by_cases hc : IsCentralLatitudeBand N j ∨ IsCentralLatitudeBand N k
  · exact Or.inl ⟨hp, hc⟩
  right
  have hjc : ¬ IsCentralLatitudeBand N j := fun h ↦ hc (Or.inl h)
  have hkc : ¬ IsCentralLatitudeBand N k := fun h ↦ hc (Or.inr h)
  rcases same_or_opposite_of_noncentral hjc hkc with hsame | hopp
  · rcases latitudeScale_trichotomy N j k with hcomp | hleft | hright
    · exact Or.inr (Or.inl ⟨hp, hc, hsame, hcomp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hp, hc, hsame, hleft⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hp, hc, hsame, hright⟩))
  · exact Or.inl ⟨hp, hc, hopp⟩

theorem comparableSame_pair_regular {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : ComparableSameLatitudePair N j k) :
    IsRegularLatitudeBand N j ∧ IsRegularLatitudeBand N k := by
  exact ⟨regular_of_not_polar (fun hj ↦ h.1 (Or.inl hj)),
    regular_of_not_polar (fun hk ↦ h.1 (Or.inr hk))⟩

theorem leftSmallSame_pair_regular {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : LeftSmallSameLatitudePair N j k) :
    IsRegularLatitudeBand N j ∧ IsRegularLatitudeBand N k := by
  exact ⟨regular_of_not_polar (fun hj ↦ h.1 (Or.inl hj)),
    regular_of_not_polar (fun hk ↦ h.1 (Or.inr hk))⟩

theorem rightSmallSame_pair_regular {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : RightSmallSameLatitudePair N j k) :
    IsRegularLatitudeBand N j ∧ IsRegularLatitudeBand N k := by
  exact ⟨regular_of_not_polar (fun hj ↦ h.1 (Or.inl hj)),
    regular_of_not_polar (fun hk ↦ h.1 (Or.inr hk))⟩

theorem smoothOpposite_pair_regular {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : SmoothOppositeLatitudePair N j k) :
    IsRegularLatitudeBand N j ∧ IsRegularLatitudeBand N k := by
  exact ⟨regular_of_not_polar (fun hj ↦ h.1 (Or.inl hj)),
    regular_of_not_polar (fun hk ↦ h.1 (Or.inr hk))⟩

theorem comparableSame_not_leftSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : ComparableSameLatitudePair N j k) :
    ¬ LeftSmallSameLatitudePair N j k := by
  unfold ComparableSameLatitudePair LeftSmallSameLatitudePair
    ComparableLatitudeScales at *
  omega

theorem comparableSame_not_rightSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : ComparableSameLatitudePair N j k) :
    ¬ RightSmallSameLatitudePair N j k := by
  unfold ComparableSameLatitudePair RightSmallSameLatitudePair
    ComparableLatitudeScales at *
  omega

theorem leftSmall_not_rightSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : LeftSmallSameLatitudePair N j k) :
    ¬ RightSmallSameLatitudePair N j k := by
  unfold LeftSmallSameLatitudePair RightSmallSameLatitudePair at *
  have hj := latitudeBandScale_pos N j
  have hk := latitudeBandScale_pos N k
  omega

theorem polarPair_excludes_centralPair {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : PolarLatitudePair N j k) :
    ¬ CentralLatitudePair N j k := by
  intro hc
  exact hc.1 h

theorem polarPair_excludes_smoothOpposite {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : PolarLatitudePair N j k) :
    ¬ SmoothOppositeLatitudePair N j k := by
  intro ho
  exact ho.1 h

theorem polarPair_excludes_comparableSame {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : PolarLatitudePair N j k) :
    ¬ ComparableSameLatitudePair N j k := by
  intro hc
  exact hc.1 h

theorem polarPair_excludes_leftSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : PolarLatitudePair N j k) :
    ¬ LeftSmallSameLatitudePair N j k := by
  intro hl
  exact hl.1 h

theorem polarPair_excludes_rightSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : PolarLatitudePair N j k) :
    ¬ RightSmallSameLatitudePair N j k := by
  intro hr
  exact hr.1 h

theorem centralPair_excludes_smoothOpposite {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : CentralLatitudePair N j k) :
    ¬ SmoothOppositeLatitudePair N j k := by
  intro ho
  exact ho.2.1 h.2

theorem centralPair_excludes_comparableSame {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : CentralLatitudePair N j k) :
    ¬ ComparableSameLatitudePair N j k := by
  intro hc
  exact hc.2.1 h.2

theorem centralPair_excludes_leftSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : CentralLatitudePair N j k) :
    ¬ LeftSmallSameLatitudePair N j k := by
  intro hl
  exact hl.2.1 h.2

theorem centralPair_excludes_rightSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : CentralLatitudePair N j k) :
    ¬ RightSmallSameLatitudePair N j k := by
  intro hr
  exact hr.2.1 h.2

theorem smoothOpposite_excludes_comparableSame {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : SmoothOppositeLatitudePair N j k) :
    ¬ ComparableSameLatitudePair N j k := by
  intro hc
  exact same_not_opposite hc.2.2.1 h.2.2

theorem smoothOpposite_excludes_leftSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : SmoothOppositeLatitudePair N j k) :
    ¬ LeftSmallSameLatitudePair N j k := by
  intro hl
  exact same_not_opposite hl.2.2.1 h.2.2

theorem smoothOpposite_excludes_rightSmall {N : ℕ}
    {j k : Fin (bandTailCount N + 1)}
    (h : SmoothOppositeLatitudePair N j k) :
    ¬ RightSmallSameLatitudePair N j k := by
  intro hr
  exact same_not_opposite hr.2.2.1 h.2.2

theorem leftSmallSame_swap {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} :
    LeftSmallSameLatitudePair N j k ↔
      RightSmallSameLatitudePair N k j := by
  simp only [LeftSmallSameLatitudePair, RightSmallSameLatitudePair,
    PolarLatitudePair, sameLatitudeHemisphere_comm, or_comm]

theorem comparableSame_swap {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} :
    ComparableSameLatitudePair N j k ↔
      ComparableSameLatitudePair N k j := by
  simp only [ComparableSameLatitudePair, PolarLatitudePair,
    comparableLatitudeScales_comm, sameLatitudeHemisphere_comm, or_comm]

/-- Names of the six priority cases in the geometric partition. -/
inductive LatitudePairCase
  | polar
  | central
  | smoothOpposite
  | comparableSame
  | leftSmallSame
  | rightSmallSame
  deriving DecidableEq, Fintype

/-- Interpretation of a case name as its precise geometric predicate. -/
def LatitudePairCase.Holds (c : LatitudePairCase) (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) : Prop :=
  match c with
  | .polar => PolarLatitudePair N j k
  | .central => CentralLatitudePair N j k
  | .smoothOpposite => SmoothOppositeLatitudePair N j k
  | .comparableSame => ComparableSameLatitudePair N j k
  | .leftSmallSame => LeftSmallSameLatitudePair N j k
  | .rightSmallSame => RightSmallSameLatitudePair N j k

theorem exists_latitudePairCase (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    ∃ c : LatitudePairCase, c.Holds N j k := by
  rcases latitudePair_geometric_partition N j k with
    h | h | h | h | h | h
  · exact ⟨.polar, h⟩
  · exact ⟨.central, h⟩
  · exact ⟨.smoothOpposite, h⟩
  · exact ⟨.comparableSame, h⟩
  · exact ⟨.leftSmallSame, h⟩
  · exact ⟨.rightSmallSame, h⟩

/-- The priority predicates are genuinely disjoint, not merely exhaustive. -/
theorem latitudePairCase_unique {N : ℕ}
    {j k : Fin (bandTailCount N + 1)} {c d : LatitudePairCase}
    (hc : c.Holds N j k) (hd : d.Holds N j k) : c = d := by
  cases c with
  | polar =>
      cases d with
      | polar => rfl
      | central => exact (polarPair_excludes_centralPair hc hd).elim
      | smoothOpposite => exact (polarPair_excludes_smoothOpposite hc hd).elim
      | comparableSame => exact (polarPair_excludes_comparableSame hc hd).elim
      | leftSmallSame => exact (polarPair_excludes_leftSmall hc hd).elim
      | rightSmallSame => exact (polarPair_excludes_rightSmall hc hd).elim
  | central =>
      cases d with
      | polar => exact (polarPair_excludes_centralPair hd hc).elim
      | central => rfl
      | smoothOpposite => exact (centralPair_excludes_smoothOpposite hc hd).elim
      | comparableSame => exact (centralPair_excludes_comparableSame hc hd).elim
      | leftSmallSame => exact (centralPair_excludes_leftSmall hc hd).elim
      | rightSmallSame => exact (centralPair_excludes_rightSmall hc hd).elim
  | smoothOpposite =>
      cases d with
      | polar => exact (polarPair_excludes_smoothOpposite hd hc).elim
      | central => exact (centralPair_excludes_smoothOpposite hd hc).elim
      | smoothOpposite => rfl
      | comparableSame =>
          exact (smoothOpposite_excludes_comparableSame hc hd).elim
      | leftSmallSame =>
          exact (smoothOpposite_excludes_leftSmall hc hd).elim
      | rightSmallSame =>
          exact (smoothOpposite_excludes_rightSmall hc hd).elim
  | comparableSame =>
      cases d with
      | polar => exact (polarPair_excludes_comparableSame hd hc).elim
      | central => exact (centralPair_excludes_comparableSame hd hc).elim
      | smoothOpposite =>
          exact (smoothOpposite_excludes_comparableSame hd hc).elim
      | comparableSame => rfl
      | leftSmallSame => exact (comparableSame_not_leftSmall hc hd).elim
      | rightSmallSame => exact (comparableSame_not_rightSmall hc hd).elim
  | leftSmallSame =>
      cases d with
      | polar => exact (polarPair_excludes_leftSmall hd hc).elim
      | central => exact (centralPair_excludes_leftSmall hd hc).elim
      | smoothOpposite => exact (smoothOpposite_excludes_leftSmall hd hc).elim
      | comparableSame => exact (comparableSame_not_leftSmall hd hc).elim
      | leftSmallSame => rfl
      | rightSmallSame => exact (leftSmall_not_rightSmall hc hd).elim
  | rightSmallSame =>
      cases d with
      | polar => exact (polarPair_excludes_rightSmall hd hc).elim
      | central => exact (centralPair_excludes_rightSmall hd hc).elim
      | smoothOpposite => exact (smoothOpposite_excludes_rightSmall hd hc).elim
      | comparableSame => exact (comparableSame_not_rightSmall hd hc).elim
      | leftSmallSame => exact (leftSmall_not_rightSmall hd hc).elim
      | rightSmallSame => rfl

theorem existsUnique_latitudePairCase (N : ℕ)
    (j k : Fin (bandTailCount N + 1)) :
    ∃! c : LatitudePairCase, c.Holds N j k := by
  obtain ⟨c, hc⟩ := exists_latitudePairCase N j k
  exact ⟨c, hc, fun d hd ↦ latitudePairCase_unique hd hc⟩

/-- One analytic premise for each geometric priority case.  All six
premises use the same majorant, allowing the geometric and arithmetic parts
of the proof to be developed independently. -/
structure HasClassifiedLatitudeBlockBounds
    (α : ℝ) (N : ℕ)
    (majorant :
      Fin (bandTailCount N + 1) →
      Fin (bandTailCount N + 1) → ℝ) : Prop where
  polar : ∀ j k, PolarLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k
  central : ∀ j k, CentralLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k
  smoothOpposite : ∀ j k, SmoothOppositeLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k
  comparableSame : ∀ j k, ComparableSameLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k
  leftSmallSame : ∀ j k, LeftSmallSameLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k
  rightSmallSame : ∀ j k, RightSmallSameLatitudePair N j k →
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k

/-- Every block is routed to exactly one field of the classified analytic
package. -/
theorem HasClassifiedLatitudeBlockBounds.bound
    {α : ℝ} {N : ℕ}
    {majorant :
      Fin (bandTailCount N + 1) →
      Fin (bandTailCount N + 1) → ℝ}
    (h : HasClassifiedLatitudeBlockBounds α N majorant)
    (j k : Fin (bandTailCount N + 1)) :
    |bandPairError N j k (latitudeKernel α)| ≤ majorant j k := by
  obtain ⟨c, hc⟩ := exists_latitudePairCase N j k
  cases c with
  | polar => exact h.polar j k hc
  | central => exact h.central j k hc
  | smoothOpposite => exact h.smoothOpposite j k hc
  | comparableSame => exact h.comparableSame j k hc
  | leftSmallSame => exact h.leftSmallSame j k hc
  | rightSmallSame => exact h.rightSmallSame j k hc

/-- Arithmetic row control of a majorant. -/
def HasLatitudeMajorantRowBound
    (α : ℝ) (N : ℕ) (C : ℝ)
    (majorant :
      Fin (bandTailCount N + 1) →
      Fin (bandTailCount N + 1) → ℝ) : Prop :=
  ∀ j, (∑ k, majorant j k) ≤
    C * (finiteBandPopulation N j : ℝ) *
      (bandCount N : ℝ) ^ (-α)

/-- A classified pointwise package feeds a row bound once its majorant has
the desired row summation.  The exponent is stated separately so this lemma
can be used for every `α`. -/
theorem HasClassifiedLatitudeBlockBounds.toRowBound
    {α C : ℝ} {N : ℕ}
    {majorant :
      Fin (bandTailCount N + 1) →
      Fin (bandTailCount N + 1) → ℝ}
    (h : HasClassifiedLatitudeBlockBounds α N majorant)
    (hrow : HasLatitudeMajorantRowBound α N C majorant) :
    HasLatitudeBlockRowBound α N C := by
  intro j
  exact (Finset.sum_le_sum fun k _ ↦ h.bound j k).trans (hrow j)

end BEMOC
