import BEMOCFormalization.AngularIntegralZero

namespace BEMOC.Definitive

/-- Restrictions of genuine homogeneous harmonic polynomials in distinct
degrees are orthogonal for normalized surface area. -/
theorem crossDegreeHarmonicOrthogonality : CrossDegreeHarmonicOrthogonality := by
  intro ℓ m hne p q hp hq
  exact harmonic_restrictions_orthogonal_of_angular_integral_zero
    angular_integral_zero hp hq hne

/-- An actual orthonormal and complete spherical harmonic basis exists. -/
theorem harmonicBasis_nonempty : Nonempty HarmonicBasis :=
  harmonicBasis_nonempty_of_crossDegree crossDegreeHarmonicOrthogonality

end BEMOC.Definitive
