import BilinearSystems.Coefficient.GraphMonomial
import BilinearSystems.Polynomial.Substitution
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Graph polynomial form
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private def oneVariableEquiv : MvPolynomial (Fin 1) ℝ ≃+* Polynomial ℝ :=
  (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv

/-- The original two-variable polynomial viewed as a polynomial in a
whose coefficients are polynomials in the inverse coefficient y. -/
def coefficientPolynomialForm (Q : MvPolynomial (Fin 2) ℝ) :
    Polynomial (Polynomial ℝ) :=
  ((MvPolynomial.finSuccEquiv ℝ 1) Q).map oneVariableEquiv.toRingHom

theorem coefficientPolynomialForm_ne_zero
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) :
    coefficientPolynomialForm Q ≠ 0 := by
  intro hz
  have hm : (MvPolynomial.finSuccEquiv ℝ 1) Q = 0 := by
    apply Polynomial.map_injective oneVariableEquiv.toRingHom oneVariableEquiv.injective
    simpa only [coefficientPolynomialForm, Polynomial.map_zero] using hz
  exact hQ ((MvPolynomial.finSuccEquiv ℝ 1).injective (by simpa using hm))

/-- Translation to delta=a-a0, an invertible polynomial substitution. -/
def translatedCoefficientPolynomial (Q : MvPolynomial (Fin 2) ℝ) :
    Polynomial (Polynomial ℝ) :=
  (coefficientPolynomialForm Q).comp
    (Polynomial.X + Polynomial.C (Polynomial.C criticalParameter))

theorem translatedCoefficientPolynomial_ne_zero
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) :
    translatedCoefficientPolynomial Q ≠ 0 := by
  simpa [translatedCoefficientPolynomial, add_comm] using
    (polynomial_affine_substitution_ne_zero
      (coefficientPolynomialForm Q) (coefficientPolynomialForm_ne_zero Q hQ)
      (Polynomial.C criticalParameter) 1 (one_ne_zero))

end
end Specification
end BilinearSystems
