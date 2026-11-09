import BilinearSystems.Definitions
import BilinearSystems.Nonsemialgebraicity.MainTheorems

/-!
# Nonsemialgebraicity of planar bilinear controllability

Polynomial coefficients may be arbitrary real numbers. Matrix inputs in the
first theorem are rational; states and controls remain real in both results.
-/
namespace BilinearSystems.Specification

/-- No semialgebraic criterion classifies all rational matrix pairs. -/
theorem no_finite_polynomial_sign_formula_on_rational_pairs :
    ¬ ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin 8) ℝ)
        (φ : SignFormula (Fin m)),
      ∀ v : MatrixPairCoordinates, HasRationalEntries v →
        (φ.eval (fun i x => MvPolynomial.eval x (p i)) v ↔
          GloballyControllable (firstMatrix v) (secondMatrix v)) :=
  rational_input_finite_formula_obstruction

/-- The full real controllability locus is not semialgebraic. -/
theorem full_controllability_locus_not_semialgebraic :
    ¬ HasFinitePolynomialSignDescription ControllabilityLocus :=
  real_input_finite_formula_obstruction

end BilinearSystems.Specification
