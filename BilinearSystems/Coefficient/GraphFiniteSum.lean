import BilinearSystems.Coefficient.GraphMonomialLimits

/-!
# Graph finite sum
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Iterated polynomial evaluation is the finite sum over all original
nonzero coefficient pairs; no bounded-degree restriction is imposed. -/
theorem iterated_polynomial_eval_double_sum
    (p : Polynomial (Polynomial ℝ)) (d y : ℝ) :
    Polynomial.eval d (Polynomial.map (Polynomial.evalRingHom y) p) =
      ∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
        (p.coeff i).coeff j * d^i * y^j := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  change Polynomial.eval y (p.coeff i) * d^i = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end Specification
end BilinearSystems
