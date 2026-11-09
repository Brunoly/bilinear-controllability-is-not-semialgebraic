import BilinearSystems.Coefficient.GraphPolynomialForm

/-!
# Graph polynomial eval
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem oneVariableEquiv_eval (y : ℝ) :
    (Polynomial.evalRingHom y).comp
      ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom) =
      MvPolynomial.eval (fun _ : Fin 1 => y) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i
    simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- Evaluation of the iterated polynomial agrees exactly with the
original Mathlib evaluation at (a,y), for arbitrary real coefficients. -/
theorem coefficientPolynomialForm_eval
    (Q : MvPolynomial (Fin 2) ℝ) (a y : ℝ) :
    Polynomial.eval a
      (Polynomial.map (Polynomial.evalRingHom y) (coefficientPolynomialForm Q)) =
      MvPolynomial.eval (Fin.cons a (fun _ : Fin 1 => y)) Q := by
  have he := MvPolynomial.eval_eq_eval_mv_eval'
    (fun _ : Fin 1 => y) a Q
  rw [he]
  rw [coefficientPolynomialForm, Polynomial.map_map]
  congr 1
  congr 1
  exact oneVariableEquiv_eval y

/-- After translation, evaluating at delta is exactly the manuscript's
a=a0+delta substitution, including arbitrary real polynomial constants. -/
theorem translatedCoefficientPolynomial_eval
    (Q : MvPolynomial (Fin 2) ℝ) (d y : ℝ) :
    Polynomial.eval d
      (Polynomial.map (Polynomial.evalRingHom y)
        (translatedCoefficientPolynomial Q)) =
      MvPolynomial.eval
        (Fin.cons (criticalParameter+d) (fun _ : Fin 1 => y)) Q := by
  calc
    _ = Polynomial.eval (criticalParameter+d)
        (Polynomial.map (Polynomial.evalRingHom y) (coefficientPolynomialForm Q)) := by
      simp [translatedCoefficientPolynomial, Polynomial.map_comp,
        Polynomial.eval_comp, add_comm]
    _ = _ := coefficientPolynomialForm_eval Q (criticalParameter+d) y

end
end Specification
end BilinearSystems
