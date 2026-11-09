import BilinearSystems.Family.Threshold

/-!
# Polynomial pullback through the rational family
-/
namespace BilinearSystems
namespace Specification
open MvPolynomial
noncomputable section

abbrev ParameterPolynomial := MvPolynomial (Fin 3) ℝ

def denominatorPolynomial : ParameterPolynomial :=
  1 + X 0 ^ 2 * (X 1 ^ 2 - 1)

def numeratorPolynomial (i : Fin 8) : ParameterPolynomial :=
  X 2 * (if i = 0 then X 0 * (X 1 - 1)
    else if i = 1 then 1
    else if i = 2 then -1
    else if i = 3 then X 0 * (X 1 + 1)
    else if i = 4 then 1
    else if i = 5 then -X 0 * (X 1 - 1)
    else if i = 6 then X 0 * (X 1 + 1)
    else 1)

theorem eval_denominatorPolynomial (x : Fin 3 → ℝ) :
    eval x denominatorPolynomial = parameterDenominator (x 0) (x 1) := by
  simp [denominatorPolynomial, parameterDenominator]

theorem eval_numeratorPolynomial (x : Fin 3 → ℝ) (i : Fin 8) :
    eval x (numeratorPolynomial i) =
      parameterDenominator (x 0) (x 1) * parameterCoordinates (x 0) (x 1) (x 2) i
      ∨ parameterDenominator (x 0) (x 1) = 0 := by
  by_cases hD : parameterDenominator (x 0) (x 1) = 0
  · exact Or.inr hD
  · apply Or.inl
    fin_cases i <;> norm_num [numeratorPolynomial, parameterCoordinates] <;>
      field_simp [hD]

/-- One common denominator power for each polynomial test, independent
of the parameters. The resulting polynomial may be identically zero. -/
theorem exists_polynomial_pullback (p : MvPolynomial (Fin 8) ℝ) :
    ∃ (n : ℕ) (P : ParameterPolynomial), ∀ x : Fin 3 → ℝ,
      parameterBox (x 0) (x 1) (x 2) →
      eval x P = parameterDenominator (x 0) (x 1)^n *
        eval (parameterCoordinates (x 0) (x 1) (x 2)) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact ⟨0, C r, fun x _ => by simp⟩
  | add p q ihp ihq =>
    obtain ⟨n, P, hP⟩ := ihp
    obtain ⟨m, Q, hQ⟩ := ihq
    refine ⟨n+m, denominatorPolynomial^m * P + denominatorPolynomial^n * Q, ?_⟩
    intro x hx
    simp only [map_add, map_mul, map_pow, eval_denominatorPolynomial, hP x hx, hQ x hx, pow_add]
    ring
  | mul_X p i ih =>
    obtain ⟨n, P, hP⟩ := ih
    refine ⟨n+1, P * numeratorPolynomial i, ?_⟩
    intro x hx
    have hi := (eval_numeratorPolynomial x i).resolve_right (parameterDenominator_pos hx).ne'
    simp only [map_mul, eval_X, hi, hP x hx, pow_succ]
    ring

theorem parameterCoordinates_rational (epsilon a s : ℚ) :
    HasRationalEntries (parameterCoordinates epsilon a s) := by
  intro i
  let D : ℚ := 1 + epsilon^2 * (a^2 - 1)
  refine ⟨(s/D) * (if i = 0 then epsilon*(a-1)
    else if i = 1 then 1 else if i = 2 then -1 else if i = 3 then epsilon*(a+1)
    else if i = 4 then 1 else if i = 5 then -epsilon*(a-1)
    else if i = 6 then epsilon*(a+1) else 1), ?_⟩
  fin_cases i <;> norm_num [D, parameterCoordinates, parameterDenominator]

theorem signFormula_eval_of_positive_factors {ι X Y : Type*} (phi : SignFormula ι)
    (f : ι → X → ℝ) (g : ι → Y → ℝ) (x : X) (y : Y)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (h : ∀ i, g i y = c i * f i x) :
    phi.eval g y ↔ phi.eval f x := by
  induction phi with
  | positive i => simp [SignFormula.eval, h, hc i]
  | zero i => simp [SignFormula.eval, h, (hc i).ne']
  | negative i =>
    simp only [SignFormula.eval, h]
    constructor
    · intro hn
      by_contra! hnonneg
      exact hn.not_ge (mul_nonneg (hc i).le hnonneg)
    · exact mul_neg_of_pos_of_neg (hc i)
  | truth => rfl
  | falsity => rfl
  | conj p q hp hq => simp [SignFormula.eval, hp, hq]
  | disj p q hp hq => simp [SignFormula.eval, hp, hq]
  | neg p hp => simp [SignFormula.eval, hp]

theorem exists_signFormula_pullback {ι : Type*} (phi : SignFormula ι)
    (p : ι → MvPolynomial (Fin 8) ℝ) :
    ∃ P : ι → ParameterPolynomial, ∀ x : Fin 3 → ℝ,
      parameterBox (x 0) (x 1) (x 2) →
      (phi.eval (fun i y => eval y (P i)) x ↔
       phi.eval (fun i y => eval y (p i)) (parameterCoordinates (x 0) (x 1) (x 2))) := by
  classical
  choose n P hP using fun i => exists_polynomial_pullback (p i)
  refine ⟨P, fun x hx => ?_⟩
  exact signFormula_eval_of_positive_factors phi _ _ _ _
    (fun i => parameterDenominator (x 0) (x 1)^n i)
    (fun _ => pow_pos (parameterDenominator_pos hx) _) (fun i => hP i x hx)

end
end Specification
end BilinearSystems
