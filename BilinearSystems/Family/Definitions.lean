import BilinearSystems.AuxiliaryDefinitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# A rational three-parameter family
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def parameterDenominator (epsilon a : ℝ) : ℝ :=
  1 + epsilon^2 * (a^2 - 1)

def parameterBox (epsilon a s : ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1/10 ∧ 1/2 < a ∧ a < 1 ∧ 1/2 < s ∧ s < 2

def parameterCoordinates (epsilon a s : ℝ) : MatrixPairCoordinates :=
  fun i => (s / parameterDenominator epsilon a) *
    (if i = 0 then epsilon * (a-1)
     else if i = 1 then 1
     else if i = 2 then -1
     else if i = 3 then epsilon * (a+1)
     else if i = 4 then 1
     else if i = 5 then -epsilon * (a-1)
     else if i = 6 then epsilon * (a+1)
     else 1)

theorem parameterDenominator_pos {epsilon a s : ℝ}
    (h : parameterBox epsilon a s) : 0 < parameterDenominator epsilon a := by
  have he := mul_pos h.1 (show 0 < 1 - epsilon by linarith [h.2.1])
  have ha := mul_nonneg (sq_nonneg epsilon) (sq_nonneg a)
  unfold parameterDenominator
  nlinarith [h.2.1]

def parameterTriple (epsilon a s : ℝ) : Fin 3 → ℝ :=
  fun i => if i = 0 then epsilon else if i = 1 then a else s

@[simp] theorem parameterTriple_zero (e a s : ℝ) : parameterTriple e a s 0 = e := by
  simp [parameterTriple]
@[simp] theorem parameterTriple_one (e a s : ℝ) : parameterTriple e a s 1 = a := by
  norm_num [parameterTriple]
@[simp] theorem parameterTriple_two (e a s : ℝ) : parameterTriple e a s 2 = s := by
  norm_num [parameterTriple]

def parameterGrowth (epsilon a : ℝ) : ℝ := cycleGrowth (perturbationMatrix epsilon a)

/-- The exact transfer, including classification at equality. -/
def ParameterThreshold : Prop :=
  ∀ epsilon a s : ℝ, parameterBox epsilon a s →
    let v := parameterCoordinates epsilon a s
    v ∈ ControllabilityLocus ↔ s < cycleGrowth (perturbationMatrix epsilon a)

end
end Specification
end BilinearSystems
