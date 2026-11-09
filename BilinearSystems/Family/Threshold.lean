import BilinearSystems.Family.Definitions
import BilinearSystems.Control.ControllabilitySufficiency
import BilinearSystems.Growth.CycleGrowthScaling

/-!
# The exact controllability threshold
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem parameterMatrix_leftInverse (epsilon a s : ℝ)
    (hs : s ≠ 0) (hD : parameterDenominator epsilon a ≠ 0) :
    (s⁻¹ • perturbationMatrix epsilon a) * firstMatrix (parameterCoordinates epsilon a s) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, perturbationMatrix, firstMatrix, parameterCoordinates] <;>
    field_simp [hs, hD] <;> unfold parameterDenominator <;> ring

theorem parameterMatrix_rightInverse (epsilon a s : ℝ)
    (hs : s ≠ 0) (hD : parameterDenominator epsilon a ≠ 0) :
    firstMatrix (parameterCoordinates epsilon a s) * (s⁻¹ • perturbationMatrix epsilon a) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, perturbationMatrix, firstMatrix, parameterCoordinates] <;>
    field_simp [hs, hD] <;> unfold parameterDenominator <;> ring

theorem parameterMatrix_second_eq (epsilon a s : ℝ) :
    secondMatrix (parameterCoordinates epsilon a s) =
      firstMatrix (parameterCoordinates epsilon a s) * quarterTurnMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, firstMatrix, secondMatrix,
      parameterCoordinates, quarterTurnMatrix] <;> ring

theorem parameterThreshold : ParameterThreshold := by
  intro epsilon a s h
  dsimp only
  have hs : 0 < s := by linarith [h.2.2.2.2.1]
  have hD := (parameterDenominator_pos h).ne'
  have hKA := parameterMatrix_leftInverse epsilon a s hs.ne' hD
  have hAK := parameterMatrix_rightInverse epsilon a s hs.ne' hD
  change GloballyControllable _ _ ↔ _
  rw [parameterMatrix_second_eq]
  rw [scaled_perturbation_controllable_iff epsilon a s⁻¹ (inv_ne_zero hs.ne') _ hKA hAK]
  rw [cycleGrowth_smul_of_pos _ _ (inv_pos.mpr hs), ← div_eq_inv_mul]
  simpa using (lt_div_iff₀ hs :
    (1 : ℝ) < cycleGrowth (perturbationMatrix epsilon a) / s ↔
      1*s < cycleGrowth (perturbationMatrix epsilon a))

end
end Specification
end BilinearSystems
