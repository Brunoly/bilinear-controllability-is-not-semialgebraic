import BilinearSystems.Growth.PerturbationEndpointLengths

/-!
# Perturbation path growth bound
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Finite-path growth bound obtained by two-edge cycle closure. -/
theorem perturbation_path_gain_growth_bound_tenth
    (epsilon a : ℝ) (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/10)
    {n : ℕ} (e : Fin (n+1) → State)
    (hunit : ∀ i, UnitDirection (e i)) :
    |indexedPathGain (perturbationMatrix epsilon a) e| / 4 ≤
      (parameterGrowth epsilon a)^(n+2) := by
  let K := perturbationMatrix epsilon a
  let T := planarLength (K.transpose.mulVec (e 0))
  let F := planarLength (K.mulVec (e (Fin.last n)))
  have he1 : epsilon ≤ 1 := heSmall.trans (by norm_num)
  have hT : 1-epsilon ≤ T :=
    perturbation_transpose_length_lower epsilon a he (e 0) (hunit 0)
  have hF : 1-epsilon ≤ F :=
    perturbation_forward_length_lower epsilon a he
      (e (Fin.last n)) (hunit (Fin.last n))
  have hprod : (1-epsilon)^2 ≤ T*F := by
    have h := mul_le_mul hT hF (sub_nonneg.mpr he1) (planarLength_nonneg _)
    nlinarith
  have hcoef : (1/4 : ℝ) ≤ (1-epsilon)^2/2 := by
    nlinarith [sq_nonneg (epsilon)]
  have hclosure := finite_path_gain_growth_bound K e hunit
  have hgain : 0 ≤ |indexedPathGain K e| := abs_nonneg _
  calc
    |indexedPathGain K e| / 4 = |indexedPathGain K e| * (1/4) := by ring
    _ ≤ |indexedPathGain K e| * ((1-epsilon)^2/2) :=
      mul_le_mul_of_nonneg_left hcoef hgain
    _ ≤ |indexedPathGain K e| * (T*F/2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by norm_num)) hgain
    _ ≤ (cycleGrowth K)^(n+2) := hclosure
    _ = (parameterGrowth epsilon a)^(n+2) := rfl

/-- Path-growth estimate for perturbations with epsilon at most 1/100. -/
theorem perturbation_path_gain_growth_bound
    (epsilon a : ℝ) (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    {n : ℕ} (e : Fin (n+1) → State)
    (hunit : ∀ i, UnitDirection (e i)) :
    |indexedPathGain (perturbationMatrix epsilon a) e| / 4 ≤
      (parameterGrowth epsilon a)^(n+2) :=
  perturbation_path_gain_growth_bound_tenth epsilon a he
    (heSmall.trans (by norm_num)) e hunit

end
end Specification
end BilinearSystems
