import BilinearSystems.Coefficient.EndpointIntegralLogEstimate

/-!
# Logarithmic expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Explicit uniform remainder version of the original logarithmic
endpoint expansion. -/
theorem coefficientIntegral_logarithmic_expansion (l : ℝ)
    (hl : 0 < l) (hlHalf : l ≤ 1/2) :
    abs (coefficientIntegral l-criticalParameter-
      (l/Real.pi)*|Real.log l|) ≤ 13*l := by
  have hl1 : l ≤ 1 := hlHalf.trans (by norm_num)
  have hlogl : |Real.log l| = -Real.log l :=
    abs_of_nonpos (Real.log_nonpos hl.le hl1)
  have hlogmul : Real.log (2*l) = Real.log 2+Real.log l :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hl.ne'
  let I := ∫ t in (0 : ℝ)..(Real.pi/2),
      endpointKernel (2*l) (Real.sin t)
  let E := I+((2*l)/4)*Real.log (2*l)
  have hE : |E| ≤ 12*l := by
    have h := endpointIntegral_log_estimate (2*l)
      (by positivity) (by linarith)
    dsimp [E,I]
    nlinarith
  have hF : coefficientIntegral l-criticalParameter = (2/Real.pi)*I :=
    coefficientIntegral_difference_kernel l
  have hidentity : coefficientIntegral l-criticalParameter-
      (l/Real.pi)*|Real.log l| =
      (2/Real.pi)*E - (l/Real.pi)*Real.log 2 := by
    rw [hF, hlogl]
    dsimp [E]
    rw [hlogmul]
    ring
  have hlog2lo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2hi : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale : 0 ≤ 2/Real.pi ∧ 2/Real.pi ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_iff₀ hpi).mpr (by linarith [Real.two_le_pi])
  have hlscale : 0 ≤ l/Real.pi ∧ l/Real.pi ≤ l := by
    constructor
    · positivity
    · exact (div_le_iff₀ hpi).mpr (by
        nlinarith [mul_nonneg hl.le (sub_nonneg.mpr
          (show (1:ℝ) ≤ Real.pi by linarith [Real.two_le_pi]))])
  rw [hidentity]
  have htri := abs_sub_le ((2/Real.pi)*E) 0 ((l/Real.pi)*Real.log 2)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  rw [abs_mul, abs_mul, abs_of_nonneg hscale.1,
    abs_of_nonneg hlscale.1, abs_of_nonneg hlog2lo] at htri
  have hmain := mul_le_mul_of_nonneg_left hE hscale.1
  have hmain2 := mul_le_mul_of_nonneg_right hscale.2 (by positivity : 0 ≤ 12*l)
  have hlogTerm := mul_le_mul_of_nonneg_left hlog2hi hlscale.1
  nlinarith [htri, hmain, hmain2, hlogTerm, hlscale.2]

end
end Specification
end BilinearSystems
