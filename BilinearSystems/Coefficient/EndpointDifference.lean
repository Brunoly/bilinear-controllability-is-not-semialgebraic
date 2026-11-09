import BilinearSystems.Coefficient.EndpointIntegralKernel

/-!
# Endpoint difference
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Set

/-- The coefficient difference is the integral of the positive endpoint
kernel, with b=2*lambda. -/
theorem coefficientIntegral_difference_kernel (l : ℝ) :
    coefficientIntegral l - criticalParameter =
      (2/Real.pi) *
        ∫ t in (0 : ℝ)..(Real.pi/2), endpointKernel (2*l) (Real.sin t) := by
  have hpi : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hsin :
      (∫ t in (0 : ℝ)..(Real.pi/2), Real.sqrt (Real.sin t ^ 2)) =
        ∫ t in (0 : ℝ)..(Real.pi/2), Real.sin t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hpi] at ht
    have htpi : t ≤ Real.pi := ht.2.trans (by linarith [Real.pi_pos])
    have hnonneg := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 htpi
    exact Real.sqrt_sq hnonneg
  have hkernel :
      (∫ t in (0 : ℝ)..(Real.pi/2), endpointKernel (2*l) (Real.sin t)) =
        (∫ t in (0 : ℝ)..(Real.pi/2),
          Real.sqrt (2*l+Real.sin t^2)) -
        (∫ t in (0 : ℝ)..(Real.pi/2), Real.sin t) := by
    unfold endpointKernel
    exact intervalIntegral.integral_sub
      ((Real.continuous_sqrt.comp
        (continuous_const.add (Real.continuous_sin.pow 2))).intervalIntegrable _ _)
      (Real.continuous_sin.intervalIntegrable _ _)
  have hzero : coefficientIntegral 0 = criticalParameter := coefficientIntegral_zero
  rw [← hzero]
  unfold coefficientIntegral
  have hbase :
      (∫ t in (0 : ℝ)..(Real.pi/2),
        Real.sqrt (2*0+Real.sin t^2)) =
      (∫ t in (0 : ℝ)..(Real.pi/2), Real.sin t) := by
    simpa only [mul_zero, zero_add] using hsin
  rw [hbase, hkernel]
  ring

end
end Specification
end BilinearSystems
