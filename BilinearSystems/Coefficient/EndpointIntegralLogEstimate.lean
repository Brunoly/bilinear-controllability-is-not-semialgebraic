import BilinearSystems.Coefficient.EndpointModelRemainder

/-!
# Endpoint integral log estimate
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Uniform logarithmic expansion of the unscaled endpoint integral.
The constant six absorbs the short replacement, tail and regular model
errors; it is independent of b. -/
theorem endpointIntegral_log_estimate (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    |(∫ t in (0 : ℝ)..(Real.pi/2),
        endpointKernel b (Real.sin t)) + (b/4)*Real.log b| ≤ 6*b := by
  let f := fun t : ℝ => endpointKernel b (Real.sin t)
  let g := endpointKernel b
  have hcG : Continuous g := by
    change Continuous (fun x : ℝ => Real.sqrt (b+x^2)-x)
    fun_prop
  have hcF : Continuous f := hcG.comp Real.continuous_sin
  have hconcat :
      (∫ t in (0 : ℝ)..(1/2), f t) +
      (∫ t in (1/2 : ℝ)..(Real.pi/2), f t) =
      ∫ t in (0 : ℝ)..(Real.pi/2), f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcF.intervalIntegrable _ _) (hcF.intervalIntegrable _ _)
  have hsub :
      (∫ t in (0 : ℝ)..(1/2), f t-g t) =
      (∫ t in (0 : ℝ)..(1/2), f t) -
      (∫ t in (0 : ℝ)..(1/2), g t) :=
    intervalIntegral.integral_sub
      (hcF.intervalIntegrable _ _) (hcG.intervalIntegrable _ _)
  have hshort : |∫ t in (0 : ℝ)..(1/2), f t-g t| ≤ b/2 :=
    endpointKernel_sine_integral_error b hb
  have htail : |∫ t in (1/2 : ℝ)..(Real.pi/2), f t| ≤ 4*b :=
    endpointKernel_tail_integral_error b hb
  have hmodel := endpointModel_integral_decomposition b hb
  have hR := endpointModelRemainder_bounds b hb hb1
  have hrewrite :
      (∫ t in (0 : ℝ)..(Real.pi/2), f t) + (b/4)*Real.log b =
        (∫ t in (0 : ℝ)..(1/2), f t-g t) +
        (∫ t in (1/2 : ℝ)..(Real.pi/2), f t) +
        endpointModelRemainder b := by
    rw [← hconcat, hsub, hmodel]
    ring
  change |(∫ t in (0 : ℝ)..(Real.pi/2), f t) + (b/4)*Real.log b| ≤ 6*b
  rw [hrewrite]
  calc
    _ ≤ |∫ t in (0 : ℝ)..(1/2), f t-g t| +
        |∫ t in (1/2 : ℝ)..(Real.pi/2), f t| +
        |endpointModelRemainder b| := by
          have htri1 := abs_add_le
            (∫ t in (0 : ℝ)..(1/2), f t-g t)
            (∫ t in (1/2 : ℝ)..(Real.pi/2), f t)
          have htri2 := abs_add_le
            ((∫ t in (0 : ℝ)..(1/2), f t-g t) +
              (∫ t in (1/2 : ℝ)..(Real.pi/2), f t))
            (endpointModelRemainder b)
          linarith
    _ ≤ b/2+4*b+b := by
      rw [abs_of_nonneg hR.1]
      linarith
    _ ≤ 6*b := by linarith

end
end Specification
end BilinearSystems
