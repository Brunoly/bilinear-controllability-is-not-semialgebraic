import BilinearSystems.Coefficient.EndpointSineComparison
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Endpoint kernel sine replacement
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Set

/-- Uniform derivative bound throughout the segment from sin(t) to t. -/
theorem endpointKernel_deriv_bound_sine_segment (b t x : ℝ)
    (hb : 0 < b) (ht : 0 < t) (htHalf : t ≤ 1/2)
    (hx : x ∈ Icc (Real.sin t) t) :
    |deriv (endpointKernel b) x| ≤ 2*b/t^2 := by
  have hsine := endpoint_sine_between t ht.le htHalf
  have hxpos : 0 < x := by linarith [hx.1]
  have hxd : t ≤ 2*x := by linarith [hx.1]
  have hquad : t^2 ≤ 4*x^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2*x-t)
      (by linarith : 0 ≤ 2*x+t)]
  have hdenle : t^2/2 ≤ 2*x^2 := by nlinarith
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  calc
    |deriv (endpointKernel b) x| ≤ b/(2*x^2) :=
      endpointKernel_deriv_abs_le b x hb hxpos
    _ ≤ b/(t^2/2) :=
      div_le_div_of_nonneg_left hb.le (by positivity) hdenle
    _ = 2*b/t^2 := by field_simp [ht2.ne']

/-- The sine-to-identity replacement error is at most 2*b*t, giving an O(b) integral error on [0,1/2]. -/
theorem endpointKernel_sine_replacement (b t : ℝ)
    (hb : 0 < b) (ht : 0 ≤ t) (htHalf : t ≤ 1/2) :
    |endpointKernel b (Real.sin t)-endpointKernel b t| ≤ 2*b*t := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hsine := endpoint_sine_between t ht htHalf
  have hdisp := endpoint_sine_displacement t ht htHalf
  have hdiff : ∀ x ∈ Icc (Real.sin t) t,
      DifferentiableAt ℝ (endpointKernel b) x := by
    intro x _
    exact (endpointKernel_hasDerivAt b x hb).differentiableAt
  have hbound : ∀ x ∈ Icc (Real.sin t) t,
      ‖deriv (endpointKernel b) x‖ ≤ 2*b/t^2 := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      endpointKernel_deriv_bound_sine_segment b t x hb htpos htHalf hx
  have hmv := (convex_Icc (Real.sin t) t).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound ⟨le_rfl,hsine.2⟩ ⟨hsine.2,le_rfl⟩
  have hmv' : |endpointKernel b (Real.sin t)-endpointKernel b t| ≤
      (2*b/t^2)*(t-Real.sin t) := by
    simpa only [Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg hdisp.1] using hmv
  have hC : 0 ≤ 2*b/t^2 := by positivity
  calc
    _ ≤ (2*b/t^2)*(t-Real.sin t) := hmv'
    _ ≤ (2*b/t^2)*t^3 := mul_le_mul_of_nonneg_left hdisp.2 hC
    _ = 2*b*t := by field_simp [htpos.ne']

/-- The integral error on the fixed short interval is O(b), with a
constant independent of b. -/
theorem endpointKernel_sine_integral_error (b : ℝ) (hb : 0 < b) :
    |∫ t in (0 : ℝ)..(1/2),
      (endpointKernel b (Real.sin t)-endpointKernel b t)| ≤ b/2 := by
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) (1/2),
      ‖endpointKernel b (Real.sin t)-endpointKernel b t‖ ≤ b := by
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at ht
    have h := endpointKernel_sine_replacement b t hb ht.1.le ht.2
    have hmul := mul_le_mul_of_nonneg_left ht.2 hb.le
    simp only [Real.norm_eq_abs]
    nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using h

end
end Specification
end BilinearSystems
