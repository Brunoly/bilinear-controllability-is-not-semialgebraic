import BilinearSystems.Coefficient.EndpointKernelSineReplacement

/-!
# Endpoint kernel tail
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Set

/-- Sine stays uniformly positive on the fixed tail interval. -/
theorem endpoint_tail_sine_lower (t : ℝ)
    (ht : t ∈ Icc (1/2 : ℝ) (Real.pi/2)) :
    1/4 ≤ Real.sin t := by
  have hhalf := (endpoint_sine_between (1/2 : ℝ) (by norm_num) (by norm_num)).1
  have hmono : Real.sin (1/2 : ℝ) ≤ Real.sin t :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) ht.2 ht.1
  linarith

/-- Uniform pointwise tail bound. -/
theorem endpointKernel_tail_le (b t : ℝ) (hb : 0 < b)
    (ht : t ∈ Icc (1/2 : ℝ) (Real.pi/2)) :
    0 ≤ endpointKernel b (Real.sin t) ∧
    endpointKernel b (Real.sin t) ≤ 2*b := by
  have hs : 1/4 ≤ Real.sin t := endpoint_tail_sine_lower t ht
  have hspos : 0 < Real.sin t := by linarith
  have hkernel := endpointKernel_le_inv b (Real.sin t) hb.le hspos
  have hmul := mul_le_mul_of_nonneg_left hs hb.le
  have hfrac : b/(2*Real.sin t) ≤ 2*b := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.sin t)).mpr
    nlinarith
  exact ⟨endpointKernel_nonneg b (Real.sin t) hb.le hspos.le,
    hkernel.trans hfrac⟩

/-- The full tail integral has absolute value at most 4b for b>0. -/
theorem endpointKernel_tail_integral_error (b : ℝ) (hb : 0 < b) :
    |∫ t in (1/2 : ℝ)..(Real.pi/2),
      endpointKernel b (Real.sin t)| ≤ 4*b := by
  have hhalfpi : (1/2 : ℝ) ≤ Real.pi/2 := by linarith [Real.one_le_pi_div_two]
  have hbound : ∀ t ∈ Set.uIoc (1/2 : ℝ) (Real.pi/2),
      ‖endpointKernel b (Real.sin t)‖ ≤ 2*b := by
    intro t ht
    rw [uIoc_of_le hhalfpi] at ht
    have h := endpointKernel_tail_le b t hb ⟨ht.1.le,ht.2⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hspan : |Real.pi/2-(1/2 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hhalfpi)]
    linarith [Real.pi_le_four]
  have hmul := mul_le_mul_of_nonneg_left hspan (by positivity : 0 ≤ 2*b)
  simpa only [Real.norm_eq_abs] using h.trans (by nlinarith)

end
end Specification
end BilinearSystems
