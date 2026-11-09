import BilinearSystems.Coefficient.EndpointKernelAntiderivative
import BilinearSystems.Analysis.ShortTrigonometricTaylor

/-!
# Endpoint sine comparison
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- On the fixed endpoint interval, sine lies between t/2 and t. -/
theorem endpoint_sine_between (t : ℝ) (ht : 0 ≤ t) (htHalf : t ≤ 1/2) :
    t/2 ≤ Real.sin t ∧ Real.sin t ≤ t := by
  have habs : |Real.sin t-t| ≤ t^3 := by
    have hh : |t| ≤ 1 := by rw [abs_of_nonneg ht]; linarith
    simpa only [abs_of_nonneg ht] using sin_short_cubic_error t hh
  have ht2 : t^2 ≤ 1/4 := by nlinarith
  have ht3 : t^3 ≤ t/2 := by
    have hmul := mul_le_mul_of_nonneg_left ht2 ht
    nlinarith
  have hlow := (abs_le.mp habs).1
  have hhigh : |Real.sin t| ≤ |t| := Real.abs_sin_le_abs
  rw [abs_of_nonneg ht] at hhigh
  constructor
  · linarith
  · exact (le_abs_self _).trans hhigh

/-- The displacement used in the mean-value comparison is cubic. -/
theorem endpoint_sine_displacement (t : ℝ) (ht : 0 ≤ t) (htHalf : t ≤ 1/2) :
    0 ≤ t-Real.sin t ∧ t-Real.sin t ≤ t^3 := by
  have hbetween := endpoint_sine_between t ht htHalf
  have hh : |t| ≤ 1 := by rw [abs_of_nonneg ht]; linarith
  have habs := sin_short_cubic_error t hh
  rw [abs_of_nonneg ht] at habs
  exact ⟨sub_nonneg.mpr hbetween.2, by linarith [(abs_le.mp habs).1]⟩

end
end Specification
end BilinearSystems
