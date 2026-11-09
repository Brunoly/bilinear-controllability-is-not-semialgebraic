import BilinearSystems.Analysis.GaugeDefectProjectiveUpper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic remainder
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Elementary cubic remainder for log(1+z) on the half-unit interval. -/
theorem log_one_add_quadratic_remainder (z : ℝ) (hz : |z| ≤ 1/2) :
    |Real.log (1+z)-z+z^2/2| ≤ 2*|z|^3 := by
  have hzlt : |-z| < 1 := by
    simpa only [abs_neg] using
      (lt_of_le_of_lt hz (by norm_num : (1/2:ℝ) < 1))
  have h := Real.abs_log_sub_add_sum_range_le (x := -z) hzlt 2
  have hsum : (∑ i ∈ Finset.range 2, (-z) ^ (i+1) / (i+1:ℝ)) =
      -z+z^2/2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have hleft : |(-z+z^2/2)+Real.log (1-(-z))| =
      |Real.log (1+z)-z+z^2/2| := by ring
  rw [hleft] at h
  have hden : 0 < 1-|z| := by linarith
  have hfactor : 1/(1-|z|) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hpow : 0 ≤ |z|^3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfactor hpow
  have hright : |z|^(2+1)/(1-|z|) ≤ 2*|z|^3 := by
    convert hmul using 1 <;> ring
  have hnorm : |Real.log (1+z)-z+z^2/2| ≤
      |z|^(2+1)/(1-|z|) := by simpa only [abs_neg] using h
  exact hnorm.trans hright

end
end Specification
end BilinearSystems
