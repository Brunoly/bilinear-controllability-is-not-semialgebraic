import BilinearSystems.Analysis.GaugeDefectUniformUpper
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Short trigonometric taylor
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- A convenient cubic sine error on the unit interval. -/
theorem sin_short_cubic_error (x : ℝ) (hx : |x| ≤ 1) :
    |Real.sin x-x| ≤ |x|^3 := by
  have h := Real.sin_bound hx
  have htri : |Real.sin x-x| ≤
      |Real.sin x-(x-x^3/6)|+|x^3/6| := by
    have heq : Real.sin x-x =
        (Real.sin x-(x-x^3/6)) + -(x^3/6) := by ring
    rw [heq]
    calc
      _ ≤ |Real.sin x-(x-x^3/6)|+|-(x^3/6)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hxnonneg : 0 ≤ |x| := abs_nonneg x
  have hx2 : |x|^2 ≤ 1 := by nlinarith
  have hx5 : |x|^5 ≤ |x|^3 := by
    have hm := mul_le_mul_of_nonneg_right hx2 (show 0 ≤ |x|^3 by positivity)
    nlinarith
  have hdiv : |x^3/6| = |x|^3/6 := by
    rw [abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ)<6)]
  rw [hdiv] at htri
  nlinarith

/-- The real cosine bound supplies a quartic error with a simple
coefficient. -/
theorem cos_short_quartic_error (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x-(1-x^2/2)| ≤ |x|^4 := by
  have h := Real.cos_bound hx
  have hn : 0 ≤ |x|^4 := by positivity
  nlinarith

end
end Specification
end BilinearSystems
