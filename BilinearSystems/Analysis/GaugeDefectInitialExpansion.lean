import BilinearSystems.Analysis.LogarithmicRemainder

/-!
# Gauge defect initial expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The zero-angle logarithmic value differs from its quadratic term by
at most a direction-independent cubic error. The constant 2 uses the
Mathlib logarithm remainder established in LogarithmicRemainder. -/
theorem gaugeDefect_initial_cubic (epsilon a l theta : ℝ)
    (he : 0 ≤ epsilon) (hehalf : epsilon ≤ 1/2)
    (hcoef : coefficientIntegral l = a) :
    |gaugeDefect epsilon a l theta 0 +
      epsilon^2*Real.sin (2*theta)^2/2| ≤ 2*epsilon^3 := by
  let s := Real.sin (2*theta)
  have hs : |s| ≤ 1 := Real.abs_sin_le_one _
  have hzbound : |-(epsilon*s)| ≤ epsilon := by
    rw [abs_neg, abs_mul, abs_of_nonneg he]
    nlinarith [abs_nonneg s]
  have hzhalf : |-(epsilon*s)| ≤ 1/2 := hzbound.trans hehalf
  have hlog := log_one_add_quadratic_remainder (-(epsilon*s)) hzhalf
  have hvalue := gaugeDefectAtZero epsilon a l theta hcoef
  have hleft : gaugeDefect epsilon a l theta 0 + epsilon^2*s^2/2 =
      Real.log (1+(-(epsilon*s))) - (-(epsilon*s)) +
        (-(epsilon*s))^2/2 := by
    rw [hvalue]
    dsimp [s]
    ring
  rw [hleft]
  have hcube : |-(epsilon*s)|^3 ≤ epsilon^3 := by
    exact pow_le_pow_left₀ (abs_nonneg _) hzbound 3
  nlinarith

end
end Specification
end BilinearSystems
