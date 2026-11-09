import BilinearSystems.Analysis.GaugeDefectSlopeExpansion

/-!
# Gauge defect slope square
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- A purely algebraic square-error estimate. The constants are deliberately
uniform in direction and valid for epsilon in [0,1]. -/
theorem quadratic_slope_square_error (epsilon R v d : ℝ)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (hR : 0 ≤ R)
    (hv : |v| ≤ R) (hd : |d-epsilon*v| ≤ 2*R*epsilon^2) :
    |d^2-epsilon^2*v^2| ≤ 8*R^2*epsilon^3 := by
  have hscaled : |epsilon*v| ≤ epsilon*R := by
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_mul_of_nonneg_left hv he
  have hplus0 : |d+epsilon*v| ≤ |d-epsilon*v|+2*|epsilon*v| := by
    calc
      _ = |(d-epsilon*v)+2*(epsilon*v)| := by congr 1; ring
      _ ≤ |d-epsilon*v|+|2*(epsilon*v)| := abs_add_le _ _
      _ = _ := by rw [abs_mul]; norm_num
  have he2 : epsilon^2 ≤ epsilon := by nlinarith
  have hplus : |d+epsilon*v| ≤ 4*R*epsilon := by
    have h2 := mul_le_mul_of_nonneg_left he2 (show 0 ≤ 2*R by positivity)
    nlinarith [hplus0, hd, hscaled]
  have hproduct := mul_le_mul hd hplus (abs_nonneg _) (by positivity : 0 ≤ 2*R*epsilon^2)
  have hfact : d^2-epsilon^2*v^2 = (d-epsilon*v)*(d+epsilon*v) := by ring
  rw [hfact, abs_mul]
  nlinarith [hproduct]

/-- The exact initial slope satisfies the manuscript's O(epsilon^3)
squared-error estimate. -/
theorem gaugeDefect_initial_slope_square_bound (epsilon a l theta : ℝ)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1/2)
    (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hcoef : coefficientIntegral l = a) :
    |(deriv (gaugeDefect epsilon a l theta) 0)^2 -
      epsilon^2*(primitiveIntegrand a l theta-a)^2| ≤
        8*(a+1)^2*epsilon^3 := by
  have hR : 0 ≤ a+1 := by linarith
  have hv := primitiveIntegrand_displacement_bound a l theta ha hl hcoef
  have hd := gaugeDefect_initial_slope_bound epsilon a l theta he he1 ha
  exact quadratic_slope_square_error epsilon (a+1)
    (primitiveIntegrand a l theta-a)
    (deriv (gaugeDefect epsilon a l theta) 0)
    he (he1.trans (by norm_num)) hR hv hd

end
end Specification
end BilinearSystems
