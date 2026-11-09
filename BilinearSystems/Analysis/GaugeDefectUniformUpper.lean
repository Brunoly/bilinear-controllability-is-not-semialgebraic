import BilinearSystems.Analysis.QuadraticRatioError

/-!
# Gauge defect uniform upper
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Every nonzero angular edge obeys lambda*epsilon² plus a cubic error
whose constant depends only on a and lambda, never on theta or t. -/
theorem gaugeDefect_uniform_upper (epsilon a l theta t : ℝ)
    (he : 0 ≤ epsilon) (hehalf : epsilon ≤ 1/2)
    (ha : 0 ≤ a) (hl : 0 < l)
    (hcoef : coefficientIntegral l = a)
    (hecurv : epsilon ≤
      1/(2*(2+1/Real.sqrt (2*l))))
    (hne : angularKernel epsilon a theta t ≠ 0) :
    Real.log |angularKernel epsilon a theta t| +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+t)-
        gaugeProfile a l theta) ≤
      l*epsilon^2 +
        (2+(8+(2+1/Real.sqrt (2*l)))*(a+1)^2)*epsilon^3 := by
  let s := Real.sin (2*theta)
  let v := primitiveIntegrand a l theta-a
  let R := a+1
  let L := 2+1/Real.sqrt (2*l)
  let d := deriv (gaugeDefect epsilon a l theta) 0
  let m := 1-epsilon*L
  have he1 : epsilon ≤ 1 := hehalf.trans (by norm_num)
  have hs : |s| ≤ 1 := Real.abs_sin_le_one _
  have hp : 0 < 1-epsilon*s := by
    have hss : s ≤ 1 := (le_abs_self s).trans hs
    have hmul := mul_le_mul_of_nonneg_left hss he
    nlinarith
  have hmargin : 1/2 ≤ m :=
    gaugeDefect_curvature_margin epsilon l hl he hecurv
  have hm : 0 < m := by linarith
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hv : |v| ≤ R :=
    primitiveIntegrand_displacement_bound a l theta ha hl.le hcoef
  have hsq : |d^2-epsilon^2*v^2| ≤ 8*R^2*epsilon^3 :=
    gaugeDefect_initial_slope_square_bound epsilon a l theta
      he hehalf ha hl.le hcoef
  have hratio : d^2/(2*m) ≤
      epsilon^2*v^2/2+(8+L)*R^2*epsilon^3 :=
    quadratic_ratio_error epsilon R L v d he he1 hR hL hmargin hv hsq
  have hinitial : |gaugeDefect epsilon a l theta 0+
      epsilon^2*s^2/2| ≤ 2*epsilon^3 :=
    gaugeDefect_initial_cubic epsilon a l theta he hehalf hcoef
  have hupper := gaugeDefect_projective_quadratic_upper
    epsilon a l theta t hl he hp hm hcoef hne
  rw [← gaugeDefectAtZero epsilon a l theta hcoef] at hupper
  have hidentity : (v^2-s^2)/2 = l :=
    primitiveIntegrand_displacement_square a l theta hl.le
  have hscaled := congrArg (fun x : ℝ => epsilon^2*x) hidentity
  dsimp [d, m, L, R, v, s] at hupper hratio hinitial hscaled ⊢
  have hinitUpper := (le_abs_self _).trans hinitial
  nlinarith

end
end Specification
end BilinearSystems
