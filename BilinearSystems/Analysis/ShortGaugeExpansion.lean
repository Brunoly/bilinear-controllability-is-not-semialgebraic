import BilinearSystems.Analysis.SecondDerivativeTaylor

/-!
# Short gauge expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The gauge derivative at a quarter turn is the source-angle cosine plus
the periodic primitive integrand. -/
theorem gaugeProfile_quarterTurn_derivative (a l theta : ℝ) :
    deriv (gaugeProfile a l) (theta+Real.pi/2) =
      Real.cos (2*theta)+primitiveIntegrand a l theta := by
  rw [(gaugeProfile_hasDerivAt a l (theta+Real.pi/2)).deriv]
  have hangle : 2*(theta+Real.pi/2) = 2*theta+Real.pi := by ring
  rw [hangle, Real.cos_add_pi, primitiveIntegrand_periodic a l theta]
  ring

/-- Uniform gauge expansion. The coefficient depends on lambda through L,
as allowed by the original pointwise-in-a asymptotic. -/
theorem shortGauge_expansion (epsilon a l theta v : ℝ)
    (he : 0 ≤ epsilon) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hv : |v| ≤ a+1) (hl : 0 < l)
    (hcoef : coefficientIntegral l = a) :
    |epsilon*(gaugeProfile a l (theta+Real.pi/2+epsilon*v)-
        gaugeProfile a l theta) -
      (epsilon*Real.sin (2*theta) +
        epsilon^2*v*(Real.cos (2*theta)+primitiveIntegrand a l theta))| ≤
      2*(2+1/Real.sqrt (2*l))*epsilon^3 := by
  let phi := theta+Real.pi/2
  let L := 2+1/Real.sqrt (2*l)
  let t := epsilon*v
  have hfirst (x : ℝ) : HasDerivAt (gaugeProfile a l)
      (deriv (gaugeProfile a l) x) x := by
    exact (gaugeProfile_hasDerivAt a l x).differentiableAt.hasDerivAt
  have hsecond (x : ℝ) : HasDerivAt (fun y => deriv (gaugeProfile a l) y)
      (deriv (fun y => deriv (gaugeProfile a l) y) x) x := by
    exact (gaugeProfile_second_hasDerivAt a l x hl).differentiableAt.hasDerivAt
  have hcurv (x : ℝ) :
      |deriv (fun y => deriv (gaugeProfile a l) y) x| ≤ L :=
    gaugeProfile_second_derivative_bound a l x hl
  have hTaylor := taylor_abs_of_second_derivative_bound
    (gaugeProfile a l) (fun x => deriv (gaugeProfile a l) x)
    (fun x => deriv (fun y => deriv (gaugeProfile a l) y) x)
    L phi t hfirst hsecond hcurv
  have hquarter := gaugeProfile_quarterTurn_difference a l theta hcoef
  have hderiv := gaugeProfile_quarterTurn_derivative a l theta
  have hEq : epsilon*(gaugeProfile a l (theta+Real.pi/2+epsilon*v)-
        gaugeProfile a l theta) -
      (epsilon*Real.sin (2*theta)+
        epsilon^2*v*(Real.cos (2*theta)+primitiveIntegrand a l theta)) =
      epsilon*(gaugeProfile a l (phi+t)-gaugeProfile a l phi-
        deriv (gaugeProfile a l) phi*t) := by
    dsimp [phi, t]
    rw [hderiv]
    linear_combination epsilon*hquarter
  rw [hEq, abs_mul, abs_of_nonneg he]
  have hmul := mul_le_mul_of_nonneg_left hTaylor he
  have hv2 : |v| ≤ 2 := by linarith
  have hvsq : v^2 ≤ 4 := by nlinarith [sq_abs v, abs_nonneg v]
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLvsq := mul_le_mul_of_nonneg_left hvsq hL
  have hprod := mul_le_mul_of_nonneg_left hLvsq
    (show 0 ≤ epsilon^3 by positivity)
  dsimp [t, L] at hmul hprod ⊢
  nlinarith [hmul, hprod]

end
end Specification
end BilinearSystems
