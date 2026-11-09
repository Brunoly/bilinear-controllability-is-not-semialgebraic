import BilinearSystems.Analysis.GaugeDefectInitialExpansion

/-!
# Gauge defect slope expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The exact slope differs from epsilon times the Hamilton-Jacobi
optimizer by a quadratic error, uniformly in the angular direction. -/
theorem gaugeDefect_initial_slope_bound (epsilon a l theta : ℝ)
    (he : 0 ≤ epsilon) (hehalf : epsilon ≤ 1/2)
    (ha : 0 ≤ a) :
    |deriv (gaugeDefect epsilon a l theta) 0 -
      epsilon*(primitiveIntegrand a l theta-a)| ≤
        2*(a+1)*epsilon^2 := by
  let s := Real.sin (2*theta)
  let k := Real.cos (2*theta)
  let p := 1-epsilon*s
  let R := a+1
  have hs : |s| ≤ 1 := Real.abs_sin_le_one _
  have hk : |k| ≤ 1 := Real.abs_cos_le_one _
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hpHalf : 1/2 ≤ p := by
    have hss : s ≤ 1 := (le_abs_self s).trans hs
    have hemul := mul_le_mul_of_nonneg_left hss he
    dsimp [p]
    nlinarith
  have hp : 0 < p := by linarith
  have hq : |a+k| ≤ R := by
    apply abs_le.mpr
    have hka := abs_le.mp hk
    dsimp [R]
    constructor <;> linarith
  have hsq : |s*(a+k)| ≤ R := by
    rw [abs_mul]
    calc
      _ ≤ 1*R := mul_le_mul hs hq (abs_nonneg _) (by norm_num)
      _ = R := one_mul _
  have hnum : |epsilon^2*s*(a+k)| ≤ epsilon^2*R := by
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg epsilon)
    simpa only [abs_mul, abs_pow, abs_of_nonneg he, abs_of_nonneg (sq_nonneg epsilon),
      mul_assoc] using hmul
  have hfrac : |epsilon^2*s*(a+k)/p| ≤ 2*R*epsilon^2 := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).2
    have hmul := mul_le_mul_of_nonneg_left hpHalf
      (show 0 ≤ 2*R*epsilon^2 by positivity)
    nlinarith [hnum]
  have hderiv := gaugeDefectDerivativeAtZero epsilon a l theta
    (by simpa [p, s] using hp)
  rw [hderiv]
  change |epsilon*(primitiveIntegrand a l theta-a) -
      epsilon^2*s*(a+k)/p -
      epsilon*(primitiveIntegrand a l theta-a)| ≤ 2*R*epsilon^2
  have hcancel : epsilon*(primitiveIntegrand a l theta-a) -
      epsilon^2*s*(a+k)/p -
      epsilon*(primitiveIntegrand a l theta-a) =
        -(epsilon^2*s*(a+k)/p) := by ring
  rw [hcancel, abs_neg]
  exact hfrac

end
end Specification
end BilinearSystems
