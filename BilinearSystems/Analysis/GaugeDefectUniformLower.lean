import BilinearSystems.Analysis.ShortGaugeExpansion

/-!
# Gauge defect uniform lower
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The explicit short edge is positive and has logarithmic gauge gain
lambda*epsilon² with a uniform cubic error over all source directions. -/
theorem gaugeDefect_explicit_lower (epsilon a l theta : ℝ)
    (he : 0 < epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a) :
    let v := primitiveIntegrand a l theta-a
    0 < angularKernel epsilon a theta (epsilon*v) ∧
    |gaugeDefect epsilon a l theta (epsilon*v)-l*epsilon^2| ≤
      (100+2*(2+1/Real.sqrt (2*l)))*epsilon^3 := by
  dsimp
  let v := primitiveIntegrand a l theta-a
  let s := Real.sin (2*theta)
  let k := Real.cos (2*theta)
  let L := 2+1/Real.sqrt (2*l)
  have hv : |v| ≤ a+1 :=
    primitiveIntegrand_displacement_bound a l theta ha hl.le hcoef
  have hsize := shortKernel_displacement_half epsilon a theta v
    he.le heSmall ha ha1 hv
  have hpos : 0 < angularKernel epsilon a theta (epsilon*v) := by
    have hh := abs_le.mp hsize
    nlinarith
  have hlog := shortKernel_log_expansion epsilon a theta v
    he.le heSmall ha ha1 hv
  have hgauge := shortGauge_expansion epsilon a l theta v
    he.le ha ha1 hv hl hcoef
  have hident : (v^2-s^2)/2 = l :=
    primitiveIntegrand_displacement_square a l theta hl.le
  have hvDef : primitiveIntegrand a l theta = v+a := by
    dsimp [v]
    ring
  have hcoeff :
      (-epsilon*s+epsilon^2*(-v^2/2-v*(a+k)-s^2/2)) +
      (epsilon*s+epsilon^2*v*(k+primitiveIntegrand a l theta)) =
      l*epsilon^2 := by
    rw [hvDef]
    calc
      _ = epsilon^2*((v^2-s^2)/2) := by ring
      _ = l*epsilon^2 := by rw [hident]; ring
  have herror : |gaugeDefect epsilon a l theta (epsilon*v)-l*epsilon^2| ≤
      (100+2*L)*epsilon^3 := by
    let A := -epsilon*s+epsilon^2*(-v^2/2-v*(a+k)-s^2/2)
    let B := epsilon*s+epsilon^2*v*(k+primitiveIntegrand a l theta)
    have hrewrite : gaugeDefect epsilon a l theta (epsilon*v)-l*epsilon^2 =
        (Real.log (angularKernel epsilon a theta (epsilon*v))-A) +
        (epsilon*(gaugeProfile a l (theta+Real.pi/2+epsilon*v)-
          gaugeProfile a l theta)-B) := by
      dsimp [A, B, gaugeDefect]
      rw [← hcoeff]
      ring
    rw [hrewrite]
    have htri := abs_add_le
      (Real.log (angularKernel epsilon a theta (epsilon*v))-A)
      (epsilon*(gaugeProfile a l (theta+Real.pi/2+epsilon*v)-
        gaugeProfile a l theta)-B)
    have hlog' : |Real.log (angularKernel epsilon a theta (epsilon*v))-A| ≤
        100*epsilon^3 := by simpa [A, s, k] using hlog
    have hgauge' : |epsilon*(gaugeProfile a l
        (theta+Real.pi/2+epsilon*v)-gaugeProfile a l theta)-B| ≤
        2*L*epsilon^3 := by simpa [B, L, s, k] using hgauge
    nlinarith
  exact ⟨hpos, herror⟩

end
end Specification
end BilinearSystems
