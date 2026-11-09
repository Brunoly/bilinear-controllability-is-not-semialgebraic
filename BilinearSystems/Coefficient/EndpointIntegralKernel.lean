import BilinearSystems.Analysis.GrowthAsymptotic

/-!
# Endpoint integral kernel
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def endpointKernel (b x : ℝ) : ℝ := Real.sqrt (b+x^2)-x

/-- Rationalization of the square-root difference, including x=0. -/
theorem endpointKernel_rationalized (b x : ℝ)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hpos : 0 < b+x^2) :
    endpointKernel b x = b/(Real.sqrt (b+x^2)+x) := by
  have hs : 0 < Real.sqrt (b+x^2) := Real.sqrt_pos.mpr hpos
  have hden : Real.sqrt (b+x^2)+x ≠ 0 := (add_pos_of_pos_of_nonneg hs hx).ne'
  have hsquare : (Real.sqrt (b+x^2))^2 = b+x^2 := Real.sq_sqrt hpos.le
  unfold endpointKernel
  apply (eq_div_iff hden).2
  nlinarith

/-- The kernel is nonnegative for nonnegative b and x. -/
theorem endpointKernel_nonneg (b x : ℝ) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    0 ≤ endpointKernel b x := by
  have hsum : 0 ≤ b+x^2 := by positivity
  have hsqrt : x = Real.sqrt (x^2) := (Real.sqrt_sq hx).symm
  have hle : Real.sqrt (x^2) ≤ Real.sqrt (b+x^2) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold endpointKernel
  linarith

/-- On the positive half-line, the kernel is bounded by b/(2x).
This controls the tail of the endpoint integral. -/
theorem endpointKernel_le_inv (b x : ℝ) (hb : 0 ≤ b) (hx : 0 < x) :
    endpointKernel b x ≤ b/(2*x) := by
  have hpos : 0 < b+x^2 := by positivity
  rw [endpointKernel_rationalized b x hb hx.le hpos]
  have hsqrt : x ≤ Real.sqrt (b+x^2) := by
    have h := Real.sqrt_le_sqrt (show x^2 ≤ b+x^2 by linarith)
    simpa [Real.sqrt_sq hx.le] using h
  have hden : 0 < 2*x := by positivity
  have hdenle : 2*x ≤ Real.sqrt (b+x^2)+x := by linarith
  exact div_le_div_of_nonneg_left hb hden hdenle

/-- The endpoint kernel vanishes at b=0 for x>=0. -/
theorem endpointKernel_zero (x : ℝ) (hx : 0 ≤ x) :
    endpointKernel 0 x = 0 := by
  simp [endpointKernel, Real.sqrt_sq hx]

/-- Derivative of the rationalized square-root kernel for b>0. -/
theorem endpointKernel_hasDerivAt (b x : ℝ)
    (hb : 0 < b) :
    HasDerivAt (endpointKernel b)
      (-b/(Real.sqrt (b+x^2)*(Real.sqrt (b+x^2)+x))) x := by
  have harg : 0 < b+x^2 := by positivity
  have hsqrt : Real.sqrt (b+x^2) ≠ 0 := (Real.sqrt_pos.mpr harg).ne'
  have hden : Real.sqrt (b+x^2)+x ≠ 0 := by
    have hs : 0 < Real.sqrt (b+x^2) := Real.sqrt_pos.mpr harg
    nlinarith [Real.sq_sqrt harg.le]
  have hinner : HasDerivAt (fun y : ℝ => b+y^2) (2*x) x := by
    have hh := (hasDerivAt_const x b).add ((hasDerivAt_id x).pow 2)
    convert hh using 1
    · funext y
      simp
    · simp
  have hroot := (Real.hasDerivAt_sqrt harg.ne').comp x hinner
  have hraw : HasDerivAt (endpointKernel b)
      (x/Real.sqrt (b+x^2)-1) x := by
    convert hroot.sub (hasDerivAt_id x) using 1
    · rfl
    · ring
  convert hraw using 1
  field_simp [hsqrt,hden]
  nlinarith [Real.sq_sqrt harg.le]

/-- Derivative bound on positive arguments for the sine-to-identity substitution. -/
theorem endpointKernel_deriv_abs_le (b x : ℝ)
    (hb : 0 < b) (hx : 0 < x) :
    |deriv (endpointKernel b) x| ≤ b/(2*x^2) := by
  rw [(endpointKernel_hasDerivAt b x hb).deriv]
  have hsqrt : x ≤ Real.sqrt (b+x^2) := by
    have h := Real.sqrt_le_sqrt (show x^2 ≤ b+x^2 by linarith)
    simpa [Real.sqrt_sq hx.le] using h
  have hden : 0 < Real.sqrt (b+x^2)*(Real.sqrt (b+x^2)+x) := by
    have hp : 0 < Real.sqrt (b+x^2) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hdenle : 2*x^2 ≤
      Real.sqrt (b+x^2)*(Real.sqrt (b+x^2)+x) := by
    have hsquare : (Real.sqrt (b+x^2))^2 = b+x^2 :=
      Real.sq_sqrt (by positivity)
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hsqrt)]
  rw [abs_div, abs_neg, abs_of_pos hb, abs_of_pos hden]
  exact div_le_div_of_nonneg_left hb.le (by positivity : 0 < 2*x^2) hdenle

end
end Specification
end BilinearSystems
