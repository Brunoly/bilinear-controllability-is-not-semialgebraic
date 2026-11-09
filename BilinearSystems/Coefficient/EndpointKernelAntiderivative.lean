import BilinearSystems.Coefficient.EndpointDifference

/-!
# Endpoint kernel antiderivative
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def endpointKernelAntiderivative (b x : ℝ) : ℝ :=
  (x*Real.sqrt (x^2+b)-x^2)/2 +
    (b/2)*Real.log (x+Real.sqrt (x^2+b))

private theorem endpoint_sqrt_add_pos (b x : ℝ) (hb : 0 < b) :
    0 < x+Real.sqrt (x^2+b) := by
  have harg : 0 < x^2+b := by positivity
  have hroot : 0 ≤ Real.sqrt (x^2+b) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (x^2+b))^2 = x^2+b := Real.sq_sqrt harg.le
  nlinarith

/-- The derivative is exactly sqrt(b+x²)-x for all real x. -/
theorem endpointKernelAntiderivative_hasDerivAt (b x : ℝ) (hb : 0 < b) :
    HasDerivAt (endpointKernelAntiderivative b) (endpointKernel b x) x := by
  let s := Real.sqrt (x^2+b)
  have harg : 0 < x^2+b := by positivity
  have hs : 0 < s := Real.sqrt_pos.mpr harg
  have hs2 : s^2 = x^2+b := Real.sq_sqrt harg.le
  have hden : 0 < x+s := endpoint_sqrt_add_pos b x hb
  have hinner : HasDerivAt (fun y : ℝ => y^2+b) (2*x) x := by
    have hh := ((hasDerivAt_id x).pow 2).add_const b
    convert hh using 1
    · funext y; simp
    · simp
  have hroot : HasDerivAt (fun y : ℝ => Real.sqrt (y^2+b)) (x/s) x := by
    have hh := (Real.hasDerivAt_sqrt harg.ne').comp x hinner
    convert hh using 1
    · rfl
    · dsimp [s]
      ring
  have hsum : HasDerivAt
      (fun y : ℝ => y+Real.sqrt (y^2+b)) (1+x/s) x := by
    convert (hasDerivAt_id x).add hroot using 1
    · funext y; simp [add_comm]
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log (y+Real.sqrt (y^2+b)))
      ((1+x/s)/(x+s)) x := by
    convert (Real.hasDerivAt_log hden.ne').comp x hsum using 1
    · rfl
    · ring
  have hprod : HasDerivAt (fun y : ℝ => y*Real.sqrt (y^2+b))
      (s+x*(x/s)) x := by
    convert (hasDerivAt_id x).mul hroot using 1
    · funext y; simp [add_comm]
    · dsimp [s]
      ring
  have hsqDeriv : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    · rfl
    · simp
  have hleft : HasDerivAt
      (fun y : ℝ => (y*Real.sqrt (y^2+b)-y^2)/2)
      ((s+x*(x/s)-2*x)/2) x := by
    convert (hprod.sub hsqDeriv).div_const 2 using 1
  have hright : HasDerivAt
      (fun y : ℝ => (b/2)*Real.log (y+Real.sqrt (y^2+b)))
      ((b/2)*((1+x/s)/(x+s))) x := hlog.const_mul _
  have htotal := hleft.add hright
  convert htotal using 1
  · rfl
  · dsimp [endpointKernel]
    have hsne : s ≠ 0 := hs.ne'
    have hdene : x+s ≠ 0 := hden.ne'
    rw [add_comm b (x^2)]
    change s-x = (s+x*(x/s)-2*x)/2 + (b/2)*((1+x/s)/(x+s))
    have hratio : (1+x/s)/(x+s) = 1/s := by
      field_simp [hsne,hdene]
      ring
    rw [hratio]
    field_simp [hsne]
    nlinarith [hs2]

/-- Closed form of the square-root model integral on [0, eta]. -/
theorem endpointKernel_model_integral (b eta : ℝ) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..eta, endpointKernel b t) =
      (eta*Real.sqrt (eta^2+b)-eta^2)/2 +
        (b/2)*Real.log (eta+Real.sqrt (eta^2+b)) -
        (b/4)*Real.log b := by
  have hc : Continuous (endpointKernel b) := by
    unfold endpointKernel
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => endpointKernelAntiderivative_hasDerivAt b x hb)
    (hc.intervalIntegrable 0 eta)
  rw [hFTC]
  unfold endpointKernelAntiderivative
  simp only [zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_add, zero_sub]
  rw [Real.log_sqrt hb.le]
  ring

end
end Specification
end BilinearSystems
