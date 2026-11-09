import BilinearSystems.Analysis.GaugeCurvature

/-!
# Gauge defect curvature
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Filter
open scoped Topology

private theorem gaugeDefect_deriv_eq_on_positive
    (epsilon a l theta x : ℝ) (hf : 0 < angularKernel epsilon a theta x) :
    deriv (gaugeDefect epsilon a l theta) x =
      deriv (fun y => Real.log (angularKernel epsilon a theta y)) x +
        epsilon * deriv (gaugeProfile a l) (theta + Real.pi/2 + x) := by
  have hdef := (gaugeDefect_hasDerivAt epsilon a l theta x hf.ne').deriv
  have hlog := (angularKernel_log_hasDerivAt epsilon a theta x hf).deriv
  have hprof := (gaugeProfile_hasDerivAt a l (theta+Real.pi/2+x)).deriv
  rw [hdef, hlog, hprof]

/-- The exact curvature identity, valid for every strictly positive edge. -/
theorem gaugeDefect_second_hasDerivAt (epsilon a l theta t : ℝ)
    (hl : 0 < l) (hf : 0 < angularKernel epsilon a theta t) :
    HasDerivAt (fun x => deriv (gaugeDefect epsilon a l theta) x)
      (-1 - (deriv (angularKernel epsilon a theta) t /
        angularKernel epsilon a theta t)^2 +
        epsilon * deriv (fun y => deriv (gaugeProfile a l) y)
          (theta + Real.pi/2 + t)) t := by
  let f := angularKernel epsilon a theta
  have hcont : Continuous f := by
    unfold f angularKernel
    fun_prop
  have hpos : ∀ᶠ x in 𝓝 t, 0 < f x :=
    hcont.continuousAt.eventually_const_lt hf
  have heq : (fun x => deriv (gaugeDefect epsilon a l theta) x) =ᶠ[𝓝 t]
      fun x => deriv (fun y => Real.log (f y)) x +
        epsilon * deriv (gaugeProfile a l) (theta+Real.pi/2+x) := by
    filter_upwards [hpos] with x hx
    exact gaugeDefect_deriv_eq_on_positive epsilon a l theta x hx
  have hlog := angularKernel_log_curvature epsilon a theta t hf
  have hshift : HasDerivAt (fun x : ℝ => theta+Real.pi/2+x) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).const_add (theta+Real.pi/2)
  have hprof := (gaugeProfile_second_hasDerivAt a l
    (theta+Real.pi/2+t) hl).comp t hshift
  have hsum := hlog.add (hprof.const_mul epsilon)
  have hsum' : HasDerivAt
      (fun x => deriv (fun y => Real.log (f y)) x +
        epsilon * deriv (gaugeProfile a l) (theta+Real.pi/2+x))
      (-1 - (deriv f t / f t)^2 +
        epsilon * deriv (fun y => deriv (gaugeProfile a l) y)
          (theta+Real.pi/2+t)) t := by
    convert hsum using 1
    · rfl
    · rw [(gaugeProfile_second_hasDerivAt a l
        (theta+Real.pi/2+t) hl).deriv]
      ring
  exact hsum'.congr_of_eventuallyEq heq

/-- Curvature bound for logarithmic weighted edge gains. -/
theorem gaugeDefect_second_derivative_le (epsilon a l theta t : ℝ)
    (hl : 0 < l) (he : 0 ≤ epsilon)
    (hf : 0 < angularKernel epsilon a theta t) :
    deriv (fun x => deriv (gaugeDefect epsilon a l theta) x) t ≤
      -(1 - epsilon * (2 + 1/Real.sqrt (2*l))) := by
  rw [(gaugeDefect_second_hasDerivAt epsilon a l theta t hl hf).deriv]
  have hbound := gaugeProfile_second_derivative_bound a l
    (theta+Real.pi/2+t) hl
  have hle := le_abs_self
    (deriv (fun y => deriv (gaugeProfile a l) y) (theta+Real.pi/2+t))
  have hm := mul_le_mul_of_nonneg_left (hle.trans hbound) he
  nlinarith [sq_nonneg (deriv (angularKernel epsilon a theta) t /
    angularKernel epsilon a theta t)]

end
end Specification
end BilinearSystems
