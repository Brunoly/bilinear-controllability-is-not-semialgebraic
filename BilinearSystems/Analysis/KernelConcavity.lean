import BilinearSystems.Analysis.AngularKernel

/-!
# Kernel concavity
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter
open scoped Topology

theorem angularKernel_hasDerivAt_derivative (epsilon a theta t : ℝ) :
    HasDerivAt
      (fun x => -Real.sin x -
        epsilon*(a*Real.cos x+Real.cos (2*theta+x)))
      (-Real.cos t +
        epsilon*(a*Real.sin t+Real.sin (2*theta+t))) t := by
  have h₁ := (Real.hasDerivAt_sin t).neg
  have h₂ := ((Real.hasDerivAt_cos t).const_mul a).add
    ((Real.hasDerivAt_cos (2*theta+t)).comp t
      ((hasDerivAt_id t).const_add (2*theta)))
  have h := h₁.sub (h₂.const_mul epsilon)
  convert h using 1
  · funext x
    change -Real.sin x - epsilon*(a*Real.cos x+Real.cos (2*theta+x)) =
      -Real.sin x - epsilon*(a*Real.cos x+Real.cos (2*theta+x))
    rfl
  · ring

theorem angularKernel_second_derivative_eq_neg (epsilon a theta t : ℝ) :
    deriv (fun x => deriv (angularKernel epsilon a theta) x) t =
      -angularKernel epsilon a theta t := by
  have hfirst : (fun x => deriv (angularKernel epsilon a theta) x) =
      fun x => -Real.sin x-epsilon*(a*Real.cos x+Real.cos (2*theta+x)) := by
    funext x
    exact (angularKernelDerivative epsilon a theta x).deriv
  rw [hfirst, (angularKernel_hasDerivAt_derivative epsilon a theta t).deriv]
  unfold angularKernel
  ring

theorem angularKernel_log_hasDerivAt (epsilon a theta t : ℝ)
    (hf : 0 < angularKernel epsilon a theta t) :
    HasDerivAt (fun x => Real.log (angularKernel epsilon a theta x))
      ((-Real.sin t-epsilon*(a*Real.cos t+Real.cos (2*theta+t))) /
        angularKernel epsilon a theta t) t := by
  convert (Real.hasDerivAt_log hf.ne').comp t
    (angularKernelDerivative epsilon a theta t) using 1
  · rfl
  · ring

/-- On a positive edge, log f has curvature at most -1. -/
theorem angularKernel_log_curvature (epsilon a theta t : ℝ)
    (hf : 0 < angularKernel epsilon a theta t) :
    HasDerivAt
      (fun x => deriv (fun y => Real.log (angularKernel epsilon a theta y)) x)
      (-1-((deriv (angularKernel epsilon a theta) t) /
        angularKernel epsilon a theta t)^2) t := by
  let f := angularKernel epsilon a theta
  have hne : f t ≠ 0 := hf.ne'
  have hderiv : (fun x => deriv (fun y => Real.log (f y)) x) =ᶠ[𝓝 t]
      fun x => deriv f x / f x := by
    have he : ∀ᶠ x in 𝓝 t, 0 < f x :=
      (show Continuous f by unfold f angularKernel; fun_prop).continuousAt.eventually_const_lt hf
    filter_upwards [he] with x hx
    simpa only [f, (angularKernelDerivative epsilon a theta x).deriv] using
      (angularKernel_log_hasDerivAt epsilon a theta x hx).deriv
  have hq : HasDerivAt (fun x => deriv f x / f x)
      (((-f t)*f t-(deriv f t)^2)/(f t)^2) t := by
    have h₂ : HasDerivAt (fun x => deriv f x) (-f t) t := by
      have hfirst : (fun x => deriv f x) =
          fun x => -Real.sin x-epsilon*(a*Real.cos x+Real.cos (2*theta+x)) := by
        funext x
        exact (angularKernelDerivative epsilon a theta x).deriv
      rw [hfirst]
      convert angularKernel_hasDerivAt_derivative epsilon a theta t using 1
      unfold f angularKernel
      ring
    have hh := h₂.div (angularKernelDerivative epsilon a theta t) hne
    convert hh using 1 <;>
      simp only [f, (angularKernelDerivative epsilon a theta t).deriv] <;> ring
  have heq : ((-f t)*f t-(deriv f t)^2)/(f t)^2 =
      -1-((deriv f t)/f t)^2 := by
    field_simp [hne] <;> ring
  rw [← heq]
  exact hq.congr_of_eventuallyEq hderiv

end
end Specification
end BilinearSystems
