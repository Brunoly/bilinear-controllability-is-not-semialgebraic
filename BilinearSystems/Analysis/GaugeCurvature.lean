import BilinearSystems.Analysis.KernelConcavity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gauge curvature
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem primitiveIntegrand_hasDerivAt (a l theta : ℝ) (hl : 0 < l) :
    HasDerivAt (primitiveIntegrand a l)
      (-(2 * Real.sin (2*theta) * Real.cos (2*theta) /
        Real.sqrt (2*l + Real.sin (2*theta)^2))) theta := by
  let q := fun t : ℝ => 2*l + Real.sin (2*t)^2
  have hq : 0 < q theta := by
    unfold q
    positivity
  have hs := (Real.hasDerivAt_sin (2*theta)).comp theta
    ((hasDerivAt_id theta).const_mul (2 : ℝ))
  have hsq := ((hasDerivAt_const theta (2*l)).add (hs.pow 2))
  have hroot := (Real.hasDerivAt_sqrt hq.ne').comp theta hsq
  have hfinal := (hasDerivAt_const theta a).sub hroot
  convert hfinal using 1
  · funext t
    change a - Real.sqrt (2*l + Real.sin (2*t)^2) =
      a - Real.sqrt (2*l + Real.sin (2*t)^2)
    rfl
  · dsimp [q]
    field_simp [Real.sqrt_ne_zero'.mpr hq]
    ring

theorem gaugeProfile_second_hasDerivAt (a l theta : ℝ) (hl : 0 < l) :
    HasDerivAt (fun t => deriv (gaugeProfile a l) t)
      (2*Real.sin (2*theta) -
        2*Real.sin (2*theta)*Real.cos (2*theta) /
          Real.sqrt (2*l+Real.sin (2*theta)^2)) theta := by
  have hfirst : (fun t => deriv (gaugeProfile a l) t) =
      fun t => -Real.cos (2*t) + primitiveIntegrand a l t := by
    funext t
    exact (gaugeProfile_hasDerivAt a l t).deriv
  rw [hfirst]
  have hc := ((Real.hasDerivAt_cos (2*theta)).comp theta
    ((hasDerivAt_id theta).const_mul (2 : ℝ))).neg
  convert hc.add (primitiveIntegrand_hasDerivAt a l theta hl) using 1
  · funext t
    change -Real.cos (2*t)+primitiveIntegrand a l t =
      -Real.cos (2*t)+primitiveIntegrand a l t
    rfl
  · ring

theorem gaugeProfile_second_derivative_bound (a l theta : ℝ) (hl : 0 < l) :
    |deriv (fun t => deriv (gaugeProfile a l) t) theta| ≤
      2 + 1/Real.sqrt (2*l) := by
  rw [(gaugeProfile_second_hasDerivAt a l theta hl).deriv]
  have hs := Real.abs_sin_le_one (2*theta)
  have hc := Real.abs_cos_le_one (2*theta)
  have hroot : Real.sqrt (2*l) ≤ Real.sqrt (2*l+Real.sin (2*theta)^2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Real.sin (2*theta))])
  have hr : 0 < Real.sqrt (2*l) := Real.sqrt_pos.2 (by positivity)
  have hR : 0 < Real.sqrt (2*l+Real.sin (2*theta)^2) := by
    positivity
  have hsc : |2*Real.sin (2*theta)*Real.cos (2*theta)| ≤ 1 := by
    have hh := sq_nonneg (Real.sin (2*theta)-Real.cos (2*theta))
    have hh' := sq_nonneg (Real.sin (2*theta)+Real.cos (2*theta))
    have hu := Real.sin_sq_add_cos_sq (2*theta)
    apply abs_le.mpr
    constructor <;> nlinarith
  calc
    _ ≤ |2*Real.sin (2*theta)| +
      |2*Real.sin (2*theta)*Real.cos (2*theta) /
        Real.sqrt (2*l+Real.sin (2*theta)^2)| := by simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (2*Real.sin (2*theta)) 0
        (2*Real.sin (2*theta)*Real.cos (2*theta) /
          Real.sqrt (2*l+Real.sin (2*theta)^2)))
    _ ≤ 2 + 1/Real.sqrt (2*l) := by
      rw [abs_div, abs_of_pos hR]
      have hfrac : |2*Real.sin (2*theta)*Real.cos (2*theta)| /
          Real.sqrt (2*l+Real.sin (2*theta)^2) ≤ 1/Real.sqrt (2*l) := by
        apply (div_le_div_iff₀ hR hr).2
        nlinarith [hsc, hroot]
      have htwo : |2*Real.sin (2*theta)| ≤ 2 := by
        rw [abs_mul]
        norm_num
        linarith
      linarith

end
end Specification
end BilinearSystems
