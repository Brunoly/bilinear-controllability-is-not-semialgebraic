import BilinearSystems.Analysis.PerturbationPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Perturbation profile
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem doubled_angle_integral (l : ℝ) :
    (∫ t in (0 : ℝ)..(Real.pi/2), Real.sqrt (2*l + Real.sin (2*t)^2)) =
    ∫ t in (0 : ℝ)..(Real.pi/2), Real.sqrt (2*l + Real.sin t^2) := by
  let f := fun t : ℝ => Real.sqrt (2*l + Real.sin t^2)
  have hc : Continuous f := Real.continuous_sqrt.comp
    (continuous_const.add (Real.continuous_sin.pow 2))
  have hsymm (t : ℝ) : f (Real.pi-t) = f t := by simp [f, Real.sin_pi_sub]
  have hs := intervalIntegral.integral_comp_sub_left f Real.pi
    (a := (0 : ℝ)) (b := Real.pi/2)
  have hhalf : Real.pi - Real.pi/2 = Real.pi/2 := by ring
  simp only [hsymm, hhalf, sub_zero] at hs
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (Real.pi/2)) (hc.intervalIntegrable (Real.pi/2) Real.pi)
  change (∫ t in (0 : ℝ)..(Real.pi/2), f (2*t)) = _
  rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0)]
  have hpi : 2*(Real.pi/2) = Real.pi := by ring
  rw [mul_zero, hpi, ← hadd, ← hs]
  simp only [smul_eq_mul]
  ring

theorem primitiveIntegrand_zero_mean (a l : ℝ) (h : coefficientIntegral l = a) :
    (∫ t in (0 : ℝ)..(Real.pi/2), primitiveIntegrand a l t) = 0 := by
  let f := fun t : ℝ => Real.sqrt (2*l + Real.sin (2*t)^2)
  have hf : Continuous f := Real.continuous_sqrt.comp
    (continuous_const.add ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2))
  change (∫ t in (0 : ℝ)..(Real.pi/2), a - f t) = 0
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    (hf.intervalIntegrable _ _), intervalIntegral.integral_const]
  change (Real.pi/2 - 0)*a - (∫ t in (0 : ℝ)..(Real.pi/2),
    Real.sqrt (2*l + Real.sin (2*t)^2)) = 0
  rw [doubled_angle_integral, ← h]
  unfold coefficientIntegral
  field_simp [Real.pi_ne_zero]
  ring

theorem perturbationPrimitive_periodic (a l : ℝ) (h : coefficientIntegral l = a) :
    Function.Periodic (perturbationPrimitive a l) (Real.pi/2) := by
  intro t
  unfold perturbationPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((primitiveIntegrand_continuous a l).intervalIntegrable 0 t)
    ((primitiveIntegrand_continuous a l).intervalIntegrable t (t+Real.pi/2))]
  rw [(primitiveIntegrand_periodic a l).intervalIntegral_add_eq t 0, zero_add,
    primitiveIntegrand_zero_mean a l h, add_zero]

theorem gaugeProfile_periodic (a l : ℝ) (h : coefficientIntegral l = a) :
    Function.Periodic (gaugeProfile a l) Real.pi := by
  intro t
  have hp := perturbationPrimitive_periodic a l h
  have hshift : t+Real.pi = t+Real.pi/2+Real.pi/2 := by ring
  have hprimitive : perturbationPrimitive a l (t+Real.pi) = perturbationPrimitive a l t := by
    rw [hshift]
    exact (hp (t+Real.pi/2)).trans (hp t)
  have hs : 2*(t+Real.pi) = 2*t+2*Real.pi := by ring
  simp [gaugeProfile, hs, hprimitive, Real.sin_add_two_pi]

theorem gaugeProfile_quarterTurn_difference (a l theta : ℝ) (h : coefficientIntegral l = a) :
    gaugeProfile a l (theta+Real.pi/2) - gaugeProfile a l theta = Real.sin (2*theta) := by
  have hs : 2*(theta+Real.pi/2) = 2*theta+Real.pi := by ring
  unfold gaugeProfile
  rw [(perturbationPrimitive_periodic a l h) theta, hs, Real.sin_add_pi]
  ring

theorem primitiveIntegrand_squared_identity (a l theta : ℝ) (hl : 0 ≤ l) :
    (primitiveIntegrand a l theta-a)^2 - Real.sin (2*theta)^2 = 2*l := by
  have hs := Real.sq_sqrt (show 0 ≤ 2*l + Real.sin (2*theta)^2 by positivity)
  unfold primitiveIntegrand
  nlinarith

end
end Specification
end BilinearSystems
