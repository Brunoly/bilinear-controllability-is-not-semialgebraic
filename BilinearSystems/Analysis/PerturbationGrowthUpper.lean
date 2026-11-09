import BilinearSystems.Growth.WeightedCycleGrowthUpper
import BilinearSystems.Analysis.UnitDirections

/-!
# Perturbation growth upper
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def angularGaugeWeight (epsilon a l : ℝ) (v : State) : ℝ :=
  Real.exp (epsilon * gaugeProfile a l (Complex.arg (⟨v 0, v 1⟩ : ℂ)))

theorem angularGaugeWeight_pos (epsilon a l : ℝ) (v : State) :
    0 < angularGaugeWeight epsilon a l v := Real.exp_pos _

/-- Uniform exponential upper bound for cycle growth. -/
theorem parameterGrowth_upper_exponential (epsilon a l : ℝ)
    (he : 0 ≤ epsilon) (hehalf : epsilon ≤ 1/2)
    (ha : 0 ≤ a) (hl : 0 < l)
    (hcoef : coefficientIntegral l = a)
    (hecurv : epsilon ≤ 1/(2*(2+1/Real.sqrt (2*l)))) :
    parameterGrowth epsilon a ≤
      Real.exp (l*epsilon^2 +
        (2+(8+(2+1/Real.sqrt (2*l)))*(a+1)^2)*epsilon^3) := by
  let B := l*epsilon^2 +
    (2+(8+(2+1/Real.sqrt (2*l)))*(a+1)^2)*epsilon^3
  change cycleGrowth (perturbationMatrix epsilon a) ≤ Real.exp B
  apply cycleGrowth_le_of_weighted_edge_bound
    (perturbationMatrix epsilon a) (angularGaugeWeight epsilon a l)
    (Real.exp B) (Real.exp_pos B).le
    (fun v _ => angularGaugeWeight_pos epsilon a l v)
  intro v w hv hw
  let theta := Complex.arg (⟨v 0, v 1⟩ : ℂ)
  let phi := Complex.arg (⟨w 0, w 1⟩ : ℂ)
  let t := phi-theta-Real.pi/2
  have hvAngle : v = angularDirection theta := unitDirection_eq_angular_arg v hv
  have hwAngle : w = angularDirection phi := unitDirection_eq_angular_arg w hw
  have hangle : theta+Real.pi/2+t = phi := by dsimp [t]; ring
  have hkernel : directionGain (perturbationMatrix epsilon a) v w =
      angularKernel epsilon a theta t := by
    rw [hvAngle, hwAngle, ← hangle]
    exact exactAngularKernel epsilon a theta t
  have hweightV : angularGaugeWeight epsilon a l v =
      Real.exp (epsilon*gaugeProfile a l theta) := rfl
  have hweightW : angularGaugeWeight epsilon a l w =
      Real.exp (epsilon*gaugeProfile a l (theta+Real.pi/2+t)) := by
    rw [hangle]
    rfl
  rw [hkernel, hweightV, hweightW]
  by_cases hk : angularKernel epsilon a theta t = 0
  · simp [hk]; positivity
  · have hupper := gaugeDefect_uniform_upper epsilon a l theta t
      he hehalf ha hl hcoef hecurv hk
    have habs : 0 < |angularKernel epsilon a theta t| := abs_pos.mpr hk
    have hlog : Real.log |angularKernel epsilon a theta t| +
        epsilon*gaugeProfile a l (theta+Real.pi/2+t) ≤
        B + epsilon*gaugeProfile a l theta := by
      dsimp [B]
      nlinarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_add, Real.exp_add, Real.exp_log habs] at hexp
    exact hexp

/-- Logarithmic form of the upper bound used by the
manuscript's asymptotic statement. -/
theorem parameterGrowth_log_upper (epsilon a l : ℝ)
    (he : 0 ≤ epsilon) (hehalf : epsilon ≤ 1/2)
    (ha : 0 ≤ a) (hl : 0 < l)
    (hcoef : coefficientIntegral l = a)
    (hecurv : epsilon ≤ 1/(2*(2+1/Real.sqrt (2*l)))) :
    Real.log (parameterGrowth epsilon a) ≤
      l*epsilon^2 +
        (2+(8+(2+1/Real.sqrt (2*l)))*(a+1)^2)*epsilon^3 := by
  have hpositive : 0 < parameterGrowth epsilon a :=
    lt_of_lt_of_le zero_lt_one (parameterGrowth_ge_one epsilon a)
  exact (Real.log_le_iff_le_exp hpositive).mpr
    (parameterGrowth_upper_exponential epsilon a l he hehalf ha hl hcoef hecurv)

end
end Specification
end BilinearSystems
