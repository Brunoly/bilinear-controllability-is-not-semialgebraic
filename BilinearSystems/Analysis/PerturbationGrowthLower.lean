import BilinearSystems.Growth.WeightedGrowthLower
import BilinearSystems.Analysis.AngularGaugeBounds

/-!
# Perturbation growth lower
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Exponential lower bound for cycle growth. -/
theorem parameterGrowth_lower_exponential (epsilon a l : ℝ)
    (he : 0 < epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a) :
    Real.exp (l*epsilon^2-
      (100+2*(2+1/Real.sqrt (2*l)))*epsilon^3) ≤
      parameterGrowth epsilon a := by
  obtain ⟨H,hH0,hH⟩ := gaugeProfile_bounded a l hcoef
  let b := l*epsilon^2-
    (100+2*(2+1/Real.sqrt (2*l)))*epsilon^3
  let W := angularGaugeWeight epsilon a l
  let c := Real.exp (-epsilon*H)
  let C := Real.exp (epsilon*H)
  change Real.exp b ≤ parameterGrowth epsilon a
  apply perturbation_growth_lower_of_weight epsilon a he.le heSmall
    W (Real.exp b) c C (Real.exp_pos _)
    (Real.exp_pos _) (Real.exp_pos _)
  · intro v hv
    exact angularGaugeWeight_bounds epsilon a l H he.le hH v
  · intro v hv
    let theta := Complex.arg (⟨v 0, v 1⟩ : ℂ)
    let t := epsilon*(primitiveIntegrand a l theta-a)
    let w := angularDirection (theta+Real.pi/2+t)
    refine ⟨w, angularDirection_unit _, ?_⟩
    have hvAngle : v = angularDirection theta := unitDirection_eq_angular_arg v hv
    have hshort := gaugeDefect_explicit_lower epsilon a l theta
      he heSmall ha ha1 hl hcoef
    dsimp at hshort
    let k := angularKernel epsilon a theta t
    have hk : 0 < k := by simpa only [k, t] using hshort.1
    have herr : |gaugeDefect epsilon a l theta t-l*epsilon^2| ≤
        (100+2*(2+1/Real.sqrt (2*l)))*epsilon^3 := by
      simpa only [t] using hshort.2
    have hlower : b ≤ gaugeDefect epsilon a l theta t := by
      have hh := (abs_le.mp herr).1
      dsimp [b]
      linarith
    have hlog : b+epsilon*gaugeProfile a l theta ≤
        Real.log k + epsilon*gaugeProfile a l (theta+Real.pi/2+t) := by
      unfold gaugeDefect at hlower
      dsimp [k] at *
      linarith
    have hexp := Real.exp_le_exp.mpr hlog
    rw [Real.exp_add, Real.exp_add, Real.exp_log hk] at hexp
    have hgain : directionGain (perturbationMatrix epsilon a) v w = k := by
      rw [hvAngle]
      exact exactAngularKernel epsilon a theta t
    have hweightV : W v = Real.exp (epsilon*gaugeProfile a l theta) := by
      rw [hvAngle]
      exact angularGaugeWeight_of_direction epsilon a l theta hcoef
    have hweightW : W w =
        Real.exp (epsilon*gaugeProfile a l (theta+Real.pi/2+t)) :=
      angularGaugeWeight_of_direction epsilon a l _ hcoef
    rw [hgain, hweightV, hweightW]
    rw [abs_of_pos hk]
    exact hexp

/-- Logarithmic lower bound for the same original growth function. -/
theorem parameterGrowth_log_lower (epsilon a l : ℝ)
    (he : 0 < epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a) :
    l*epsilon^2-
      (100+2*(2+1/Real.sqrt (2*l)))*epsilon^3 ≤
      Real.log (parameterGrowth epsilon a) := by
  have hg : 0 < parameterGrowth epsilon a :=
    lt_of_lt_of_le zero_lt_one (parameterGrowth_ge_one epsilon a)
  exact (Real.le_log_iff_exp_le hg).mpr
    (parameterGrowth_lower_exponential epsilon a l he heSmall ha ha1 hl hcoef)

end
end Specification
end BilinearSystems
