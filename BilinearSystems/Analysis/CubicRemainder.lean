import BilinearSystems.Analysis.PerturbationGrowthLower
import BilinearSystems.Analysis.PerturbationGrowthUpper
import BilinearSystems.Analysis.AsymptoticStatements

/-!
# Cubic remainder
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Pointwise cubic remainder for the logarithm of cycle growth. -/
theorem perturbationCubicRemainder : PerturbationCubicRemainder := by
  intro a l ha ha1 hl hcoef
  have ha0 : 0 ≤ a := by
    have hcrit : 0 < criticalParameter := by
      unfold criticalParameter
      positivity
    linarith
  let L : ℝ := 2+1/Real.sqrt (2*l)
  have hL : 0 < L := by dsimp [L]; positivity
  let Cplus : ℝ := 2+(8+L)*(a+1)^2
  let Cminus : ℝ := 100+2*L
  let C : ℝ := max Cplus Cminus
  let delta : ℝ := min (1/100) (1/(2*L))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (by positivity)
  have hC : 0 ≤ C := by
    dsimp [C, Cminus, L]
    exact le_max_of_le_right (by positivity)
  refine ⟨C,delta,hC,hdelta,?_⟩
  intro epsilon he hedelta
  have heSmall : epsilon ≤ 1/100 :=
    le_trans hedelta.le (min_le_left _ _)
  have hehalf : epsilon ≤ 1/2 := heSmall.trans (by norm_num)
  have hecurv : epsilon ≤ 1/(2*(2+1/Real.sqrt (2*l))) := by
    have hh : epsilon ≤ 1/(2*L) :=
      le_trans hedelta.le (min_le_right _ _)
    exact hh
  have hupper := parameterGrowth_log_upper epsilon a l
    he.le hehalf ha0 hl hcoef hecurv
  have hlower := parameterGrowth_log_lower epsilon a l
    he heSmall ha0 ha1.le hl hcoef
  have hplus : Cplus ≤ C := le_max_left _ _
  have hminus : Cminus ≤ C := le_max_right _ _
  have he3 : 0 ≤ epsilon^3 := pow_nonneg he.le _
  have hplusScaled := mul_le_mul_of_nonneg_right hplus he3
  have hminusScaled := mul_le_mul_of_nonneg_right hminus he3
  apply abs_le.mpr
  dsimp [Cplus, Cminus, L] at hplusScaled hminusScaled hupper hlower
  constructor <;> linarith

end
end Specification
end BilinearSystems
