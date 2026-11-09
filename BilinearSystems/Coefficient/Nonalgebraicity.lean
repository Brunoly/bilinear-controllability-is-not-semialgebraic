import BilinearSystems.Coefficient.GraphNoVanishing

/-!
# Nonalgebraicity
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

private theorem criticalParameter_lt_one : criticalParameter < 1 := by
  have hne : (1 : ℝ) ≠ Real.pi/2 := by
    intro heq
    have hcos := Real.cos_one_pos
    rw [heq, Real.cos_pi_div_two] at hcos
    exact (lt_irrefl (0:ℝ)) hcos
  have hhalf : (1:ℝ) < Real.pi/2 :=
    lt_of_le_of_ne Real.one_le_pi_div_two hne
  have hpi : (2:ℝ) < Real.pi := by linarith
  change 2/Real.pi < 1
  exact (div_lt_iff₀ Real.pi_pos).mpr (by linarith)

/-- Nonalgebraicity of the positive coefficient graph, for arbitrary real polynomial coefficients. -/
theorem coefficientGraphNonalgebraic : CoefficientGraphNonalgebraic := by
  intro Q hQ hvanish
  let p := translatedCoefficientPolynomial Q
  have hp : p ≠ 0 := translatedCoefficientPolynomial_ne_zero Q hQ
  apply iterated_polynomial_not_eventually_zero p hp
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      d < 1-criticalParameter :=
    nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr criticalParameter_lt_one))
  filter_upwards [self_mem_nhdsWithin, hsmall] with d hd hs
  have hdpos : 0 < d := hd
  have ha : criticalParameter < criticalParameter+d := by linarith
  have ha1 : criticalParameter+d < 1 := by linarith
  have hbranch := positiveCoefficientBranch_spec (criticalParameter+d) ha
  have hzero := hvanish (criticalParameter+d) (branchNearOnset d)
    ha ha1 hbranch.1 hbranch.2
  exact (translatedCoefficientPolynomial_eval Q d (branchNearOnset d)).trans hzero

end
end Specification
end BilinearSystems
