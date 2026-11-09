import BilinearSystems.Analysis.AngularKernel
import BilinearSystems.Family.GrowthBounds

/-!
# Asymptotic statements
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Set Filter
open scoped Topology

/-- The uniform-in-angle estimate for each fixed a and its positive
integral coefficient. Constants may depend on a. -/
def PerturbationCubicRemainder : Prop :=
  ∀ a l : ℝ, criticalParameter < a → a < 1 →
    0 < l → coefficientIntegral l = a →
    ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta →
        |Real.log (parameterGrowth epsilon a)-l*epsilon^2| ≤ C*epsilon^3

/-- The exact positive branch and its logarithmic right-onset. -/
def CoefficientLogarithmicOnset : Prop :=
  ∃ l : ℝ → ℝ,
    (∀ a : ℝ, criticalParameter < a → 0 < l a ∧ coefficientIntegral (l a) = a) ∧
    Tendsto (fun delta : ℝ =>
      l (criticalParameter+delta) / (Real.pi*delta/|Real.log delta|))
      (𝓝[>] (0 : ℝ)) (𝓝 1)

end
end Specification
end BilinearSystems
