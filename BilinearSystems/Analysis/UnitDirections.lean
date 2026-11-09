import BilinearSystems.Analysis.GaugeDefectUniformLower
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Unit directions
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The complex number associated with a unit state has norm one. -/
theorem complex_norm_of_unitDirection (v : State) (hv : UnitDirection v) :
    ‖(⟨v 0, v 1⟩ : ℂ)‖ = 1 := by
  have hsum : v 0 * v 0 + v 1 * v 1 = 1 := hv
  rw [Complex.norm_def, Complex.normSq_apply]
  change Real.sqrt (v 0*v 0+v 1*v 1) = 1
  rw [hsum, Real.sqrt_one]

/-- A unit direction is exactly its complex argument parametrization. -/
theorem unitDirection_eq_angular_arg (v : State) (hv : UnitDirection v) :
    v = angularDirection (Complex.arg (⟨v 0, v 1⟩ : ℂ)) := by
  let z : ℂ := ⟨v 0, v 1⟩
  have hn : ‖z‖ = 1 := complex_norm_of_unitDirection v hv
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hn
  funext i
  fin_cases i
  · change v 0 = Real.cos (Complex.arg z)
    rw [Complex.cos_arg hz, hn]
    simp [z]
  · change v 1 = Real.sin (Complex.arg z)
    rw [Complex.sin_arg z, hn]
    simp [z]

/-- Surjectivity of the standard angular parametrization on the actual
Euclidean unit-direction predicate, without changing that predicate. -/
theorem unitDirection_has_angle (v : State) (hv : UnitDirection v) :
    ∃ theta : ℝ, v = angularDirection theta :=
  ⟨Complex.arg (⟨v 0, v 1⟩ : ℂ), unitDirection_eq_angular_arg v hv⟩

end
end Specification
end BilinearSystems
