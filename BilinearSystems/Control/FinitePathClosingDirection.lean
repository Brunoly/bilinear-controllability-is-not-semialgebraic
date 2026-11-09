import BilinearSystems.Control.TwoLinearForms
import BilinearSystems.Control.ExpandingReturn

/-!
# Closing paths through an intermediate direction
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem transpose_dot (K : Matrix2) (v w : State) :
    euclideanDot v (K.mulVec w) =
      euclideanDot (K.transpose.mulVec v) w := by
  simp [euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.transpose_apply]
  ring

/-- Two extra edges can close any finite unit-direction path while retaining
at least half the product of its endpoint matrix lengths. -/
theorem finite_path_closing_direction (K : Matrix2) {n : ℕ}
    (e : Fin (n+1) → State) :
    ∃ f : State, UnitDirection f ∧
      |indexedPathGain K e| *
        (planarLength (K.transpose.mulVec (e 0)) *
          planarLength (K.mulVec (e (Fin.last n))) / 2) ≤
      |indexedPathGain K e *
        directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0)| := by
  obtain ⟨f,hf,hbound⟩ :=
    two_linear_forms (K.transpose.mulVec (e 0))
      (K.mulVec (e (Fin.last n)))
  refine ⟨f,hf,?_⟩
  have hleft : euclideanDot (K.transpose.mulVec (e 0)) f =
      directionGain K f (e 0) := by
    rw [← transpose_dot]
    rfl
  have hright : euclideanDot f (K.mulVec (e (Fin.last n))) =
      directionGain K (e (Fin.last n)) f := rfl
  rw [hleft, hright] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound (abs_nonneg (indexedPathGain K e))
  calc
    |indexedPathGain K e| *
        (planarLength (K.transpose.mulVec (e 0)) *
          planarLength (K.mulVec (e (Fin.last n))) / 2) ≤
        |indexedPathGain K e| *
          |directionGain K f (e 0) * directionGain K (e (Fin.last n)) f| := hscaled
    _ = |indexedPathGain K e *
        directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0)| := by
      simp only [abs_mul]
      ring

end
end Specification
end BilinearSystems
