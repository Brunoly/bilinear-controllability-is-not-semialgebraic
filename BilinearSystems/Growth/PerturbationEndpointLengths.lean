import BilinearSystems.Growth.FinitePathCycleClosure

/-!
# Perturbation endpoint lengths
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem dot_self_nonneg (v : State) : 0 ≤ euclideanDot v v := by
  dsimp [euclideanDot]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

private theorem dot_cauchy_square (u v : State) :
    (euclideanDot u v)^2 ≤ euclideanDot u u * euclideanDot v v := by
  have h := sq_nonneg (u 0*v 1-u 1*v 0)
  dsimp [euclideanDot]
  nlinarith [h]

theorem dot_le_planarLength_of_unit (u v : State) (hu : UnitDirection u) :
    euclideanDot u v ≤ planarLength v := by
  have hcs := dot_cauchy_square u v
  change euclideanDot u u = 1 at hu
  rw [hu, one_mul] at hcs
  have hsq : (planarLength v)^2 = euclideanDot v v := by
    exact Real.sq_sqrt (dot_self_nonneg v)
  have hlen := planarLength_nonneg v
  nlinarith

private def positiveQuarterTurn (v : State) : State :=
  fun i => if i = 0 then -v 1 else v 0

private def negativeQuarterTurn (v : State) : State :=
  fun i => if i = 0 then v 1 else -v 0

private theorem positiveQuarterTurn_unit (v : State) (hv : UnitDirection v) :
    UnitDirection (positiveQuarterTurn v) := by
  simpa [UnitDirection, euclideanDot, positiveQuarterTurn, add_comm] using hv

private theorem negativeQuarterTurn_unit (v : State) (hv : UnitDirection v) :
    UnitDirection (negativeQuarterTurn v) := by
  simpa [UnitDirection, euclideanDot, negativeQuarterTurn, add_comm] using hv

private theorem unit_coordinate_product_bounds (v : State) (hv : UnitDirection v) :
    -1 ≤ 2*v 0*v 1 ∧ 2*v 0*v 1 ≤ 1 := by
  change v 0*v 0+v 1*v 1=1 at hv
  constructor <;> nlinarith [sq_nonneg (v 0+v 1), sq_nonneg (v 0-v 1)]

private theorem perturbation_forward_dot (epsilon a : ℝ) (v : State)
    (hv : UnitDirection v) :
    euclideanDot (positiveQuarterTurn v)
      ((perturbationMatrix epsilon a).mulVec v) = 1-2*epsilon*v 0*v 1 := by
  change v 0*v 0+v 1*v 1=1 at hv
  simp [positiveQuarterTurn, perturbationMatrix, euclideanDot,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith

private theorem perturbation_transpose_dot (epsilon a : ℝ) (v : State)
    (hv : UnitDirection v) :
    euclideanDot (negativeQuarterTurn v)
      ((perturbationMatrix epsilon a).transpose.mulVec v) =
      1+2*epsilon*v 0*v 1 := by
  change v 0*v 0+v 1*v 1=1 at hv
  simp [negativeQuarterTurn, perturbationMatrix, euclideanDot,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
  nlinarith

/-- Uniform lower bound on the image length, independent of a. -/
theorem perturbation_forward_length_lower (epsilon a : ℝ)
    (he : 0 ≤ epsilon) (v : State) (hv : UnitDirection v) :
    1-epsilon ≤ planarLength ((perturbationMatrix epsilon a).mulVec v) := by
  have hb := (unit_coordinate_product_bounds v hv).2
  have hmul := mul_le_mul_of_nonneg_left hb he
  have hdot := perturbation_forward_dot epsilon a v hv
  have hcs := dot_le_planarLength_of_unit
    (positiveQuarterTurn v) ((perturbationMatrix epsilon a).mulVec v)
    (positiveQuarterTurn_unit v hv)
  rw [hdot] at hcs
  nlinarith

/-- The same bound for the transpose, needed at the initial endpoint. -/
theorem perturbation_transpose_length_lower (epsilon a : ℝ)
    (he : 0 ≤ epsilon) (v : State) (hv : UnitDirection v) :
    1-epsilon ≤ planarLength ((perturbationMatrix epsilon a).transpose.mulVec v) := by
  have hb := (unit_coordinate_product_bounds v hv).1
  have hmul := mul_le_mul_of_nonneg_left hb he
  have hdot := perturbation_transpose_dot epsilon a v hv
  have hcs := dot_le_planarLength_of_unit
    (negativeQuarterTurn v) ((perturbationMatrix epsilon a).transpose.mulVec v)
    (negativeQuarterTurn_unit v hv)
  rw [hdot] at hcs
  nlinarith

end
end Specification
end BilinearSystems
