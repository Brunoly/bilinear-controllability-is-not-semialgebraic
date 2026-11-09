import BilinearSystems.Control.ControllabilitySufficiency
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse-pencil cycle criterion
-/
namespace BilinearSystems.Specification
noncomputable section

/-- The coordinate cycle has exactly the product of the two off-diagonal entries. -/
theorem coordinate_negative_reverse_return (K : Matrix2)
    (hoff : K 0 1 * K 1 0 < 0) :
    ∃ v : State, UnitDirection v ∧
      ReversePath K 2 v ((K 0 1 * K 1 0) • v) := by
  let v : State := fun i => if i = 0 then 1 else 0
  let w : State := fun i => if i = 0 then 0 else 1
  have hv : UnitDirection v := by norm_num [UnitDirection, euclideanDot, v]
  have hw : UnitDirection w := by norm_num [UnitDirection, euclideanDot, w]
  have h₁ : directionGain K v w = K 1 0 := by
    norm_num [directionGain, euclideanDot, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, v, w]
  have h₂ : directionGain K w v = K 0 1 := by
    norm_num [directionGain, euclideanDot, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, v, w]
  have hu : ∀ e ∈ [w, v], UnitDirection e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hw
    · exact hv
  have hg : pathGain K v [w, v] = K 0 1 * K 1 0 := by
    simp only [pathGain, h₁, h₂, mul_one]
    ring
  have hp := reversePath_of_nonzero_gain K v [w, v] hu 1
    (by simpa only [one_mul, hg] using hoff.ne)
  refine ⟨v, hv, ?_⟩
  simpa only [one_smul, one_mul, hg, pathLast, List.length_cons, List.length_nil] using hp

/-- Exact control criterion with an explicitly specified two-sided inverse. -/
theorem inverse_pencil_controllable_iff_cycleGrowth (K A : Matrix2)
    (hKA : K*A = 1) (hAK : A*K = 1)
    (hoff : K 0 1 * K 1 0 < 0) :
    GloballyControllable A (A * quarterTurnMatrix) ↔ 1 < cycleGrowth K := by
  constructor
  · exact cycleGrowth_gt_one_of_controllable K A hKA
  · intro hG
    apply controllable_of_cycleGrowth_of_negative_returns K A hKA hAK hG
    intro v hv
    obtain ⟨w, hw, hp⟩ := coordinate_negative_reverse_return K hoff
    obtain ⟨n, c, _, hc, hpath⟩ :=
      negative_return_at_unit_base K A hKA hAK hw hoff hp v hv
    exact ⟨n, c, hc, hpath⟩

/-- Standard Mathlib matrix inverse formulation. This implies the manuscript's
Lemma 1, whose additional K₁₁ ≠ 0 assumption is unnecessary for this proof. -/
theorem nonsingular_inverse_pencil_controllable_iff (K : Matrix2)
    (hdet : K.det ≠ 0) (hoff : K 0 1 * K 1 0 < 0) :
    GloballyControllable K⁻¹ (K⁻¹ * quarterTurnMatrix) ↔ 1 < cycleGrowth K := by
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hdet
  exact inverse_pencil_controllable_iff_cycleGrowth K K⁻¹
    (Matrix.mul_nonsing_inv K hunit) (Matrix.nonsing_inv_mul K hunit) hoff

end
end BilinearSystems.Specification
