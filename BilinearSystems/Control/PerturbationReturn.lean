import BilinearSystems.AuxiliaryDefinitions
import BilinearSystems.Control.SignedReturns

/-!
# Negative coordinate returns for the perturbation
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private def firstDirection : State := fun i => if i = 0 then 1 else 0
private def secondDirection : State := fun i => if i = 0 then 0 else 1

private theorem firstDirection_unit : UnitDirection firstDirection := by
  norm_num [UnitDirection, euclideanDot, firstDirection]

private theorem secondDirection_unit : UnitDirection secondDirection := by
  norm_num [UnitDirection, euclideanDot, secondDirection]

/-- The two off-diagonal entries give the exact signed gain -k².
This also applies to the canonical matrix scaled by the inverse threshold. -/
theorem scaled_perturbation_negative_return (epsilon a k : ℝ) (hk : k ≠ 0) :
    ∃ v : State, UnitDirection v ∧
      ReversePath (k • perturbationMatrix epsilon a) 2 v ((-(k^2)) • v) := by
  let K := k • perturbationMatrix epsilon a
  have h₁ : directionGain K firstDirection secondDirection = k := by
    norm_num [K, directionGain, euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      perturbationMatrix, firstDirection, secondDirection, Matrix.smul_apply, smul_eq_mul]
  have h₂ : directionGain K secondDirection firstDirection = -k := by
    norm_num [K, directionGain, euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      perturbationMatrix, firstDirection, secondDirection, Matrix.smul_apply, smul_eq_mul]
  have hu : ∀ e ∈ [secondDirection, firstDirection], UnitDirection e := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact secondDirection_unit
    · exact firstDirection_unit
  have hg : pathGain K firstDirection [secondDirection, firstDirection] = -(k^2) := by
    simp only [pathGain, h₁, h₂, mul_one]
    ring
  have hp := reversePath_of_nonzero_gain K firstDirection [secondDirection, firstDirection] hu 1
    (by simpa only [one_mul, hg, neg_ne_zero] using pow_ne_zero 2 hk)
  refine ⟨firstDirection, firstDirection_unit, ?_⟩
  simp only [one_smul, one_mul, hg, pathLast] at hp
  exact hp

theorem scaled_perturbation_negative_return_at_unit_base (epsilon a k : ℝ) (hk : k ≠ 0)
    (A : Matrix2) (hKA : (k • perturbationMatrix epsilon a)*A = 1)
    (hAK : A*(k • perturbationMatrix epsilon a) = 1)
    (v : State) (hv : UnitDirection v) :
    ∃ (n : ℕ) (c : ℝ), 0 < n ∧ c < 0 ∧
      ReversePath (k • perturbationMatrix epsilon a) n v (c • v) := by
  obtain ⟨w, hw, hp⟩ := scaled_perturbation_negative_return epsilon a k hk
  exact negative_return_at_unit_base _ A hKA hAK hw (neg_neg_of_pos (sq_pos_of_ne_zero hk)) hp v hv

end
end Specification
end BilinearSystems
