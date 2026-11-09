import BilinearSystems.Control.SignedCycleTrajectories
import BilinearSystems.Control.TrajectorySemantics

/-!
# From reverse paths to real controls
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def quarterTurnMatrix : Matrix2 :=
  fun i j => if i = j then 0 else if i = 0 then -1 else 1

theorem quarterTurnMatrix_mulVec (x : State) :
    quarterTurnMatrix.mulVec x = quarterTurn x := by
  funext i
  fin_cases i <;> simp [quarterTurnMatrix, quarterTurn, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]

theorem canonical_step_mulVec (K A : Matrix2) (hKA : K * A = 1)
    (u : ℝ) (x : State) :
    K.mulVec (step A (A * quarterTurnMatrix) u x) = x + u • quarterTurn x := by
  simp only [step, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec,
    ← Matrix.mul_assoc, one_mul, quarterTurnMatrix_mulVec]

theorem reverseStep_iff_forwardControl (K A : Matrix2)
    (hKA : K * A = 1) (hAK : A * K = 1) (x y : State) :
    ReverseStep K y x ↔ ∃ u : ℝ, step A (A * quarterTurnMatrix) u x = y := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have h := congrArg A.mulVec ((canonical_step_mulVec K A hKA u x).trans hu.symm)
    simpa only [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec] using h
  · rintro ⟨u, rfl⟩
    exact ⟨u, canonical_step_mulVec K A hKA u x⟩

theorem reversePath_to_controls (K A : Matrix2)
    (hKA : K * A = 1) (hAK : A * K = 1)
    {n : ℕ} {y x : State} (h : ReversePath K n y x) :
    ∃ controls : List ℝ, controls.length = n ∧
      trajectoryEndpoint A (A * quarterTurnMatrix) x controls = y := by
  induction h with
  | nil x => exact ⟨[], rfl, rfl⟩
  | @cons n x y z hs _ ih =>
    obtain ⟨u, hu⟩ := (reverseStep_iff_forwardControl K A hKA hAK y x).mp hs
    obtain ⟨controls, hlen, hend⟩ := ih
    refine ⟨controls ++ [u], by simp [hlen], ?_⟩
    rw [trajectoryEndpoint_append, hend]
    exact hu

theorem ReversePath.snoc {K : Matrix2} {n : ℕ} {x y z : State}
    (h : ReversePath K n x y) (hs : ReverseStep K y z) :
    ReversePath K (n+1) x z := by
  induction h with
  | nil x => exact ReversePath.cons hs (ReversePath.nil z)
  | cons hstep _ ih => exact ReversePath.cons hstep (ih hs)

theorem controls_to_reversePath (K A : Matrix2) (hKA : K * A = 1)
    (controls : List ℝ) (x : State) :
    ReversePath K controls.length
      (trajectoryEndpoint A (A * quarterTurnMatrix) x controls) x := by
  induction controls generalizing x with
  | nil => exact ReversePath.nil x
  | cons u us ih =>
    have hs : ReverseStep K (step A (A * quarterTurnMatrix) u x) x :=
      ⟨u, canonical_step_mulVec K A hKA u x⟩
    exact (ih _).snoc hs

/-- Every nonempty direction list of nonzero gain gives forward reachability
from the scaled last direction to the scaled first direction. -/
theorem reachable_of_nonzero_pathGain (K A : Matrix2)
    (hKA : K * A = 1) (hAK : A * K = 1)
    (v : State) (ws : List State) (hws : ws ≠ [])
    (hunit : ∀ w ∈ ws, UnitDirection w) (r : ℝ)
    (hgain : r * pathGain K v ws ≠ 0) :
    Reachable A (A * quarterTurnMatrix)
      ((r * pathGain K v ws) • pathLast v ws) (r • v) := by
  obtain ⟨controls, hlen, hend⟩ := reversePath_to_controls K A hKA hAK
    (reversePath_of_nonzero_gain K v ws hunit r hgain)
  refine ⟨controls, ?_, hend⟩
  intro hz
  apply hws
  exact List.length_eq_zero_iff.mp (by simpa [hz] using hlen.symm)

end
end Specification
end BilinearSystems
