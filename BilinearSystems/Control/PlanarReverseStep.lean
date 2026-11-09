import BilinearSystems.Control.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The planar reverse-step identity
-/
namespace BilinearSystems
noncomputable section

def euclideanDot (x y : State) : ℝ := x 0 * y 0 + x 1 * y 1

def quarterTurn (x : State) : State := fun i => if i = 0 then -x 1 else x 0

theorem euclideanDot_self_pos (x : State) (hx : x ≠ 0) : 0 < euclideanDot x x := by
  have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i <;> simp [h.1,h.2]
  rcases hn with h | h
  · have hp := sq_pos_of_ne_zero h
    dsimp [euclideanDot]
    nlinarith [sq_nonneg (x 1)]
  · have hp := sq_pos_of_ne_zero h
    dsimp [euclideanDot]
    nlinarith [sq_nonneg (x 0)]

theorem planar_orthogonal_decomposition (x w : State) (hx : x ≠ 0) :
    w = (euclideanDot x w / euclideanDot x x) • x +
      (euclideanDot (quarterTurn x) w / euclideanDot x x) • quarterTurn x := by
  have hd := (euclideanDot_self_pos x hx).ne'
  have hn : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by simpa [euclideanDot,pow_two] using hd
  have hn' : x 1 ^ 2 + x 0 ^ 2 ≠ 0 := by simpa only [add_comm] using hn
  funext i
  fin_cases i <;> simp [quarterTurn, euclideanDot] at *
  all_goals ring_nf
  all_goals field_simp [hn,hn']
  all_goals ring

/-- Existence of a real control is equivalent to the Euclidean constraint. -/
theorem exists_control_iff_euclidean_constraint (x w : State) (hx : x ≠ 0) :
    (∃ u : ℝ, w = x + u • quarterTurn x) ↔ euclideanDot x w = euclideanDot x x := by
  constructor
  · rintro ⟨u,rfl⟩
    simp [euclideanDot,quarterTurn]
    <;> ring
  · intro h
    refine ⟨euclideanDot (quarterTurn x) w / euclideanDot x x, ?_⟩
    have hd := (euclideanDot_self_pos x hx).ne'
    simpa only [h, div_self hd, one_smul] using planar_orthogonal_decomposition x w hx

/-- Explicit control formula for a reverse step. -/
theorem canonical_control_formula (K : Matrix2) (x y : State) (hx : x ≠ 0)
    (h : euclideanDot x (K.mulVec y) = euclideanDot x x) :
    K.mulVec y = x +
      (euclideanDot (quarterTurn x) (K.mulVec y) / euclideanDot x x) • quarterTurn x := by
  have hd := (euclideanDot_self_pos x hx).ne'
  simpa only [h, div_self hd, one_smul] using planar_orthogonal_decomposition x (K.mulVec y) hx

end
end BilinearSystems
