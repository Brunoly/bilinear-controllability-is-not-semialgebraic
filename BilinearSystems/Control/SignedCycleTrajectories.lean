import BilinearSystems.Growth.CycleGrowth
import BilinearSystems.Control.ProjectionStep

/-!
# Signed gains and reverse paths
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def directionGain (K : Matrix2) (v w : State) : ℝ :=
  euclideanDot w (K.mulVec v)

def indexedPathGain (K : Matrix2) {n : ℕ} (e : Fin (n+1) → State) : ℝ :=
  ∏ i : Fin n, directionGain K (e i.castSucc) (e i.succ)

/-- The relation runs from the later state to the earlier state. -/
def ReverseStep (K : Matrix2) (y x : State) : Prop :=
  ∃ u : ℝ, K.mulVec y = x + u • quarterTurn x

inductive ReversePath (K : Matrix2) : ℕ → State → State → Prop
  | nil (x : State) : ReversePath K 0 x x
  | cons {n : ℕ} {x y z : State} :
      ReverseStep K x y → ReversePath K n y z → ReversePath K (n+1) x z

theorem unitDirection_ne_zero {w : State} (hw : UnitDirection w) : w ≠ 0 := by
  intro h
  simp [UnitDirection, h, euclideanDot] at hw

private theorem dot_smul_both (r t : ℝ) (x y : State) :
    euclideanDot (r • x) (t • y) = r*t*euclideanDot x y := by
  simp [euclideanDot, Pi.smul_apply, smul_eq_mul]
  ring

theorem reverseStep_scaled_iff (K : Matrix2) (v w : State)
    (hw : UnitDirection w) (r t : ℝ) (ht : t ≠ 0) :
    ReverseStep K (r • v) (t • w) ↔ t = r * directionGain K v w := by
  have hx : t • w ≠ 0 := smul_ne_zero ht (unitDirection_ne_zero hw)
  change (∃ u : ℝ, K.mulVec (r • v) = t • w + u • quarterTurn (t • w)) ↔ _
  rw [exists_control_iff_euclidean_constraint _ _ hx]
  rw [Matrix.mulVec_smul, dot_smul_both, dot_smul_both]
  change euclideanDot w w = 1 at hw
  rw [hw, mul_one]
  unfold directionGain
  constructor
  · intro h
    exact (mul_left_cancel₀ ht (by simpa only [mul_assoc] using h)).symm
  · intro h
    calc
      t*r*euclideanDot w (K.mulVec v) = t*(r*euclideanDot w (K.mulVec v)) := by ring
      _ = t*t := congrArg (t * ·) h.symm

def pathGain (K : Matrix2) (v : State) : List State → ℝ
  | [] => 1
  | w :: ws => directionGain K v w * pathGain K w ws

def pathLast (v : State) : List State → State
  | [] => v
  | w :: ws => pathLast w ws

/-- A nonzero total gain ensures that every scaled state stays nonzero,
provided the initial scalar is nonzero. The length is tracked exactly. -/
theorem reversePath_of_nonzero_gain (K : Matrix2) (v : State) (ws : List State)
    (hunit : ∀ w ∈ ws, UnitDirection w) (r : ℝ)
    (hgain : r * pathGain K v ws ≠ 0) :
    ReversePath K ws.length (r • v) ((r * pathGain K v ws) • pathLast v ws) := by
  induction ws generalizing v r with
  | nil => simpa [pathGain, pathLast] using ReversePath.nil (K := K) (r • v)
  | cons w ws ih =>
    have hprod : (r * directionGain K v w) * pathGain K w ws ≠ 0 := by
      simpa only [pathGain, mul_assoc] using hgain
    have ht : r * directionGain K v w ≠ 0 := left_ne_zero_of_mul hprod
    have hstep := (reverseStep_scaled_iff K v w (hunit w (by simp)) r _ ht).mpr rfl
    have htail := ih w (fun x hx => hunit x (List.mem_cons_of_mem w hx)) _ hprod
    simpa only [List.length_cons, pathGain, pathLast, mul_assoc] using
      ReversePath.cons hstep htail

end
end Specification
end BilinearSystems
