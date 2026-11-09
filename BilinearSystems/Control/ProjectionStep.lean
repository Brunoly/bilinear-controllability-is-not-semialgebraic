import BilinearSystems.Control.PlanarReverseStep
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Euclidean line projections
-/
namespace BilinearSystems
noncomputable section

def euclideanLineProjection (x w : State) : State :=
  (euclideanDot x w / euclideanDot x x) • x

theorem lineProjection_eq_self_iff (x w : State) (hx : x ≠ 0) :
    euclideanLineProjection x w = x ↔ euclideanDot x w = euclideanDot x x := by
  have hd := (euclideanDot_self_pos x hx).ne'
  constructor
  · intro h
    have hscalar : euclideanDot x w / euclideanDot x x = 1 :=
      smul_left_injective ℝ hx (h.trans (one_smul ℝ x).symm)
    exact (div_eq_one_iff_eq hd).mp hscalar
  · intro h
    simp only [euclideanLineProjection,h,div_self hd,one_smul]

 theorem canonical_step_iff_reverse_projection (K : Matrix2) (x y : State) (hx : x ≠ 0) :
    (∃ u : ℝ, K.mulVec y = x + u • quarterTurn x) ↔
      euclideanLineProjection x (K.mulVec y) = x :=
  (exists_control_iff_euclidean_constraint x (K.mulVec y) hx).trans
    (lineProjection_eq_self_iff x (K.mulVec y) hx).symm

end
end BilinearSystems
