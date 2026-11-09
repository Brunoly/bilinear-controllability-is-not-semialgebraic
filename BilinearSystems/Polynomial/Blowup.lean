import BilinearSystems.Polynomial.Pullback
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# Injectivity of the polynomial blowup
-/
namespace BilinearSystems
namespace Specification
open MvPolynomial Set Filter
open scoped Topology
noncomputable section

def boundaryBlowup (P : ParameterPolynomial) : ParameterPolynomial :=
  eval₂Hom C (fun i : Fin 3 => if i = 2 then 1 + X 0 ^ 2 * X 2 else X i) P

theorem eval_boundaryBlowup (P : ParameterPolynomial) (e a z : ℝ) :
    eval (parameterTriple e a z) (boundaryBlowup P) =
      eval (parameterTriple e a (1+e^2*z)) P := by
  unfold boundaryBlowup
  rw [← RingHom.comp_apply, comp_eval₂Hom]
  have hc : (eval (parameterTriple e a z)).comp C = RingHom.id ℝ := by
    ext r
    simp
  rw [hc]
  change eval (fun i => eval (parameterTriple e a z)
    (if i = (2 : Fin 3) then 1 + X 0 ^ 2 * X 2 else X i)) P = _
  congr 2
  funext i
  fin_cases i <;> norm_num [parameterTriple]

theorem boundaryBlowup_ne_zero (P : ParameterPolynomial) (hP : P ≠ 0) :
    boundaryBlowup P ≠ 0 := by
  intro hzero
  apply hP
  apply MvPolynomial.funext_set (fun _ : Fin 3 => Ioi (0 : ℝ))
    (fun _ => Ioi_infinite (0 : ℝ))
  intro x hx
  rw [map_zero]
  have he : 0 < x 0 := hx 0 (by simp)
  let z := (x 2 - 1) / (x 0)^2
  have hlast : 1 + (x 0)^2*z = x 2 := by
    unfold z
    field_simp [he.ne']
    ring
  have heval := eval_boundaryBlowup P (x 0) (x 1) z
  rw [hzero, map_zero, hlast] at heval
  have htuple : parameterTriple (x 0) (x 1) (x 2) = x := by
    funext i
    fin_cases i <;> rfl
  rw [htuple] at heval
  simpa using heval.symm

theorem parameterTriple_eq_cons (e a z : ℝ) :
    parameterTriple e a z = Fin.cons e (Fin.cons a (fun _ : Fin 1 => z)) := by
  funext i
  fin_cases i <;> rfl

end
end Specification
end BilinearSystems
