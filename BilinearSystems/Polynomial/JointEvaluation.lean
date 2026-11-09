import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuity of polynomial joint evaluation
-/
namespace BilinearSystems
open Filter Set
open scoped Topology
noncomputable section

 theorem continuous_polynomial_joint_evaluation {σ : Type*}
    (p : Polynomial (MvPolynomial σ ℝ)) :
    Continuous (fun x : ℝ × (σ → ℝ) => p.eval₂ (MvPolynomial.eval x.2) x.1) := by
  simp only [Polynomial.eval₂_eq_sum]
  exact continuous_finsetSum _ fun j _ =>
    ((MvPolynomial.continuous_eval (p := p.coeff j)).comp continuous_snd).mul
      (continuous_fst.pow j)

end
end BilinearSystems
