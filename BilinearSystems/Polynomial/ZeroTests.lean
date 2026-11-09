import BilinearSystems.Polynomial.SignFormulas
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Eliminating zero-polynomial tests
-/
namespace BilinearSystems
open Filter Set MvPolynomial
open scoped Topology BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Remove zero-polynomial atoms without altering any truth value. -/
def SignFormula.removeZeroPolynomials {ι σ : Type*}
    (p : ι → MvPolynomial σ ℝ) : SignFormula ι → SignFormula {i // p i ≠ 0}
  | .positive i => if h : p i = 0 then .falsity else .positive ⟨i,h⟩
  | .zero i => if h : p i = 0 then .truth else .zero ⟨i,h⟩
  | .negative i => if h : p i = 0 then .falsity else .negative ⟨i,h⟩
  | .truth => .truth
  | .falsity => .falsity
  | .conj a b => .conj (a.removeZeroPolynomials p) (b.removeZeroPolynomials p)
  | .disj a b => .disj (a.removeZeroPolynomials p) (b.removeZeroPolynomials p)
  | .neg a => .neg (a.removeZeroPolynomials p)

theorem SignFormula.removeZeroPolynomials_eval {ι σ : Type*}
    (p : ι → MvPolynomial σ ℝ) (φ : SignFormula ι) (x : σ → ℝ) :
    (φ.removeZeroPolynomials p).eval (fun i y => MvPolynomial.eval y (p i.val)) x ↔
      φ.eval (fun i y => MvPolynomial.eval y (p i)) x := by
  classical
  induction φ with
  | positive i => by_cases h : p i = 0 <;> simp [removeZeroPolynomials, eval, h]
  | zero i => by_cases h : p i = 0 <;> simp [removeZeroPolynomials, eval, h]
  | negative i => by_cases h : p i = 0 <;> simp [removeZeroPolynomials, eval, h]
  | truth => rfl
  | falsity => rfl
  | conj a b ha hb => exact and_congr ha hb
  | disj a b ha hb => exact or_congr ha hb
  | neg a ha => exact not_congr ha

end
end BilinearSystems
