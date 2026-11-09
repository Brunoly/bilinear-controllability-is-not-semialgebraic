import BilinearSystems.Control.PlanarReverseStep
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Euclidean cycle growth and perturbation coefficients
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology BigOperators

/-- Euclidean unit vectors, explicitly avoiding the coordinate sup norm. -/
def UnitDirection (x : State) : Prop := euclideanDot x x = 1

/-- n edges, with n positive; endpoint equals initial oriented vector. -/
def CycleGains (K : Matrix2) : Set ℝ :=
  {r | ∃ (n : ℕ) (hn : 0 < n) (e : Fin (n+1) → State),
    (∀ i, UnitDirection (e i)) ∧ e (Fin.last n) = e 0 ∧
    r = Real.rpow (abs (∏ i : Fin n,
      euclideanDot (e i.succ) (K.mulVec (e i.castSucc)))) (1 / (n : ℝ))}

/-- Real supremum; nonemptiness and boundedness must be proved before
using its order properties. Zero edge gains are allowed. -/
def cycleGrowth (K : Matrix2) : ℝ := sSup (CycleGains K)

def CycleGrowthWellDefined : Prop :=
  ∀ K : Matrix2, (CycleGains K).Nonempty ∧ BddAbove (CycleGains K)

theorem cycleGains_nonempty (K : Matrix2) : (CycleGains K).Nonempty := by
  let e : State := fun i => if i = 0 then 1 else 0
  refine ⟨_, 1, Nat.zero_lt_succ 0, fun _ => e, ?_, rfl, rfl⟩
  intro i
  norm_num [UnitDirection, euclideanDot, e]

def perturbationMatrix (epsilon a : ℝ) : Matrix2 :=
  fun i j => if i = j then epsilon * (if i = 0 then a+1 else a-1)
    else if i = 0 then -1 else 1

def criticalParameter : ℝ := 2 / Real.pi

/-- The manuscript's coefficient function; positive lambda is enforced
in the targets rather than assumed by a choice of inverse. -/
def coefficientIntegral (l : ℝ) : ℝ :=
  (2 / Real.pi) * ∫ t in (0 : ℝ)..(Real.pi / 2),
    Real.sqrt (2*l + Real.sin t ^ 2)

def CoefficientExistenceUniqueness : Prop :=
  ∀ a : ℝ, criticalParameter < a →
    ∃! l : ℝ, 0 < l ∧ coefficientIntegral l = a

/-- Pointwise growth asymptotic at a specified positive integral coefficient. -/
def GrowthAsymptotic : Prop :=
  ∀ a l : ℝ, criticalParameter < a → a < 1 →
    0 < l → coefficientIntegral l = a →
    Tendsto (fun epsilon : ℝ =>
      (cycleGrowth (perturbationMatrix epsilon a) - 1) / epsilon^2)
      (𝓝[>] (0 : ℝ)) (𝓝 l)

/-- All real coefficient polynomials are excluded. This states the
relation directly on the positive solution set, without an arbitrary
choice function outside its domain. -/
def CoefficientGraphNonalgebraic : Prop :=
  ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 →
    ¬ (∀ a l : ℝ, criticalParameter < a → a < 1 →
      0 < l → coefficientIntegral l = a →
      MvPolynomial.eval (Fin.cons a (fun _ : Fin 1 => l)) Q = 0)

end
end Specification
end BilinearSystems
