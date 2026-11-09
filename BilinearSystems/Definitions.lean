import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Lean.Elab.Tactic.Omega

/-!
# Planar bilinear systems and polynomial-sign descriptions

The state domain is ℝ² minus {0}. Controls are arbitrary real scalars and
trajectories have positive finite length, including for equal endpoints.
Matrix pairs are unrestricted. Coordinates list A then B in row-major order.
A semialgebraic description means a finite Boolean combination of real
polynomial equalities and inequalities, with no fixed degree or size bound.
-/
namespace BilinearSystems
noncomputable section

abbrev State := Fin 2 → ℝ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def step (A B : Matrix2) (u : ℝ) (x : State) : State :=
  (A + u • B).mulVec x

def trajectoryEndpoint (A B : Matrix2) (x : State) (controls : List ℝ) : State :=
  controls.foldl (fun state control => step A B control state) x

/-- A positive finite number of steps; controls are in chronological order. -/
def Reachable (A B : Matrix2) (x y : State) : Prop :=
  ∃ controls : List ℝ, controls ≠ [] ∧ trajectoryEndpoint A B x controls = y

/-- Global controllability on ℝ² \ {0}: every ordered pair of nonzero real
states is connected by a positive finite trajectory with real controls.
This concerns actual vectors, including magnitude and sign. -/
def GloballyControllable (A B : Matrix2) : Prop :=
  ∀ x y : State, x ≠ 0 → y ≠ 0 → Reachable A B x y

inductive SignFormula (ι : Type*) where
  | positive : ι → SignFormula ι
  | zero : ι → SignFormula ι
  | negative : ι → SignFormula ι
  | truth : SignFormula ι
  | falsity : SignFormula ι
  | conj : SignFormula ι → SignFormula ι → SignFormula ι
  | disj : SignFormula ι → SignFormula ι → SignFormula ι
  | neg : SignFormula ι → SignFormula ι

def SignFormula.eval {ι X : Type*} (f : ι → X → ℝ) (x : X) : SignFormula ι → Prop
  | .positive i => 0 < f i x
  | .zero i => f i x = 0
  | .negative i => f i x < 0
  | .truth => True
  | .falsity => False
  | .conj a b => a.eval f x ∧ b.eval f x
  | .disj a b => a.eval f x ∨ b.eval f x
  | .neg a => ¬ a.eval f x

/-- Literal finite Boolean polynomial-sign descriptions with arbitrary real constants. -/
def HasFinitePolynomialSignDescription {n : ℕ} (S : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin n) ℝ) (φ : SignFormula (Fin m)),
    ∀ x, φ.eval (fun i y => MvPolynomial.eval y (p i)) x ↔ x ∈ S

abbrev MatrixPairCoordinates := Fin 8 → ℝ

def firstMatrix (v : MatrixPairCoordinates) : Matrix2 :=
  fun i j => v ⟨2*i.val+j.val, by omega⟩

def secondMatrix (v : MatrixPairCoordinates) : Matrix2 :=
  fun i j => v ⟨4+2*i.val+j.val, by omega⟩

def ControllabilityLocus : Set MatrixPairCoordinates :=
  {v | GloballyControllable (firstMatrix v) (secondMatrix v)}

def HasRationalEntries (v : MatrixPairCoordinates) : Prop :=
  ∀ i, ∃ q : ℚ, (q : ℝ) = v i

/-- Nonsemialgebraicity of the full real controllability locus. -/
def RealInputFiniteFormulaObstruction : Prop :=
  ¬ HasFinitePolynomialSignDescription ControllabilityLocus

/-- Rational-input obstruction with real states, controls, and arbitrary real polynomial coefficients. -/
def RationalInputFiniteFormulaObstruction : Prop :=
  ¬ ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin 8) ℝ) (φ : SignFormula (Fin m)),
    ∀ v : MatrixPairCoordinates, HasRationalEntries v →
      (φ.eval (fun i x => MvPolynomial.eval x (p i)) v ↔
        GloballyControllable (firstMatrix v) (secondMatrix v))

end
end BilinearSystems
