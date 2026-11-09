import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Affine polynomial substitutions
-/
namespace BilinearSystems
open Polynomial

 theorem polynomial_affine_substitution_ne_zero {R : Type*}
    [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0)
    (offset scale : R) (hscale : scale ≠ 0) :
    p.comp (C offset + C scale * X) ≠ 0 := by
  intro h
  rcases Polynomial.comp_eq_zero_iff.mp h with hz | ⟨_, hc⟩
  · exact hp hz
  · have he := congrArg (fun q : Polynomial R => q.coeff 1) hc
    exact hscale (by simpa using he)

 theorem polynomial_blowup_substitution_ne_zero {σ : Type*}
    (epsilon : σ) (p : Polynomial (MvPolynomial σ ℝ)) (hp : p ≠ 0) :
    p.comp (C 1 + C ((MvPolynomial.X epsilon)^2) * X) ≠ 0 :=
  polynomial_affine_substitution_ne_zero p hp 1 _
    (pow_ne_zero 2 (MvPolynomial.X_ne_zero epsilon))

end BilinearSystems
