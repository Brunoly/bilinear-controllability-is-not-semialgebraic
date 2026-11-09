import BilinearSystems.Analysis.ShortAngularLogExpansion
import Mathlib.Analysis.Convex.Deriv

/-!
# Second derivative taylor
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

/-- The upper half of a second-order Taylor estimate, proved by concavity
of f(phi+x)-L*x²/2. -/
theorem taylor_upper_of_second_derivative_le
    (f df ddf : ℝ → ℝ) (L phi t : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hf2 : ∀ x, HasDerivAt df (ddf x) x)
    (hbound : ∀ x, ddf x ≤ L) :
    f (phi+t) ≤ f phi + df phi*t + L*t^2/2 := by
  let g : ℝ → ℝ := fun x => f (phi+x)-L*x^2/2
  let gp : ℝ → ℝ := fun x => df (phi+x)-L*x
  let gpp : ℝ → ℝ := fun x => ddf (phi+x)-L
  have hshift (x : ℝ) : HasDerivAt (fun y : ℝ => phi+y) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_add phi
  have hquad (x : ℝ) : HasDerivAt (fun y : ℝ => L*y^2/2) (L*x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul L).div_const 2 using 1
    · funext y
      simp only [id_eq, Pi.pow_apply]
    · simp only [id_eq]
      ring
  have hlinear (x : ℝ) : HasDerivAt (fun y : ℝ => L*y) L x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul L
  have hfirst (x : ℝ) : HasDerivAt g (gp x) x := by
    have h := ((hf (phi+x)).comp x (hshift x)).sub (hquad x)
    convert h using 1
    · rfl
    · ring
  have hsecond (x : ℝ) : HasDerivAt gp (gpp x) x := by
    have h := ((hf2 (phi+x)).comp x (hshift x)).sub (hlinear x)
    convert h using 1
    · rfl
    · ring
  have hconc : ConcaveOn ℝ (univ : Set ℝ) g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    · intro x _
      exact (hfirst x).continuousAt.continuousWithinAt
    · intro x _
      exact (hfirst x).hasDerivWithinAt
    · intro x _
      exact (hsecond x).hasDerivWithinAt
    · intro x _
      exact sub_nonpos.mpr (hbound (phi+x))
  have htangent := concave_tangent_at_zero hconc (mem_univ 0) (mem_univ t)
    (hfirst 0)
  dsimp [g, gp] at htangent
  norm_num at htangent
  linarith

/-- Two-sided Taylor estimate when the second derivative is absolutely
bounded. The constant one-half matches the manuscript gauge remainder. -/
theorem taylor_abs_of_second_derivative_bound
    (f df ddf : ℝ → ℝ) (L phi t : ℝ)
    (hf : ∀ x, HasDerivAt f (df x) x)
    (hf2 : ∀ x, HasDerivAt df (ddf x) x)
    (hbound : ∀ x, |ddf x| ≤ L) :
    |f (phi+t)-f phi-df phi*t| ≤ L*t^2/2 := by
  have hu := taylor_upper_of_second_derivative_le f df ddf L phi t
    hf hf2 (fun x => (le_abs_self _).trans (hbound x))
  have hn : ∀ x, HasDerivAt (fun y => -f y) (-(df x)) x :=
    fun x => (hf x).neg
  have hn2 : ∀ x, HasDerivAt (fun y => -df y) (-(ddf x)) x :=
    fun x => (hf2 x).neg
  have hl := taylor_upper_of_second_derivative_le
    (fun y => -f y) (fun y => -df y) (fun y => -ddf y)
    L phi t hn hn2
    (fun x => (neg_le_abs (ddf x)).trans (hbound x))
  apply abs_le.mpr
  constructor <;> nlinarith

end
end Specification
end BilinearSystems
