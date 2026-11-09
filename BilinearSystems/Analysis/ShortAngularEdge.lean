import BilinearSystems.Analysis.GaugeDefectEnvelope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Short angular edge
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

private theorem angularKernel_short_lower (epsilon a theta x : ℝ)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (ha : 0 ≤ a)
    (hx : |x| ≤ epsilon*(a+1)) :
    1-epsilon*(1+(a+1)^2/2+a*(a+1)) ≤ angularKernel epsilon a theta x := by
  have hR : 0 ≤ a+1 := by linarith
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have hsin : Real.sin x ≤ |x| := (le_abs_self _).trans Real.abs_sin_le_abs
  have hsin2 : Real.sin (2*theta+x) ≤ 1 := Real.sin_le_one _
  have hprod : a*Real.sin x + Real.sin (2*theta+x) ≤ a*|x|+1 := by
    nlinarith
  have hmult := mul_le_mul_of_nonneg_left hprod he
  have hx2 : x^2 ≤ (epsilon*(a+1))^2 := by
    nlinarith [sq_abs x, abs_nonneg x]
  have he2 : epsilon^2 ≤ epsilon := by nlinarith
  have hsq : x^2 ≤ epsilon*(a+1)^2 := by
    have hm := mul_le_mul_of_nonneg_right he2 (sq_nonneg (a+1))
    nlinarith [hx2]
  have hcross : epsilon*a*|x| ≤ epsilon*a*(a+1) := by
    have h1 := mul_le_mul_of_nonneg_left hx (show 0 ≤ epsilon*a by positivity)
    have h2 := mul_le_mul_of_nonneg_right he2 (show 0 ≤ a*(a+1) by positivity)
    nlinarith [h1, h2]
  unfold angularKernel
  nlinarith [hmult]

/-- Positivity of the angular kernel under the stated smallness bound. -/
theorem angularKernel_pos_of_short (epsilon a theta x : ℝ)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (ha : 0 ≤ a)
    (hx : |x| ≤ epsilon*(a+1))
    (hsmall : epsilon*(1+(a+1)^2/2+a*(a+1)) ≤ 1/2) :
    0 < angularKernel epsilon a theta x := by
  have h := angularKernel_short_lower epsilon a theta x he he1 ha hx
  linarith

/-- The optimizing candidate t=epsilon v(theta) is a nonzero positive
edge whenever epsilon is positive and lambda is positive. -/
theorem explicitShortEdge_positive (epsilon a l theta : ℝ)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) (ha : 0 ≤ a)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a)
    (hsmall : epsilon*(1+(a+1)^2/2+a*(a+1)) ≤ 1/2) :
    0 < angularKernel epsilon a theta
      (epsilon*(primitiveIntegrand a l theta-a)) := by
  have hv := primitiveIntegrand_displacement_bound a l theta ha hl.le hcoef
  have hR : 0 ≤ a+1 := by linarith
  have hangle : |epsilon*(primitiveIntegrand a l theta-a)| ≤ epsilon*(a+1) := by
    rw [abs_mul, abs_of_pos he]
    exact mul_le_mul_of_nonneg_left hv he.le
  exact angularKernel_pos_of_short epsilon a theta _ he.le he1 ha hangle hsmall

/-- The whole interval from zero to the explicit step stays in the
positive-kernel component. -/
theorem explicitShortEdge_segment_positive (epsilon a l theta : ℝ)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) (ha : 0 ≤ a)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a)
    (hsmall : epsilon*(1+(a+1)^2/2+a*(a+1)) ≤ 1/2) :
    ∀ x ∈ Icc (min 0 (epsilon*(primitiveIntegrand a l theta-a)))
      (max 0 (epsilon*(primitiveIntegrand a l theta-a))),
      0 < angularKernel epsilon a theta x := by
  let t := epsilon*(primitiveIntegrand a l theta-a)
  have hv := primitiveIntegrand_displacement_bound a l theta ha hl.le hcoef
  have htbound : |t| ≤ epsilon*(a+1) := by
    dsimp [t]
    rw [abs_mul, abs_of_pos he]
    exact mul_le_mul_of_nonneg_left hv he.le
  intro x hx
  have hxabs : |x| ≤ |t| := by
    rcases le_total 0 t with ht | ht
    · rw [min_eq_left ht, max_eq_right ht] at hx
      rw [abs_of_nonneg ht, abs_of_nonneg hx.1]
      exact hx.2
    · rw [min_eq_right ht, max_eq_left ht] at hx
      rw [abs_of_nonpos ht, abs_of_nonpos hx.2]
      linarith [hx.1]
  exact angularKernel_pos_of_short epsilon a theta x he.le he1 ha
    (hxabs.trans htbound) hsmall

end
end Specification
end BilinearSystems
