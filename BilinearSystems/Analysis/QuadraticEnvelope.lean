import BilinearSystems.Analysis.GaugeProfileBounds
import Mathlib.Analysis.Convex.Deriv

/-!
# Quadratic envelope
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

/-- A differentiable concave function lies below its tangent at zero, on
both sides of zero in a convex set. -/
theorem concave_tangent_at_zero {S : Set ℝ} {g : ℝ → ℝ} {d t : ℝ}
    (hg : ConcaveOn ℝ S g) (hzero : 0 ∈ S) (ht : t ∈ S)
    (hd : HasDerivAt g d 0) : g t ≤ g 0 + d*t := by
  by_cases hzeroT : t = 0
  · subst t
    simp
  have hconv : ConvexOn ℝ S (fun x => -g x) := hg.neg
  rcases lt_or_gt_of_ne hzeroT with hneg | hpos
  · have h := hconv.slope_le_of_hasDerivAt ht hzero hneg hd.neg
    rw [slope_def_field] at h
    have hden : 0 < (0:ℝ)-t := by linarith
    apply (div_le_iff₀ hden).mp at h
    nlinarith
  · have h := hconv.le_slope_of_hasDerivAt hzero ht hpos hd.neg
    rw [slope_def_field] at h
    have hden : 0 < t-(0:ℝ) := by linarith
    apply (le_div_iff₀ hden).mp at h
    nlinarith

/-- Quadratic upper bound from a negative second-derivative bound. -/
theorem quadratic_envelope {S : Set ℝ} {f : ℝ → ℝ}
    {m d t : ℝ} (hm : 0 < m)
    (hg : ConcaveOn ℝ S (fun x => f x + m*x^2/2))
    (hzero : 0 ∈ S) (ht : t ∈ S)
    (hd : HasDerivAt f d 0) :
    f t ≤ f 0 + d^2/(2*m) := by
  have hquad : HasDerivAt (fun x : ℝ => m*x^2/2) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).const_mul m).div_const 2 using 1
    · funext x
      simp only [id_eq, Pi.pow_apply]
    · norm_num
  have htangent := concave_tangent_at_zero hg hzero ht (hd.add hquad)
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_div,
    add_zero] at htangent
  have hsq : 0 ≤ (d-m*t)^2 := sq_nonneg _
  have hm2 : 0 < 2*m := by positivity
  have hmul := mul_le_mul_of_nonneg_right htangent hm2.le
  have htarget : (f t-f 0)*(2*m) ≤ d^2 := by nlinarith [hsq]
  have hfinal := (le_div_iff₀ hm2).mpr htarget
  linarith

end
end Specification
end BilinearSystems
