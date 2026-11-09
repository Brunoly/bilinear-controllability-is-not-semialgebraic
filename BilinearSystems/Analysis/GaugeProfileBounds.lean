import BilinearSystems.Analysis.GaugeDefectCurvature

/-!
# Gauge profile bounds
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The coefficient equation bounds the positive branch by a²/2. -/
theorem coefficient_lambda_le_half_square (a l : ℝ)
    (ha : 0 ≤ a) (hl : 0 ≤ l) (heq : coefficientIntegral l = a) :
    2*l ≤ a^2 := by
  have hroot : Real.sqrt (2*l) ≤ a := by
    rw [← heq]
    exact sqrt_le_coefficientIntegral l
  have hs : (Real.sqrt (2*l))^2 = 2*l := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (2*l)]

/-- The integrand displacement is bounded by R=a+1 independently of angle. -/
theorem primitiveIntegrand_displacement_bound (a l theta : ℝ)
    (ha : 0 ≤ a) (hl : 0 ≤ l) (heq : coefficientIntegral l = a) :
    |primitiveIntegrand a l theta-a| ≤ a+1 := by
  have hsq := coefficient_lambda_le_half_square a l ha hl heq
  have hsin := Real.abs_sin_le_one (2*theta)
  have hsin2 : Real.sin (2*theta)^2 ≤ 1 := by
    nlinarith [sq_abs (Real.sin (2*theta)), abs_nonneg (Real.sin (2*theta))]
  have hnonneg : 0 ≤ 2*l+Real.sin (2*theta)^2 := by positivity
  have hroot : 0 ≤ Real.sqrt (2*l+Real.sin (2*theta)^2) := Real.sqrt_nonneg _
  have hrootSq : (Real.sqrt (2*l+Real.sin (2*theta)^2))^2 =
      2*l+Real.sin (2*theta)^2 := Real.sq_sqrt hnonneg
  have hR : 0 ≤ a+1 := by linarith
  have hupper : Real.sqrt (2*l+Real.sin (2*theta)^2) ≤ a+1 := by
    nlinarith
  unfold primitiveIntegrand
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hroot]
  exact hupper

/-- The exact cancellation used in both one-step expansions. -/
theorem primitiveIntegrand_displacement_square (a l theta : ℝ)
    (hl : 0 ≤ l) :
    ((primitiveIntegrand a l theta-a)^2-Real.sin (2*theta)^2)/2 = l := by
  have h := primitiveIntegrand_squared_identity a l theta hl
  linarith

/-- The curvature parameter is at least one half under the stated perturbation bound. -/
theorem gaugeDefect_curvature_margin (epsilon l : ℝ)
    (hl : 0 < l) (he : 0 ≤ epsilon)
    (hesmall : epsilon ≤ 1/(2*(2+1/Real.sqrt (2*l)))) :
    1/2 ≤ 1-epsilon*(2+1/Real.sqrt (2*l)) := by
  have hroot : 0 < Real.sqrt (2*l) := Real.sqrt_pos.2 (by positivity)
  have hL : 0 < 2+1/Real.sqrt (2*l) := by positivity
  have hmul : epsilon * (2+1/Real.sqrt (2*l)) ≤ 1/2 := by
    calc
      _ ≤ (1/(2*(2+1/Real.sqrt (2*l)))) *
          (2+1/Real.sqrt (2*l)) :=
        mul_le_mul_of_nonneg_right hesmall hL.le
      _ = 1/2 := by field_simp [hL.ne']
  linarith

end
end Specification
end BilinearSystems
