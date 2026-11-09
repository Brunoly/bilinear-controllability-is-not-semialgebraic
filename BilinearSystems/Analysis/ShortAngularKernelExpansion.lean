import BilinearSystems.Analysis.ShortTrigonometricTaylor

/-!
# Short angular kernel expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Exact rearrangement isolating cosine and sine Taylor remainders. -/
theorem angularKernel_short_expansion_identity (epsilon a theta v : ℝ) :
    angularKernel epsilon a theta (epsilon*v) -
      (1-epsilon*Real.sin (2*theta) +
        epsilon^2*(-v^2/2-v*(a+Real.cos (2*theta)))) =
      (1-epsilon*Real.sin (2*theta)) *
        (Real.cos (epsilon*v)-(1-(epsilon*v)^2/2)) +
      epsilon*Real.sin (2*theta)*(epsilon*v)^2/2 -
      epsilon*(a+Real.cos (2*theta)) *
        (Real.sin (epsilon*v)-epsilon*v) := by
  rw [angularKernel_linear_combination]
  ring

/-- A local quantitative remainder, before bounding the explicit angle by
epsilon*(a+1). This keeps every dependence visible. -/
theorem angularKernel_short_local_error (epsilon a theta v : ℝ)
    (he : 0 ≤ epsilon) (ht : |epsilon*v| ≤ 1) :
    |angularKernel epsilon a theta (epsilon*v) -
      (1-epsilon*Real.sin (2*theta) +
        epsilon^2*(-v^2/2-v*(a+Real.cos (2*theta))))| ≤
      |1-epsilon*Real.sin (2*theta)| * |epsilon*v|^4 +
      epsilon* |Real.sin (2*theta)| *(epsilon*v)^2/2 +
      epsilon* |a+Real.cos (2*theta)| * |epsilon*v|^3 := by
  let s := Real.sin (2*theta)
  let q := a+Real.cos (2*theta)
  let t := epsilon*v
  let A := (1-epsilon*s)*(Real.cos t-(1-t^2/2))
  let B := epsilon*s*t^2/2
  let C := -(epsilon*q*(Real.sin t-t))
  have hcos := cos_short_quartic_error t ht
  have hsin := sin_short_cubic_error t ht
  have hA : |A| ≤ |1-epsilon*s| * |t|^4 := by
    dsimp [A]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
  have hB : |B| ≤ epsilon* |s| *t^2/2 := by
    dsimp [B]
    rw [abs_div, abs_mul, abs_mul]
    simp only [abs_pow, abs_of_nonneg he, abs_of_pos (by norm_num : (0:ℝ)<2), sq_abs]
    rfl
  have hC : |C| ≤ epsilon* |q| * |t|^3 := by
    dsimp [C]
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg he]
    exact mul_le_mul_of_nonneg_left hsin (by positivity)
  rw [angularKernel_short_expansion_identity]
  change |A+B+C| ≤ _
  have htri : |A+B+C| ≤ |A|+|B|+|C| := by
    linarith [abs_add_le (A+B) C, abs_add_le A B]
  dsimp [A, B, C, t, s, q] at htri hA hB hC ⊢
  nlinarith

end
end Specification
end BilinearSystems
