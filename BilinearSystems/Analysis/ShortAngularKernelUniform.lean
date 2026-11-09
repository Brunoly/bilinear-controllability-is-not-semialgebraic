import BilinearSystems.Analysis.ShortAngularKernelExpansion

/-!
# Short angular kernel uniform
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- For a in [0,1], a short step with |v| ≤ a+1 has a numerical cubic
remainder, uniformly over all angular directions. -/
theorem angularKernel_short_uniform_error (epsilon a theta v : ℝ)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : |v| ≤ a+1) :
    |angularKernel epsilon a theta (epsilon*v) -
      (1-epsilon*Real.sin (2*theta) +
        epsilon^2*(-v^2/2-v*(a+Real.cos (2*theta))))| ≤
      50*epsilon^3 := by
  let s := Real.sin (2*theta)
  let q := a+Real.cos (2*theta)
  let t := epsilon*v
  have hs : |s| ≤ 1 := Real.abs_sin_le_one _
  have hk : |Real.cos (2*theta)| ≤ 1 := Real.abs_cos_le_one _
  have hv2 : |v| ≤ 2 := by linarith
  have hq2 : |q| ≤ 2 := by
    apply abs_le.mpr
    have hk' := abs_le.mp hk
    dsimp [q]
    constructor <;> linarith
  have ht2 : |t| ≤ 2*epsilon := by
    dsimp [t]
    rw [abs_mul, abs_of_nonneg he]
    nlinarith [abs_nonneg v]
  have ht1 : |t| ≤ 1 := by linarith
  have hp2 : |1-epsilon*s| ≤ 2 := by
    apply abs_le.mpr
    have hs' := abs_le.mp hs
    have h1 := mul_le_mul_of_nonneg_left hs'.2 he
    have h2 := mul_le_mul_of_nonneg_left hs'.1 he
    constructor <;> nlinarith
  have he4 : epsilon^4 ≤ epsilon^3 := by
    nlinarith [pow_nonneg he 3]
  have ht4 : |t|^4 ≤ 16*epsilon^4 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht2 4
    nlinarith
  have ht3 : |t|^3 ≤ 8*epsilon^3 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht2 3
    nlinarith
  have ht2sq : t^2 ≤ 4*epsilon^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) ht2 2
    nlinarith [sq_abs t]
  have hlocal := angularKernel_short_local_error epsilon a theta v he ht1
  have hfirst : |1-epsilon*s| * |t|^4 ≤ 32*epsilon^3 := by
    have h := mul_le_mul hp2 ht4 (by positivity) (by norm_num)
    nlinarith [he4]
  have hsecond : epsilon* |s| *t^2/2 ≤ 2*epsilon^3 := by
    have h1 := mul_le_mul_of_nonneg_left hs he
    have h2 := mul_le_mul h1 ht2sq (sq_nonneg t) (by positivity)
    nlinarith
  have hthird : epsilon* |q| * |t|^3 ≤ 16*epsilon^3 := by
    have h1 := mul_le_mul_of_nonneg_left hq2 he
    have h2 := mul_le_mul h1 ht3 (by positivity) (by positivity)
    nlinarith [he4]
  dsimp [s, q, t] at hfirst hsecond hthird hlocal
  nlinarith

end
end Specification
end BilinearSystems
