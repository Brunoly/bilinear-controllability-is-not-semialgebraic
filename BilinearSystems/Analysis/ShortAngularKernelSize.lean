import BilinearSystems.Analysis.ShortAngularKernelUniform

/-!
# Short angular kernel size
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The quadratic coefficient of the short kernel expansion is uniformly
bounded on the parameter interval a in [0,1]. -/
theorem shortKernel_quadratic_coefficient_bound (a theta v : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : |v| ≤ a+1) :
    |-v^2/2-v*(a+Real.cos (2*theta))| ≤ 6 := by
  have hv2 : |v| ≤ 2 := by linarith
  have hk := Real.abs_cos_le_one (2*theta)
  have hq : |a+Real.cos (2*theta)| ≤ 2 := by
    apply abs_le.mpr
    have hk' := abs_le.mp hk
    constructor <;> linarith
  have hvsq : v^2 ≤ 4 := by nlinarith [sq_abs v, abs_nonneg v]
  have hvq : |v*(a+Real.cos (2*theta))| ≤ 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hv2 hq (abs_nonneg _) (by norm_num : (0:ℝ)≤2)]
  have htri := abs_add_le (-(v^2/2)) (-(v*(a+Real.cos (2*theta))))
  have hfirst : |-(v^2/2)| = v^2/2 := by
    rw [abs_neg, abs_div, abs_pow, abs_of_pos (by norm_num : (0:ℝ)<2)]
    rw [sq_abs]
  rw [hfirst, abs_neg] at htri
  have htargetEq : -(v^2/2)+-(v*(a+Real.cos (2*theta))) =
      -v^2/2-v*(a+Real.cos (2*theta)) := by ring
  rw [htargetEq] at htri
  nlinarith

/-- The chosen edge satisfies |f-1| ≤ 2 epsilon, uniformly in theta.
The small interval epsilon ≤ 1/100 is sufficient for an asymptotic result. -/
theorem shortKernel_displacement_bound (epsilon a theta v : ℝ)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : |v| ≤ a+1) :
    |angularKernel epsilon a theta (epsilon*v)-1| ≤ 2*epsilon := by
  let z := angularKernel epsilon a theta (epsilon*v)-1
  let s := Real.sin (2*theta)
  let c := -v^2/2-v*(a+Real.cos (2*theta))
  have hs := Real.abs_sin_le_one (2*theta)
  have hc := shortKernel_quadratic_coefficient_bound a theta v ha ha1 hv
  have hrem : |z-(-epsilon*s+epsilon^2*c)| ≤ 50*epsilon^3 := by
    convert angularKernel_short_uniform_error epsilon a theta v he heSmall ha ha1 hv using 1
    · congr 1
      dsimp [z, s, c]
      ring
  have htri0 : |z| ≤ |z-(-epsilon*s+epsilon^2*c)| +
      |epsilon*s| + |epsilon^2*c| := by
    calc
      |z| = |(z-(-epsilon*s+epsilon^2*c)) +
          (-epsilon*s+epsilon^2*c)| := by congr 1; ring
      _ ≤ |z-(-epsilon*s+epsilon^2*c)| +
          |-epsilon*s+epsilon^2*c| := abs_add_le _ _
      _ ≤ |z-(-epsilon*s+epsilon^2*c)| +
          (|epsilon*s|+|epsilon^2*c|) := by
        have h2 := abs_add_le (-epsilon*s) (epsilon^2*c)
        have hneg : -epsilon*s = -(epsilon*s) := by ring
        rw [hneg, abs_neg] at h2
        have hgoalEq : -epsilon*s+epsilon^2*c =
            -(epsilon*s)+epsilon^2*c := by ring
        rw [hgoalEq]
        linarith
      _ = _ := by ring
  have hsTerm : |epsilon*s| ≤ epsilon := by
    rw [abs_mul, abs_of_nonneg he]
    change |s| ≤ 1 at hs
    have hm := mul_le_mul_of_nonneg_left hs he
    nlinarith
  have hcTerm : |epsilon^2*c| ≤ 6*epsilon^2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg he]
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg epsilon)]
  have he2 : epsilon^2 ≤ epsilon/100 := by nlinarith
  have he3 : epsilon^3 ≤ epsilon/10000 := by
    have hm := mul_le_mul_of_nonneg_left he2 he
    nlinarith
  nlinarith [htri0]

/-- In particular the explicit edge stays inside the log Taylor domain. -/
theorem shortKernel_displacement_half (epsilon a theta v : ℝ)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : |v| ≤ a+1) :
    |angularKernel epsilon a theta (epsilon*v)-1| ≤ 1/2 := by
  have h := shortKernel_displacement_bound epsilon a theta v he heSmall ha ha1 hv
  linarith

end
end Specification
end BilinearSystems
