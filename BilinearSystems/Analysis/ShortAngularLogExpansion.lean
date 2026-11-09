import BilinearSystems.Analysis.ShortAngularKernelSize

/-!
# Short angular log expansion
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The logarithm of the chosen kernel has its claimed first two
coefficients, with a numerical cubic error valid throughout a in [0,1]. -/
theorem shortKernel_log_expansion (epsilon a theta v : ℝ)
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hv : |v| ≤ a+1) :
    |Real.log (angularKernel epsilon a theta (epsilon*v)) -
      (-epsilon*Real.sin (2*theta) +
        epsilon^2*(-v^2/2-v*(a+Real.cos (2*theta))-
          Real.sin (2*theta)^2/2))| ≤ 100*epsilon^3 := by
  let s := Real.sin (2*theta)
  let c := -v^2/2-v*(a+Real.cos (2*theta))
  let z := angularKernel epsilon a theta (epsilon*v)-1
  have hs : |s| ≤ 1 := Real.abs_sin_le_one _
  have hc : |c| ≤ 6 := shortKernel_quadratic_coefficient_bound a theta v ha ha1 hv
  have hrem : |z-(-epsilon*s+epsilon^2*c)| ≤ 50*epsilon^3 := by
    convert angularKernel_short_uniform_error epsilon a theta v he heSmall ha ha1 hv using 1
    congr 1
    dsimp [z, s, c]
    ring
  have hz : |z| ≤ 2*epsilon :=
    shortKernel_displacement_bound epsilon a theta v he heSmall ha ha1 hv
  have hzhalf : |z| ≤ 1/2 :=
    shortKernel_displacement_half epsilon a theta v he heSmall ha ha1 hv
  have hlog := log_one_add_quadratic_remainder z hzhalf
  have hsTerm : |epsilon*s| ≤ epsilon := by
    rw [abs_mul, abs_of_nonneg he]
    have hm := mul_le_mul_of_nonneg_left hs he
    nlinarith
  have hcTerm : |epsilon^2*c| ≤ 6*epsilon^2 := by
    rw [abs_mul, abs_pow, abs_of_nonneg he]
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg epsilon)]
  have he3 : epsilon^3 ≤ epsilon^2/100 := by
    have hm := mul_le_mul_of_nonneg_left heSmall (sq_nonneg epsilon)
    nlinarith
  have hza : |z+epsilon*s| ≤ 7*epsilon^2 := by
    have hident : z+epsilon*s =
        (z-(-epsilon*s+epsilon^2*c))+epsilon^2*c := by ring
    rw [hident]
    have htri := abs_add_le (z-(-epsilon*s+epsilon^2*c)) (epsilon^2*c)
    nlinarith [htri]
  have hzb : |z-epsilon*s| ≤ 3*epsilon := by
    have htri := abs_sub_le z 0 (epsilon*s)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    nlinarith [htri]
  have hquad : |z^2-epsilon^2*s^2| ≤ 21*epsilon^3 := by
    have hfact : z^2-epsilon^2*s^2 =
        (z+epsilon*s)*(z-epsilon*s) := by ring
    rw [hfact, abs_mul]
    have hm := mul_le_mul hza hzb (abs_nonneg _) (by positivity : 0 ≤ 7*epsilon^2)
    nlinarith [hm]
  have hlogBound : |Real.log (1+z)-z+z^2/2| ≤ 16*epsilon^3 := by
    have hz3 := pow_le_pow_left₀ (abs_nonneg z) hz 3
    nlinarith
  have hlogIdentity : Real.log (angularKernel epsilon a theta (epsilon*v)) -
      (-epsilon*s+epsilon^2*(c-s^2/2)) =
      (Real.log (1+z)-z+z^2/2) +
      (z-(-epsilon*s+epsilon^2*c)) -
      (z^2-epsilon^2*s^2)/2 := by
    have hzKernel : angularKernel epsilon a theta (epsilon*v) = 1+z := by
      dsimp [z]
      ring
    rw [hzKernel]
    ring
  have htri : |Real.log (1+z)-z+z^2/2 +
      (z-(-epsilon*s+epsilon^2*c)) -
      (z^2-epsilon^2*s^2)/2| ≤
      |Real.log (1+z)-z+z^2/2| +
      |z-(-epsilon*s+epsilon^2*c)| +
      |(z^2-epsilon^2*s^2)/2| := by
    have h1 := abs_add_le
      (Real.log (1+z)-z+z^2/2 + (z-(-epsilon*s+epsilon^2*c)))
      (-(z^2-epsilon^2*s^2)/2)
    have h2 := abs_add_le (Real.log (1+z)-z+z^2/2)
      (z-(-epsilon*s+epsilon^2*c))
    have hleftEq :
        Real.log (1+z)-z+z^2/2 + (z-(-epsilon*s+epsilon^2*c)) +
          -(z^2-epsilon^2*s^2)/2 =
        Real.log (1+z)-z+z^2/2 + (z-(-epsilon*s+epsilon^2*c)) -
          (z^2-epsilon^2*s^2)/2 := by ring
    rw [hleftEq] at h1
    have hrightEq : |-(z^2-epsilon^2*s^2)/2| =
        |(z^2-epsilon^2*s^2)/2| := by
      rw [show -(z^2-epsilon^2*s^2)/2 =
        -((z^2-epsilon^2*s^2)/2) by ring, abs_neg]
    rw [hrightEq] at h1
    nlinarith [h1, h2]
  have hhalfQuad : |(z^2-epsilon^2*s^2)/2| ≤ 21*epsilon^3/2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith
  dsimp [s, c] at hlogIdentity ⊢
  rw [hlogIdentity]
  nlinarith [htri, hlogBound, hrem, hhalfQuad]

end
end Specification
end BilinearSystems
