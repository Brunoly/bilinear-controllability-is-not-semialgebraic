import BilinearSystems.Analysis.AngularPhase

/-!
# Projective angular representative
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

theorem angularKernel_sub_int_pi (epsilon a theta t : ℝ) (n : ℤ) :
    angularKernel epsilon a theta (t-(n:ℝ)*Real.pi) =
      (-1:ℝ)^n * angularKernel epsilon a theta t := by
  rw [angularKernel_linear_combination, angularKernel_linear_combination,
    Real.cos_sub_int_mul_pi, Real.sin_sub_int_mul_pi]
  ring

theorem angularKernel_abs_sub_int_pi (epsilon a theta t : ℝ) (n : ℤ) :
    |angularKernel epsilon a theta (t-(n:ℝ)*Real.pi)| =
      |angularKernel epsilon a theta t| := by
  rw [angularKernel_sub_int_pi, abs_mul]
  have hneg : |(-1:ℝ)^n| = 1 := by simp
  rw [hneg, one_mul]

theorem angularDirection_sub_int_pi (phi : ℝ) (n : ℤ) :
    angularDirection (phi-(n:ℝ)*Real.pi) =
      (-1:ℝ)^n • angularDirection phi := by
  funext i
  fin_cases i
  · simp [angularDirection, Real.cos_sub_int_mul_pi, Pi.smul_apply, smul_eq_mul]
  · simp [angularDirection, Real.sin_sub_int_mul_pi, Pi.smul_apply, smul_eq_mul]

theorem gaugeProfile_sub_int_pi (a l phi : ℝ)
    (hcoef : coefficientIntegral l = a) (n : ℤ) :
    gaugeProfile a l (phi-(n:ℝ)*Real.pi) = gaugeProfile a l phi :=
  (gaugeProfile_periodic a l hcoef).sub_int_mul_eq n

/-- Every nonzero angular edge has a representative in the positive
component containing t=0, and the new representative has the original
projection magnitude and gauge value. -/
theorem angularKernel_projective_representative
    (epsilon a l theta t : ℝ)
    (hp : 0 < 1-epsilon*Real.sin (2*theta))
    (hcoef : coefficientIntegral l = a)
    (hne : angularKernel epsilon a theta t ≠ 0) :
    ∃ n : ℤ,
      (∀ x ∈ Icc (min 0 (t-(n:ℝ)*Real.pi))
          (max 0 (t-(n:ℝ)*Real.pi)),
        0 < angularKernel epsilon a theta x) ∧
      |angularKernel epsilon a theta (t-(n:ℝ)*Real.pi)| =
        |angularKernel epsilon a theta t| ∧
      gaugeProfile a l (theta+Real.pi/2+(t-(n:ℝ)*Real.pi)) =
        gaugeProfile a l (theta+Real.pi/2+t) := by
  let p := 1-epsilon*Real.sin (2*theta)
  let q := epsilon*(a+Real.cos (2*theta))
  have hlinear (x : ℝ) : angularKernel epsilon a theta x =
      p*Real.cos x-q*Real.sin x :=
    angularKernel_linear_combination epsilon a theta x
  obtain ⟨n, hsegment⟩ := sineCosine_positive_representative p q t hp
    (by simpa only [← hlinear] using hne)
  refine ⟨n, ?_, angularKernel_abs_sub_int_pi epsilon a theta t n, ?_⟩
  · intro x hx
    rw [hlinear]
    exact hsegment x hx
  · have harg : theta+Real.pi/2+(t-(n:ℝ)*Real.pi) =
        (theta+Real.pi/2+t)-(n:ℝ)*Real.pi := by ring
    rw [harg, gaugeProfile_sub_int_pi a l _ hcoef n]

end
end Specification
end BilinearSystems
