import BilinearSystems.Analysis.ProjectiveAngularRepresentative

/-!
# Gauge defect projective upper
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

/-- Every nonzero edge obeys the quadratic-envelope bound after its
positive projective representative is chosen. -/
theorem gaugeDefect_projective_quadratic_upper
    (epsilon a l theta t : ℝ)
    (hl : 0 < l) (he : 0 ≤ epsilon)
    (hp : 0 < 1-epsilon*Real.sin (2*theta))
    (hm : 0 < 1-epsilon*(2+1/Real.sqrt (2*l)))
    (hcoef : coefficientIntegral l = a)
    (hne : angularKernel epsilon a theta t ≠ 0) :
    Real.log |angularKernel epsilon a theta t| +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+t)-
        gaugeProfile a l theta) ≤
      Real.log (1-epsilon*Real.sin (2*theta)) +
        epsilon*Real.sin (2*theta) +
        (deriv (gaugeDefect epsilon a l theta) 0)^2 /
          (2*(1-epsilon*(2+1/Real.sqrt (2*l)))) := by
  obtain ⟨n, hsegment, hmag, hprofile⟩ :=
    angularKernel_projective_representative epsilon a l theta t
      hp hcoef hne
  let t' := t-(n:ℝ)*Real.pi
  have hpos : 0 < angularKernel epsilon a theta t' := by
    exact hsegment t' (by simp [t'])
  have hzero : 0 < angularKernel epsilon a theta 0 := by
    simpa [angularKernel_zero] using hp
  have hderiv : HasDerivAt (gaugeDefect epsilon a l theta)
      (deriv (gaugeDefect epsilon a l theta) 0) 0 :=
    (gaugeDefect_hasDerivAt epsilon a l theta 0 hzero.ne').differentiableAt.hasDerivAt
  have hupper := gaugeDefect_segment_upper epsilon a l theta t'
    (deriv (gaugeDefect epsilon a l theta) 0)
    hl he hm hsegment hderiv
  have hleft : gaugeDefect epsilon a l theta t' =
      Real.log |angularKernel epsilon a theta t| +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+t)-
        gaugeProfile a l theta) := by
    unfold gaugeDefect
    rw [← hmag, abs_of_pos hpos, hprofile]
  rw [hleft, gaugeDefectAtZero epsilon a l theta hcoef] at hupper
  simpa using hupper

/-- Upper bound in terms of the derivative at zero. -/
theorem gaugeDefect_projective_explicit_upper
    (epsilon a l theta t : ℝ)
    (hl : 0 < l) (he : 0 ≤ epsilon)
    (hp : 0 < 1-epsilon*Real.sin (2*theta))
    (hm : 0 < 1-epsilon*(2+1/Real.sqrt (2*l)))
    (hcoef : coefficientIntegral l = a)
    (hne : angularKernel epsilon a theta t ≠ 0) :
    Real.log |angularKernel epsilon a theta t| +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+t)-
        gaugeProfile a l theta) ≤
      Real.log (1-epsilon*Real.sin (2*theta)) +
        epsilon*Real.sin (2*theta) +
        (epsilon*(primitiveIntegrand a l theta-a) -
          epsilon^2*Real.sin (2*theta)*(a+Real.cos (2*theta)) /
            (1-epsilon*Real.sin (2*theta)))^2 /
          (2*(1-epsilon*(2+1/Real.sqrt (2*l)))) := by
  have h := gaugeDefect_projective_quadratic_upper epsilon a l theta t
    hl he hp hm hcoef hne
  rw [gaugeDefectDerivativeAtZero epsilon a l theta hp] at h
  exact h

end
end Specification
end BilinearSystems
