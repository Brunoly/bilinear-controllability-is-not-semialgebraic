import BilinearSystems.Analysis.PerturbationProfile
import BilinearSystems.Control.SignedCycleTrajectories

namespace BilinearSystems
namespace Specification
noncomputable section

def angularDirection (theta : ℝ) : State :=
  fun i => if i = 0 then Real.cos theta else Real.sin theta

theorem angularDirection_unit (theta : ℝ) : UnitDirection (angularDirection theta) := by
  simpa [UnitDirection, euclideanDot, angularDirection, sq, add_comm] using
    (Real.sin_sq_add_cos_sq theta)

def angularKernel (epsilon a theta t : ℝ) : ℝ :=
  Real.cos t - epsilon * (a * Real.sin t + Real.sin (2*theta+t))

def ExactAngularKernel : Prop :=
  ∀ epsilon a theta t : ℝ,
    directionGain (perturbationMatrix epsilon a) (angularDirection theta)
      (angularDirection (theta+Real.pi/2+t)) = angularKernel epsilon a theta t

theorem exactAngularKernel : ExactAngularKernel := by
  intro epsilon a theta t
  have hangle : theta+Real.pi/2+t = (theta+t)+Real.pi/2 := by ring
  rw [hangle]
  simp [angularDirection, directionGain, perturbationMatrix,
    euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    angularKernel, Real.sin_add, Real.cos_add]
  have hs := Real.sin_two_mul theta
  have hc := Real.cos_two_mul theta
  have hunit := Real.sin_sq_add_cos_sq theta
  rw [hs, hc]
  linear_combination (Real.cos t - epsilon*a*Real.sin t + epsilon*Real.sin t) * hunit

theorem angularKernel_zero (epsilon a theta : ℝ) :
    angularKernel epsilon a theta 0 = 1-epsilon*Real.sin (2*theta) := by
  simp [angularKernel]

def AngularKernelDerivative : Prop :=
  ∀ epsilon a theta t : ℝ,
    HasDerivAt (angularKernel epsilon a theta)
      (-Real.sin t - epsilon*(a*Real.cos t+Real.cos (2*theta+t))) t

theorem angularKernelDerivative : AngularKernelDerivative := by
  intro epsilon a theta t
  have h₁ := Real.hasDerivAt_cos t
  have h₂ := ((Real.hasDerivAt_sin t).const_mul a).add
    ((Real.hasDerivAt_sin (2*theta+t)).comp t
      ((hasDerivAt_id t).const_add (2*theta)))
  have h₃ := h₁.sub (h₂.const_mul epsilon)
  convert h₃ using 1
  · funext x
    change Real.cos x - epsilon*(a*Real.sin x + Real.sin (2*theta+x)) =
      Real.cos x - epsilon*(a*Real.sin x + Real.sin (2*theta+x))
    rfl
  · ring

theorem angularKernel_derivative_zero (epsilon a theta : ℝ) :
    deriv (angularKernel epsilon a theta) 0 =
      -epsilon*(a+Real.cos (2*theta)) := by
  rw [(angularKernelDerivative epsilon a theta 0).deriv]
  simp

def gaugeDefect (epsilon a l theta t : ℝ) : ℝ :=
  Real.log (angularKernel epsilon a theta t) +
    epsilon*(gaugeProfile a l (theta+Real.pi/2+t)-gaugeProfile a l theta)

def GaugeDefectAtZero : Prop :=
  ∀ epsilon a l theta : ℝ, coefficientIntegral l = a →
    gaugeDefect epsilon a l theta 0 =
      Real.log (1-epsilon*Real.sin (2*theta)) +
        epsilon*Real.sin (2*theta)

theorem gaugeDefectAtZero : GaugeDefectAtZero := by
  intro epsilon a l theta h
  change Real.log (angularKernel epsilon a theta 0) +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+0)-gaugeProfile a l theta) = _
  rw [angularKernel_zero]
  simpa only [add_zero, gaugeProfile_quarterTurn_difference a l theta h]

def GaugeDefectDerivativeAtZero : Prop :=
  ∀ epsilon a l theta : ℝ,
    0 < 1-epsilon*Real.sin (2*theta) →
    deriv (gaugeDefect epsilon a l theta) 0 =
      epsilon*(primitiveIntegrand a l theta-a) -
        epsilon^2*Real.sin (2*theta)*(a+Real.cos (2*theta)) /
          (1-epsilon*Real.sin (2*theta))

theorem gaugeDefect_hasDerivAt (epsilon a l theta t : ℝ)
    (hf : angularKernel epsilon a theta t ≠ 0) :
    HasDerivAt (gaugeDefect epsilon a l theta)
      ((-Real.sin t-epsilon*(a*Real.cos t+Real.cos (2*theta+t))) /
        angularKernel epsilon a theta t +
        epsilon*(-Real.cos (2*(theta+Real.pi/2+t))+
          primitiveIntegrand a l (theta+Real.pi/2+t))) t := by
  have hlog := (Real.hasDerivAt_log hf).comp t
    (angularKernelDerivative epsilon a theta t)
  have hprofile := (gaugeProfile_hasDerivAt a l (theta+Real.pi/2+t)).comp t
    ((hasDerivAt_id t).const_add (theta+Real.pi/2))
  have hsum := hlog.add ((hprofile.sub_const (gaugeProfile a l theta)).const_mul epsilon)
  convert hsum using 1
  · funext x
    change Real.log (angularKernel epsilon a theta x) +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+x)-gaugeProfile a l theta) =
      Real.log (angularKernel epsilon a theta x) +
      epsilon*(gaugeProfile a l (theta+Real.pi/2+x)-gaugeProfile a l theta)
    rfl
  · ring

theorem gaugeDefectDerivativeAtZero : GaugeDefectDerivativeAtZero := by
  intro epsilon a l theta hf
  have hd := (gaugeDefect_hasDerivAt epsilon a l theta 0
    (by simpa [angularKernel_zero] using hf.ne')).deriv
  rw [hd]
  simp only [add_zero, Real.sin_zero, Real.cos_zero, neg_zero,
    angularKernel_zero]
  have hs : 2*(theta+Real.pi/2) = 2*theta+Real.pi := by ring
  rw [hs, Real.cos_add_pi]
  rw [primitiveIntegrand_periodic a l theta]
  field_simp [hf.ne']
  <;> ring

end
end Specification
end BilinearSystems
