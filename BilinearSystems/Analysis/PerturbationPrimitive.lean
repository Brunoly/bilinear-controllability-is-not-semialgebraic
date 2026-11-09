import BilinearSystems.Coefficient.Integral

/-!
# Perturbation primitive
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def primitiveIntegrand (a l theta : ℝ) : ℝ :=
  a - Real.sqrt (2*l + Real.sin (2*theta)^2)

def perturbationPrimitive (a l theta : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..theta, primitiveIntegrand a l t

def gaugeProfile (a l theta : ℝ) : ℝ :=
  -(Real.sin (2*theta))/2 + perturbationPrimitive a l theta

theorem primitiveIntegrand_continuous (a l : ℝ) :
    Continuous (primitiveIntegrand a l) := by
  unfold primitiveIntegrand
  exact continuous_const.sub (Real.continuous_sqrt.comp (continuous_const.add
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)))

theorem primitiveIntegrand_periodic (a l : ℝ) :
    Function.Periodic (primitiveIntegrand a l) (Real.pi/2) := by
  intro theta
  have h : 2 * (theta + Real.pi/2) = 2*theta + Real.pi := by ring
  simp [primitiveIntegrand, h, Real.sin_add_pi]

theorem perturbationPrimitive_hasDerivAt (a l theta : ℝ) :
    HasDerivAt (perturbationPrimitive a l) (primitiveIntegrand a l theta) theta :=
  ((primitiveIntegrand_continuous a l).integral_hasStrictDerivAt 0 theta).hasDerivAt

theorem gaugeProfile_hasDerivAt (a l theta : ℝ) :
    HasDerivAt (gaugeProfile a l)
      (-Real.cos (2*theta) + primitiveIntegrand a l theta) theta := by
  have h := (Real.hasDerivAt_sin (2*theta)).comp theta
    ((hasDerivAt_id theta).const_mul (2 : ℝ))
  have hs := (h.neg.div_const (2 : ℝ)).add (perturbationPrimitive_hasDerivAt a l theta)
  convert hs using 1
  · rfl
  · ring

end
end Specification
end BilinearSystems
