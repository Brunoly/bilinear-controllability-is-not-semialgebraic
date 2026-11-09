import BilinearSystems.Analysis.PerturbationGrowthUpper
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Angular gauge bounds
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The gauge profile is continuous and periodic, hence globally bounded. -/
theorem gaugeProfile_bounded (a l : ℝ) (hcoef : coefficientIntegral l = a) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ theta, |gaugeProfile a l theta| ≤ H := by
  have hc : Continuous (gaugeProfile a l) :=
    continuous_iff_continuousAt.mpr
      (fun theta => (gaugeProfile_hasDerivAt a l theta).continuousAt)
  have hb := (gaugeProfile_periodic a l hcoef).isBounded_of_continuous
    Real.pi_ne_zero hc
  obtain ⟨H,hH⟩ := isBounded_iff_forall_norm_le.mp hb
  have hforall : ∀ theta, |gaugeProfile a l theta| ≤ H := by
    intro theta
    simpa only [Real.norm_eq_abs] using hH _ ⟨theta,rfl⟩
  exact ⟨H, (abs_nonneg _).trans (hforall 0), hforall⟩

/-- `Complex.arg` of the unit vector at theta differs from theta by an
integer multiple of 2pi, so it has the same pi-periodic gauge value. -/
theorem gaugeProfile_complex_arg_angularDirection (a l theta : ℝ)
    (hcoef : coefficientIntegral l = a) :
    gaugeProfile a l
      (Complex.arg (⟨Real.cos theta, Real.sin theta⟩ : ℂ)) =
      gaugeProfile a l theta := by
  let z : ℂ := ⟨Real.cos theta, Real.sin theta⟩
  have hz : Complex.cos (theta : ℂ) + Complex.sin (theta : ℂ) * Complex.I = z := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    change (z.re : ℂ) + z.im * Complex.I = z
    exact Complex.re_add_im z
  have harg := Complex.arg_cos_add_sin_mul_I_sub theta
  rw [hz] at harg
  let m : ℤ := 2 * ⌊(Real.pi-theta)/(2*Real.pi)⌋
  have hm : Complex.arg z = theta + (m : ℝ)*Real.pi := by
    dsimp [m]
    push_cast
    nlinarith [harg]
  have hp := ((gaugeProfile_periodic a l hcoef).int_mul m) theta
  rw [← hm] at hp
  exact hp

/-- The shared weight has the intended profile value on an angular unit
vector, independently of the principal argument branch. -/
theorem angularGaugeWeight_of_direction (epsilon a l theta : ℝ)
    (hcoef : coefficientIntegral l = a) :
    angularGaugeWeight epsilon a l (angularDirection theta) =
      Real.exp (epsilon*gaugeProfile a l theta) := by
  change Real.exp (epsilon*gaugeProfile a l
    (Complex.arg (⟨Real.cos theta, Real.sin theta⟩ : ℂ))) = _
  rw [gaugeProfile_complex_arg_angularDirection a l theta hcoef]

/-- Uniform positive comparison constants for the angular gauge. -/
theorem angularGaugeWeight_bounds (epsilon a l H : ℝ)
    (he : 0 ≤ epsilon) (hH : ∀ theta, |gaugeProfile a l theta| ≤ H)
    (v : State) :
    Real.exp (-epsilon*H) ≤ angularGaugeWeight epsilon a l v ∧
    angularGaugeWeight epsilon a l v ≤ Real.exp (epsilon*H) := by
  let theta := Complex.arg (⟨v 0, v 1⟩ : ℂ)
  have hb := abs_le.mp (hH theta)
  unfold angularGaugeWeight
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hb.1 he]
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hb.2 he

end
end Specification
end BilinearSystems
