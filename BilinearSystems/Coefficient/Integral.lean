import BilinearSystems.AuxiliaryDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral
-/
namespace BilinearSystems
namespace Specification
open Set
noncomputable section

private theorem coefficientIntegrand_continuous (l : ℝ) :
    Continuous (fun t : ℝ => Real.sqrt (2*l + Real.sin t ^ 2)) :=
  Real.continuous_sqrt.comp (continuous_const.add (Real.continuous_sin.pow 2))

theorem coefficientIntegral_zero : coefficientIntegral 0 = criticalParameter := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hcongr : (∫ t in (0 : ℝ)..(Real.pi / 2), Real.sqrt (2*0 + Real.sin t ^ 2)) =
      ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hpi] at ht
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (ht.2.trans (by linarith [Real.pi_pos]))
    simp [Real.sqrt_sq hs]
  unfold coefficientIntegral criticalParameter
  rw [hcongr, integral_sin]
  simp

theorem coefficientIntegral_strictMonoOn : StrictMonoOn coefficientIntegral (Ici 0) := by
  intro l hl m hm hlt
  have hpoint (t : ℝ) :
      Real.sqrt (2*l + Real.sin t ^ 2) < Real.sqrt (2*m + Real.sin t ^ 2) := by
    have hl0 : 0 ≤ l := hl
    apply Real.sqrt_lt_sqrt
    · positivity
    · linarith
  unfold coefficientIntegral
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity) (coefficientIntegrand_continuous l).continuousOn
    (coefficientIntegrand_continuous m).continuousOn
    (fun t _ => (hpoint t).le) ⟨0, ⟨le_rfl, by positivity⟩, hpoint 0⟩

theorem sqrt_le_coefficientIntegral (l : ℝ) : Real.sqrt (2*l) ≤ coefficientIntegral l := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have hmono : (∫ _ in (0 : ℝ)..(Real.pi / 2), Real.sqrt (2*l)) ≤
      ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sqrt (2*l + Real.sin t ^ 2) :=
    intervalIntegral.integral_mono_on hpi.le
      (continuous_const.intervalIntegrable _ _)
      ((coefficientIntegrand_continuous l).intervalIntegrable _ _)
      (fun t _ => Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (Real.sin t))))
  have h := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 2 / Real.pi by positivity)
  rw [intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  unfold coefficientIntegral
  convert h using 1
  field_simp [Real.pi_ne_zero]

/-- Joint continuity and compactness of the integration interval give
continuity even at the endpoint l = 0. -/
theorem coefficientIntegral_continuous : Continuous coefficientIntegral := by
  unfold coefficientIntegral
  apply continuous_const.mul
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi/2 by positivity),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  change Continuous (fun z : ℝ × ℝ => Real.sqrt (2*z.1 + Real.sin z.2 ^ 2))
  exact Real.continuous_sqrt.comp
    ((continuous_const.mul continuous_fst).add ((Real.continuous_sin.comp continuous_snd).pow 2))

theorem coefficientExistenceUniqueness : CoefficientExistenceUniqueness := by
  intro a ha
  have ha0 : 0 < a := (show 0 < criticalParameter by unfold criticalParameter; positivity).trans ha
  have hupper : a ≤ coefficientIntegral (a^2) := by
    calc
      a = Real.sqrt (a^2) := (Real.sqrt_sq ha0.le).symm
      _ ≤ Real.sqrt (2*(a^2)) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
      _ ≤ _ := sqrt_le_coefficientIntegral _
  have hmem : a ∈ Icc (coefficientIntegral 0) (coefficientIntegral (a^2)) :=
    ⟨coefficientIntegral_zero.symm ▸ ha.le, hupper⟩
  obtain ⟨l, hl, heq⟩ := intermediate_value_Icc (sq_nonneg a)
    coefficientIntegral_continuous.continuousOn hmem
  have hlpos : 0 < l := by
    refine lt_of_le_of_ne hl.1 ?_
    intro hz
    exact ha.ne' (by simpa [← hz, coefficientIntegral_zero] using heq.symm)
  refine ⟨l, ⟨hlpos, heq⟩, ?_⟩
  intro m hm
  exact coefficientIntegral_strictMonoOn.injOn hm.1.le hlpos.le (hm.2.trans heq.symm)

/-- The positive inverse branch is forced into every neighborhood of zero
when a decreases to its onset value. -/
theorem coefficient_lt_of_parameter_lt {l eta : ℝ}
    (hl : 0 ≤ l) (heta : 0 ≤ eta)
    (h : coefficientIntegral l < coefficientIntegral eta) : l < eta := by
  by_contra! hle
  exact h.not_ge (coefficientIntegral_strictMonoOn.monotoneOn heta hl hle)

end
end Specification
end BilinearSystems
