import BilinearSystems.Analysis.CubicRemainder
import Mathlib.Analysis.Calculus.DSlope

/-!
# Growth asymptotic
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

private theorem logGrowth_ratio_limit (a l : ℝ)
    (ha : criticalParameter < a) (ha1 : a < 1)
    (hl : 0 < l) (hcoef : coefficientIntegral l = a) :
    Tendsto (fun epsilon : ℝ =>
      Real.log (parameterGrowth epsilon a) / epsilon^2)
      (𝓝[>] (0 : ℝ)) (𝓝 l) := by
  obtain ⟨C,delta,hC,hdelta,hrem⟩ :=
    perturbationCubicRemainder a l ha ha1 hl hcoef
  have he0 : Tendsto (fun e : ℝ => e) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), 0 < e ∧ e < delta := by
    have hlt : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), e < delta :=
      nhdsWithin_le_nhds (Iio_mem_nhds hdelta)
    filter_upwards [hlt, self_mem_nhdsWithin] with e hlt hpos
    exact ⟨hpos,hlt⟩
  have hineq : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      l-C*e ≤ Real.log (parameterGrowth e a)/e^2 ∧
      Real.log (parameterGrowth e a)/e^2 ≤ l+C*e := by
    filter_upwards [hsmall] with e he
    have he2 : 0 < e^2 := sq_pos_of_pos he.1
    have hb := abs_le.mp (hrem e he.1 he.2)
    constructor
    · apply (le_div_iff₀ he2).mpr
      nlinarith [hb.1]
    · apply (div_le_iff₀ he2).mpr
      nlinarith [hb.2]
  have hleft : Tendsto (fun e : ℝ => l-C*e) (𝓝[>] (0 : ℝ)) (𝓝 l) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul he0) using 1 <;> simp
  have hright : Tendsto (fun e : ℝ => l+C*e) (𝓝[>] (0 : ℝ)) (𝓝 l) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul he0) using 1 <;> simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
    (hineq.mono fun _ h => h.1) (hineq.mono fun _ h => h.2)

/-- The manuscript's original quotient limit for the original cycle
growth, with all its original quantified hypotheses. -/
theorem growthAsymptotic : GrowthAsymptotic := by
  intro a l ha ha1 hl hcoef
  have hratio := logGrowth_ratio_limit a l ha ha1 hl hcoef
  have he0 : Tendsto (fun e : ℝ => e) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he2 : Tendsto (fun e : ℝ => e^2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using he0.pow 2
  have hproduct := hratio.mul he2
  have hlog : Tendsto (fun e : ℝ => Real.log (parameterGrowth e a))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have heq : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
        Real.log (parameterGrowth e a)/e^2 * e^2 =
          Real.log (parameterGrowth e a) := by
      filter_upwards [self_mem_nhdsWithin] with e he
      have he' : 0 < e := he
      field_simp [he'.ne']
    convert hproduct.congr' heq using 1 <;> simp
  have hd : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
  have hds : ContinuousAt (dslope Real.exp 0) 0 :=
    continuousAt_dslope_same.mpr hd.differentiableAt
  have hds0 : dslope Real.exp 0 0 = 1 := by rw [dslope_same, hd.deriv]
  have hslope : Tendsto (fun e : ℝ =>
      dslope Real.exp 0 (Real.log (parameterGrowth e a)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def, hds0] using hds.tendsto.comp hlog
  have htarget := hslope.mul hratio
  have heq : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      (parameterGrowth e a-1)/e^2 =
        dslope Real.exp 0 (Real.log (parameterGrowth e a)) *
          (Real.log (parameterGrowth e a)/e^2) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    have hg : 0 < parameterGrowth e a :=
      lt_of_lt_of_le zero_lt_one (parameterGrowth_ge_one e a)
    have hdslope := sub_smul_dslope Real.exp 0
      (Real.log (parameterGrowth e a))
    simp only [zero_add, Real.exp_zero, Real.exp_log hg, sub_zero, smul_eq_mul] at hdslope
    rw [← hdslope]
    ring
  have htarget' : Tendsto (fun e : ℝ =>
      dslope Real.exp 0 (Real.log (parameterGrowth e a)) *
        (Real.log (parameterGrowth e a)/e^2))
      (𝓝[>] (0 : ℝ)) (𝓝 l) := by simpa using htarget
  exact htarget'.congr' (heq.mono fun _ h => h.symm)

end
end Specification
end BilinearSystems
