import BilinearSystems.Coefficient.BranchAtOnset

/-!
# Integral ratio limit
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

private theorem abs_log_tendsto_atTop :
    Tendsto (fun l : ℝ => |Real.log l|) (𝓝[>] (0 : ℝ)) atTop := by
  have hneg : Tendsto (fun l : ℝ => -Real.log l)
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hsmall : ∀ᶠ l : ℝ in 𝓝[>] (0 : ℝ), l ≤ 1 :=
    nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ)<1))
  have heq : (fun l : ℝ => |Real.log l|) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun l => -Real.log l) := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with l hl hpos
    exact abs_of_nonpos (Real.log_nonpos hpos.le hl)
  exact hneg.congr' heq.symm

/-- The direct endpoint ratio tends to 1/pi, with the same coefficient
used later in the inverse onset. -/
theorem coefficientIntegral_ratio_limit :
    Tendsto (fun l : ℝ =>
      (coefficientIntegral l-criticalParameter)/(l*|Real.log l|))
      (𝓝[>] (0 : ℝ)) (𝓝 (1/Real.pi)) := by
  have hL := abs_log_tendsto_atTop
  have hinv : Tendsto (fun l : ℝ => (|Real.log l|)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have herror : Tendsto (fun l : ℝ => 13/(|Real.log l|))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun l : ℝ => 13*(|Real.log l|)⁻¹)
          (𝓝[>] (0 : ℝ)) (𝓝 (13*0)))
  have hsmall : ∀ᶠ l : ℝ in 𝓝[>] (0 : ℝ), 0 < l ∧ l ≤ 1/2 := by
    have hlt : ∀ᶠ l : ℝ in 𝓝[>] (0 : ℝ), l < 1/2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
    filter_upwards [hlt, self_mem_nhdsWithin] with l hlt hpos
    exact ⟨hpos,hlt.le⟩
  have hbounds : ∀ᶠ l : ℝ in 𝓝[>] (0 : ℝ),
      1/Real.pi-13/|Real.log l| ≤
        (coefficientIntegral l-criticalParameter)/(l*|Real.log l|) ∧
      (coefficientIntegral l-criticalParameter)/(l*|Real.log l|) ≤
        1/Real.pi+13/|Real.log l| := by
    filter_upwards [hsmall] with l hl
    have hlogneg : Real.log l < 0 := Real.log_neg hl.1 (by linarith)
    have hLpos : 0 < |Real.log l| := abs_pos.mpr hlogneg.ne
    have hden : 0 < l*|Real.log l| := mul_pos hl.1 hLpos
    have hrem := coefficientIntegral_logarithmic_expansion l hl.1 hl.2
    have heq :
        (coefficientIntegral l-criticalParameter)/(l*|Real.log l|)-1/Real.pi =
        (coefficientIntegral l-criticalParameter-
          (l/Real.pi)*|Real.log l|)/(l*|Real.log l|) := by
      field_simp [hl.1.ne', hLpos.ne']
    have habs :
        |(coefficientIntegral l-criticalParameter)/(l*|Real.log l|)-1/Real.pi| ≤
        13/|Real.log l| := by
      rw [heq, abs_div, abs_of_pos hden]
      calc
        _ ≤ (13*l)/(l*|Real.log l|) :=
          div_le_div_of_nonneg_right hrem hden.le
        _ = 13/|Real.log l| := by field_simp [hl.1.ne', hLpos.ne']
    constructor <;> linarith [abs_le.mp habs]
  have hleft : Tendsto (fun l : ℝ => 1/Real.pi-13/|Real.log l|)
      (𝓝[>] (0 : ℝ)) (𝓝 (1/Real.pi)) := by
    convert tendsto_const_nhds.sub herror using 1 <;> simp
  have hright : Tendsto (fun l : ℝ => 1/Real.pi+13/|Real.log l|)
      (𝓝[>] (0 : ℝ)) (𝓝 (1/Real.pi)) := by
    convert tendsto_const_nhds.add herror using 1 <;> simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

end
end Specification
end BilinearSystems
