import BilinearSystems.Coefficient.IntegralRatioLimit

/-!
# Inverse onset
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

private def onsetBranch (d : ℝ) : ℝ :=
  positiveCoefficientBranch (criticalParameter + d)

private theorem onsetBranch_pos :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < onsetBranch d := by
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hdpos : 0 < d := hd
  exact (positiveCoefficientBranch_spec _ (by linarith)).1

private theorem onsetBranch_tendsto_zero :
    Tendsto onsetBranch (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hshift : Tendsto (fun d : ℝ => criticalParameter + d)
      (𝓝[>] (0 : ℝ)) (𝓝[>] criticalParameter) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add
        (tendsto_nhdsWithin_iff.mp (tendsto_id :
          Tendsto (id : ℝ → ℝ) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)))).1)
    · filter_upwards [self_mem_nhdsWithin] with d hd
      have hdpos : 0 < d := hd
      change criticalParameter < criticalParameter + d
      linarith
  exact positiveCoefficientBranch_tendsto_zero.comp hshift

private theorem onsetBranch_tendsto_right :
    Tendsto onsetBranch (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨onsetBranch_tendsto_zero, onsetBranch_pos⟩

/-- The exact direct-ratio estimate transported to the inverse branch. -/
theorem coefficient_inverse_direct_ratio :
    Tendsto (fun d : ℝ =>
      d / (onsetBranch d * |Real.log (onsetBranch d)|))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / Real.pi)) := by
  have hcomp := coefficientIntegral_ratio_limit.comp onsetBranch_tendsto_right
  have heq : (fun d : ℝ =>
      d / (onsetBranch d * |Real.log (onsetBranch d)|)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d => (coefficientIntegral (onsetBranch d)-criticalParameter) /
        (onsetBranch d * |Real.log (onsetBranch d)|)) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hdpos : 0 < d := hd
    have hs := positiveCoefficientBranch_spec _
      (show criticalParameter < criticalParameter+d by linarith)
    have hs' : coefficientIntegral (onsetBranch d) = criticalParameter + d := hs.2
    rw [hs']
    congr 1
    ring
  exact hcomp.congr' (heq.mono fun _ h => h.symm)

private theorem onset_log_magnitude_atTop :
    Tendsto (fun d : ℝ => |Real.log (onsetBranch d)|)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hneg : Tendsto (fun d : ℝ => -Real.log (onsetBranch d))
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_log_nhdsGT_zero.comp onsetBranch_tendsto_right)
  have hlt : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), onsetBranch d < 1 :=
    onsetBranch_tendsto_zero.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have heq : (fun d : ℝ => |Real.log (onsetBranch d)|) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d => -Real.log (onsetBranch d)) := by
    filter_upwards [hlt, onsetBranch_pos] with d hd hpos
    exact abs_of_nonpos (Real.log_nonpos hpos.le hd.le)
  exact hneg.congr' (heq.mono fun _ h => h.symm)

private theorem onset_log_ratio :
    Tendsto (fun d : ℝ =>
      |Real.log d| / |Real.log (onsetBranch d)|)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let L : ℝ → ℝ := fun d => |Real.log (onsetBranch d)|
  let k : ℝ → ℝ := fun d => d / (onsetBranch d * L d)
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) atTop := onset_log_magnitude_atTop
  have hk : Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 (1 / Real.pi)) :=
    coefficient_inverse_direct_ratio
  have hLinv : Tendsto (fun d => (L d)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hlogL : Tendsto (fun d => Real.log (L d) / L d)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hL
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using h
  have hlogk : Tendsto (fun d => Real.log (k d))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (1 / Real.pi))) :=
    (Real.continuousAt_log (by positivity : (1/Real.pi : ℝ) ≠ 0)).tendsto.comp hk
  have hlogkdiv : Tendsto (fun d => Real.log (k d) / L d)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hlogk.mul hLinv using 1 <;> simp [div_eq_mul_inv]
  have htarget : Tendsto (fun d => 1 - Real.log (L d)/L d - Real.log (k d)/L d)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    convert (tendsto_const_nhds.sub hlogL).sub hlogkdiv using 1 <;> simp
  have hsmallD : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have hsmallB : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), onsetBranch d < 1 :=
    onsetBranch_tendsto_zero.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have heq : (fun d : ℝ => |Real.log d| / L d) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d => 1 - Real.log (L d)/L d - Real.log (k d)/L d) := by
    filter_upwards [self_mem_nhdsWithin, hsmallD, onsetBranch_pos, hsmallB]
      with d hd hdsmall hb hbsmall
    have hdpos : 0 < d := hd
    have hLd : 0 < L d := abs_pos.mpr
      (Real.log_neg hb hbsmall).ne
    have hkpos : 0 < k d := div_pos hdpos (mul_pos hb hLd)
    have hmul : d = onsetBranch d * L d * k d := by
      dsimp [k]
      field_simp [hb.ne', hLd.ne']
    have hlog : Real.log d = Real.log (onsetBranch d) +
        Real.log (L d) + Real.log (k d) := by
      calc
        Real.log d = Real.log (onsetBranch d * L d * k d) := congrArg Real.log hmul
        _ = _ := by rw [Real.log_mul (mul_ne_zero hb.ne' hLd.ne') hkpos.ne',
          Real.log_mul hb.ne' hLd.ne']
    have hLeq : L d = -Real.log (onsetBranch d) :=
      abs_of_neg (Real.log_neg hb hbsmall)
    rw [abs_of_neg (Real.log_neg hdpos hdsmall), hlog]
    have hLeq' : Real.log (onsetBranch d) = -L d := by linarith
    rw [hLeq']
    field_simp [hLd.ne']
    ring
  exact htarget.congr' (heq.mono fun _ h => h.symm)

/-- Asymptotic of the positive inverse integral branch at its critical endpoint. -/
theorem positiveCoefficientBranch_logarithmic_onset :
    Tendsto (fun delta : ℝ =>
      positiveCoefficientBranch (criticalParameter+delta) /
        (Real.pi*delta/|Real.log delta|))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hlogratio := onset_log_ratio
  let k : ℝ → ℝ := fun d =>
    d / (onsetBranch d * |Real.log (onsetBranch d)|)
  have hk : Tendsto k (𝓝[>] (0 : ℝ)) (𝓝 (1/Real.pi)) :=
    coefficient_inverse_direct_ratio
  have hfactor : Tendsto (fun d => 1/(Real.pi*k d))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hmul : Tendsto (fun d : ℝ => Real.pi*k d)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi*(1/Real.pi))) :=
      tendsto_const_nhds.mul hk
    have hlim : (Real.pi:ℝ) * (1/Real.pi) = 1 := by
      field_simp [Real.pi_ne_zero]
    have hmul' : Tendsto (fun d : ℝ => Real.pi*k d)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa only [hlim] using hmul
    convert tendsto_const_nhds.div hmul' (by norm_num : (1:ℝ) ≠ 0) using 1 <;>
      norm_num
  have hprod := hlogratio.mul hfactor
  have heq : (fun d : ℝ =>
      positiveCoefficientBranch (criticalParameter+d) /
        (Real.pi*d/|Real.log d|)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d => (|Real.log d|/|Real.log (onsetBranch d)|) *
        (1/(Real.pi*k d))) := by
    have hsmallD : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
    have hsmallB : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), onsetBranch d < 1 :=
      onsetBranch_tendsto_zero.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [self_mem_nhdsWithin, hsmallD, onsetBranch_pos, hsmallB]
      with d hd hdsmall hb hbsmall
    have hdpos : 0 < d := hd
    have hLd : 0 < |Real.log (onsetBranch d)| :=
      abs_pos.mpr (Real.log_neg hb hbsmall).ne
    have hDd : 0 < |Real.log d| :=
      abs_pos.mpr (Real.log_neg hdpos hdsmall).ne
    change onsetBranch d / (Real.pi*d/|Real.log d|) = _
    dsimp [k]
    field_simp [hdpos.ne', hb.ne', hLd.ne', hDd.ne', Real.pi_ne_zero]
  simpa using hprod.congr' (heq.mono fun _ h => h.symm)

/-- Logarithmic onset of the coefficient branch. -/
theorem coefficientLogarithmicOnset : CoefficientLogarithmicOnset :=
  ⟨positiveCoefficientBranch, positiveCoefficientBranch_spec,
    positiveCoefficientBranch_logarithmic_onset⟩

end
end Specification
end BilinearSystems
