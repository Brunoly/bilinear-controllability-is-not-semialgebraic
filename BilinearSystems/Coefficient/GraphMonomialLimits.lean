import BilinearSystems.Coefficient.GraphMonomialAlgebra

/-!
# Graph monomial limits
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

def branchNearOnset (d : ℝ) : ℝ :=
  positiveCoefficientBranch (criticalParameter+d)

def logMagnitude (d : ℝ) : ℝ := |Real.log d|

private theorem nearOnset_side_conditions :
    ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      d ≠ 0 ∧ logMagnitude d ≠ 0 := by
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [self_mem_nhdsWithin, hsmall] with d hd hs
  have hdpos : 0 < d := hd
  exact ⟨hdpos.ne', (abs_pos.mpr (Real.log_neg hdpos hs).ne).ne'⟩

/-- For j at least j0, the normalized monomial has the predicted
product limit. The exponent gap may be zero. -/
theorem normalized_coefficient_monomial_ge_limit
    (i j m j₀ : ℕ) (hdeg : m ≤ i+j) (hj : j₀ ≤ j) :
    Tendsto (fun d : ℝ =>
      d^i * (branchNearOnset d)^j / (d^m/(logMagnitude d)^j₀))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.pi)^j * (0:ℝ)^(i+j-m) * (0:ℝ)^(j-j₀))) := by
  have hscale : Tendsto (fun d : ℝ =>
      (branchNearOnset d * logMagnitude d / d)^j)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi^j)) :=
    positiveCoefficientBranch_scaled_limit.pow j
  have hd : Tendsto (fun d : ℝ => d^(i+j-m))
      (𝓝[>] (0 : ℝ)) (𝓝 ((0:ℝ)^(i+j-m))) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).pow _
  have hL : Tendsto (fun d : ℝ => (logMagnitude d)⁻¹ ^ (j-j₀))
      (𝓝[>] (0 : ℝ)) (𝓝 ((0:ℝ)^(j-j₀))) := by
    by_cases hs : j-j₀=0
    · simpa [hs] using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1))
    · have hspos : 0 < j-j₀ := Nat.pos_of_ne_zero hs
      simpa [logMagnitude, hs] using
        inv_abs_log_pow_tendsto_zero (j-j₀) hspos
  have hprod := (hscale.mul hd).mul hL
  have heq : (fun d : ℝ =>
      d^i * (branchNearOnset d)^j / (d^m/(logMagnitude d)^j₀)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d : ℝ => (branchNearOnset d*logMagnitude d/d)^j *
        d^(i+j-m) * (logMagnitude d)⁻¹ ^ (j-j₀)) := by
    filter_upwards [nearOnset_side_conditions] with d hside
    have hdeg' : i+j=m+(i+j-m) := by omega
    have hj' : j=j₀+(j-j₀) := by omega
    rw [normalized_monomial_ge d (branchNearOnset d) (logMagnitude d)
      hside.1 hside.2 i j m j₀ (i+j-m) (j-j₀) hdeg' hj']
    simp only [div_eq_mul_inv, inv_pow]
  exact hprod.congr' (heq.mono fun _ h => h.symm)

/-- For j below j0, every higher-total-degree monomial vanishes after
normalization; this is the case requiring delta^r*|log delta|^k -> 0. -/
theorem normalized_coefficient_monomial_lt_limit
    (i j m j₀ : ℕ) (hdeg : m < i+j) (hj : j < j₀) :
    Tendsto (fun d : ℝ =>
      d^i * (branchNearOnset d)^j / (d^m/(logMagnitude d)^j₀))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hr : 0 < i+j-m := by omega
  have hs : 0 < j₀-j := by omega
  have hscale : Tendsto (fun d : ℝ =>
      (branchNearOnset d * logMagnitude d / d)^j)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi^j)) :=
    positiveCoefficientBranch_scaled_limit.pow j
  have hsmall := delta_pow_mul_abs_log_pow_tendsto_zero (i+j-m) (j₀-j) hr
  have hprod := hscale.mul hsmall
  have heq : (fun d : ℝ =>
      d^i * (branchNearOnset d)^j / (d^m/(logMagnitude d)^j₀)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d : ℝ => (branchNearOnset d*logMagnitude d/d)^j *
        (d^(i+j-m) * (logMagnitude d)^(j₀-j))) := by
    filter_upwards [nearOnset_side_conditions] with d hside
    have hdeg' : i+j=m+(i+j-m) := by omega
    have hj' : j₀=j+(j₀-j) := by omega
    rw [normalized_monomial_lt d (branchNearOnset d) (logMagnitude d)
      hside.1 hside.2 i j m j₀ (i+j-m) (j₀-j) hdeg' hj']
    ring
  simpa [logMagnitude, mul_zero] using hprod.congr' (heq.mono fun _ h => h.symm)

end
end Specification
end BilinearSystems
