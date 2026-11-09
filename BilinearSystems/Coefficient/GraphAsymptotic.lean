import BilinearSystems.Coefficient.InverseOnset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Graph asymptotic
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

/-- Every positive power of delta dominates every fixed power of its
absolute logarithm at the right endpoint. -/
theorem delta_pow_mul_abs_log_pow_tendsto_zero (r k : ℕ) (hr : 0 < r) :
    Tendsto (fun d : ℝ => d^r * |Real.log d|^k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hrs : (-(r : ℝ)) < 0 := by exact neg_neg_of_pos (Nat.cast_pos.mpr hr)
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) hrs).tendsto_div_nhds_zero
  have heq : (fun d : ℝ => d^r * |Real.log d|^k) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d : ℝ => |Real.log d| ^ (k : ℝ) / d ^ (-(r : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hdpos : 0 < d := hd
    rw [Real.rpow_natCast, Real.rpow_neg hdpos.le, Real.rpow_natCast]
    field_simp [pow_ne_zero _ hdpos.ne']
  exact h.congr' (heq.mono fun _ hd => hd.symm)

/-- Logarithmic onset in the form used for monomial limits. -/
theorem positiveCoefficientBranch_scaled_limit :
    Tendsto (fun d : ℝ =>
      positiveCoefficientBranch (criticalParameter+d) * |Real.log d| / d)
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
  have h := positiveCoefficientBranch_logarithmic_onset
  have hp : Tendsto (fun d : ℝ =>
      Real.pi * (positiveCoefficientBranch (criticalParameter+d) /
        (Real.pi*d/|Real.log d|)))
      (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) := by
    convert tendsto_const_nhds.mul h using 1 <;> ring
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  have heq : (fun d : ℝ =>
      positiveCoefficientBranch (criticalParameter+d) * |Real.log d| / d) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun d => Real.pi * (positiveCoefficientBranch (criticalParameter+d) /
        (Real.pi*d/|Real.log d|))) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with d hd hs
    have hdpos : 0 < d := hd
    have hLpos : 0 < |Real.log d| := abs_pos.mpr
      (Real.log_neg hdpos hs).ne
    field_simp [hdpos.ne', hLpos.ne', Real.pi_ne_zero]
  exact hp.congr' (heq.mono fun _ h => h.symm)

/-- The reciprocal logarithm vanishes to any fixed positive power. -/
theorem inv_abs_log_pow_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun d : ℝ => (|Real.log d|)⁻¹ ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have htop : Tendsto (fun d : ℝ => |Real.log d|)
      (𝓝[>] (0 : ℝ)) atTop := by
    have hneg : Tendsto (fun d : ℝ => -Real.log d)
        (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [Function.comp_def] using
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d ≤ 1 :=
      nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ)<1))
    have heq : (fun d : ℝ => |Real.log d|) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun d => -Real.log d) := by
      filter_upwards [hsmall, self_mem_nhdsWithin] with d hs hd
      exact abs_of_nonpos (Real.log_nonpos (le_of_lt hd) hs)
    exact hneg.congr' (heq.mono fun _ h => h.symm)
  have h := (tendsto_inv_atTop_zero.comp htop).pow k
  simpa [zero_pow hk.ne'] using h

end
end Specification
end BilinearSystems
