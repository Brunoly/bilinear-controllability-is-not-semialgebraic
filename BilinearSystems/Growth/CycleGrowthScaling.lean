import BilinearSystems.Control.ExpandingReturn

namespace BilinearSystems
namespace Specification
noncomputable section

theorem directionGain_smul (k : ℝ) (K : Matrix2) (v w : State) :
    directionGain (k • K) v w = k * directionGain K v w := by
  simp only [directionGain, Matrix.smul_mulVec, euclideanDot, Pi.smul_apply, smul_eq_mul]
  ring

theorem indexedPathGain_smul (k : ℝ) (K : Matrix2) {n : ℕ} (e : Fin (n+1) → State) :
    indexedPathGain (k • K) e = k^n * indexedPathGain K e := by
  simp [indexedPathGain, directionGain_smul, Finset.prod_mul_distrib]

private theorem geometricMean_smul (k : ℝ) (hk : 0 < k) (K : Matrix2) {n : ℕ}
    (hn : 0 < n) (e : Fin (n+1) → State) :
    |indexedPathGain (k • K) e| ^ (1 / (n : ℝ)) =
      k * |indexedPathGain K e| ^ (1 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hnR.ne']
  rw [indexedPathGain_smul, abs_mul, abs_of_nonneg (pow_nonneg hk.le n),
    Real.mul_rpow (pow_nonneg hk.le n) (abs_nonneg _),
    ← Real.rpow_natCast k n, ← Real.rpow_mul hk.le, hcancel, Real.rpow_one]

/-- Positive homogeneity, for the positive threshold parameter s. -/
theorem cycleGrowth_smul_of_pos (K : Matrix2) (k : ℝ) (hk : 0 < k) :
    cycleGrowth (k • K) = k * cycleGrowth K := by
  have heq : CycleGains (k • K) = (fun g => k*g) '' CycleGains K := by
    ext g
    constructor
    · rintro ⟨n, hn, e, he, hl, hg⟩
      let a := |indexedPathGain K e| ^ (1 / (n : ℝ))
      refine ⟨a, ⟨n, hn, e, he, hl, rfl⟩, ?_⟩
      exact (geometricMean_smul k hk K hn e).symm.trans hg.symm
    · rintro ⟨a, ⟨n, hn, e, he, hl, ha⟩, rfl⟩
      refine ⟨n, hn, e, he, hl, ?_⟩
      exact (congrArg (k * ·) ha).trans (geometricMean_smul k hk K hn e).symm
  unfold cycleGrowth
  apply le_antisymm
  · apply csSup_le (cycleGains_nonempty _)
    rw [heq]
    rintro _ ⟨g, hg, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup (cycleGains_bddAbove K) hg) hk.le
  · apply (le_div_iff₀' hk).mp
    apply csSup_le (cycleGains_nonempty K)
    intro g hg
    apply (le_div_iff₀' hk).mpr
    exact le_csSup (cycleGains_bddAbove _) (heq.symm ▸ ⟨g, hg, rfl⟩)

/-- The zero matrix has zero closed-cycle growth. -/
theorem cycleGrowth_zero : cycleGrowth (0 : Matrix2) = 0 := by
  have h := cycleGrowth_smul_of_pos (0 : Matrix2) 2 (by norm_num)
  simp only [smul_zero] at h
  linarith

/-- Absolute homogeneity for every real scalar, including zero and negatives. -/
theorem cycleGrowth_smul (K : Matrix2) (k : ℝ) :
    cycleGrowth (k • K) = |k| * cycleGrowth K := by
  have hsame : CycleGains (k • K) = CycleGains (|k| • K) := by
    ext r
    constructor
    · rintro ⟨n, hn, e, he, hl, hr⟩
      refine ⟨n, hn, e, he, hl, ?_⟩
      change r = |indexedPathGain (|k| • K) e| ^ (1 / (n : ℝ))
      change r = |indexedPathGain (k • K) e| ^ (1 / (n : ℝ)) at hr
      simpa only [indexedPathGain_smul, abs_mul, abs_pow, abs_abs] using hr
    · rintro ⟨n, hn, e, he, hl, hr⟩
      refine ⟨n, hn, e, he, hl, ?_⟩
      change r = |indexedPathGain (k • K) e| ^ (1 / (n : ℝ))
      change r = |indexedPathGain (|k| • K) e| ^ (1 / (n : ℝ)) at hr
      simpa only [indexedPathGain_smul, abs_mul, abs_pow, abs_abs] using hr
  by_cases hk : k = 0
  · subst k
    simp only [zero_smul, cycleGrowth_zero, abs_zero, zero_mul]
  · have hg : cycleGrowth (k • K) = cycleGrowth (|k| • K) := by
      exact congrArg sSup hsame
    rw [hg, cycleGrowth_smul_of_pos K |k| (abs_pos.mpr hk)]

end
end Specification
end BilinearSystems
