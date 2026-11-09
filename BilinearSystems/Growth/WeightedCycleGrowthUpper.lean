import BilinearSystems.Family.GrowthBounds

/-!
# Weighted cycle growth upper
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open scoped BigOperators

/-- The weighted edge bound accumulates with the path length. -/
theorem weighted_path_gain_le (K : Matrix2) (W : State → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hW : ∀ v, UnitDirection v → 0 ≤ W v)
    (hEdge : ∀ v w, UnitDirection v → UnitDirection w →
      |directionGain K v w| * W w ≤ M * W v)
    {n : ℕ} (e : Fin (n+1) → State) (he : ∀ i, UnitDirection (e i)) :
    |indexedPathGain K e| * W (e (Fin.last n)) ≤ M^n * W (e 0) := by
  induction n with
  | zero => simp [indexedPathGain]
  | succ n ih =>
    let tail : Fin (n+1) → State := fun i => e i.succ
    have hsplit : indexedPathGain K e =
        directionGain K (e 0) (tail 0) * indexedPathGain K tail := by
      unfold indexedPathGain
      rw [Fin.prod_univ_succ]
      rfl
    have hlast : tail (Fin.last n) = e (Fin.last (n+1)) := by
      apply congrArg e
      exact Fin.ext rfl
    have htail := ih tail (fun i => he i.succ)
    rw [hlast] at htail
    have hhead := hEdge (e 0) (tail 0) (he 0) (he (Fin.succ 0))
    have hgain : 0 ≤ |directionGain K (e 0) (tail 0)| := abs_nonneg _
    have hp : 0 ≤ M^n := pow_nonneg hM _
    calc
      |indexedPathGain K e| * W (e (Fin.last (n+1))) =
          |directionGain K (e 0) (tail 0)| *
          (|indexedPathGain K tail| * W (e (Fin.last (n+1)))) := by
            rw [hsplit, abs_mul]; ring
      _ ≤ |directionGain K (e 0) (tail 0)| * (M^n * W (tail 0)) :=
        mul_le_mul_of_nonneg_left htail hgain
      _ = M^n * (|directionGain K (e 0) (tail 0)| * W (tail 0)) := by ring
      _ ≤ M^n * (M * W (e 0)) := mul_le_mul_of_nonneg_left hhead hp
      _ = M^(n+1) * W (e 0) := by rw [pow_succ]; ring

/-- A strictly positive weight on unit vectors turns the weighted path
bound into an upper bound on the manuscript's cycle growth. -/
theorem cycleGrowth_le_of_weighted_edge_bound
    (K : Matrix2) (W : State → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hW : ∀ v, UnitDirection v → 0 < W v)
    (hEdge : ∀ v w, UnitDirection v → UnitDirection w →
      |directionGain K v w| * W w ≤ M * W v) :
    cycleGrowth K ≤ M := by
  apply csSup_le (cycleGains_nonempty K)
  rintro _ ⟨n, hn, e, he, hclosed, rfl⟩
  change |indexedPathGain K e| ^ (1 / (n : ℝ)) ≤ M
  have hp := weighted_path_gain_le K W M hM
    (fun v hv => (hW v hv).le) hEdge e he
  rw [hclosed] at hp
  have hfirst := hW (e 0) (he 0)
  have hgain : |indexedPathGain K e| ≤ M^n := by
    exact le_of_mul_le_mul_right hp hfirst
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hc : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hnR.ne']
  calc
    _ ≤ (M^n) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) hgain (one_div_nonneg.mpr hnR.le)
    _ = M := by rw [← Real.rpow_natCast M n, ← Real.rpow_mul hM, hc, Real.rpow_one]

end
end Specification
end BilinearSystems
