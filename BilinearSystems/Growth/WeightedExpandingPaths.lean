import BilinearSystems.Growth.PerturbationPathGrowthBound

/-!
# Weighted expanding paths
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- A positive one-step weighted expansion produces a finite path of
arbitrary length with the corresponding product inequality. -/
theorem weighted_expanding_path (K : Matrix2) (W : State → ℝ)
    (m : ℝ) (hm : 0 ≤ m)
    (hW : ∀ v, UnitDirection v → 0 ≤ W v)
    (hStep : ∀ v, UnitDirection v → ∃ w, UnitDirection w ∧
      m*W v ≤ |directionGain K v w| *W w)
    (v₀ : State) (hv₀ : UnitDirection v₀) (n : ℕ) :
    ∃ e : Fin (n+1) → State,
      e 0 = v₀ ∧ (∀ i, UnitDirection (e i)) ∧
      m^n*W v₀ ≤ |indexedPathGain K e| *W (e (Fin.last n)) := by
  induction n with
  | zero =>
    refine ⟨fun _ => v₀, rfl, fun _ => hv₀, ?_⟩
    simp [indexedPathGain]
  | succ n ih =>
    obtain ⟨e,he0,he,hgain⟩ := ih
    obtain ⟨w,hw,hstep⟩ := hStep (e (Fin.last n)) (he (Fin.last n))
    let e' : Fin (n+1+1) → State := Fin.snoc e w
    refine ⟨e', ?_, ?_, ?_⟩
    · simpa [e', Fin.snoc_apply_zero] using he0
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
      · simpa only [e', Fin.snoc_castSucc] using he j
      · simpa only [e', Fin.snoc_last] using hw
    · have hsplit : indexedPathGain K e' =
          indexedPathGain K e * directionGain K (e (Fin.last n)) w :=
        indexedPathGain_snoc K e w
      have hlast : e' (Fin.last (n+1)) = w := by simp [e', Fin.snoc_last]
      rw [hsplit, hlast, abs_mul]
      have hgainNonneg : 0 ≤ |indexedPathGain K e| := abs_nonneg _
      have hmPow : 0 ≤ m^n := pow_nonneg hm _
      calc
        m^(n+1)*W v₀ = m*(m^n*W v₀) := by rw [pow_succ]; ring
        _ ≤ m*(|indexedPathGain K e| *W (e (Fin.last n))) :=
          mul_le_mul_of_nonneg_left hgain hm
        _ ≤ |indexedPathGain K e| *
          (|directionGain K (e (Fin.last n)) w| *W w) := by
            calc
              _ = |indexedPathGain K e| *(m*W (e (Fin.last n))) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hstep hgainNonneg
        _ = (|indexedPathGain K e| *|directionGain K (e (Fin.last n)) w|)*W w := by ring

end
end Specification
end BilinearSystems
