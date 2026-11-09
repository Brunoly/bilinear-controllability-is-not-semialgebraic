import BilinearSystems.Control.FinitePathClosingDirection
import BilinearSystems.Family.GrowthBounds

/-!
# Finite path cycle closure
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open scoped BigOperators

theorem indexedPathGain_snoc (K : Matrix2) {n : ℕ}
    (e : Fin (n+1) → State) (f : State) :
    indexedPathGain K (Fin.snoc e f) =
      indexedPathGain K e * directionGain K (e (Fin.last n)) f := by
  unfold indexedPathGain
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    have hidx : (i.castSucc).succ = (i.succ).castSucc := Fin.ext rfl
    rw [hidx]
    simp only [Fin.snoc_castSucc]
  · have hidx : (Fin.last n).succ = Fin.last (n+1) := Fin.ext rfl
    rw [hidx]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem unitDirection_snoc {n : ℕ} (e : Fin n → State)
    (he : ∀ i, UnitDirection (e i)) (f : State) (hf : UnitDirection f) :
    ∀ i, UnitDirection ((Fin.snoc e f : Fin (n+1) → State) i) := by
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc] using he j
  · simpa only [Fin.snoc_last] using hf

/-- A finite path plus the two closing edges belongs to the precise
cycle set, at length n+2. -/
theorem closed_path_gain_mem_cycleGains (K : Matrix2) {n : ℕ}
    (e : Fin (n+1) → State) (he : ∀ i, UnitDirection (e i))
    (f : State) (hf : UnitDirection f) :
    Real.rpow
      |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0)|
      (1 / ((n+2 : ℕ) : ℝ)) ∈ CycleGains K := by
  let c : Fin (n+2+1) → State := Fin.snoc (Fin.snoc e f) (e 0)
  have hc : ∀ i, UnitDirection (c i) := by
    apply unitDirection_snoc
    · exact unitDirection_snoc e he f hf
    · exact he 0
  have hclosed : c (Fin.last (n+2)) = c 0 := by
    simp [c, Fin.snoc_last, Fin.snoc_castSucc]
  have hgain : indexedPathGain K c =
      indexedPathGain K e * directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0) := by
    rw [indexedPathGain_snoc, indexedPathGain_snoc]
    simp [c, Fin.snoc_last, Fin.snoc_castSucc]
  refine ⟨n+2, by omega, c, hc, hclosed, ?_⟩
  change Real.rpow
    |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
      directionGain K f (e 0)|
    (1 / ((n+2 : ℕ) : ℝ)) =
    Real.rpow |indexedPathGain K c| (1 / ((n+2 : ℕ) : ℝ))
  rw [hgain]

/-- An endpoint-weighted finite-path bound from actual cycle gains.
No positivity or invertibility of K is assumed at this stage. -/
theorem finite_path_gain_growth_bound (K : Matrix2) {n : ℕ}
    (e : Fin (n+1) → State) (he : ∀ i, UnitDirection (e i)) :
    |indexedPathGain K e| *
      (planarLength (K.transpose.mulVec (e 0)) *
        planarLength (K.mulVec (e (Fin.last n))) / 2) ≤
      (cycleGrowth K)^(n+2) := by
  obtain ⟨f,hf,hclose⟩ := finite_path_closing_direction K e
  have hmem := closed_path_gain_mem_cycleGains K e he f hf
  have hsup : Real.rpow
      |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0)|
      (1 / ((n+2 : ℕ) : ℝ)) ≤ cycleGrowth K :=
    le_csSup (cycleGains_bddAbove K) hmem
  have hgamma : 0 ≤ cycleGrowth K := by
    have hnonneg : 0 ≤ Real.rpow
        |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
          directionGain K f (e 0)|
        (1 / ((n+2 : ℕ) : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    exact hnonneg.trans hsup
  have hn : 0 < ((n+2 : ℕ) : ℝ) := by positivity
  have hproduct :
      |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
        directionGain K f (e 0)| ≤ (cycleGrowth K)^(n+2) := by
    change |indexedPathGain K e * directionGain K (e (Fin.last n)) f *
      directionGain K f (e 0)| ^ (1 / ((n+2 : ℕ) : ℝ)) ≤ cycleGrowth K at hsup
    have h := (Real.rpow_inv_le_iff_of_pos
      (abs_nonneg _) hgamma hn).mp (by simpa only [one_div] using hsup)
    simpa only [Real.rpow_natCast] using h
  exact hclose.trans hproduct

end
end Specification
end BilinearSystems
