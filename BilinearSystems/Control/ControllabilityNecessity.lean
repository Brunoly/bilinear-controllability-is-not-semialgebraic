import BilinearSystems.Control.DirectionNormalization

/-!
# Controllability implies expanding cycle growth
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private def indexedDirections (v : State) (ws : List State) : Fin (ws.length + 1) → State :=
  match ws with
  | [] => fun _ => v
  | w :: rest => Fin.cases v (indexedDirections w rest)

private theorem indexedDirections_zero (v : State) (ws : List State) :
    indexedDirections v ws 0 = v := by
  cases ws <;> rfl

private theorem indexedDirections_last (v : State) (ws : List State) :
    indexedDirections v ws (Fin.last ws.length) = pathLast v ws := by
  induction ws generalizing v with
  | nil => rfl
  | cons w ws ih => exact ih w

private theorem indexedDirections_unit (v : State) (ws : List State)
    (hv : UnitDirection v) (hw : ∀ w ∈ ws, UnitDirection w) :
    ∀ i, UnitDirection (indexedDirections v ws i) := by
  induction ws generalizing v with
  | nil => intro i; exact hv
  | cons w ws ih =>
    intro i
    refine Fin.cases hv (fun j => ?_) i
    exact ih w (hw w (by simp)) (fun a ha => hw a (List.mem_cons_of_mem w ha)) j

private theorem indexedDirections_gain (K : Matrix2) (v : State) (ws : List State) :
    (∏ i : Fin ws.length,
      directionGain K (indexedDirections v ws i.castSucc) (indexedDirections v ws i.succ)) =
      pathGain K v ws := by
  induction ws generalizing v with
  | nil => simp [pathGain]
  | cons w ws ih =>
    change (∏ i : Fin (ws.length + 1), directionGain K
      (indexedDirections v (w :: ws) i.castSucc)
      (indexedDirections v (w :: ws) i.succ)) = _
    rw [Fin.prod_univ_succ]
    change directionGain K v (indexedDirections w ws 0) * _ = _
    rw [indexedDirections_zero]
    congr 1
    exact ih w

theorem cycleGrowth_gt_one_of_closed_pathGain (K : Matrix2)
    (v : State) (ws : List State) (hv : UnitDirection v)
    (hu : ∀ e ∈ ws, UnitDirection e) (hclosed : pathLast v ws = v)
    (hlen : 0 < ws.length) (hgain : 1 < |pathGain K v ws|) :
    1 < cycleGrowth K := by
  let g := Real.rpow (abs (pathGain K v ws)) (1 / (ws.length : ℝ))
  have hg : g ∈ CycleGains K := by
    refine ⟨ws.length, hlen, indexedDirections v ws, indexedDirections_unit v ws hv hu, ?_, ?_⟩
    · rw [indexedDirections_last, indexedDirections_zero, hclosed]
    · unfold g
      rw [← indexedDirections_gain K v ws]
      rfl
  have hp : 0 < 1 / (ws.length : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hlen)
  have hgt : 1 < g := by
    unfold g
    exact Real.one_lt_rpow hgain hp
  exact hgt.trans_le (le_csSup (cycleGains_bddAbove K) hg)

theorem cycleGrowth_gt_one_of_controllable (K A : Matrix2)
    (hKA : K * A = 1) (hc : GloballyControllable A (A * quarterTurnMatrix)) :
    1 < cycleGrowth K := by
  let v : State := fun i => if i = 0 then 1 else 0
  have hv : UnitDirection v := by norm_num [UnitDirection, euclideanDot, v]
  have hv0 := unitDirection_ne_zero hv
  have hhalf : 0 < (1/2 : ℝ) := by norm_num
  obtain ⟨us, hne, hend⟩ := hc v ((1/2 : ℝ) • v) hv0 (smul_ne_zero hhalf.ne' hv0)
  have hp := controls_to_reversePath K A hKA us v
  rw [hend] at hp
  obtain ⟨ws, hlen, hu, hlast, hg⟩ :=
    directions_of_reversePath hp (1/2) 1 v v hhalf zero_lt_one hv hv rfl (by simp)
  apply cycleGrowth_gt_one_of_closed_pathGain K v ws hv hu hlast
  · rw [hlen]
    exact List.length_pos_iff.mpr hne
  · have ht : pathGain K v ws = 2 := by linarith
    rw [ht]
    norm_num

end
end Specification
end BilinearSystems
