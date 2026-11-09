import BilinearSystems.Control.ControllabilityNecessity

/-!
# Expanding cycles and positive returns
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem reversePath_of_indexed_gain (K : Matrix2) {n : ℕ}
    (e : Fin (n+1) → State) (he : ∀ i, UnitDirection (e i))
    (r : ℝ) (hr : r * indexedPathGain K e ≠ 0) :
    ReversePath K n (r • e 0) ((r * indexedPathGain K e) • e (Fin.last n)) := by
  induction n generalizing r with
  | zero =>
    simpa [indexedPathGain] using ReversePath.nil (K := K) (r • e 0)
  | succ n ih =>
    let tail : Fin (n+1) → State := fun i => e i.succ
    have hsplit : indexedPathGain K e =
        directionGain K (e 0) (tail 0) * indexedPathGain K tail := by
      unfold indexedPathGain
      rw [Fin.prod_univ_succ]
      rfl
    have hprod : (r * directionGain K (e 0) (tail 0)) * indexedPathGain K tail ≠ 0 := by
      simpa only [hsplit, mul_assoc] using hr
    have hstep := (reverseStep_scaled_iff K (e 0) (tail 0) (he (0 : Fin (n+1)).succ) r
      (r * directionGain K (e 0) (tail 0)) (left_ne_zero_of_mul hprod)).mpr rfl
    have htail := ih tail (fun i => he i.succ) _ hprod
    have hlast : tail (Fin.last n) = e (Fin.last (n+1)) := by
      apply congrArg e
      exact Fin.ext rfl
    simpa only [hsplit, mul_assoc, hlast] using ReversePath.cons hstep htail

theorem ReversePath.append {K : Matrix2} {n m : ℕ} {x y z : State}
    (h : ReversePath K n x y) (h' : ReversePath K m y z) :
    ReversePath K (m+n) x z := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact ReversePath.cons hs (ih h')

theorem exists_positive_expanding_return (K : Matrix2) (h : 1 < cycleGrowth K) :
    ∃ (n : ℕ) (v : State) (c : ℝ), 0 < n ∧ UnitDirection v ∧ 1 < c ∧
      ∀ r : ℝ, r ≠ 0 → ReversePath K n (r • v) ((r*c) • v) := by
  have hex : ∃ g ∈ CycleGains K, 1 < g := by
    by_contra! hnone
    exact h.not_ge (csSup_le (cycleGains_nonempty K) hnone)
  obtain ⟨_, ⟨n, hn, e, he, hclosed, rfl⟩, hg⟩ := hex
  let d := indexedPathGain K e
  change 1 < Real.rpow |d| (1 / (n : ℝ)) at hg
  have habs : 1 < |d| := by
    by_contra! hh
    have hle := Real.rpow_le_rpow (abs_nonneg d) hh
      (div_nonneg zero_le_one (Nat.cast_nonneg n))
    exact hg.not_ge (by simpa using hle)
  have hd : d ≠ 0 := by intro hd; norm_num [hd] at habs
  have hsq : 1 < d*d := by
    rcases abs_choice d with ha | ha <;> rw [ha] at habs <;>
      nlinarith [sq_nonneg (d-1), sq_nonneg (d+1)]
  refine ⟨n+n, e 0, d*d, Nat.add_pos_left hn _, he 0, hsq, ?_⟩
  intro r hr
  have h1 := reversePath_of_indexed_gain K e he r (mul_ne_zero hr hd)
  have h2 := reversePath_of_indexed_gain K e he (r*d) (mul_ne_zero (mul_ne_zero hr hd) hd)
  rw [hclosed] at h1 h2
  simpa only [mul_assoc] using h1.append h2

/-- Scalar multiplication commutes with the same reverse control. -/
theorem ReverseStep.scale {K : Matrix2} {x y : State}
    (h : ReverseStep K x y) (r : ℝ) : ReverseStep K (r • x) (r • y) := by
  obtain ⟨u, hu⟩ := h
  have hJ : quarterTurn (r • y) = r • quarterTurn y := by
    funext i
    by_cases hi : i = 0 <;>
      simp [quarterTurn, hi, Pi.smul_apply, smul_eq_mul]
  refine ⟨u, ?_⟩
  rw [Matrix.mulVec_smul, hu, smul_add, hJ, smul_comm r u]

theorem ReversePath.scale {K : Matrix2} {n : ℕ} {x y : State}
    (h : ReversePath K n x y) (r : ℝ) : ReversePath K n (r • x) (r • y) := by
  induction h with
  | nil => exact ReversePath.nil _
  | cons hs _ ih => exact ReversePath.cons (hs.scale r) ih

/-- Repeat a return while keeping its length and signed scale explicit. -/
theorem reversePath_repeat_return {K : Matrix2} {n : ℕ} {v : State} {c : ℝ}
    (h : ReversePath K n v (c • v)) (m : ℕ) :
    ReversePath K (m*n) v ((c^m) • v) := by
  induction m with
  | zero => simpa using ReversePath.nil (K := K) v
  | succ m ih =>
    have hnext := h.scale (c^m)
    rw [smul_smul, ← pow_succ] at hnext
    simpa only [Nat.succ_mul, Nat.add_comm] using ih.append hnext

/-- Every finite positive target can be exceeded by a positive-length return. -/
theorem exists_reverse_return_above (K : Matrix2) (h : 1 < cycleGrowth K) :
    ∃ v : State, UnitDirection v ∧ ∀ R : ℝ,
      ∃ (n : ℕ) (c : ℝ), 0 < n ∧ max 1 R < c ∧ ReversePath K n v (c • v) := by
  obtain ⟨n, v, c, hn, hv, hc, hp⟩ := exists_positive_expanding_return K h
  have hreturn : ReversePath K n v (c • v) := by
    simpa using hp 1 one_ne_zero
  refine ⟨v, hv, fun R => ?_⟩
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (max 1 R) hc
  have hmpos : 0 < m := by
    by_contra! hzero
    have he : m = 0 := Nat.eq_zero_of_le_zero hzero
    exact (not_lt_of_ge (le_max_left (1 : ℝ) R)) (by simpa [he] using hm)
  exact ⟨m*n, c^m, Nat.mul_pos hmpos hn, hm, reversePath_repeat_return hreturn m⟩

end
end Specification
end BilinearSystems
