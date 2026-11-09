import BilinearSystems.Control.DirectionBridge

/-!
# Transporting negative returns
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem bridge_return_bridge {K : Matrix2} {n : ℕ} {v w : State}
    {a b d : ℝ} (hin : ReversePath K 2 v (a • w))
    (hreturn : ReversePath K n w (b • w))
    (hout : ReversePath K 2 w (d • v)) :
    ReversePath K (2 + (n + 2)) v ((b * (a*d)) • v) := by
  have hmid := hreturn.scale a
  rw [smul_smul] at hmid
  have hlast := hout.scale (a*b)
  rw [smul_smul] at hlast
  have hp := (hin.append hmid).append hlast
  have hmul : a*b*d = b*(a*d) := by ring
  rw [hmul] at hp
  exact hp

/-- A negative return anywhere gives a negative return at every unit base.
The two bridge gains can have either sign. -/
theorem negative_return_at_unit_base (K A : Matrix2)
    (hKA : K*A = 1) (hAK : A*K = 1) {n : ℕ} {w : State} {b : ℝ}
    (hw : UnitDirection w) (hb : b < 0) (hneg : ReversePath K n w (b • w))
    (v : State) (hv : UnitDirection v) :
    ∃ (m : ℕ) (c : ℝ), 0 < m ∧ c < 0 ∧ ReversePath K m v (c • v) := by
  obtain ⟨a, ha, hin⟩ := exists_two_step_reverse_bridge K A hKA hAK v w hv hw
  obtain ⟨d, hd, hout⟩ := exists_two_step_reverse_bridge K A hKA hAK w v hw hv
  rcases lt_or_gt_of_ne (mul_ne_zero ha hd) with hsign | hsign
  · have hnext := hneg.scale b
    rw [smul_smul] at hnext
    have htwice := hneg.append hnext
    exact ⟨2 + (n+n+2), (b*b)*(a*d), by omega,
      mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hb hb) hsign,
      bridge_return_bridge hin htwice hout⟩
  · exact ⟨2 + (n+2), b*(a*d), by omega, mul_neg_of_neg_of_pos hb hsign,
      bridge_return_bridge hin hneg hout⟩

/-- Any negative diagonal gain already gives the negative return required
by the transport lemma. -/
theorem negative_return_of_negative_quadraticForm (K : Matrix2) (x : State)
    (hx : euclideanDot x (K.mulVec x) < 0) :
    ∃ (v : State) (c : ℝ), UnitDirection v ∧ c < 0 ∧ ReversePath K 1 v (c • v) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [euclideanDot] at hx
  obtain ⟨r, hr, v, hv, he⟩ := exists_positive_scale_unitDirection x hx0
  let c := directionGain K v v
  have hform : euclideanDot x (K.mulVec x) = r^2 * c := by
    rw [he, Matrix.mulVec_smul]
    simp only [c, directionGain, euclideanDot, Pi.smul_apply, smul_eq_mul]
    ring
  have hc : c < 0 := by
    by_contra! hn
    exact hx.not_ge (hform ▸ mul_nonneg (sq_nonneg r) hn)
  refine ⟨v, c, hv, hc, ?_⟩
  have hp := reversePath_of_nonzero_gain K v [v] (by simpa using hv) 1
    (by simpa [pathGain, c] using hc.ne)
  simpa [pathGain, pathLast, c] using hp

end
end Specification
end BilinearSystems
