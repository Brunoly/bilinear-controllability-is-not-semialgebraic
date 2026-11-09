import BilinearSystems.Control.CanonicalTrajectory

/-!
# Normalization to Euclidean unit directions
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem exists_positive_scale_unitDirection (x : State) (hx : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ e : State, UnitDirection e ∧ x = r • e := by
  let r := Real.sqrt (euclideanDot x x)
  have hp := euclideanDot_self_pos x hx
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hsq : r ^ 2 = euclideanDot x x := Real.sq_sqrt hp.le
  refine ⟨r, hr, r⁻¹ • x, ?_, ?_⟩
  · change euclideanDot (r⁻¹ • x) (r⁻¹ • x) = 1
    simp only [euclideanDot, Pi.smul_apply, smul_eq_mul] at hsq ⊢
    field_simp [hr.ne']
    nlinarith
  · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem ReverseStep.source_ne_zero {K : Matrix2} {y x : State}
    (h : ReverseStep K y x) (hx : x ≠ 0) : y ≠ 0 := by
  rintro rfl
  have hd := (exists_control_iff_euclidean_constraint x (K.mulVec 0) hx).mp h
  have hp := euclideanDot_self_pos x hx
  simp [euclideanDot] at hd
  exact hp.ne' hd.symm

theorem ReversePath.source_ne_zero {K : Matrix2} {n : ℕ} {y x : State}
    (h : ReversePath K n y x) (hx : x ≠ 0) : y ≠ 0 := by
  induction h with
  | nil => exact hx
  | cons hs _ ih => exact hs.source_ne_zero (ih hx)

private theorem positive_unit_scale_unique {v w : State} {r t : ℝ}
    (hv : UnitDirection v) (hw : UnitDirection w) (hr : 0 < r) (ht : 0 < t)
    (h : r • v = t • w) : r = t ∧ v = w := by
  have hs (q : ℝ) (e : State) (he : UnitDirection e) :
      euclideanDot (q • e) (q • e) = q^2 := by
    change euclideanDot e e = 1 at he
    calc
      _ = q^2 * euclideanDot e e := by
        simp only [euclideanDot, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [he, mul_one]
  have hsq : r^2 = t^2 := by
    rw [← hs r v hv, ← hs t w hw, h]
  have hrt : r = t := by
    have hzero : (r-t)*(r+t) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (add_pos hr ht).ne')
  subst t
  refine ⟨rfl, ?_⟩
  have hi := congrArg (fun e : State => r⁻¹ • e) h
  simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using hi

/-- Prescribed positive scales and unit directions at both endpoints.
The list contains one direction per reverse edge. -/
theorem directions_of_reversePath {K : Matrix2} {n : ℕ} {x y : State}
    (h : ReversePath K n x y) :
    ∀ (r t : ℝ) (v w : State), 0 < r → 0 < t →
      UnitDirection v → UnitDirection w → x = r • v → y = t • w →
      ∃ ws : List State, ws.length = n ∧ (∀ e ∈ ws, UnitDirection e) ∧
        pathLast v ws = w ∧ t = r * pathGain K v ws := by
  induction h with
  | nil x =>
    intro r t v w hr ht hv hw hx hy
    obtain ⟨hrt, hvw⟩ := positive_unit_scale_unique hv hw hr ht (hx.symm.trans hy)
    exact ⟨[], rfl, by simp, hvw, by simpa [pathGain] using hrt.symm⟩
  | @cons n x y z hs hp ih =>
    intro r t v w hr ht hv hw hx hz
    have hz0 : z ≠ 0 := hz ▸ smul_ne_zero ht.ne' (unitDirection_ne_zero hw)
    obtain ⟨q, hq, e, he, hy⟩ :=
      exists_positive_scale_unitDirection y (hp.source_ne_zero hz0)
    have hs' : ReverseStep K (r • v) (q • e) := by simpa only [← hx, ← hy] using hs
    have hqeq := (reverseStep_scaled_iff K v e he r q hq.ne').mp hs'
    obtain ⟨ws, hlen, hu, hlast, hgain⟩ := ih q t e w hq ht he hw hy hz
    refine ⟨e :: ws, by simp [hlen], ?_, hlast, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact he
      · exact hu a ha
    · simpa only [hqeq, pathGain, mul_assoc] using hgain

end
end Specification
end BilinearSystems
