import BilinearSystems.Control.DirectionNormalization

/-!
# Avoiding two planar kernels
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Euclidean length in the coordinates used throughout this project. -/
def planarLength (v : State) : ℝ := Real.sqrt (euclideanDot v v)

theorem planarLength_nonneg (v : State) : 0 ≤ planarLength v := Real.sqrt_nonneg _

theorem planarLength_pos {v : State} (hv : v ≠ 0) : 0 < planarLength v :=
  Real.sqrt_pos.mpr (euclideanDot_self_pos v hv)

private theorem dot_add_self (u v : State) :
    euclideanDot (u+v) (u+v) =
      euclideanDot u u + 2*euclideanDot u v + euclideanDot v v := by
  simp [euclideanDot, Pi.add_apply]
  ring

private theorem dot_add_left (u v w : State) :
    euclideanDot (u+v) w = euclideanDot u w + euclideanDot v w := by
  simp [euclideanDot, Pi.add_apply]
  ring

private theorem dot_add_right (u v w : State) :
    euclideanDot u (v+w) = euclideanDot u v + euclideanDot u w := by
  simp [euclideanDot, Pi.add_apply]
  ring

private theorem dot_smul_left (r : ℝ) (u v : State) :
    euclideanDot (r • u) v = r*euclideanDot u v := by
  simp [euclideanDot, Pi.smul_apply, smul_eq_mul]
  ring

private theorem dot_smul_right (r : ℝ) (u v : State) :
    euclideanDot u (r • v) = r*euclideanDot u v := by
  simp [euclideanDot, Pi.smul_apply, smul_eq_mul]
  ring

private theorem dot_comm (u v : State) : euclideanDot u v = euclideanDot v u := by
  simp [euclideanDot]
  ring

/-- Normalized positive-dot case of the two-linear-forms lemma. -/
theorem two_linear_forms_unit_nonnegative (u v : State)
    (hu : UnitDirection u) (hv : UnitDirection v)
    (hd : 0 ≤ euclideanDot u v) :
    ∃ f : State, UnitDirection f ∧
      1/2 ≤ |(euclideanDot u f)*(euclideanDot f v)| := by
  let z := u+v
  have hz : z ≠ 0 := by
    intro h
    have hdot : euclideanDot z z = 0 := by rw [h]; simp [euclideanDot]
    rw [dot_add_self] at hdot
    change euclideanDot u u = 1 at hu
    change euclideanDot v v = 1 at hv
    linarith
  obtain ⟨r, hr, f, hf, hfz⟩ := exists_positive_scale_unitDirection z hz
  have hru : euclideanDot u z = r*euclideanDot u f := by
    rw [hfz, dot_smul_right]
  have hrv : euclideanDot z v = r*euclideanDot f v := by
    rw [hfz, dot_smul_left]
  have hr2 : r^2 = 2+2*euclideanDot u v := by
    have hdot : euclideanDot z z = r^2 := by
      rw [hfz, dot_smul_left, dot_smul_right]
      change euclideanDot f f = 1 at hf
      rw [hf]
      ring
    rw [dot_add_self] at hdot
    change euclideanDot u u = 1 at hu
    change euclideanDot v v = 1 at hv
    linarith
  have huf : r*euclideanDot u f = 1+euclideanDot u v := by
    rw [← hru, dot_add_right]
    change euclideanDot u u = 1 at hu
    rw [hu]
  have hfv : r*euclideanDot f v = 1+euclideanDot u v := by
    rw [← hrv, dot_add_left]
    change euclideanDot v v = 1 at hv
    rw [hv]
    ring
  refine ⟨f, hf, ?_⟩
  have hprod : (euclideanDot u f)*(euclideanDot f v) =
      (1+euclideanDot u v)/2 := by
    have hrr : r ≠ 0 := hr.ne'
    have hratio : (1+euclideanDot u v)^2 =
        r^2 * ((euclideanDot u f)*(euclideanDot f v)) := by
      nlinarith [mul_self_nonneg (r*euclideanDot u f - r*euclideanDot f v)]
    nlinarith [sq_pos_of_pos hr]
  rw [hprod, abs_of_nonneg (by linarith)]
  linarith

/-- The sign of one unit vector can be chosen to make the dot product
nonnegative; the absolute product is unaffected. -/
theorem two_linear_forms_unit (u v : State)
    (hu : UnitDirection u) (hv : UnitDirection v) :
    ∃ f : State, UnitDirection f ∧
      1/2 ≤ |(euclideanDot u f)*(euclideanDot f v)| := by
  by_cases hd : 0 ≤ euclideanDot u v
  · exact two_linear_forms_unit_nonnegative u v hu hv hd
  · have hvneg : UnitDirection (-v) := by
      change euclideanDot (-v) (-v) = 1
      simpa [UnitDirection, euclideanDot, Pi.neg_apply] using hv
    have hdneg : 0 ≤ euclideanDot u (-v) := by
      simp [euclideanDot, Pi.neg_apply] at hd ⊢
      linarith
    obtain ⟨f,hf,hbound⟩ :=
      two_linear_forms_unit_nonnegative u (-v) hu hvneg hdneg
    refine ⟨f,hf,?_⟩
    have hdot : euclideanDot f (-v) = -euclideanDot f v := by
      simp [euclideanDot, Pi.neg_apply]
      ring
    rw [hdot, mul_neg, abs_neg] at hbound
    exact hbound

private theorem planarLength_unit_scale (r : ℝ) (u : State)
    (hr : 0 < r) (hu : UnitDirection u) :
    planarLength (r • u) = r := by
  have hd : euclideanDot (r • u) (r • u) = r^2 := by
    rw [dot_smul_left, dot_smul_right]
    change euclideanDot u u = 1 at hu
    rw [hu]
    ring
  rw [planarLength, hd, Real.sqrt_sq_eq_abs, abs_of_pos hr]

/-- A unit direction gives a lower bound for the product of two linear forms. -/
theorem two_linear_forms (p q : State) :
    ∃ f : State, UnitDirection f ∧
      planarLength p * planarLength q / 2 ≤
        |(euclideanDot p f)*(euclideanDot f q)| := by
  by_cases hp : p = 0
  · let f : State := fun i => if i = 0 then 1 else 0
    refine ⟨f, by norm_num [f, UnitDirection, euclideanDot], ?_⟩
    simp [hp, planarLength, euclideanDot]
  by_cases hq : q = 0
  · let f : State := fun i => if i = 0 then 1 else 0
    refine ⟨f, by norm_num [f, UnitDirection, euclideanDot], ?_⟩
    simp [hq, planarLength, euclideanDot]
  obtain ⟨rp,hrp,u,hu,hpu⟩ := exists_positive_scale_unitDirection p hp
  obtain ⟨rq,hrq,v,hv,hqv⟩ := exists_positive_scale_unitDirection q hq
  obtain ⟨f,hf,hbound⟩ := two_linear_forms_unit u v hu hv
  refine ⟨f,hf,?_⟩
  have hlenp : planarLength p = rp := by
    rw [hpu]
    exact planarLength_unit_scale rp u hrp hu
  have hlenq : planarLength q = rq := by
    rw [hqv]
    exact planarLength_unit_scale rq v hrq hv
  have hdotp : euclideanDot p f = rp*euclideanDot u f := by
    rw [hpu, dot_smul_left]
  have hdotq : euclideanDot f q = rq*euclideanDot f v := by
    rw [hqv, dot_smul_right]
  rw [hlenp, hlenq, hdotp, hdotq]
  have hscale : 0 ≤ rp*rq := mul_nonneg hrp.le hrq.le
  calc
    rp*rq/2 = (rp*rq)*(1/2) := by ring
    _ ≤ (rp*rq)*|(euclideanDot u f)*(euclideanDot f v)| :=
      mul_le_mul_of_nonneg_left hbound hscale
    _ = |(rp*rq)*((euclideanDot u f)*(euclideanDot f v))| := by
      simp only [abs_mul, abs_of_nonneg hscale]
    _ = |(rp*euclideanDot u f)*(rq*euclideanDot f v)| := by
      congr 1
      ring

end
end Specification
end BilinearSystems
