import BilinearSystems.Analysis.ShortAngularEdge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Angular phase
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

theorem angularKernel_linear_combination (epsilon a theta t : ℝ) :
    angularKernel epsilon a theta t =
      (1-epsilon*Real.sin (2*theta))*Real.cos t -
        (epsilon*(a+Real.cos (2*theta)))*Real.sin t := by
  unfold angularKernel
  rw [Real.sin_add]
  ring

theorem angularKernel_shift_pi (epsilon a theta t : ℝ) :
    angularKernel epsilon a theta (t+Real.pi) =
      -angularKernel epsilon a theta t := by
  rw [angularKernel_linear_combination, angularKernel_linear_combination,
    Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- A sine-cosine kernel with positive value at zero is a positive multiple
of one shifted cosine. -/
theorem sineCosine_phase_factorization (p q t : ℝ) (hp : 0 < p) :
    p*Real.cos t-q*Real.sin t =
      (p/Real.cos (Real.arctan (q/p))) *
        Real.cos (t+Real.arctan (q/p)) := by
  let beta := Real.arctan (q/p)
  have hcos : 0 < Real.cos beta :=
    Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo (q/p))
  have htan : Real.sin beta / Real.cos beta = q/p := by
    rw [← Real.tan_eq_sin_div_cos]
    exact Real.tan_arctan (q/p)
  rw [Real.cos_add]
  dsimp [beta] at *
  have hpn : p ≠ 0 := hp.ne'
  field_simp [hcos.ne', hpn] at *
  have hmul := congrArg (fun r : ℝ => r*Real.sin t) htan
  nlinarith [hmul]

/-- The factor multiplying cos(t+beta) is strictly positive. -/
theorem sineCosine_phase_amplitude_pos (p q : ℝ) (hp : 0 < p) :
    0 < p/Real.cos (Real.arctan (q/p)) :=
  div_pos hp (Real.cos_pos_of_mem_Ioo (Real.arctan_mem_Ioo _))

/-- If the phase at both endpoints lies in the positive cosine interval,
then the full intervening segment has positive kernel. -/
theorem sineCosine_positive_segment (p q t : ℝ) (hp : 0 < p)
    (hphase : -(Real.pi/2) < t+Real.arctan (q/p) ∧
      t+Real.arctan (q/p) < Real.pi/2) :
    ∀ x ∈ Icc (min 0 t) (max 0 t), 0 < p*Real.cos x-q*Real.sin x := by
  let beta := Real.arctan (q/p)
  have hb : beta ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    Real.arctan_mem_Ioo _
  intro x hx
  have hbetween : x+beta ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := by
    rcases le_total 0 t with ht | ht
    · rw [min_eq_left ht, max_eq_right ht] at hx
      exact ⟨by linarith [hb.1, hx.1], by linarith [hphase.2, hx.2]⟩
    · rw [min_eq_right ht, max_eq_left ht] at hx
      exact ⟨by linarith [hphase.1, hx.1], by linarith [hb.2, hx.2]⟩
  rw [sineCosine_phase_factorization p q x hp]
  exact mul_pos (sineCosine_phase_amplitude_pos p q hp)
    (Real.cos_pos_of_mem_Ioo hbetween)

/-- Every nonzero cosine phase has a representative in the open positive
half-wave containing zero. The integer shift is retained so that the output
direction and kernel magnitude can later be compared exactly. -/
theorem positivePhase_representative (beta t : ℝ)
    (hcos : Real.cos (t+beta) ≠ 0) :
    ∃ n : ℤ, -(Real.pi/2) < t-(n:ℝ)*Real.pi+beta ∧
      t-(n:ℝ)*Real.pi+beta < Real.pi/2 := by
  let y : ℝ := t+beta+Real.pi/2
  let n : ℤ := ⌊y/Real.pi⌋
  have hlow := Int.sub_floor_div_mul_nonneg y Real.pi_pos
  have hupp := Int.sub_floor_div_mul_lt y Real.pi_pos
  have hphase : t-(n:ℝ)*Real.pi+beta =
      y-(n:ℝ)*Real.pi-Real.pi/2 := by
    dsimp [y]
    ring
  have hcosShift : Real.cos ((t+beta)-(n:ℝ)*Real.pi) ≠ 0 := by
    rw [Real.cos_sub_int_mul_pi]
    exact mul_ne_zero (zpow_ne_zero n (by norm_num)) hcos
  refine ⟨n, ?_, ?_⟩
  · rw [hphase]
    have hnot : y-(n:ℝ)*Real.pi ≠ 0 := by
      intro hz
      apply hcosShift
      have harg : (t+beta)-(n:ℝ)*Real.pi = -Real.pi/2 := by
        dsimp [y] at hz
        linarith
      rw [harg]
      have hneg : -Real.pi/2 = -(Real.pi/2) := by ring
      rw [hneg, Real.cos_neg]
      exact Real.cos_pi_div_two
    change 0 ≤ y-(n:ℝ)*Real.pi at hlow
    rcases lt_or_eq_of_le hlow with hpositive | heq
    · linarith
    · exact (hnot heq.symm).elim
  · rw [hphase]
    change y-(n:ℝ)*Real.pi < Real.pi at hupp
    linarith

/-- A nonzero sine-cosine kernel admits a phase-normalized representative
whose whole segment from zero is positive. -/
theorem sineCosine_positive_representative (p q t : ℝ)
    (hp : 0 < p) (hne : p*Real.cos t-q*Real.sin t ≠ 0) :
    ∃ n : ℤ, ∀ x ∈ Icc (min 0 (t-(n:ℝ)*Real.pi))
        (max 0 (t-(n:ℝ)*Real.pi)),
      0 < p*Real.cos x-q*Real.sin x := by
  let beta := Real.arctan (q/p)
  have hc : Real.cos (t+beta) ≠ 0 := by
    intro hz
    apply hne
    rw [sineCosine_phase_factorization p q t hp, hz, mul_zero]
  obtain ⟨n, hn1, hn2⟩ := positivePhase_representative beta t hc
  refine ⟨n, ?_⟩
  exact sineCosine_positive_segment p q (t-(n:ℝ)*Real.pi) hp ⟨hn1, hn2⟩

end
end Specification
end BilinearSystems
