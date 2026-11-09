import BilinearSystems.Control.PerturbationReturn
import BilinearSystems.Control.SmallReturns

/-!
# From expanding cycles to global controllability
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- The only sign input is a negative return at each unit base.
It is supplied below for the explicit perturbation family. -/
theorem controllable_of_cycleGrowth_of_negative_returns (K A : Matrix2)
    (hKA : K*A = 1) (hAK : A*K = 1) (hG : 1 < cycleGrowth K)
    (hneg : ∀ v : State, UnitDirection v → ∃ (n : ℕ) (b : ℝ),
      b < 0 ∧ ReversePath K n v (b • v)) :
    GloballyControllable A (A * quarterTurnMatrix) := by
  obtain ⟨v, hv, hlarge⟩ := exists_reverse_return_above K hG
  obtain ⟨d, hd, hsmall⟩ := exists_interval_of_positive_returns K A hKA hAK v hv
  have hpos : ∀ c : ℝ, 0 < c → ∃ n : ℕ, ReversePath K n v (c • v) := by
    intro c hc
    obtain ⟨n, p, _, hp, hpath⟩ := hlarge (c/d)
    have hp0 : 0 < p := zero_lt_one.trans ((le_max_left _ _).trans_lt hp)
    have hcp : c/p ≤ d := by
      apply (div_le_iff₀ hp0).2
      have hh := (div_lt_iff₀ hd).1 ((le_max_right _ _).trans_lt hp)
      linarith
    have hscale := (hsmall (c/p) (div_pos hc hp0) hcp).scale p
    rw [smul_smul] at hscale
    have hm : p * (c/p) = c := by field_simp
    rw [hm] at hscale
    exact ⟨_, hpath.append hscale⟩
  have hsigned : ∀ c : ℝ, c ≠ 0 → ∃ n : ℕ, ReversePath K n v (c • v) := by
    intro c hc
    rcases lt_or_gt_of_ne hc with hcn | hcp
    · obtain ⟨m, b, hb, hpath⟩ := hneg v hv
      obtain ⟨n, hp⟩ := hpos (c/b) (div_pos_of_neg_of_neg hcn hb)
      have hscale := hp.scale b
      rw [smul_smul] at hscale
      have hm : b * (c/b) = c := by field_simp [hb.ne]
      rw [hm] at hscale
      exact ⟨_, hpath.append hscale⟩
    · exact hpos c hcp
  intro x y hx hy
  obtain ⟨r, hr, w, hw, hyw⟩ := exists_positive_scale_unitDirection y hy
  obtain ⟨t, ht, z, hz, hxz⟩ := exists_positive_scale_unitDirection x hx
  obtain ⟨a, ha, hin⟩ := exists_two_step_reverse_bridge K A hKA hAK w v hw hv
  obtain ⟨b, hb, hout⟩ := exists_two_step_reverse_bridge K A hKA hAK v z hv hz
  let c := t / (r*a*b)
  have hc : c ≠ 0 := div_ne_zero ht.ne' (mul_ne_zero (mul_ne_zero hr.ne' ha) hb)
  obtain ⟨n, hmid⟩ := hsigned c hc
  have h₁ := hin.scale r
  have h₂ := hmid.scale (r*a)
  have h₃ := hout.scale (r*a*c)
  rw [smul_smul] at h₁ h₂ h₃
  have hfinish : r*a*c*b = t := by
    unfold c
    field_simp
    <;> ring
  rw [← hyw] at h₁
  rw [hfinish, ← hxz] at h₃
  obtain ⟨us, hlen, hend⟩ := reversePath_to_controls K A hKA hAK ((h₁.append h₂).append h₃)
  refine ⟨us, ?_, hend⟩
  intro he
  rw [he] at hlen
  simp at hlen

theorem scaled_perturbation_controllable_iff (epsilon a k : ℝ) (hk : k ≠ 0)
    (A : Matrix2) (hKA : (k • perturbationMatrix epsilon a)*A = 1)
    (hAK : A*(k • perturbationMatrix epsilon a) = 1) :
    GloballyControllable A (A * quarterTurnMatrix) ↔
      1 < cycleGrowth (k • perturbationMatrix epsilon a) := by
  constructor
  · exact cycleGrowth_gt_one_of_controllable _ A hKA
  · intro hG
    apply controllable_of_cycleGrowth_of_negative_returns _ A hKA hAK hG
    intro v hv
    obtain ⟨n, c, _, hc, hp⟩ :=
      scaled_perturbation_negative_return_at_unit_base epsilon a k hk A hKA hAK v hv
    exact ⟨n, c, hc, hp⟩

end
end Specification
end BilinearSystems
