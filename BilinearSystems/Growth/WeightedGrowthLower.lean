import BilinearSystems.Growth.WeightedExpandingPaths
import BilinearSystems.Analysis.AngularKernel
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weighted growth lower
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem exponential_base_le_of_all_powers
    (g r c C : ℝ) (hg : 0 < g) (hr : 0 < r) (hc : 0 < c)
    (h : ∀ n : ℕ, r^n*c ≤ 4*g^(n+2)*C) : r ≤ g := by
  by_contra hnot
  have hrg : g < r := lt_of_not_ge hnot
  have hratio : 1 < r/g := (one_lt_div hg).mpr hrg
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4*g^2*C/c) hratio
  have hpow : 0 < g^n := pow_pos hg n
  have heq : (r/g)^n*c*g^n = r^n*c := by
    rw [div_pow]
    field_simp [hg.ne']
  have hb : (r/g)^n*c ≤ 4*g^2*C := by
    apply le_of_mul_le_mul_right _ hpow
    calc
      ((r/g)^n*c)*g^n = r^n*c := heq
      _ ≤ 4*g^(n+2)*C := h n
      _ = (4*g^2*C)*g^n := by rw [pow_add]; ring
  have hstrict : 4*g^2*C < (r/g)^n*c := by
    have hmul := mul_lt_mul_of_pos_right hn hc
    rw [div_mul_cancel₀ _ hc.ne'] at hmul
    exact hmul
  linarith

/-- A positive bounded weight with an expanding successor at every unit
direction forces the original perturbation cycle growth above the step
factor. No infinite chosen orbit and no maximizing cycle are assumed. -/
theorem perturbation_growth_lower_of_weight
    (epsilon a : ℝ) (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/100)
    (W : State → ℝ) (r c C : ℝ)
    (hr : 0 < r) (hc : 0 < c) (hC : 0 < C)
    (hW : ∀ v, UnitDirection v → c ≤ W v ∧ W v ≤ C)
    (hStep : ∀ v, UnitDirection v → ∃ w, UnitDirection w ∧
      r*W v ≤ |directionGain (perturbationMatrix epsilon a) v w| * W w) :
    r ≤ parameterGrowth epsilon a := by
  let v₀ := angularDirection 0
  have hv₀ : UnitDirection v₀ := angularDirection_unit 0
  have hg : 0 < parameterGrowth epsilon a :=
    lt_of_lt_of_le zero_lt_one (parameterGrowth_ge_one epsilon a)
  apply exponential_base_le_of_all_powers
    (parameterGrowth epsilon a) r c C hg hr hc
  intro n
  obtain ⟨e,he0,heUnit,heGain⟩ :=
    weighted_expanding_path (perturbationMatrix epsilon a) W r hr.le
      (fun v hv => (hc.trans_le (hW v hv).1).le) hStep v₀ hv₀ n
  have hfirst : c ≤ W v₀ := (hW v₀ hv₀).1
  have hlast : W (e (Fin.last n)) ≤ C := (hW _ (heUnit _)).2
  have hpath := perturbation_path_gain_growth_bound epsilon a he heSmall e heUnit
  let G := |indexedPathGain (perturbationMatrix epsilon a) e|
  have hG : 0 ≤ G := abs_nonneg _
  have hGamma : 0 ≤ (parameterGrowth epsilon a)^(n+2) := pow_nonneg hg.le _
  have hGbound : G ≤ 4*(parameterGrowth epsilon a)^(n+2) := by
    dsimp [G] at *
    nlinarith
  calc
    r^n*c ≤ r^n*W v₀ := mul_le_mul_of_nonneg_left hfirst (pow_nonneg hr.le _)
    _ ≤ G*W (e (Fin.last n)) := heGain
    _ ≤ G*C := mul_le_mul_of_nonneg_left hlast hG
    _ ≤ 4*(parameterGrowth epsilon a)^(n+2)*C :=
      mul_le_mul_of_nonneg_right hGbound hC.le

end
end Specification
end BilinearSystems
