import BilinearSystems.Definitions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.ByContra

/-!
# Local constancy of finite sign formulas
-/
namespace BilinearSystems
open Filter Set
open scoped Topology

theorem continuous_tests_same_sign_near {ι X : Type*} [TopologicalSpace X]
    (f : ι → X → ℝ) (q : X) (hf : ∀ i, ContinuousAt (f i) q)
    (hn : ∀ i, f i q ≠ 0) (i : ι) :
    ∀ᶠ x in 𝓝 q, (0 < f i x ↔ 0 < f i q) ∧
      (f i x = 0 ↔ f i q = 0) ∧ (f i x < 0 ↔ f i q < 0) := by
  rcases lt_or_gt_of_ne (hn i) with h | h
  · filter_upwards [(hf i).eventually_lt_const h] with x hx
    simp [h, hx, ne_of_lt h, ne_of_lt hx, not_lt_of_ge h.le, not_lt_of_ge hx.le]
  · filter_upwards [(hf i).eventually_const_lt h] with x hx
    simp [h, hx, ne_of_gt h, ne_of_gt hx, not_lt_of_ge h.le, not_lt_of_ge hx.le]

theorem SignFormula.locally_constant_away_from_zeros {ι X : Type*} [TopologicalSpace X]
    (φ : SignFormula ι) (f : ι → X → ℝ) (q : X)
    (hf : ∀ i, ContinuousAt (f i) q) (hn : ∀ i, f i q ≠ 0) :
    ∀ᶠ x in 𝓝 q, φ.eval f x ↔ φ.eval f q := by
  induction φ with
  | positive i => exact (continuous_tests_same_sign_near f q hf hn i).mono fun _ h => h.1
  | zero i => exact (continuous_tests_same_sign_near f q hf hn i).mono fun _ h => h.2.1
  | negative i => exact (continuous_tests_same_sign_near f q hf hn i).mono fun _ h => h.2.2
  | truth => exact Eventually.of_forall fun _ => Iff.rfl
  | falsity => exact Eventually.of_forall fun _ => Iff.rfl
  | conj a b ha hb =>
      filter_upwards [ha, hb] with x hx hy
      exact and_congr hx hy
  | disj a b ha hb =>
      filter_upwards [ha, hb] with x hx hy
      exact or_congr hx hy
  | neg a ha => exact ha.mono fun _ h => not_congr h

end BilinearSystems
