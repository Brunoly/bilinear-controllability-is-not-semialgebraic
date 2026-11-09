import BilinearSystems.Control.DirectionBridge
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-!
# Small positive return multipliers
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Set

theorem exists_interval_of_positive_returns (K A : Matrix2)
    (hKA : K*A = 1) (hAK : A*K = 1) (v : State) (hv : UnitDirection v) :
    ∃ d : ℝ, 0 < d ∧ ∀ q : ℝ, 0 < q → q ≤ d → ReversePath K 4 v (q • v) := by
  obtain ⟨e, he, hf, hg⟩ := exists_bridge_direction K A hKA hAK v v hv hv
  let u := K.mulVec v
  let z := quarterTurn u
  have hu : u ≠ 0 := by
    intro hz
    have h := congrArg A.mulVec hz
    exact unitDirection_ne_zero hv (by simpa [u, Matrix.mulVec_mulVec, hAK] using h)
  have hz : z ≠ 0 := by
    intro hh
    apply hu
    have h₀ := congrFun hh (0 : Fin 2)
    have h₁ := congrFun hh (1 : Fin 2)
    simp [z, quarterTurn] at h₀ h₁
    funext i
    fin_cases i
    · exact h₁
    · exact h₀
  have horth : euclideanDot z u = 0 := by
    simp [z, euclideanDot, quarterTurn]
    ring
  let w := fun t : ℝ => (1-t) • z + t • e
  have hw₀ : w 0 = z := by simp [w]
  have hw₁ : w 1 = e := by simp [w]
  have hwDot (t : ℝ) : euclideanDot (w t) u = t * directionGain K v e := by
    change euclideanDot ((1-t) • z + t • e) u = t * euclideanDot e u
    simp only [euclideanDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at horth ⊢
    linear_combination (1-t) * horth
  have hwne (t : ℝ) : w t ≠ 0 := by
    by_cases ht : t = 0
    · simpa [ht, hw₀] using hz
    · intro h
      have h' := hwDot t
      rw [h] at h'
      apply mul_ne_zero ht hf
      simpa [euclideanDot] using h'.symm
  let F := fun t : ℝ =>
    ((directionGain K v (w t) * directionGain K (w t) v) /
      euclideanDot (w t) (w t))^2
  have hF : Continuous F := by
    apply Continuous.pow
    apply Continuous.div
    · unfold directionGain euclideanDot w
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    · unfold euclideanDot w
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    · exact fun t => (euclideanDot_self_pos _ (hwne t)).ne'
  have hF₀ : F 0 = 0 := by
    simp [F, hw₀, directionGain, show K.mulVec v = u from rfl, horth]
  have hF₁ : F 1 = (directionGain K v e * directionGain K e v)^2 := by
    change euclideanDot e e = 1 at he
    simp [F, hw₁, he]
  refine ⟨F 1, by rw [hF₁]; exact sq_pos_of_ne_zero (mul_ne_zero hf hg), ?_⟩
  intro q hq hqd
  have hmem : q ∈ Icc (F 0) (F 1) := ⟨hF₀.symm ▸ hq.le, hqd⟩
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc zero_le_one hF.continuousOn hmem
  obtain ⟨r, hr, p, hp, hwp⟩ := exists_positive_scale_unitDirection (w t) (hwne t)
  let b := directionGain K v p * directionGain K p v
  have hqeq : q = b^2 := by
    rw [← ht]
    unfold F
    rw [hwp]
    have hn : euclideanDot p p = 1 := hp
    have hs : euclideanDot (r • p) (r • p) = r^2 := by
      simp only [euclideanDot, Pi.smul_apply, smul_eq_mul] at hn ⊢
      linear_combination r^2 * hn
    have h₁ : directionGain K v (r • p) = r * directionGain K v p := by
      simp only [directionGain, euclideanDot, Pi.smul_apply, smul_eq_mul]
      ring
    have h₂ : directionGain K (r • p) v = r * directionGain K p v := by
      simp only [directionGain, Matrix.mulVec_smul, euclideanDot, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, h₁, h₂]
    congr 1
    unfold b
    field_simp [hr.ne']
    <;> ring
  have hb : b ≠ 0 := by
    intro hb
    norm_num [hqeq, hb] at hq
  have hu' : ∀ x ∈ [p,v], UnitDirection x := by simpa using And.intro hp hv
  have hp' := reversePath_of_nonzero_gain K v [p,v] hu' 1
    (by simpa [pathGain, b] using hb)
  have htwo : ReversePath K 2 v (b • v) := by
    simp only [one_smul, one_mul, pathGain, pathLast, mul_one] at hp'
    exact hp'
  rw [hqeq]
  have hnext := htwo.scale b
  rw [smul_smul, ← pow_two] at hnext
  exact htwo.append hnext

end
end Specification
end BilinearSystems
