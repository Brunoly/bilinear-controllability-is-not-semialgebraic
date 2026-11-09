import BilinearSystems.Control.ExpandingReturn

/-!
# Two-step bridges between directions
-/
namespace BilinearSystems
namespace Specification
noncomputable section

private theorem exists_both_ne_zero (f g : State → ℝ)
    (hf : ∀ x y, f (x+y) = f x + f y)
    (hg : ∀ x y, g (x+y) = g x + g y)
    (x y : State) (hx : f x ≠ 0) (hy : g y ≠ 0) :
    ∃ z, f z ≠ 0 ∧ g z ≠ 0 := by
  by_cases hgx : g x = 0
  · by_cases hfy : f y = 0
    · exact ⟨x+y, by simpa [hf, hfy] using hx, by simpa [hg, hgx] using hy⟩
    · exact ⟨y, hfy, hy⟩
  · exact ⟨x, hx, hgx⟩

/-- Both edge gains are nonzero, with no restriction on their signs. -/
theorem exists_bridge_direction (K A : Matrix2) (hKA : K*A = 1) (hAK : A*K = 1)
    (v w : State) (hv : UnitDirection v) (hw : UnitDirection w) :
    ∃ e : State, UnitDirection e ∧ directionGain K v e ≠ 0 ∧ directionGain K e w ≠ 0 := by
  let f := fun e => directionGain K v e
  let g := fun e => directionGain K e w
  have hvK : K.mulVec v ≠ 0 := by
    intro h
    have hh := congrArg A.mulVec h
    exact unitDirection_ne_zero hv (by simpa [Matrix.mulVec_mulVec, hAK] using hh)
  have hf : ∀ x y, f (x+y) = f x + f y := by
    intro x y
    simp [f, directionGain, euclideanDot, Pi.add_apply]
    ring
  have hg : ∀ x y, g (x+y) = g x + g y := by
    intro x y
    simp [g, directionGain, Matrix.mulVec_add, euclideanDot, Pi.add_apply]
    ring
  have hfw : f (K.mulVec v) ≠ 0 := (euclideanDot_self_pos _ hvK).ne'
  have hgw : g (A.mulVec w) ≠ 0 := by
    change euclideanDot w w = 1 at hw
    simp [g, directionGain, Matrix.mulVec_mulVec, hKA, hw]
  obtain ⟨z, hfz, hgz⟩ := exists_both_ne_zero f g hf hg _ _ hfw hgw
  have hz : z ≠ 0 := by
    intro h
    apply hfz
    simp [h, f, directionGain, euclideanDot]
  obtain ⟨r, hr, e, he, hze⟩ := exists_positive_scale_unitDirection z hz
  have hfscale : f z = r * directionGain K v e := by
    rw [hze]
    simp [f, directionGain, euclideanDot, Pi.smul_apply, smul_eq_mul]
    ring
  have hgscale : g z = r * directionGain K e w := by
    rw [hze]
    simp [g, directionGain, Matrix.mulVec_smul, euclideanDot, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfscale] at hfz
  rw [hgscale] at hgz
  exact ⟨e, he, right_ne_zero_of_mul hfz, right_ne_zero_of_mul hgz⟩

theorem exists_two_step_reverse_bridge (K A : Matrix2)
    (hKA : K*A = 1) (hAK : A*K = 1) (v w : State)
    (hv : UnitDirection v) (hw : UnitDirection w) :
    ∃ c : ℝ, c ≠ 0 ∧ ReversePath K 2 v (c • w) := by
  obtain ⟨e, he, h₁, h₂⟩ := exists_bridge_direction K A hKA hAK v w hv hw
  let c := directionGain K v e * directionGain K e w
  have hc : c ≠ 0 := mul_ne_zero h₁ h₂
  refine ⟨c, hc, ?_⟩
  have hp := reversePath_of_nonzero_gain K v [e,w] (by simpa using And.intro he hw) 1
    (by simpa [pathGain, c] using hc)
  simpa [pathGain, pathLast, c] using hp

end
end Specification
end BilinearSystems
