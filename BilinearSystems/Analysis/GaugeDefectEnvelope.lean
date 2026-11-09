import BilinearSystems.Analysis.QuadraticEnvelope

/-!
# Gauge defect envelope
-/
namespace BilinearSystems
namespace Specification
noncomputable section

open Set

private theorem quadratic_hasDerivAt (m x : ℝ) :
    HasDerivAt (fun y : ℝ => m*y^2/2) (m*x) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul m).div_const 2 using 1
  · funext y
    simp only [id_eq, Pi.pow_apply]
  · simp only [id_eq]
    ring

private theorem linear_hasDerivAt (m x : ℝ) :
    HasDerivAt (fun y : ℝ => m*y) m x := by
  simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul m

private theorem defectQuadratic_first_hasDerivAt
    (epsilon a l theta m x : ℝ)
    (hf : 0 < angularKernel epsilon a theta x) :
    HasDerivAt (fun y => gaugeDefect epsilon a l theta y + m*y^2/2)
      (deriv (gaugeDefect epsilon a l theta) x + m*x) x := by
  have hd := gaugeDefect_hasDerivAt epsilon a l theta x hf.ne'
  have hs := hd.add (quadratic_hasDerivAt m x)
  convert hs using 1
  rw [hd.deriv]

private theorem defectQuadratic_second_hasDerivAt
    (epsilon a l theta m x : ℝ) (hl : 0 < l)
    (hf : 0 < angularKernel epsilon a theta x) :
    HasDerivAt (fun y => deriv (gaugeDefect epsilon a l theta) y + m*y)
      (deriv (fun y => deriv (gaugeDefect epsilon a l theta) y) x + m) x := by
  have hd := gaugeDefect_second_hasDerivAt epsilon a l theta x hl hf
  have hs := hd.add (linear_hasDerivAt m x)
  convert hs using 1
  rw [hd.deriv]

/-- Every positive-kernel segment satisfies the quadratic tangent bound.
This covers both signs of t without optimizing over the direction. -/
theorem gaugeDefect_segment_upper (epsilon a l theta t d : ℝ)
    (hl : 0 < l) (he : 0 ≤ epsilon)
    (hm : 0 < 1-epsilon*(2+1/Real.sqrt (2*l)))
    (hpos : ∀ x ∈ Icc (min 0 t) (max 0 t),
      0 < angularKernel epsilon a theta x)
    (hd : HasDerivAt (gaugeDefect epsilon a l theta) d 0) :
    gaugeDefect epsilon a l theta t ≤
      gaugeDefect epsilon a l theta 0 +
        d^2/(2*(1-epsilon*(2+1/Real.sqrt (2*l)))) := by
  let S : Set ℝ := Icc (min 0 t) (max 0 t)
  let m : ℝ := 1-epsilon*(2+1/Real.sqrt (2*l))
  let g : ℝ → ℝ := fun x => gaugeDefect epsilon a l theta x + m*x^2/2
  let gp : ℝ → ℝ := fun x => deriv (gaugeDefect epsilon a l theta) x + m*x
  let gpp : ℝ → ℝ := fun x =>
    deriv (fun y => deriv (gaugeDefect epsilon a l theta) y) x + m
  have hfirst (x : ℝ) (hx : x ∈ S) : HasDerivAt g (gp x) x :=
    defectQuadratic_first_hasDerivAt epsilon a l theta m x (hpos x hx)
  have hsecond (x : ℝ) (hx : x ∈ S) : HasDerivAt gp (gpp x) x :=
    defectQuadratic_second_hasDerivAt epsilon a l theta m x hl (hpos x hx)
  have hnonpos (x : ℝ) (hx : x ∈ S) : gpp x ≤ 0 := by
    have hc := gaugeDefect_second_derivative_le epsilon a l theta x hl he (hpos x hx)
    dsimp [gpp, m]
    linarith
  have hconc : ConcaveOn ℝ S g := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    · intro x hx
      exact (hfirst x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfirst x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact (hsecond x (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      exact hnonpos x (interior_subset hx)
  have hzero : (0:ℝ) ∈ S := by
    simp [S]
  have ht : t ∈ S := by
    simp [S]
  exact quadratic_envelope hm hconc hzero ht hd

end
end Specification
end BilinearSystems
