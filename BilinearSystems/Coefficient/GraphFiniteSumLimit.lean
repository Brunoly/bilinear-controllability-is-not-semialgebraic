import BilinearSystems.Coefficient.GraphDominantTerm

/-!
# Graph finite sum limit
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

/-- The normalized bivariate polynomial has the unique nonzero
lowest-degree term as its limit. -/
theorem iterated_polynomial_normalized_limit
    (p : Polynomial (Polynomial ℝ)) (i₀ j₀ : ℕ)
    (hij₀ : (p.coeff i₀).coeff j₀ ≠ 0)
    (hmin : ∀ i j : ℕ, (p.coeff i).coeff j ≠ 0 → i₀+j₀ ≤ i+j)
    (hsecond : ∀ i j : ℕ, (p.coeff i).coeff j ≠ 0 →
      i+j=i₀+j₀ → j₀ ≤ j) :
    Tendsto (fun d : ℝ =>
      Polynomial.eval d
        (Polynomial.map (Polynomial.evalRingHom (branchNearOnset d)) p) /
          (d^(i₀+j₀)/(logMagnitude d)^j₀))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((p.coeff i₀).coeff j₀ * Real.pi^j₀)) := by
  have hi₀ : i₀ ∈ p.support := Polynomial.mem_support_iff.mpr (by
    intro hz
    exact hij₀ (by simp [hz]))
  have hj₀ : j₀ ∈ (p.coeff i₀).support :=
    Polynomial.mem_support_iff.mpr hij₀
  have hsum : Tendsto (fun d : ℝ =>
      ∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
        (p.coeff i).coeff j *
          (d^i * (branchNearOnset d)^j /
            (d^(i₀+j₀)/(logMagnitude d)^j₀)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
        if i=i₀ ∧ j=j₀ then
          (p.coeff i₀).coeff j₀ * Real.pi^j₀ else 0)) := by
    apply tendsto_finsetSum p.support
    intro i hi
    apply tendsto_finsetSum (p.coeff i).support
    intro j hj
    exact normalized_polynomial_term_limit p i₀ j₀ i j
      hij₀ hmin hsecond (Polynomial.mem_support_iff.mp hj)
  have hlimit :
      (∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
        if i=i₀ ∧ j=j₀ then
          (p.coeff i₀).coeff j₀ * Real.pi^j₀ else 0) =
      (p.coeff i₀).coeff j₀ * Real.pi^j₀ := by
    classical
    calc
      (∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
          if i=i₀ ∧ j=j₀ then
            (p.coeff i₀).coeff j₀ * Real.pi^j₀ else 0) =
        ∑ i ∈ p.support, if i=i₀ then
          (p.coeff i₀).coeff j₀ * Real.pi^j₀ else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hii : i=i₀
          · subst i
            simp [hj₀]
          · simp [hii]
      _ = _ := by simp [hi₀]
  have heq : (fun d : ℝ =>
      Polynomial.eval d
        (Polynomial.map (Polynomial.evalRingHom (branchNearOnset d)) p) /
          (d^(i₀+j₀)/(logMagnitude d)^j₀)) =
      (fun d : ℝ => ∑ i ∈ p.support, ∑ j ∈ (p.coeff i).support,
        (p.coeff i).coeff j *
          (d^i * (branchNearOnset d)^j /
            (d^(i₀+j₀)/(logMagnitude d)^j₀))) := by
    funext d
    rw [iterated_polynomial_eval_double_sum]
    simp only [Finset.sum_div, mul_div_assoc]
    rw [Finset.sum_congr rfl]
    intro i hi
    rw [Finset.sum_congr rfl]
    intro j hj
    ring
  simpa only [heq, hlimit] using hsum

end
end Specification
end BilinearSystems
