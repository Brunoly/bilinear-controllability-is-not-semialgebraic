import BilinearSystems.Coefficient.GraphFiniteSum

/-!
# Graph dominant term
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

/-- Termwise limit of the normalized polynomial expansion. -/
theorem normalized_polynomial_term_limit
    (p : Polynomial (Polynomial ℝ)) (i₀ j₀ i j : ℕ)
    (hij₀ : (p.coeff i₀).coeff j₀ ≠ 0)
    (hmin : ∀ i' j' : ℕ, (p.coeff i').coeff j' ≠ 0 →
      i₀+j₀ ≤ i'+j')
    (hsecond : ∀ i' j' : ℕ, (p.coeff i').coeff j' ≠ 0 →
      i'+j' = i₀+j₀ → j₀ ≤ j')
    (hij : (p.coeff i).coeff j ≠ 0) :
    Tendsto (fun d : ℝ => (p.coeff i).coeff j *
      (d^i * (branchNearOnset d)^j /
        (d^(i₀+j₀)/(logMagnitude d)^j₀)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (if i=i₀ ∧ j=j₀ then
        (p.coeff i₀).coeff j₀ * Real.pi^j₀ else 0)) := by
  by_cases hdist : i=i₀ ∧ j=j₀
  · rcases hdist with ⟨hi,hj⟩
    subst i
    subst j
    have h := normalized_coefficient_monomial_ge_limit
      i₀ j₀ (i₀+j₀) j₀ (by omega) le_rfl
    simpa using (tendsto_const_nhds.mul h :
      Tendsto (fun d : ℝ => (p.coeff i₀).coeff j₀ *
        (d^i₀ * (branchNearOnset d)^j₀ /
          (d^(i₀+j₀)/(logMagnitude d)^j₀)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((p.coeff i₀).coeff j₀ *
          (Real.pi^j₀ * (0:ℝ)^(i₀+j₀-(i₀+j₀)) * (0:ℝ)^(j₀-j₀)))))
  · have hdeg := hmin i j hij
    rcases lt_or_eq_of_le hdeg with hgt | heq
    · by_cases hj : j₀ ≤ j
      · have h := normalized_coefficient_monomial_ge_limit
          i j (i₀+j₀) j₀ hdeg hj
        have hr : i+j-(i₀+j₀) ≠ 0 := by omega
        simpa [hdist, hr] using
          (tendsto_const_nhds.mul h :
            Tendsto (fun d : ℝ => (p.coeff i).coeff j *
              (d^i * (branchNearOnset d)^j /
                (d^(i₀+j₀)/(logMagnitude d)^j₀)))
              (𝓝[>] (0 : ℝ))
              (𝓝 ((p.coeff i).coeff j *
                (Real.pi^j * (0:ℝ)^(i+j-(i₀+j₀)) * (0:ℝ)^(j-j₀)))))
      · have hj' : j < j₀ := Nat.lt_of_not_ge hj
        have h := normalized_coefficient_monomial_lt_limit
          i j (i₀+j₀) j₀ hgt hj'
        simpa [hdist] using
          (tendsto_const_nhds.mul h :
            Tendsto (fun d : ℝ => (p.coeff i).coeff j *
              (d^i * (branchNearOnset d)^j /
                (d^(i₀+j₀)/(logMagnitude d)^j₀)))
              (𝓝[>] (0 : ℝ)) (𝓝 ((p.coeff i).coeff j * 0)))
    · have hj : j₀ ≤ j := hsecond i j hij heq.symm
      have hj' : j₀ < j := by
        rcases hj.eq_or_lt with heqj | hlt
        · have hi : i=i₀ := by omega
          exact False.elim (hdist ⟨hi, heqj.symm⟩)
        · exact hlt
      have h := normalized_coefficient_monomial_ge_limit
        i j (i₀+j₀) j₀ hdeg hj
      have hs : j-j₀ ≠ 0 := by omega
      simpa [hdist, hs] using
        (tendsto_const_nhds.mul h :
          Tendsto (fun d : ℝ => (p.coeff i).coeff j *
            (d^i * (branchNearOnset d)^j /
              (d^(i₀+j₀)/(logMagnitude d)^j₀)))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((p.coeff i).coeff j *
              (Real.pi^j * (0:ℝ)^(i+j-(i₀+j₀)) * (0:ℝ)^(j-j₀)))))

end
end Specification
end BilinearSystems
