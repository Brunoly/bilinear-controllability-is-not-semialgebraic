import BilinearSystems.Coefficient.GraphAsymptotic
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Graph monomial
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- A nonzero polynomial in two iterated variables has a distinguished
nonzero coefficient of minimal total degree and, within that degree,
minimal exponent in the second variable. -/
theorem polynomial_least_total_degree_monomial
    (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0) :
    ∃ i j : ℕ,
      (p.coeff i).coeff j ≠ 0 ∧
      (∀ i' j' : ℕ, (p.coeff i').coeff j' ≠ 0 →
        i+j ≤ i'+j') ∧
      (∀ i' j' : ℕ, (p.coeff i').coeff j' ≠ 0 →
        i'+j' = i+j → j ≤ j') := by
  classical
  have hex : ∃ i j : ℕ, (p.coeff i).coeff j ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext i j
    simpa using h i j
  have hm : ∃ m : ℕ, ∃ i j : ℕ,
      i+j=m ∧ (p.coeff i).coeff j ≠ 0 := by
    rcases hex with ⟨i,j,hij⟩
    exact ⟨i+j,i,j,rfl,hij⟩
  let m := Nat.find hm
  have hms : ∃ i j : ℕ,
      i+j=m ∧ (p.coeff i).coeff j ≠ 0 := Nat.find_spec hm
  have hj : ∃ j : ℕ, ∃ i : ℕ,
      i+j=m ∧ (p.coeff i).coeff j ≠ 0 := by
    rcases hms with ⟨i,j,hij,hne⟩
    exact ⟨j,i,hij,hne⟩
  let j := Nat.find hj
  obtain ⟨i, hij, hne⟩ := Nat.find_spec hj
  refine ⟨i,j,hne,?_,?_⟩
  · intro i' j' hne'
    have hCandidate : ∃ i'' j'' : ℕ,
        i''+j''=i'+j' ∧ (p.coeff i'').coeff j'' ≠ 0 :=
      ⟨i',j',rfl,hne'⟩
    rw [hij]
    exact Nat.find_min' hm hCandidate
  · intro i' j' hne' heq
    have hCandidate : ∃ i'' : ℕ,
        i''+j'=m ∧ (p.coeff i'').coeff j' ≠ 0 := by
      refine ⟨i',?_,hne'⟩
      exact heq.trans hij
    exact Nat.find_min' hj hCandidate

end
end Specification
end BilinearSystems
