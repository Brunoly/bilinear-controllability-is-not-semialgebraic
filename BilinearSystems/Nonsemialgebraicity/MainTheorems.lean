import BilinearSystems.Polynomial.Blowup
import BilinearSystems.Nonsemialgebraicity.RealCorollary
import BilinearSystems.Nonsemialgebraicity.RationalContact
import BilinearSystems.Nonsemialgebraicity.LimitingRelation
import BilinearSystems.Analysis.GrowthAsymptotic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The rational-input obstruction and real-input corollary
-/
namespace BilinearSystems.Specification
open Filter Set MvPolynomial
open scoped Topology
noncomputable section

/-- The rational-input theorem, for all matrix pairs,
with arbitrary real polynomial coefficients, controls, and endpoint states. -/
theorem rational_input_finite_formula_obstruction :
    RationalInputFiniteFormulaObstruction := by
  classical
  by_contra hn
  obtain ⟨P, hP, hz⟩ := rational_classifier_forces_rational_fiber_polynomial hn
  let r : ℕ → ℚ := fun n => 1 / ((n : ℚ) + 1)
  let t : ℕ → ℝ := fun n => (r n : ℝ)
  have ht_eq (n : ℕ) : t n = 1 / ((n : ℝ) + 1) := by simp [t, r]
  have ht : Tendsto t atTop (𝓝 0) := by
    have heq : t = (fun n : ℕ => 1 / ((n : ℝ) + 1)) := funext ht_eq
    rw [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (n : ℕ) : 0 < t n := by rw [ht_eq]; positivity
  have htright : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall htpos⟩
  let S : Set ℝ := range (fun q : ℚ => (q : ℝ)) ∩ Ioo criticalParameter 1
  let z : ℝ → ℕ → ℝ := fun a n => (parameterGrowth (t n) a - 1) / (t n)^2
  have hlim : ∀ a ∈ S, Tendsto (z a) atTop (𝓝 (positiveCoefficientBranch a)) := by
    intro a ha
    have hs := positiveCoefficientBranch_spec a ha.2.1
    exact (growthAsymptotic a (positiveCoefficientBranch a)
      ha.2.1 ha.2.2 hs.1 hs.2).comp htright
  have hzero : ∀ a ∈ S, ∀ᶠ n in atTop,
      eval (Fin.cons (t n) (Fin.cons a (fun _ : Fin 1 => z a n)))
        (boundaryBlowup P) = 0 := by
    rintro a ⟨⟨q, rfl⟩, hqa, hq1⟩
    have hcrit : (1/2 : ℝ) ≤ criticalParameter := by
      unfold criticalParameter
      apply (le_div_iff₀ Real.pi_pos).2
      linarith [Real.pi_le_four]
    have hsmall : ∀ᶠ n in atTop, t n < 1/10 :=
      ht.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hsmall] with n hnsmall
    have hsub : 1 + (t n)^2 * z (q : ℝ) n = parameterGrowth (t n) q := by
      unfold z
      field_simp [(htpos n).ne']
      <;> ring
    rw [← parameterTriple_eq_cons, eval_boundaryBlowup, hsub]
    exact hz (r n) q (parameterGrowth_interior (t n) q
      (htpos n) hnsmall (hcrit.trans_lt hqa) hq1)
  obtain ⟨Q, hQ, hrel⟩ := three_variable_relation_along_sequence
    (boundaryBlowup P) (boundaryBlowup_ne_zero P hP) S t ht
    (Eventually.of_forall (fun n => (htpos n).ne')) z positiveCoefficientBranch hlim hzero
  have hrelall := coefficient_relation_of_rational_parameters Q
    (fun q hqa hq1 => hrel (q : ℝ) ⟨⟨q, rfl⟩, hqa, hq1⟩)
  apply coefficientGraphNonalgebraic Q hQ
  intro a l ha ha1 hl hcoef
  have heq : l = positiveCoefficientBranch a :=
    (coefficientExistenceUniqueness a ha).unique ⟨hl, hcoef⟩
      (positiveCoefficientBranch_spec a ha)
  rw [heq]
  exact hrelall a ⟨ha, ha1⟩

/-- The real-input result follows from the rational-input obstruction. -/
theorem real_input_finite_formula_obstruction :
    RealInputFiniteFormulaObstruction :=
  rational_obstruction_implies_real_obstruction
    rational_input_finite_formula_obstruction

end
end BilinearSystems.Specification
