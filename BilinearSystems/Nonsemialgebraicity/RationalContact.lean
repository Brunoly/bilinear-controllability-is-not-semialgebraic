import BilinearSystems.Polynomial.Pullback
import BilinearSystems.Polynomial.ZeroTests
import BilinearSystems.Family.GrowthBounds

/-!
# Polynomial contact along rational parameter fibers
-/
namespace BilinearSystems
open Filter Set MvPolynomial
open scoped Topology BigOperators
noncomputable section

/-- Evaluating after a change of variables agrees with pulling back each test. -/
theorem SignFormula.eval_precomp {ι X Y : Type*} (φ : SignFormula ι)
    (f : ι → X → ℝ) (g : Y → X) (y : Y) :
    φ.eval (fun i y => f i (g y)) y ↔ φ.eval f (g y) := by
  induction φ <;> simp_all [SignFormula.eval]

/-- Local constancy of a finite sign formula contradicts opposite answers at
rational scales on the two sides of an interior real threshold. -/
theorem sign_formula_rational_threshold_contact {ι : Type*}
    (φ : SignFormula ι) (f : ι → ℝ → ℝ) (l g u : ℝ)
    (hl : l < g) (hu : g < u) (hf : ∀ i, ContinuousAt (f i) g)
    (hc : ∀ s : ℚ, l < (s : ℝ) → (s : ℝ) < u →
      (φ.eval f (s : ℝ) ↔ (s : ℝ) < g)) :
    ∃ i, f i g = 0 := by
  by_contra! hn
  have he := φ.locally_constant_away_from_zeros f g hf hn
  obtain ⟨l', u', hg, hsub⟩ := he.exists_Ioo_subset
  obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn (max_lt hl hg.1)
  obtain ⟨s, hslo, hshi⟩ := exists_rat_btwn (lt_min hu hg.2)
  have hr : φ.eval f (r : ℝ) :=
    (hc r ((le_max_left _ _).trans_lt hrlo) (hrhi.trans hu)).mpr hrhi
  have hs : ¬ φ.eval f (s : ℝ) := by
    intro hh
    exact hslo.not_gt ((hc s (hl.trans hslo)
      (hshi.trans_le (min_le_left _ _))).mp hh)
  have her := hsub ⟨(le_max_right _ _).trans_lt hrlo, hrhi.trans hg.2⟩
  have hes := hsub ⟨hg.1.trans hslo, hshi.trans_le (min_le_right _ _)⟩
  exact hs (hes.mpr (her.mp hr))

namespace Specification

/-- A single nonzero polynomial vanishes at every rational-parameter threshold.
The threshold scale itself need not be rational. -/
theorem rational_classifier_forces_rational_fiber_polynomial
    (hclassifier : ¬ RationalInputFiniteFormulaObstruction) :
    ∃ P : ParameterPolynomial, P ≠ 0 ∧ ∀ e a : ℚ,
      parameterBox (e : ℝ) (a : ℝ) (parameterGrowth e a) →
      MvPolynomial.eval (parameterTriple e a (parameterGrowth e a)) P = 0 := by
  classical
  unfold RationalInputFiniteFormulaObstruction at hclassifier
  obtain ⟨m, p, φ, hφ⟩ := not_not.mp hclassifier
  obtain ⟨P, hP⟩ := exists_signFormula_pullback φ p
  let I := {i : Fin m // P i ≠ 0}
  let Q : ParameterPolynomial := ∏ i : I, P i.val
  refine ⟨Q, Finset.prod_ne_zero_iff.mpr (fun i _ => i.property), ?_⟩
  intro e a hb
  have hcorrect (s : ℚ) (hs : (1/2 : ℝ) < (s : ℝ)) (hs' : (s : ℝ) < 2) :
      φ.eval (fun i y => MvPolynomial.eval y (P i)) (parameterTriple e a s) ↔
        (s : ℝ) < parameterGrowth e a := by
    have hbox : parameterBox (e : ℝ) (a : ℝ) (s : ℝ) :=
      ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hs, hs'⟩
    have hp := hP (parameterTriple e a s) (by simpa using hbox)
    have hc := hφ (parameterCoordinates e a s) (parameterCoordinates_rational e a s)
    have ht := parameterThreshold (e : ℝ) (a : ℝ) (s : ℝ) hbox
    exact hp.trans (hc.trans (by
      simpa only [ControllabilityLocus, Set.mem_setOf_eq, parameterGrowth] using ht))
  have htup : Continuous (parameterTriple (e : ℝ) (a : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [parameterTriple, continuous_const] <;> exact continuous_id
  obtain ⟨i, hi⟩ := sign_formula_rational_threshold_contact
    (φ.removeZeroPolynomials P)
    (fun i s => MvPolynomial.eval (parameterTriple e a s) (P i.val))
    (1/2) (parameterGrowth e a) 2 hb.2.2.2.2.1 hb.2.2.2.2.2
    (fun i => ((MvPolynomial.continuous_eval (p := P i.val)).comp htup).continuousAt)
    (fun s hs hs' => ((φ.removeZeroPolynomials P).eval_precomp
      (fun i y => MvPolynomial.eval y (P i.val)) (parameterTriple e a) (s : ℝ)).trans
      ((φ.removeZeroPolynomials_eval P (parameterTriple e a s)).trans
        (hcorrect s hs hs')))
  change MvPolynomial.eval (parameterTriple e a (parameterGrowth e a))
    (∏ i : I, P i.val) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

end Specification
end
end BilinearSystems
