import Mathlib.Algebra.Polynomial.Div
import BilinearSystems.Polynomial.JointEvaluation
import BilinearSystems.Coefficient.Nonalgebraicity

/-!
# Limiting polynomial relations from rational sequences
-/
namespace BilinearSystems
open Filter Set
open scoped Topology
noncomputable section

/-- Extract one nonzero coefficient relation from zeros along a sequence.
Specializing a may annihilate individual coefficients; no hypothesis excludes it. -/
theorem nonzero_polynomial_relation_of_sequence {σ A : Type*}
    (p : Polynomial (MvPolynomial σ ℝ)) (hp : p ≠ 0) (S : Set A)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (htne : ∀ᶠ n in atTop, t n ≠ 0)
    (v : A → ℕ → σ → ℝ) (v₀ : A → σ → ℝ)
    (hv : ∀ a ∈ S, Tendsto (v a) atTop (𝓝 (v₀ a)))
    (hz : ∀ a ∈ S, ∀ᶠ n in atTop,
      p.eval₂ (MvPolynomial.eval (v a n)) (t n) = 0) :
    ∃ Q : MvPolynomial σ ℝ, Q ≠ 0 ∧
      ∀ a ∈ S, MvPolynomial.eval (v₀ a) Q = 0 := by
  obtain ⟨q, hfac, hndiv⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  have hfac' : p = Polynomial.X ^ p.rootMultiplicity 0 * q := by simpa using hfac
  have hq : q.coeff 0 ≠ 0 := by
    simpa only [Polynomial.C_0, sub_zero, Polynomial.X_dvd_iff] using hndiv
  refine ⟨q.coeff 0, hq, ?_⟩
  intro a ha
  have he : ∀ᶠ n in atTop, q.eval₂ (MvPolynomial.eval (v a n)) (t n) = 0 := by
    filter_upwards [hz a ha, htne] with n hn ht0
    rw [hfac', Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hn
    exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ ht0)
  have hlim := (continuous_polynomial_joint_evaluation q).continuousAt.tendsto.comp
    (ht.prodMk_nhds (hv a ha))
  have hlim' : Tendsto (fun n => q.eval₂ (MvPolynomial.eval (v a n)) (t n)) atTop
      (𝓝 (MvPolynomial.eval (v₀ a) (q.coeff 0))) := by
    simpa only [Function.comp_def, Polynomial.eval₂_at_zero] using hlim
  exact tendsto_nhds_unique hlim' (tendsto_const_nhds.congr'
    (he.mono fun _ h => h.symm))

/-- Three-coordinate version: epsilon is first, then a and the blown-up growth. -/
theorem three_variable_relation_along_sequence
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ≠ 0) (S : Set ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0))
    (htne : ∀ᶠ n in atTop, t n ≠ 0)
    (z : ℝ → ℕ → ℝ) (lambda : ℝ → ℝ)
    (hlim : ∀ a ∈ S, Tendsto (z a) atTop (𝓝 (lambda a)))
    (hzero : ∀ a ∈ S, ∀ᶠ n in atTop,
      MvPolynomial.eval (Fin.cons (t n) (Fin.cons a (fun _ : Fin 1 => z a n))) p = 0) :
    ∃ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 ∧
      ∀ a ∈ S, MvPolynomial.eval (Fin.cons a (fun _ : Fin 1 => lambda a)) Q = 0 := by
  have hp' : MvPolynomial.finSuccEquiv ℝ 2 p ≠ 0 :=
    fun h => hp ((MvPolynomial.finSuccEquiv ℝ 2).injective
      (h.trans (map_zero _).symm))
  apply nonzero_polynomial_relation_of_sequence (MvPolynomial.finSuccEquiv ℝ 2 p)
    hp' S t ht htne (fun a n => Fin.cons a (fun _ : Fin 1 => z a n))
    (fun a => Fin.cons a (fun _ : Fin 1 => lambda a))
  · intro a ha
    apply tendsto_pi_nhds.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact tendsto_const_nhds
    · exact hlim a ha
  · intro a ha
    filter_upwards [hzero a ha] with n hn
    simpa only [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map] using hn

namespace Specification

/-- Continuity of the inverse integral branch, not continuity of cycle growth. -/
theorem positiveCoefficientBranch_continuousOn :
    ContinuousOn positiveCoefficientBranch (Ioi criticalParameter) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  apply tendsto_order.mpr
  have hspec := positiveCoefficientBranch_spec a ha
  have hnear : ∀ᶠ b in 𝓝 a, criticalParameter < b := Ioi_mem_nhds ha
  constructor
  · intro r hr
    by_cases hr0 : 0 ≤ r
    · have hFr : coefficientIntegral r < a := by
        rw [← hspec.2]
        exact coefficientIntegral_strictMonoOn hr0 hspec.1.le hr
      filter_upwards [hnear, Ioi_mem_nhds hFr] with b hb hFb
      have hs := positiveCoefficientBranch_spec b hb
      apply coefficient_lt_of_parameter_lt hr0 hs.1.le
      rwa [hs.2]
    · filter_upwards [hnear] with b hb
      exact (lt_of_not_ge hr0).trans (positiveCoefficientBranch_spec b hb).1
  · intro r hr
    have hr0 : 0 < r := hspec.1.trans hr
    have hFr : a < coefficientIntegral r := by
      rw [← hspec.2]
      exact coefficientIntegral_strictMonoOn hspec.1.le hr0.le hr
    filter_upwards [hnear, Iio_mem_nhds hFr] with b hb hFb
    have hs := positiveCoefficientBranch_spec b hb
    apply coefficient_lt_of_parameter_lt hs.1.le hr0.le
    rwa [hs.2]

/-- A continuous polynomial relation holding for rational a on the positive
branch extends to the whole interval. No continuity of the growth is involved. -/
theorem coefficient_relation_of_rational_parameters
    (Q : MvPolynomial (Fin 2) ℝ)
    (hQ : ∀ a : ℚ, criticalParameter < (a : ℝ) → (a : ℝ) < 1 →
      MvPolynomial.eval (Fin.cons (a : ℝ)
        (fun _ : Fin 1 => positiveCoefficientBranch a)) Q = 0) :
    ∀ a ∈ Ioo criticalParameter 1,
      MvPolynomial.eval (Fin.cons a
        (fun _ : Fin 1 => positiveCoefficientBranch a)) Q = 0 := by
  intro a ha
  have hb : ContinuousAt positiveCoefficientBranch a :=
    positiveCoefficientBranch_continuousOn.continuousAt (isOpen_Ioi.mem_nhds ha.1)
  have hc : ContinuousAt (fun a : ℝ => MvPolynomial.eval
      (Fin.cons a (fun _ : Fin 1 => positiveCoefficientBranch a)) Q) a := by
    apply (MvPolynomial.continuous_eval (p := Q)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuousAt_id
    · exact hb
  let D : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  haveI : NeBot (𝓝[D] a) := Rat.denseRange_cast.nhdsWithin_neBot a
  have he : ∀ᶠ b in 𝓝[D] a,
      MvPolynomial.eval (Fin.cons b (fun _ : Fin 1 => positiveCoefficientBranch b)) Q = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ha)] with b hb hba
    obtain ⟨q, rfl⟩ := hb
    exact hQ q hba.1 hba.2
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))

end Specification
end
end BilinearSystems
