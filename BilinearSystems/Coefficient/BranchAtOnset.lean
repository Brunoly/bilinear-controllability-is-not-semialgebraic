import BilinearSystems.Coefficient.LogarithmicExpansion

/-!
# Branch at onset
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

/-- The unique positive branch on a>a0, set to zero elsewhere only to
make it a total real function. Its values outside the branch domain are
never used in the main claims. -/
def positiveCoefficientBranch (a : ℝ) : ℝ :=
  if h : criticalParameter < a then
    Classical.choose ((coefficientExistenceUniqueness a h).exists)
  else 0

theorem positiveCoefficientBranch_spec (a : ℝ)
    (ha : criticalParameter < a) :
    0 < positiveCoefficientBranch a ∧
      coefficientIntegral (positiveCoefficientBranch a) = a := by
  simpa only [positiveCoefficientBranch, dite_eq_left ha] using
    Classical.choose_spec ((coefficientExistenceUniqueness a ha).exists)

/-- The branch approaches lambda=0 from the right at the onset. -/
theorem positiveCoefficientBranch_tendsto_zero :
    Tendsto positiveCoefficientBranch (𝓝[>] criticalParameter) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact hr.trans (positiveCoefficientBranch_spec a ha).1
  · intro r hr
    have hFr : criticalParameter < coefficientIntegral r := by
      have hmono := coefficientIntegral_strictMonoOn
        (show (0:ℝ) ∈ Ici 0 by simp) (show r ∈ Ici 0 by simpa using hr.le) hr
      simpa only [coefficientIntegral_zero] using hmono
    have hevent : ∀ᶠ a in 𝓝[>] criticalParameter,
        a < coefficientIntegral r :=
      nhdsWithin_le_nhds (Iio_mem_nhds hFr)
    filter_upwards [hevent, self_mem_nhdsWithin] with a hlt ha
    have hs := positiveCoefficientBranch_spec a ha
    apply coefficient_lt_of_parameter_lt hs.1.le hr.le
    rw [hs.2]
    exact hlt

end
end Specification
end BilinearSystems
