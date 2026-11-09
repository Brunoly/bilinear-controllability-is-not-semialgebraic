import BilinearSystems.Coefficient.GraphFiniteSumLimit

/-!
# Graph no vanishing
-/
namespace BilinearSystems
namespace Specification
noncomputable section
open Filter Set
open scoped Topology

/-- A nonzero polynomial cannot vanish along the logarithmic coefficient branch. -/
theorem iterated_polynomial_not_eventually_zero
    (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0) :
    ¬ (∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      Polynomial.eval d
        (Polynomial.map (Polynomial.evalRingHom (branchNearOnset d)) p) = 0) := by
  intro hzero
  obtain ⟨i₀,j₀,hij₀,hmin,hsecond⟩ :=
    polynomial_least_total_degree_monomial p hp
  have hlim := iterated_polynomial_normalized_limit p i₀ j₀ hij₀ hmin hsecond
  have hzeroNorm : Tendsto (fun d : ℝ =>
      Polynomial.eval d
        (Polynomial.map (Polynomial.evalRingHom (branchNearOnset d)) p) /
          (d^(i₀+j₀)/(logMagnitude d)^j₀))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with d hd
    simp [hd]
  have hcoeff : (p.coeff i₀).coeff j₀ * Real.pi^j₀ ≠ 0 :=
    mul_ne_zero hij₀ (pow_ne_zero _ Real.pi_ne_zero)
  exact hcoeff (tendsto_nhds_unique hlim hzeroNorm)

end
end Specification
end BilinearSystems
