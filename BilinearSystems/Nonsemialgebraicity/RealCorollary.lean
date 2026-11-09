import BilinearSystems.Definitions

/-!
# From rational-input obstruction to real nonsemialgebraicity
-/
namespace BilinearSystems
noncomputable section

/-- The rational-input obstruction implies real-input nonsemialgebraicity. -/
theorem rational_obstruction_implies_real_obstruction
    (hQ : RationalInputFiniteFormulaObstruction) : RealInputFiniteFormulaObstruction := by
  rintro ⟨m,p,φ,hφ⟩
  apply hQ
  refine ⟨m,p,φ,?_⟩
  intro v hv
  simpa only [ControllabilityLocus, Set.mem_setOf_eq] using hφ v

end
end BilinearSystems
