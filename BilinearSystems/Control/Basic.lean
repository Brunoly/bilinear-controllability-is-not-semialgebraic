import BilinearSystems.Definitions

/-!
# Zero absorption and finite trajectories
-/
namespace BilinearSystems
noncomputable section

@[simp] theorem step_zero (A B : Matrix2) (u : ℝ) : step A B u 0 = 0 := by
  simp [step]

@[simp] theorem trajectoryEndpoint_zero (A B : Matrix2) (controls : List ℝ) :
    trajectoryEndpoint A B 0 controls = 0 := by
  induction controls with
  | nil => rfl
  | cons u us ih => simpa [trajectoryEndpoint, List.foldl_cons] using ih

 theorem zero_not_reachable_nonzero (A B : Matrix2) (y : State) (hy : y ≠ 0) :
    ¬ Reachable A B 0 y := by
  rintro ⟨controls, _, he⟩
  exact hy (he.symm.trans (trajectoryEndpoint_zero A B controls))

end
end BilinearSystems
