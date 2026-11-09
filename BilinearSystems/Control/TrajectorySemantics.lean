import BilinearSystems.Control.Basic

/-!
# Nonzero states along finite trajectories
-/
namespace BilinearSystems

 theorem trajectoryEndpoint_append (A B : Matrix2) (x : State) (u v : List ℝ) :
    trajectoryEndpoint A B x (u ++ v) =
      trajectoryEndpoint A B (trajectoryEndpoint A B x u) v := by
  simp only [trajectoryEndpoint,List.foldl_append]

 theorem nonzero_endpoint_implies_nonzero_prefix (A B : Matrix2) (x : State)
    (u v : List ℝ) (h : trajectoryEndpoint A B x (u ++ v) ≠ 0) :
    trajectoryEndpoint A B x u ≠ 0 := by
  intro hz
  apply h
  rw [trajectoryEndpoint_append,hz,trajectoryEndpoint_zero]

end BilinearSystems
