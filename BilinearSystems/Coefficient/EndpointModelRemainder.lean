import BilinearSystems.Coefficient.EndpointKernelTail

/-!
# Endpoint model remainder
-/
namespace BilinearSystems
namespace Specification
noncomputable section

def endpointModelRemainder (b : ℝ) : ℝ :=
  (((1/2 : ℝ)*Real.sqrt ((1/2 : ℝ)^2+b)-(1/2 : ℝ)^2)/2) +
    (b/2)*Real.log ((1/2 : ℝ)+Real.sqrt ((1/2 : ℝ)^2+b))

/-- Uniform O(b) bound on the regular model terms for 0<b<=1. -/
theorem endpointModelRemainder_bounds (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ≤ endpointModelRemainder b ∧ endpointModelRemainder b ≤ b := by
  let s := Real.sqrt ((1/2 : ℝ)^2+b)
  have harg : 0 ≤ (1/2 : ℝ)^2+b := by positivity
  have hs2 : s^2 = (1/2 : ℝ)^2+b := Real.sq_sqrt harg
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hslow : 1/2 ≤ s := by nlinarith
  have hshigh : s ≤ 3/2 := by nlinarith
  have hylo : 1 ≤ (1/2 : ℝ)+s := by linarith
  have hyhi : (1/2 : ℝ)+s ≤ 2 := by linarith
  have hloglo : 0 ≤ Real.log ((1/2 : ℝ)+s) := Real.log_nonneg hylo
  have hloghi : Real.log ((1/2 : ℝ)+s) ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hkernel : 0 ≤ endpointKernel b (1/2) ∧
      endpointKernel b (1/2) ≤ b := by
    constructor
    · exact endpointKernel_nonneg b (1/2) hb.le (by norm_num)
    · simpa using endpointKernel_le_inv b (1/2) hb.le (by norm_num)
  have hfirst : 0 ≤ (1/4 : ℝ)*endpointKernel b (1/2) ∧
      (1/4 : ℝ)*endpointKernel b (1/2) ≤ b/4 := by
    constructor
    · exact mul_nonneg (by norm_num) hkernel.1
    · nlinarith [hkernel.2]
  have hsecond : 0 ≤ (b/2)*Real.log ((1/2 : ℝ)+s) ∧
      (b/2)*Real.log ((1/2 : ℝ)+s) ≤ b/2 := by
    constructor
    · positivity
    · have h := mul_le_mul_of_nonneg_left hloghi (by positivity : 0 ≤ b/2)
      simpa using h
  have hrewrite : endpointModelRemainder b =
      (1/4 : ℝ)*endpointKernel b (1/2) +
        (b/2)*Real.log ((1/2 : ℝ)+s) := by
    dsimp [endpointModelRemainder, endpointKernel, s]
    ring
  rw [hrewrite]
  constructor
  · linarith [hfirst.1, hsecond.1]
  · linarith [hfirst.2, hsecond.2]

/-- Evaluated model integral separated into singular and bounded terms. -/
theorem endpointModel_integral_decomposition (b : ℝ) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..(1/2), endpointKernel b t) =
      -(b/4)*Real.log b + endpointModelRemainder b := by
  rw [endpointKernel_model_integral b (1/2) hb]
  unfold endpointModelRemainder
  ring

end
end Specification
end BilinearSystems
