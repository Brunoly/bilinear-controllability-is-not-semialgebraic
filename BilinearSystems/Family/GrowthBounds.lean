import BilinearSystems.Control.SignedCycleTrajectories
import BilinearSystems.Family.Definitions

/-!
# Bounds for perturbation cycle growth
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem cycleGrowth_le_of_edge_bound (K : Matrix2) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ v w : State, UnitDirection v → UnitDirection w → |directionGain K v w| ≤ M) :
    cycleGrowth K ≤ M := by
  apply csSup_le (cycleGains_nonempty K)
  rintro _ ⟨n, hn, e, he, _, rfl⟩
  change |indexedPathGain K e| ^ (1 / (n : ℝ)) ≤ M
  have hp : |indexedPathGain K e| ≤ M^n := by
    unfold indexedPathGain
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => h _ _ (he i.castSucc) (he i.succ))
      _ = _ := by simp
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hc : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hnR.ne']
  calc
    _ ≤ (M^n) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) hp (one_div_nonneg.mpr hnR.le)
    _ = M := by rw [← Real.rpow_natCast M n, ← Real.rpow_mul hM, hc, Real.rpow_one]

private theorem abs_product_pair_le_one (v w : State)
    (hv : UnitDirection v) (hw : UnitDirection w) :
    |w 0 * v 0| + |w 1 * v 1| ≤ 1 ∧
    |w 0 * v 1| + |w 1 * v 0| ≤ 1 := by
  change v 0 * v 0 + v 1 * v 1 = 1 at hv
  change w 0 * w 0 + w 1 * w 1 = 1 at hw
  simp only [abs_mul]
  constructor
  · nlinarith [sq_nonneg (|w 0| - |v 0|), sq_nonneg (|w 1| - |v 1|),
      sq_abs (w 0), sq_abs (w 1), sq_abs (v 0), sq_abs (v 1)]
  · nlinarith [sq_nonneg (|w 0| - |v 1|), sq_nonneg (|w 1| - |v 0|),
      sq_abs (w 0), sq_abs (w 1), sq_abs (v 0), sq_abs (v 1)]

theorem perturbation_edge_bound (e a : ℝ) (he : 0 ≤ e) (ha : 0 ≤ a)
    (v w : State) (hv : UnitDirection v) (hw : UnitDirection w) :
    |directionGain (perturbationMatrix e a) v w| ≤ 1 + e*(a+1) := by
  have hid : directionGain (perturbationMatrix e a) v w =
      (-(w 0 * v 1) + w 1 * v 0) +
        e * ((a+1)*(w 0 * v 0) + (a-1)*(w 1 * v 1)) := by
    norm_num [directionGain, perturbationMatrix, euclideanDot, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    <;> ring
  obtain ⟨hd, hj⟩ := abs_product_pair_le_one v w hv hw
  have hJ : |-(w 0 * v 1) + w 1 * v 0| ≤ 1 := by
    exact (abs_add_le _ _).trans (by simpa using hj)
  have hdiag : |(a+1)*(w 0 * v 0) + (a-1)*(w 1 * v 1)| ≤ a+1 := by
    have ha' : 0 ≤ a+1 := by linarith
    have habs : |a-1| ≤ a+1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      _ ≤ |(a+1)*(w 0*v 0)| + |(a-1)*(w 1*v 1)| := abs_add_le _ _
      _ ≤ (a+1) * (|w 0*v 0| + |w 1*v 1|) := by
        simp only [abs_mul, abs_of_nonneg ha', mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right habs
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hd ha'
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg he]
  exact add_le_add hJ (mul_le_mul_of_nonneg_left hdiag he)

theorem parameterGrowth_ge_one (e a : ℝ) : 1 ≤ parameterGrowth e a := by
  let v : State := fun i => if i = 0 then 1 else 0
  let w : State := fun i => if i = 0 then 0 else 1
  let d : Fin 3 → State := fun i => if i = 1 then w else v
  have hu : ∀ i, UnitDirection (d i) := by
    intro i
    fin_cases i <;> norm_num [d, v, w, UnitDirection, euclideanDot]
  have hp : indexedPathGain (perturbationMatrix e a) d = -1 := by
    unfold indexedPathGain
    rw [Fin.prod_univ_two]
    norm_num [d, v, w, directionGain, perturbationMatrix, euclideanDot, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Fin.succ, Fin.castSucc]
  apply le_csSup (cycleGains_bddAbove _)
  refine ⟨2, by decide, d, hu, rfl, ?_⟩
  change 1 = |indexedPathGain (perturbationMatrix e a) d| ^ (1 / (2 : ℝ))
  rw [hp]
  simp

theorem parameterGrowth_interior (e a : ℝ) (he : 0 < e) (he' : e < 1/10)
    (ha : 1/2 < a) (ha' : a < 1) : parameterBox e a (parameterGrowth e a) := by
  have ha0 : 0 ≤ a := by linarith
  have hM : 0 ≤ 1 + e*(a+1) := by positivity
  have hupper := cycleGrowth_le_of_edge_bound (perturbationMatrix e a) _ hM
    (perturbation_edge_bound e a he.le ha0)
  have he2 : e*(a+1) < e*2 := mul_lt_mul_of_pos_left (by linarith) he
  refine ⟨he, he', ha, ha', ?_, ?_⟩
  · linarith [parameterGrowth_ge_one e a]
  · unfold parameterGrowth
    linarith

end
end Specification
end BilinearSystems
