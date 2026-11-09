import BilinearSystems.AuxiliaryDefinitions

namespace BilinearSystems
namespace Specification
noncomputable section

private theorem unitDirection_abs_le_one {x : State} (hx : UnitDirection x)
    (i : Fin 2) : |x i| ≤ 1 := by
  change x 0 * x 0 + x 1 * x 1 = 1 at hx
  have hcoord (t : ℝ) (ht : t*t ≤ 1) : |t| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> by_contra h <;> push Not at h <;>
      nlinarith [sq_nonneg (t + 1), sq_nonneg (t - 1)]
  fin_cases i
  · change |x 0| ≤ 1
    exact hcoord _ (by nlinarith [sq_nonneg (x 1)])
  · change |x 1| ≤ 1
    exact hcoord _ (by nlinarith [sq_nonneg (x 0)])

private theorem edge_abs_le_entry_sum (K : Matrix2) {x y : State}
    (hx : UnitDirection x) (hy : UnitDirection y) :
    |euclideanDot y (K.mulVec x)| ≤ |K 0 0| + |K 0 1| + (|K 1 0| + |K 1 1|) := by
  have hterm (i j : Fin 2) : |y i * (K i j * x j)| ≤ |K i j| := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 1 * (|K i j| * 1) :=
        mul_le_mul (unitDirection_abs_le_one hy i)
          (mul_le_mul_of_nonneg_left (unitDirection_abs_le_one hx j) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one
      _ = _ := by simp
  simp only [euclideanDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_add]
  exact (abs_add_le _ _).trans
    (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hterm 0 0) (hterm 0 1)))
      ((abs_add_le _ _).trans (add_le_add (hterm 1 0) (hterm 1 1))))

theorem cycleGains_bddAbove (K : Matrix2) : BddAbove (CycleGains K) := by
  let M := |K 0 0| + |K 0 1| + (|K 1 0| + |K 1 1|)
  have hM : 0 ≤ M := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨M, ?_⟩
  rintro r ⟨n, hn, e, he, _, rfl⟩
  have hprod : |∏ i : Fin n, euclideanDot (e i.succ) (K.mulVec (e i.castSucc))| ≤ M^n := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod₀
        (fun _ _ => abs_nonneg _) (fun i _ => edge_abs_le_entry_sum K (he i.castSucc) (he i.succ))
      _ = _ := by simp
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ ≤ Real.rpow (M^n) (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) hprod (div_nonneg zero_le_one hnR.le)
    _ = M := by
      change (M ^ n) ^ (1 / (n : ℝ)) = M
      have hcancel : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
        field_simp [hnR.ne']
      rw [← Real.rpow_natCast M n, ← Real.rpow_mul hM, hcancel, Real.rpow_one]

theorem cycleGrowth_wellDefined : CycleGrowthWellDefined :=
  fun K => ⟨cycleGains_nonempty K, cycleGains_bddAbove K⟩

end
end Specification
end BilinearSystems
