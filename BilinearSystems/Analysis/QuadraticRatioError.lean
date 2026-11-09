import BilinearSystems.Analysis.GaugeDefectSlopeSquare

/-!
# Quadratic ratio error
-/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- An abstract, uniform upper estimate for the squared slope divided by
the curvature margin. -/
theorem quadratic_ratio_error (epsilon R L v d : ℝ)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hm : 1/2 ≤ 1-epsilon*L)
    (hv : |v| ≤ R)
    (hsq : |d^2-epsilon^2*v^2| ≤ 8*R^2*epsilon^3) :
    d^2/(2*(1-epsilon*L)) ≤
      epsilon^2*v^2/2+(8+L)*R^2*epsilon^3 := by
  let m := 1-epsilon*L
  let C := (8+L)*R^2*epsilon^3
  have hmhalf : 1/2 ≤ m := hm
  have hmpos : 0 < m := by linarith
  have htwo : 0 < 2*m := by positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hvsq : v^2 ≤ R^2 := by
    nlinarith [sq_abs v, abs_nonneg v]
  have hxbound : epsilon^2*v^2 ≤ epsilon^2*R^2 :=
    mul_le_mul_of_nonneg_left hvsq (sq_nonneg epsilon)
  have hterm : (1-m)*(epsilon^2*v^2) ≤ L*R^2*epsilon^3 := by
    calc
      _ = (epsilon*L)*(epsilon^2*v^2) := by dsimp [m]; ring
      _ ≤ (epsilon*L)*(epsilon^2*R^2) :=
        mul_le_mul_of_nonneg_left hxbound (by positivity)
      _ = _ := by ring
  have hdle : d^2 ≤ epsilon^2*v^2+8*R^2*epsilon^3 := by
    have h := le_abs_self (d^2-epsilon^2*v^2)
    linarith
  have hbase : d^2 ≤ m*(epsilon^2*v^2)+C := by
    dsimp [C]
    nlinarith [hterm, hdle]
  have hscale : C ≤ 2*m*C := by
    have hmul := mul_le_mul_of_nonneg_right hmhalf hC
    nlinarith
  have hfinal : d^2 ≤ 2*m*(epsilon^2*v^2/2+C) := by
    nlinarith [hbase, hscale]
  change d^2/(2*m) ≤ epsilon^2*v^2/2+C
  apply (div_le_iff₀ htwo).2
  nlinarith [hfinal]

end
end Specification
end BilinearSystems
