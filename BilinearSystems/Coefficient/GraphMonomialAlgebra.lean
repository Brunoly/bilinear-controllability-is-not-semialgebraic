import BilinearSystems.Coefficient.GraphPolynomialEval

/-!
# Graph monomial algebra
-/
namespace BilinearSystems
namespace Specification
noncomputable section

theorem normalized_monomial_ge
    (d b L : ℝ) (hd : d ≠ 0) (hL : L ≠ 0)
    (i j m j₀ r s : ℕ) (hdeg : i+j=m+r) (hj : j=j₀+s) :
    d^i*b^j/(d^m/L^j₀) = (b*L/d)^j*d^r/L^s := by
  have hA : d^i*d^j=d^m*d^r := by
    calc
      d^i*d^j = d^(i+j) := (pow_add d i j).symm
      _ = d^(m+r) := by rw [hdeg]
      _ = d^m*d^r := pow_add d m r
  have hB : L^j=L^j₀*L^s := by rw [hj, pow_add]
  rw [div_pow, mul_pow]
  field_simp [hd, hL]
  calc
    d^i * b^j * L^j₀ * d^j * L^s =
        (d^i*d^j)*(L^j₀*L^s)*b^j := by ring
    _ = (d^m*d^r)*L^j*b^j := by rw [hA, ← hB]
    _ = b^j*d^m*L^j*d^r := by ring

theorem normalized_monomial_lt
    (d b L : ℝ) (hd : d ≠ 0) (hL : L ≠ 0)
    (i j m j₀ r s : ℕ) (hdeg : i+j=m+r) (hj : j₀=j+s) :
    d^i*b^j/(d^m/L^j₀) = (b*L/d)^j*d^r*L^s := by
  have hA : d^i*d^j=d^m*d^r := by
    calc
      d^i*d^j = d^(i+j) := (pow_add d i j).symm
      _ = d^(m+r) := by rw [hdeg]
      _ = d^m*d^r := pow_add d m r
  have hB : L^j₀=L^j*L^s := by rw [hj, pow_add]
  rw [div_pow, mul_pow]
  field_simp [hd, hL]
  calc
    d^i * b^j * L^j₀ * d^j =
        (d^i*d^j)*b^j*L^j₀ := by ring
    _ = (d^m*d^r)*b^j*(L^j*L^s) := by rw [hA, hB]
    _ = b^j*d^m*L^j*d^r*L^s := by ring

end
end Specification
end BilinearSystems
