import BilinearSystems.PublicTheorems
import Lean.Util.FoldConsts

/-! Expanded public theorem types and their semantic dependency closure. -/
namespace BilinearSystems
namespace Specification
noncomputable section

/-- Rational-input theorem, with the real-control dynamics written out. -/
theorem expanded_unrestricted_rational_statement :
    ¬ ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin 8) ℝ)
        (φ : SignFormula (Fin m)),
      ∀ v : Fin 8 → ℝ,
        (∀ i, ∃ q : ℚ, (q : ℝ) = v i) →
        (φ.eval (fun i z => MvPolynomial.eval z (p i)) v ↔
          ∀ x y : Fin 2 → ℝ, x ≠ 0 → y ≠ 0 →
            ∃ controls : List ℝ, controls ≠ [] ∧
              controls.foldl
                (fun state u =>
                  (firstMatrix v + u • secondMatrix v).mulVec state) x = y) := by
  exact no_finite_polynomial_sign_formula_on_rational_pairs

/-- Real-input theorem: the full controllability locus is not described by
any finite Boolean formula of real-coefficient polynomial signs. -/
theorem expanded_unrestricted_real_statement :
    ¬ ∃ (m : ℕ) (p : Fin m → MvPolynomial (Fin 8) ℝ)
        (φ : SignFormula (Fin m)),
      ∀ v : Fin 8 → ℝ,
        (φ.eval (fun i z => MvPolynomial.eval z (p i)) v ↔
          (∀ x y : Fin 2 → ℝ, x ≠ 0 → y ≠ 0 →
            ∃ controls : List ℝ, controls ≠ [] ∧
              controls.foldl
                (fun state u =>
                  (firstMatrix v + u • secondMatrix v).mulVec state) x = y)) := by
  exact full_controllability_locus_not_semialgebraic

end
end Specification
end BilinearSystems

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := #[
    `BilinearSystems.Specification.no_finite_polynomial_sign_formula_on_rational_pairs,
    `BilinearSystems.Specification.full_controllability_locus_not_semialgebraic]
  let mut pending : Array Name := #[]
  for root in roots do
    let some ci := env.find? root | throwError "Missing public theorem {root}"
    pending := pending ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if !seen.contains name then
      seen := seen.insert name
      if let some idx := env.getModuleIdxFor? name then
        let modName := env.header.moduleNames[idx.toNat]!
        if modName.toString.startsWith "BilinearSystems" then
          unless modName == `BilinearSystems.Definitions do
            throwError "Semantic dependency outside Definitions.lean: {name} in {modName}"
          let some ci := env.find? name | throwError "Missing constant {name}"
          for dep in ci.getUsedConstantsAsSet.toList do
            pending := pending.push dep
          match ci with
          | .inductInfo info =>
            for ctor in info.ctors do
              pending := pending.push ctor
          | _ => pure ()
  logInfo "Semantic dependency check passed."
