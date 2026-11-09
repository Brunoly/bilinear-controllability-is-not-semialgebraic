import BilinearSystems
import Lean.Util.CollectAxioms

/-! Check the transitive axiom dependencies of all project declarations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if origin.toString.startsWith "BilinearSystems" then
        count := count + 1
        for axiomName in (← Lean.collectAxioms name).toList do
          unless allowed.contains axiomName do
            throwError "Unexpected axiom {axiomName} in {name}"
  logInfo m!"Axiom audit passed for {count} project declarations."
