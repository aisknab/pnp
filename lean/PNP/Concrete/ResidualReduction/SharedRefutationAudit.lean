import Lean
import PNP.Concrete.ResidualReduction.SharedRefutationRegression

/-! Fail closed over the complete compiled shared-refutation namespace,
including private and compiler-generated declarations. This audits the current
construction, not the project's eligible root or publication gate. -/

open Lean Elab Command


run_cmd do
  let environment ← getEnv
  let mut checked := 0
  let mut rejected := 0
  for (name, _) in environment.constants.toList do
    if (name.toString.splitOn "PNP.Concrete.ResidualReduction.SharedRefutation").length > 1 then
      checked := checked + 1
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        if axiomName != ``propext && axiomName != ``Quot.sound then
          logInfo m!"SHARED_REFUTATION_UNEXPECTED_AXIOM {name}: {axiomName}"
          rejected := rejected + 1
  if checked = 0 then
    throwError "Shared-refutation axiom audit found no declarations"
  if rejected > 0 then
    throwError "Shared-refutation axiom audit rejected {rejected} dependency closures"
  logInfo m!"SHARED_REFUTATION_ALL_DECLARATIONS_AXIOM_OK {checked}"
