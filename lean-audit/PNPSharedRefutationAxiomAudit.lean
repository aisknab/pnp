import PNP
import Lean

/-! Root-context contract and axiom audit for source-generated shared refutations.
The public extractor is relative to a false verdict of the existing partial
reducer. Circuit size is not an encoded-runtime or circuit-identity-testing bound.
The namespace audit includes private and compiler-generated declarations. -/

open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SharedRefutationAssembly
open PNP.Concrete.ResidualReduction.SharedRefutationExtraction

example {n : Nat} : Family n → Option (Certificate n) := extract

example {n : Nat} (F : Family n) (q : Certificate n) :
    WellFormed F q ↔
      PNP.Concrete.ResidualReduction.SharedRefutationCircuit.codeValid q.1 = true ∧
      (∀ i ∈ q.2, i < q.1.length) ∧ q.2.length = F.length := Iff.rfl

example {n : Nat} (F : Family n) (q : Certificate n) :
    Refutes F q ↔ ∀ x,
      PNP.Concrete.ResidualReduction.SharedRefutationSourceLift.pairedSum
        (PNP.Concrete.ResidualReduction.SharedRefutationCircuit.outputs q.1 x q.2)
        (F.map (fun r => r.eval x)) = some true := Iff.rfl

example {n : Nat} (F : Family n) (falseVerdict : verdict F = some false) :
    ∃ q, extract F = some q ∧ WellFormed F q ∧ Refutes F q ∧
      q.1.length ≤ 2 + (4 * F.length + 1) * n :=
  extract_of_false_verdict F falseVerdict

example {n : Nat} (F : Family n) (q : Certificate n)
    (accepted : extract F = some q) : verdict F = some false :=
  extract_some_false_verdict F q accepted

example {n : Nat} (F : Family n) (q : Certificate n)
    (accepted : extract F = some q) :
    WellFormed F q ∧ Refutes F q ∧ q.1.length ≤ 2 + (4 * F.length + 1) * n :=
  extract_contract F q accepted

example {n : Nat} (F : Family n) (q : Certificate n)
    (accepted : extract F = some q) : ¬ ∃ x, models F x = true :=
  extract_unsatisfiable F q accepted

example {n d : Nat} (F : Family n) (history : List StepRecord)
    (G : Family d) (linked : Linked F history G) (seed : Certificate d)
    (wellFormed : WellFormed G seed) (refutation : Refutes G seed) :
    ∃ q, unwind seed n history = some q ∧ WellFormed F q ∧ Refutes F q ∧
      q.1.length ≤ seed.1.length + (4 * F.length + 1) * history.length :=
  unwind_linked F history G linked seed wellFormed refutation

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
          logInfo m!"SHARED_REFUTATION_ROOT_UNEXPECTED_AXIOM {name}: {axiomName}"
          rejected := rejected + 1
  if checked = 0 then
    throwError "Root-context shared-refutation audit found no declarations"
  if rejected > 0 then
    throwError "Root-context shared-refutation audit rejected {rejected} dependency closures"
  logInfo m!"SHARED_REFUTATION_ROOT_ALL_DECLARATIONS_AXIOM_OK {checked}"
