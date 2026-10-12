/-
Copyright (c) 2026 PNP Labs.

The complete cut is derived from the original encoded width and formula.
Matching, terminal exploration, source-order clauses and source-order variables
are computed in sequence. No matching, trace, selected family or correctness
certificate is present in the caller interface.
-/
import PNP.Concrete.NormalizerCutSelections

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister

def afterClauses (input : BitString) : State := clausesResult (initialized input)
def prepared (input : BitString) : State := variablesResult (afterClauses input)
def prepareBlock : Block 36 := .seq initializeBlock (.seq deriveClauses deriveVariables)
def prepareSteps (input : BitString) : Nat :=
  initializeSteps input + (clausesSteps (initialized input) + variablesSteps (afterClauses input))
theorem prepare_exec (input : BitString) :
    Exec prepareBlock (initial input).store (prepareSteps input) (prepared input).store :=
  Exec.seq (initialize_exec input) <|
    Exec.seq (deriveClauses_exec (initialized input)) (deriveVariables_exec (afterClauses input))

theorem initialized_data (width : Nat) (clauses : List (List CNFLiteral)) :
    (initialized (MatchingDriver.encode width clauses)).core.width = List.replicate width true ∧
    (initialized (MatchingDriver.encode width clauses)).core.formula = GraphQuery.clauseData clauses ∧
    (initialized (MatchingDriver.encode width clauses)).core.table =
      MatchingTable.encode (MatchingLoop.fullTable width clauses) ∧
    (initialized (MatchingDriver.encode width clauses)).trace =
      TraceData.encode (Search.traceValue width clauses (MatchingLoop.fullTable width clauses)) := by
  rw [(initialized_fields _).1, (initialized_fields _).2]
  have frame := CutTrace.result_frame (MatchingDriver.encode width clauses)
  have original := MatchingDriver.result_data width clauses
  exact ⟨frame.1.trans original.width, frame.2.1.trans original.formula,
    CutTrace.result_matching width clauses, CutTrace.result_canonical width clauses⟩

structure Canonical (width : Nat) (formula : List (List CNFLiteral)) (r : State) : Prop where
  widthRead : r.core.width = List.replicate width true
  formulaRead : r.core.formula = GraphQuery.clauseData formula
  matchingRead : r.core.table = MatchingTable.encode (MatchingLoop.fullTable width formula)
  traceRead : r.trace =
    TraceData.encode (Search.traceValue width formula (MatchingLoop.fullTable width formula))
  clausesRead : r.clauses = SearchVertices.encodeVertices
    (CutSelection.selected true (Search.traceValue width formula (MatchingLoop.fullTable width formula)) formula.length 0)
  variablesRead : r.variables = SearchVertices.encodeVertices
    (CutSelection.selected false (Search.traceValue width formula (MatchingLoop.fullTable width formula)) width 0)

theorem prepared_canonical (width : Nat) (formula : List (List CNFLiteral)) :
    Canonical width formula (prepared (MatchingDriver.encode width formula)) := by
  let input := MatchingDriver.encode width formula
  let trace := Search.traceValue width formula (MatchingLoop.fullTable width formula)
  have first := initialized_data width formula
  have clausesFrame := clausesResult_frame (initialized input)
  have clauses := clausesResult_canonical (initialized input) formula trace first.2.1 first.2.2.2
  have variables := variablesResult_canonical (afterClauses input) width trace
    (clausesFrame.1.trans first.1) (clausesFrame.2.2.2.1.trans first.2.2.2)
  have finalFrame := variablesResult_frame (afterClauses input)
  exact ⟨finalFrame.1.trans (clausesFrame.1.trans first.1),
    finalFrame.2.1.trans (clausesFrame.2.1.trans first.2.1),
    finalFrame.2.2.1.trans (clausesFrame.2.2.1.trans first.2.2.1),
    finalFrame.2.2.2.1.trans (clausesFrame.2.2.2.1.trans first.2.2.2),
    finalFrame.2.2.2.2.trans clauses, variables⟩

theorem prepared_frame (input : BitString) :
    (prepared input).core.width = (initialized input).core.width ∧
    (prepared input).core.formula = (initialized input).core.formula ∧
    (prepared input).core.table = (initialized input).core.table ∧
    (prepared input).trace = (initialized input).trace := by
  have first := clausesResult_frame (initialized input)
  have last := variablesResult_frame (afterClauses input)
  exact ⟨last.1.trans first.1, last.2.1.trans first.2.1,
    last.2.2.1.trans first.2.2.1, last.2.2.2.1.trans first.2.2.2.1⟩

end PNP.Concrete.NormalizerBlocks.CutDriver
