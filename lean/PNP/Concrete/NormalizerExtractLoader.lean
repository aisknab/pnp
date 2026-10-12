/-
Copyright (c) 2026 PNP Labs.

Closed extraction input loader. Formula, matching and complete trace are
length-delimited data sections, followed by the existing ordered-vertex
encoding. No target, selected vertex or eligibility verdict is supplied.
-/

import PNP.Concrete.NormalizerExtractFinish

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister Occurrence

def initial (input : BitString) : State := ⟨Eligibility.initial input, [], [], [], [], []⟩
def loadData : Block 27 := liftCore (.seq CandidatePacket.resetCore BatchPacket.coreLoader)
def dataResult (r : State) : State := r.withRegisters (BatchPacket.coreResult r.registers.input)
def dataFuel (r : State) : Nat := 8 + BatchPacket.coreFuel r.registers.input
theorem loadData_exec (r : State) : Exec loadData r.store (dataFuel r) (dataResult r).store :=
  liftCore_exec _ r _ _ (Exec.seq (CandidatePacket.resetCore_exec r.registers) (BatchPacket.core_exec r.registers.input))

def saveFormula : Block 27 := .action (.copy 11 8)
def formulaSaved (r : State) : State :=
  r.withParent {r.parent with graph := {r.parent.graph with core := {r.parent.graph.core with formula := r.registers.output}}}
theorem saveFormula_exec (r : State) : Exec saveFormula r.store 1 (formulaSaved r).store := .action _ _

def saveMatching : Block 27 := .action (.copy 12 8)
def matchingSaved (r : State) : State :=
  r.withParent {r.parent with graph := {r.parent.graph with core := {r.parent.graph.core with matching := r.registers.output}}}
theorem saveMatching_exec (r : State) : Exec saveMatching r.store 1 (matchingSaved r).store := .action _ _

def saveTrace : Block 27 := .action (.copy 24 8)
def traceSaved (r : State) : State := {r with trace := r.registers.output}
theorem saveTrace_exec (r : State) : Exec saveTrace r.store 1 (traceSaved r).store := .action _ _

def activate : Block 27 := .action (.push 25 true)
def activated (r : State) : State := {r with active := true :: r.active}
theorem activate_exec (r : State) : Exec activate r.store 1 (activated r).store := .action _ _

def defaultAnswer : Block 27 := .seq (.action (.clear 19)) (.action (.push 19 false))
def defaulted (r : State) : State := r.withParent {r.parent with output := [false]}
theorem defaultAnswer_exec (r : State) : Exec defaultAnswer r.store 2 (defaulted r).store :=
  Exec.seq (.action _ _) (.action _ _)

def formulaLoaded (input : BitString) : State := formulaSaved (dataResult (initial input))
def matchingLoaded (input : BitString) : State := matchingSaved (dataResult (formulaLoaded input))
def traceLoaded (input : BitString) : State := traceSaved (dataResult (matchingLoaded input))
def loaded (input : BitString) : State := defaulted (activated (pendingSaved (traceLoaded input)))

theorem loaded_fields (input : BitString) :
    (loaded input).parent.graph.core.formula = (BatchPacket.coreResult input).output ∧
      (loaded input).parent.graph.core.matching = (BatchPacket.coreResult (BatchPacket.coreResult input).input).output ∧
        (loaded input).trace = (BatchPacket.coreResult (BatchPacket.coreResult (BatchPacket.coreResult input).input).input).output ∧
          (loaded input).pending = (BatchPacket.coreResult (BatchPacket.coreResult (BatchPacket.coreResult input).input).input).input ∧
            (loaded input).skipped = [] ∧ (loaded input).active = [true] ∧ (loaded input).parent.output = [false] := by
  simp only [loaded, defaulted, activated, pendingSaved, traceLoaded, traceSaved, matchingLoaded, matchingSaved,
    formulaLoaded, formulaSaved, dataResult, State.withRegisters, State.withParent, State.parent, State.registers,
    ParentQuery.State.withRegisters, ParentQuery.State.registers]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩

def loader : Block 27 :=
  .seq loadData <| .seq saveFormula <| .seq loadData <| .seq saveMatching <|
    .seq loadData <| .seq saveTrace <| .seq savePending (.seq activate defaultAnswer)
def loaderFuel (input : BitString) : Nat :=
  dataFuel (initial input) + (1 + (dataFuel (formulaLoaded input) +
    (1 + (dataFuel (matchingLoaded input) + (1 + (1 + (1 + 2)))))))
theorem loader_exec (input : BitString) : Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (loadData_exec (initial input)) <| Exec.seq (saveFormula_exec (dataResult (initial input))) <|
    Exec.seq (loadData_exec (formulaLoaded input)) <| Exec.seq (saveMatching_exec (dataResult (formulaLoaded input))) <|
      Exec.seq (loadData_exec (matchingLoaded input)) <| Exec.seq (saveTrace_exec (dataResult (matchingLoaded input))) <|
        Exec.seq (savePending_exec (traceLoaded input)) <| Exec.seq (activate_exec (pendingSaved (traceLoaded input)))
          (defaultAnswer_exec (activated (pendingSaved (traceLoaded input))))

theorem loader_cursors (input : BitString) :
    (formulaLoaded input).registers.input.length ≤ input.length ∧
      (matchingLoaded input).registers.input.length ≤ input.length ∧
        (traceLoaded input).registers.input.length ≤ input.length := by
  have first := BatchPacket.core_size input
  change (formulaLoaded input).parent.graph.core.formula.length +
    (formulaLoaded input).registers.input.length ≤ input.length at first
  have second := BatchPacket.core_size (formulaLoaded input).registers.input
  change (matchingLoaded input).parent.graph.core.matching.length +
    (matchingLoaded input).registers.input.length ≤ (formulaLoaded input).registers.input.length at second
  have third := BatchPacket.core_size (matchingLoaded input).registers.input
  change (traceLoaded input).trace.length +
    (traceLoaded input).registers.input.length ≤ (matchingLoaded input).registers.input.length at third
  exact ⟨by omega, by omega, by omega⟩

theorem loaded_size (input : BitString) :
    (loaded input).parent.graph.core.formula.length ≤ input.length ∧
      (loaded input).parent.graph.core.matching.length ≤ input.length ∧
        (loaded input).trace.length ≤ input.length ∧ (loaded input).pending.length ≤ input.length := by
  have fields := loaded_fields input
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1]
  have first := BatchPacket.core_size input
  have second := BatchPacket.core_size (BatchPacket.coreResult input).input
  have third := BatchPacket.core_size (BatchPacket.coreResult (BatchPacket.coreResult input).input).input
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 99 * input.length + 157 := by
  have cursors := loader_cursors input
  have first := BatchPacket.coreFuel_bound input
  have second := BatchPacket.coreFuel_bound (formulaLoaded input).registers.input
  have third := BatchPacket.coreFuel_bound (matchingLoaded input).registers.input
  change (8 + BatchPacket.coreFuel input) + (1 + ((8 + BatchPacket.coreFuel (formulaLoaded input).registers.input) +
    (1 + ((8 + BatchPacket.coreFuel (matchingLoaded input).registers.input) + (1 + (1 + (1 + 2))))))) ≤ _
  omega

def encode (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen : List CNFLiteral) : BitString :=
  TableInit.encodeCount (GraphQuery.clauseData clauses).length
    (GraphQuery.clauseData clauses ++ TableInit.encodeCount (MatchingTable.encode entries).length
      (MatchingTable.encode entries ++ TableInit.encodeCount (TraceData.encode trace).length
        (TraceData.encode trace ++ SearchVertices.encodeVertices unseen)))

theorem loaded_canonical (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen : List CNFLiteral) :
    Canonical (loaded (encode clauses entries trace unseen)) clauses entries trace unseen [] := by
  have fields := loaded_fields (encode clauses entries trace unseen)
  constructor
  · rw [fields.1]
    simp only [encode, BatchPacket.core_canonical]
  · rw [fields.2.1]
    simp only [encode, BatchPacket.core_canonical]
  · rw [fields.2.2.1]
    simp only [encode, BatchPacket.core_canonical]
  · rw [fields.2.2.2.1]
    simp only [encode, BatchPacket.core_canonical]
  · exact fields.2.2.2.2.1
  · exact fields.2.2.2.2.2.1
  · exact fields.2.2.2.2.2.2

end PNP.Concrete.NormalizerBlocks.Extraction
