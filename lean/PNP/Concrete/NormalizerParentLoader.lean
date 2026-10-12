/-
Copyright (c) 2026 PNP Labs.

Closed parent-query input loader. A target tag and unary index precede two
length-delimited data sections (formula and matching). The remaining bytes
are the complete trace, including optional predecessor metadata.
-/

import PNP.Concrete.NormalizerParentPhase

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister Occurrence

def initial (input : BitString) : State := ⟨EdgeKinds.initial input, [], [], [], [], []⟩
def tags : Block 21 := .seq (.action (.copy 18 0)) (.action (.pop 0))
def tagged (input : BitString) : State := {(initial input).withRegisters (initialRegisters input.tail) with targetTag := input}
theorem tags_exec (input : BitString) : Exec tags (initial input).store 2 (tagged input).store :=
  Exec.seq (.action _ _) (.action _ _)

def saveTarget : Block 21 := .action (.copy 17 1)
def targetSaved (r : State) : State := {r with targetIndex := r.registers.target}
theorem saveTarget_exec (r : State) : Exec saveTarget r.store 1 (targetSaved r).store := .action _ _

def saveFormula : Block 21 := .action (.copy 11 8)
def formulaSaved (r : State) : State := {r with graph := {r.graph with core := {r.graph.core with formula := r.registers.output}}}
theorem saveFormula_exec (r : State) : Exec saveFormula r.store 1 (formulaSaved r).store := .action _ _

def saveMatching : Block 21 := .action (.copy 12 8)
def matchingSaved (r : State) : State := {r with graph := {r.graph with core := {r.graph.core with matching := r.registers.output}}}
theorem saveMatching_exec (r : State) : Exec saveMatching r.store 1 (matchingSaved r).store := .action _ _

def saveTrace : Block 21 := .action (.copy 16 0)
def traceSaved (r : State) : State := {r with pending := r.registers.input}
theorem saveTrace_exec (r : State) : Exec saveTrace r.store 1 (traceSaved r).store := .action _ _

def targetLoaded (input : BitString) : State := targetSaved (headerResult (tagged input))
def formulaLoaded (input : BitString) : State := formulaSaved (dataResult (targetLoaded input))
def matchingLoaded (input : BitString) : State := matchingSaved (dataResult (formulaLoaded input))
def loaded (input : BitString) : State := traceSaved (matchingLoaded input)

def loader : Block 21 :=
  .seq tags <| .seq readHeader <| .seq saveTarget <| .seq loadData <|
    .seq saveFormula <| .seq loadData <| .seq saveMatching saveTrace
def loaderFuel (input : BitString) : Nat :=
  2 + (headerFuel (tagged input) + (1 + (dataFuel (targetLoaded input) +
    (1 + (dataFuel (formulaLoaded input) + (1 + 1))))))
theorem loader_exec (input : BitString) : Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (tags_exec input) <| Exec.seq (readHeader_exec (tagged input)) <|
    Exec.seq (saveTarget_exec (headerResult (tagged input))) <|
      Exec.seq (loadData_exec (targetLoaded input)) <|
        Exec.seq (saveFormula_exec (dataResult (targetLoaded input))) <|
          Exec.seq (loadData_exec (formulaLoaded input)) <|
            Exec.seq (saveMatching_exec (dataResult (formulaLoaded input))) (saveTrace_exec (matchingLoaded input))

theorem input_tail_bound (input : BitString) : input.tail.length ≤ input.length := by
  cases input <;> simp only [List.tail_nil, List.tail_cons, List.length_nil, List.length_cons] <;> omega

theorem loader_cursors (input : BitString) :
    (targetLoaded input).registers.input.length ≤ input.length ∧
      (formulaLoaded input).registers.input.length ≤ input.length ∧
        (matchingLoaded input).registers.input.length ≤ input.length := by
  have tail := input_tail_bound input
  have first := Occurrence.header_input_bound input.tail (TableInit.seeded input.tail)
  change (targetLoaded input).registers.input.length ≤ input.tail.length at first
  have second := BatchPacket.core_size (targetLoaded input).registers.input
  change (formulaLoaded input).graph.core.formula.length +
    (formulaLoaded input).registers.input.length ≤ (targetLoaded input).registers.input.length at second
  have third := BatchPacket.core_size (formulaLoaded input).registers.input
  change (matchingLoaded input).graph.core.matching.length +
    (matchingLoaded input).registers.input.length ≤ (formulaLoaded input).registers.input.length at third
  exact ⟨by omega, by omega, by omega⟩

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 70 * input.length + 120 := by
  have tail := input_tail_bound input
  have header := TableInit.headerFuel_bound input.tail
  have cursors := loader_cursors input
  have formula := BatchPacket.coreFuel_bound (targetLoaded input).registers.input
  have matching := BatchPacket.coreFuel_bound (formulaLoaded input).registers.input
  change 2 + ((8 + TableInit.headerFuel input.tail) +
    (1 + ((8 + BatchPacket.coreFuel (targetLoaded input).registers.input) +
    (1 + ((8 + BatchPacket.coreFuel (formulaLoaded input).registers.input) + (1 + 1)))))) ≤ _
  omega

theorem loaded_size (input : BitString) :
    (loaded input).targetIndex.length ≤ 5 * input.length + 6 ∧
      (loaded input).graph.core.formula.length ≤ input.length ∧
        (loaded input).graph.core.matching.length ≤ input.length ∧ (loaded input).pending.length ≤ input.length := by
  have tail := input_tail_bound input
  have target := TableInit.count_length_bound input.tail
  change (loaded input).targetIndex.length ≤ 5 * input.tail.length + 6 at target
  have cursors := loader_cursors input
  have formula := BatchPacket.core_size (targetLoaded input).registers.input
  change (loaded input).graph.core.formula.length + (formulaLoaded input).registers.input.length ≤
    (targetLoaded input).registers.input.length at formula
  have matching := BatchPacket.core_size (formulaLoaded input).registers.input
  change (loaded input).graph.core.matching.length + (loaded input).pending.length ≤
    (formulaLoaded input).registers.input.length at matching
  exact ⟨by omega, by omega, by omega, cursors.2.2⟩

def encode (target : CNFLiteral) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) : BitString :=
  target.positive :: TableInit.encodeCount target.variableIndex
    (TableInit.encodeCount (GraphQuery.clauseData clauses).length
      (GraphQuery.clauseData clauses ++ TableInit.encodeCount (MatchingTable.encode entries).length
        (MatchingTable.encode entries ++ TraceData.encode trace)))

theorem loaded_canonical (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    Canonical (loaded (encode target clauses entries trace)) target clauses entries ∧
      (loaded (encode target clauses entries trace)).pending = TraceData.encode trace := by
  constructor
  · constructor
    · change (TableInit.readCount (encode target clauses entries trace).tail).state.target = _
      simp only [encode, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader]
    · rfl
    · change (BatchPacket.coreResult (TableInit.readCount (encode target clauses entries trace).tail).state.input).output = _
      simp only [encode, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader, BatchPacket.core_canonical]
    · change (BatchPacket.coreResult (BatchPacket.coreResult
        (TableInit.readCount (encode target clauses entries trace).tail).state.input).input).output = _
      simp only [encode, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader, BatchPacket.core_canonical]
  · change (BatchPacket.coreResult (BatchPacket.coreResult
      (TableInit.readCount (encode target clauses entries trace).tail).state.input).input).input = _
    simp only [encode, List.tail_cons, BatchPacket.header_canonical, TableInit.canonicalHeader, BatchPacket.core_canonical]

end PNP.Concrete.NormalizerBlocks.ParentQuery
