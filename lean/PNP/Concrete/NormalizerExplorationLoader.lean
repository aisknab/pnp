/-
Copyright (c) 2026 PNP Labs.

Closed exploration data loader. Read the original variable width and the
formula/matching sections, then count the actual formula separators.
Neither a clause count, vertex list, predecessor trace nor search budget
is supplied by the caller.
-/

import PNP.Concrete.NormalizerClauseCountCanonical

namespace PNP.Concrete.NormalizerBlocks.Exploration
open BitRegister Occurrence

def initial (input : BitString) : State := ⟨Extraction.initial input, []⟩
def readWidth : Block 28 := liftCore TableInit.header
def widthRead (input : BitString) : State :=
  (initial input).withRegisters (TableInit.readCount input).state
theorem readWidth_exec (input : BitString) :
    Exec readWidth (initial input).store (TableInit.headerFuel input) (widthRead input).store :=
  liftCore_exec _ (initial input) _ _ (TableInit.header_exec input)

def saveWidth : Block 28 := .action (.copy 17 1)
def widthSaved (r : State) : State :=
  r.withCore (r.core.withParent {r.core.parent with targetIndex := r.registers.target})
theorem saveWidth_exec (r : State) : Exec saveWidth r.store 1 (widthSaved r).store := .action _ _

def loadData : Block 28 := lift Extraction.loadData
def dataResult (r : State) : State := r.withCore (Extraction.dataResult r.core)
def dataFuel (r : State) : Nat := Extraction.dataFuel r.core
theorem loadData_exec (r : State) : Exec loadData r.store (dataFuel r) (dataResult r).store :=
  lift_exec _ r _ _ (Extraction.loadData_exec r.core)

def saveFormula : Block 28 := lift Extraction.saveFormula
def formulaSaved (r : State) : State := r.withCore (Extraction.formulaSaved r.core)
theorem saveFormula_exec (r : State) : Exec saveFormula r.store 1 (formulaSaved r).store :=
  lift_exec _ r _ _ (Extraction.saveFormula_exec r.core)
def saveMatching : Block 28 := lift Extraction.saveMatching
def matchingSaved (r : State) : State := r.withCore (Extraction.matchingSaved r.core)
theorem saveMatching_exec (r : State) : Exec saveMatching r.store 1 (matchingSaved r).store :=
  lift_exec _ r _ _ (Extraction.saveMatching_exec r.core)

def prepareCount : Block 28 := .seq (.action (.copy 0 11)) (.action (.clear 1))
def countPrepared (r : State) : State :=
  r.withRegisters {r.registers with input := r.core.parent.graph.core.formula, target := []}
theorem prepareCount_exec (r : State) : Exec prepareCount r.store 2 (countPrepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

def countFormula : Block 28 := liftCore ClauseCount.loop
def counted (r : State) : State :=
  r.withRegisters (ClauseCount.run r.registers.input r.registers).state
def countFuel (r : State) : Nat := (ClauseCount.run r.registers.input r.registers).fuel
theorem countFormula_exec (r : State) : Exec countFormula r.store (countFuel r) (counted r).store :=
  liftCore_exec _ r _ _ (ClauseCount.run_exec r.registers.input r.registers)
theorem counted_result (r : State) :
    counted r = r.withRegisters {r.registers with input := [], target := List.replicate (ClauseCount.count r.registers.input) true ++ r.registers.target} := by
  unfold counted
  rw [ClauseCount.run_result]

def saveCount : Block 28 := .action (.copy 20 1)
def countSaved (r : State) : State :=
  r.withCore (r.core.withParent {r.core.parent with currentIndex := r.registers.target})
theorem saveCount_exec (r : State) : Exec saveCount r.store 1 (countSaved r).store := .action _ _

def afterWidth (input : BitString) : State := widthSaved (widthRead input)
def formulaLoaded (input : BitString) : State := formulaSaved (dataResult (afterWidth input))
def matchingLoaded (input : BitString) : State := matchingSaved (dataResult (formulaLoaded input))
def loaded (input : BitString) : State := countSaved (counted (countPrepared (matchingLoaded input)))
def loader : Block 28 :=
  .seq readWidth <| .seq saveWidth <| .seq loadData <| .seq saveFormula <|
    .seq loadData <| .seq saveMatching <| .seq prepareCount (.seq countFormula saveCount)
def loaderFuel (input : BitString) : Nat :=
  TableInit.headerFuel input + (1 + (dataFuel (afterWidth input) +
    (1 + (dataFuel (formulaLoaded input) + (1 + (2 + (countFuel (countPrepared (matchingLoaded input)) + 1)))))))

theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  Exec.seq (readWidth_exec input) <| Exec.seq (saveWidth_exec (widthRead input)) <|
    Exec.seq (loadData_exec (afterWidth input)) <| Exec.seq (saveFormula_exec (dataResult (afterWidth input))) <|
      Exec.seq (loadData_exec (formulaLoaded input)) <| Exec.seq (saveMatching_exec (dataResult (formulaLoaded input))) <|
        Exec.seq (prepareCount_exec (matchingLoaded input)) <|
          Exec.seq (countFormula_exec (countPrepared (matchingLoaded input)))
            (saveCount_exec (counted (countPrepared (matchingLoaded input))))

def sourceWidth (input : BitString) : BitString := (TableInit.readCount input).state.target
def sourceTail (input : BitString) : BitString := (TableInit.readCount input).state.input
def sourceFormula (input : BitString) : BitString := (BatchPacket.coreResult (sourceTail input)).output
def sourceMatching (input : BitString) : BitString :=
  (BatchPacket.coreResult (BatchPacket.coreResult (sourceTail input)).input).output
def sourceCount (input : BitString) : Nat := ClauseCount.count (sourceFormula input)

theorem loaded_fields (input : BitString) :
    (loaded input).core.parent.targetIndex = sourceWidth input ∧
      (loaded input).core.parent.currentIndex = List.replicate (sourceCount input) true ∧
        (loaded input).core.parent.graph.core.formula = sourceFormula input ∧
          (loaded input).core.parent.graph.core.matching = sourceMatching input ∧
            (loaded input).core.trace = [] ∧ (loaded input).remaining = [] := by
  unfold loaded
  rw [counted_result]
  simp only [countSaved, countPrepared, matchingLoaded, matchingSaved, formulaLoaded, formulaSaved,
    dataResult, afterWidth, widthSaved, widthRead, State.withRegisters, State.withCore, State.registers,
    Extraction.State.withRegisters, Extraction.State.withParent, Extraction.State.parent,
    Extraction.State.registers, ParentQuery.State.withRegisters, ParentQuery.State.registers,
    Extraction.dataResult, Extraction.formulaSaved, Extraction.matchingSaved]
  exact ⟨rfl, by rw [List.append_nil]; rfl, rfl, rfl, rfl, rfl⟩

theorem source_sizes (input : BitString) :
    (sourceWidth input).length ≤ 5 * input.length + 6 ∧
      (sourceFormula input).length ≤ input.length ∧ (sourceMatching input).length ≤ input.length ∧
        sourceCount input ≤ input.length := by
  have width := TableInit.count_length_bound input
  have tail := Occurrence.header_input_bound input (TableInit.seeded input)
  have formula := BatchPacket.core_size (sourceTail input)
  have matching := BatchPacket.core_size (BatchPacket.coreResult (sourceTail input)).input
  change (sourceTail input).length ≤ input.length at tail
  change (sourceFormula input).length + (BatchPacket.coreResult (sourceTail input)).input.length ≤
    (sourceTail input).length at formula
  change (sourceMatching input).length +
    (BatchPacket.coreResult (BatchPacket.coreResult (sourceTail input)).input).input.length ≤
      (BatchPacket.coreResult (sourceTail input)).input.length at matching
  have counted := ClauseCount.count_bound (sourceFormula input)
  exact ⟨width, by omega, by omega, by unfold sourceCount; omega⟩

theorem loaderFuel_bound (input : BitString) : loaderFuel input ≤ 100 * input.length + 200 := by
  have header := TableInit.headerFuel_bound input
  have tail := Occurrence.header_input_bound input (TableInit.seeded input)
  have firstSize := BatchPacket.core_size (sourceTail input)
  have first := BatchPacket.coreFuel_bound (sourceTail input)
  have second := BatchPacket.coreFuel_bound (BatchPacket.coreResult (sourceTail input)).input
  have count := ClauseCount.run_fuel_bound
    (countPrepared (matchingLoaded input)).registers.input (countPrepared (matchingLoaded input)).registers
  change (sourceTail input).length ≤ input.length at tail
  change (sourceFormula input).length + (BatchPacket.coreResult (sourceTail input)).input.length ≤
    (sourceTail input).length at firstSize
  change countFuel (countPrepared (matchingLoaded input)) ≤ 6 * (sourceFormula input).length + 1 at count
  change TableInit.headerFuel input + (1 + ((8 + BatchPacket.coreFuel (sourceTail input)) +
    (1 + ((8 + BatchPacket.coreFuel (BatchPacket.coreResult (sourceTail input)).input) +
      (1 + (2 + (countFuel (countPrepared (matchingLoaded input)) + 1))))))) ≤ _
  omega

def encode (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : BitString :=
  TableInit.encodeCount variables
    (TableInit.encodeCount (GraphQuery.clauseData clauses).length
      (GraphQuery.clauseData clauses ++
        TableInit.encodeCount (MatchingTable.encode entries).length (MatchingTable.encode entries ++ [])))

theorem source_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    sourceWidth (encode variables clauses entries) = List.replicate variables true ∧
      sourceFormula (encode variables clauses entries) = GraphQuery.clauseData clauses ∧
        sourceMatching (encode variables clauses entries) = MatchingTable.encode entries ∧
          sourceCount (encode variables clauses entries) = clauses.length := by
  simp only [sourceWidth, sourceFormula, sourceMatching, sourceCount, sourceTail, encode,
    BatchPacket.header_canonical, BatchPacket.core_canonical, TableInit.canonicalHeader,
    ClauseCount.count_formula]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

end PNP.Concrete.NormalizerBlocks.Exploration
