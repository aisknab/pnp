/-
Copyright (c) 2026 PNP Labs.

Internal calls used by the complete cut. Clause count comes from the saved
formula bytes; variable count comes from the saved input width. Both calls
read the same internally computed trace. Their outputs are retained outside
the shared scratch registers for subsequent preparation and serialization.
-/
import PNP.Concrete.NormalizerCutState

namespace PNP.Concrete.NormalizerBlocks.CutDriver
open BitRegister Occurrence

def prepareCount : Block 36 := .seq (.action (.copy 0 30)) (.action (.clear 1))
def countPrepared (r : State) : State :=
  r.withRegisters {r.registers with input := r.core.formula, target := []}
theorem prepareCount_exec (r : State) : Exec prepareCount r.store 2 (countPrepared r).store := by
  dsimp only [prepareCount, countPrepared, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact Exec.seq (.action _ _) (.action _ _)

def countFormula : Block 36 := liftCore ClauseCount.loop
def counted (r : State) : State :=
  r.withRegisters (ClauseCount.run r.registers.input r.registers).state
def countSteps (r : State) : Nat := (ClauseCount.run r.registers.input r.registers).fuel
theorem countFormula_exec (r : State) :
    Exec countFormula r.store (countSteps r) (counted r).store :=
  liftCore_exec _ r _ _ (ClauseCount.run_exec r.registers.input r.registers)
theorem counted_target (r : State) :
    (counted r).registers.target =
      List.replicate (ClauseCount.count r.registers.input) true ++ r.registers.target := by
  change (ClauseCount.run r.registers.input r.registers).state.target = _
  rw [ClauseCount.run_result]

def loadTrace : Block 36 := .action (.copy 0 33)
def traceLoaded (r : State) : State := r.withRegisters {r.registers with input := r.trace}
theorem loadTrace_exec (r : State) : Exec loadTrace r.store 1 (traceLoaded r).store := by
  dsimp only [loadTrace, traceLoaded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact .action _ _

def loadWidth : Block 36 := .action (.copy 1 29)
def widthLoaded (r : State) : State := r.withRegisters {r.registers with target := r.core.width}
theorem loadWidth_exec (r : State) : Exec loadWidth r.store 1 (widthLoaded r).store := by
  dsimp only [loadWidth, widthLoaded, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact .action _ _

def prepareClauses : Block 36 := .seq prepareCount (.seq countFormula loadTrace)
def clauseReady (r : State) : State := traceLoaded (counted (countPrepared r))
def clausePrepSteps (r : State) : Nat := 2 + (countSteps (countPrepared r) + 1)
theorem prepareClauses_exec (r : State) :
    Exec prepareClauses r.store (clausePrepSteps r) (clauseReady r).store :=
  Exec.seq (prepareCount_exec r) <| Exec.seq (countFormula_exec (countPrepared r)) (loadTrace_exec _)
theorem clausePrepSteps_bound (r : State) : clausePrepSteps r ≤ 6 * r.core.formula.length + 4 := by
  have counted := ClauseCount.run_fuel_bound (countPrepared r).registers.input (countPrepared r).registers
  change countSteps (countPrepared r) ≤ 6 * r.core.formula.length + 1 at counted
  unfold clausePrepSteps
  omega
theorem clauseReady_input (r : State) : (clauseReady r).registers.input = r.trace := rfl
theorem clauseReady_target (r : State) :
    (clauseReady r).registers.target = List.replicate (ClauseCount.count r.core.formula) true := by
  change (counted (countPrepared r)).registers.target = _
  rw [counted_target]
  exact List.append_nil _
theorem clauseReady_frame (r : State) :
    (clauseReady r).core.width = r.core.width ∧ (clauseReady r).core.formula = r.core.formula ∧
    (clauseReady r).core.table = r.core.table ∧ (clauseReady r).trace = r.trace ∧
    (clauseReady r).clauses = r.clauses ∧ (clauseReady r).variables = r.variables :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def prepareVariables : Block 36 := .seq loadWidth loadTrace
def variableReady (r : State) : State := traceLoaded (widthLoaded r)
theorem prepareVariables_exec (r : State) :
    Exec prepareVariables r.store 2 (variableReady r).store :=
  Exec.seq (loadWidth_exec r) (loadTrace_exec (widthLoaded r))
theorem variableReady_fields (r : State) :
    (variableReady r).registers.input = r.trace ∧ (variableReady r).registers.target = r.core.width :=
  ⟨rfl,rfl⟩
theorem variableReady_frame (r : State) :
    (variableReady r).core.width = r.core.width ∧ (variableReady r).core.formula = r.core.formula ∧
    (variableReady r).core.table = r.core.table ∧ (variableReady r).trace = r.trace ∧
    (variableReady r).clauses = r.clauses ∧ (variableReady r).variables = r.variables :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def select (tag : Bool) : Block 36 := liftSelection (CutSelection.call tag)
def selected (tag : Bool) (r : State) : State := r.withSelection (CutSelection.called tag r.selection)
def selectSteps (tag : Bool) (r : State) : Nat := CutSelection.callSteps tag r.selection
theorem select_exec (tag : Bool) (r : State) :
    Exec (select tag) r.store (selectSteps tag r) (selected tag r).store :=
  liftSelection_exec _ r _ _ (CutSelection.call_exec tag r.selection)
theorem selectSteps_bound (tag : Bool) (r : State) (bound : Nat) (h : r.store.Bounded bound) :
    selectSteps tag r ≤ CutSelection.callBound.eval bound :=
  CutSelection.callSteps_bound tag r.selection bound (selection_bounded r bound h)
theorem selected_output (tag : Bool) (r : State) (count : Nat) (trace : List TraceData.Row)
    (countRead : r.registers.target = List.replicate count true)
    (traceRead : r.registers.input = TraceData.encode trace) :
    (selected tag r).registers.output =
      SearchVertices.encodeVertices (CutSelection.selected tag trace count 0) := by
  exact CutSelection.called_canonical tag r.selection count trace countRead traceRead
theorem selected_frame (tag : Bool) (r : State) :
    (selected tag r).core.width = r.core.width ∧ (selected tag r).core.formula = r.core.formula ∧
    (selected tag r).core.table = r.core.table ∧ (selected tag r).trace = r.trace ∧
    (selected tag r).clauses = r.clauses ∧ (selected tag r).variables = r.variables :=
  withSelection_frame r (CutSelection.called tag r.selection)

def saveClauses : Block 36 := .action (.copy 34 8)
def clausesSaved (r : State) : State := {r with clauses := r.registers.output}
theorem saveClauses_exec (r : State) : Exec saveClauses r.store 1 (clausesSaved r).store := by
  dsimp only [saveClauses, clausesSaved, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact .action _ _
def saveVariables : Block 36 := .action (.copy 35 8)
def variablesSaved (r : State) : State := {r with variables := r.registers.output}
theorem saveVariables_exec (r : State) : Exec saveVariables r.store 1 (variablesSaved r).store := by
  dsimp only [saveVariables, variablesSaved, State.store, State.frame, State.registers, MatchingDriver.State.store, MatchingDriver.State.frame, MatchingDriver.State.registers, Search.State.store, Search.State.frame, Search.State.registers, Search.State.parent, Exploration.State.store, Exploration.State.frame, Exploration.State.registers, Extraction.State.store, Extraction.State.frame, Extraction.State.parent, Extraction.State.registers, Eligibility.State.store, Eligibility.State.frame, ParentQuery.State.store, ParentQuery.State.frame, ParentQuery.State.registers, EdgeKinds.State.store, EdgeKinds.State.frame, ForwardEdge.State.store, ForwardEdge.State.frame, Registers.store, Frame.join, State.withRegisters, State.withCore, MatchingDriver.State.withRegisters, MatchingDriver.State.withCore, Search.State.withRegisters, Search.State.withCore, Exploration.State.withRegisters, Exploration.State.withCore, Extraction.State.withRegisters, Extraction.State.withParent, ParentQuery.State.withRegisters]
  exact .action _ _

end PNP.Concrete.NormalizerBlocks.CutDriver
