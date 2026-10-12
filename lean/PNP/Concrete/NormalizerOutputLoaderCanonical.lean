/-
Copyright (c) 2026 PNP Labs.

Exact frontend-record consumption. Both widths and all ordered clause
bytes are derived from the record; only the original width survives as
recovery data. No decoded formula or boundary certificate is supplied.
-/
import PNP.Concrete.NormalizerOutputLoader

namespace PNP.Concrete.NormalizerBlocks.OutputLoader
open BitRegister Occurrence
open OutputBranches (State)

def originalHeader (input : BitString) : Registers := (TableInit.readCount input.tail).state
def frontendHeader (input : BitString) : Registers := (TableInit.readCount (originalHeader input).input).state
def checkerInput (input : BitString) : BitString :=
  TableInit.encodeCount (frontendHeader input).target.length (BitString.frame (frontendHeader input).input)
theorem headers_result (r : State) :
    headers.result r = {r.withRegisters (frontendHeader r.registers.input) with
      b := (originalHeader r.registers.input).target,a := (frontendHeader r.registers.input).target} := rfl
theorem frameInput_result (r : State) :
    frameInput.result r = r.withRegisters {r.registers with
      excess := [],output := TableInit.encodeCount r.a.length (BitString.frame r.registers.input)} := rfl
theorem commitInput_result (r : State) :
    commitInput.result r = {r.withRegisters (initialRegisters r.registers.output) with a := []} := rfl
theorem loaded_result (r : State) :
    loaded r = {r.withRegisters (initialRegisters (checkerInput r.registers.input)) with
      b := (originalHeader r.registers.input).target,a := []} := by
  change commitInput.result (frameInput.result (headers.result r)) = _
  rw [commitInput_result,frameInput_result,headers_result]
  rfl

def initial (input : BitString) : State := OutputBranches.extend (CutDriver.initial input) []
def ready (input : BitString) : State :=
  OutputBranches.extend (CutDriver.initial (checkerInput input)) (originalHeader input).target
private theorem initial_replace (input next width : BitString) :
    {(initial input).withRegisters (initialRegisters next) with b := width,a := []} =
      OutputBranches.extend (CutDriver.initial next) width := by
  dsimp only [initial,OutputBranches.extend,SourceAssembly.extended,SourceAssembly.rowsView,
    SourceAssembly.coefficientView,SourceAssembly.word,SourceAssembly.recovery,
    CutDriver.initial,MatchingDriver.initial,Search.initial,Exploration.initial,
    Extraction.initial,Eligibility.initial,ParentQuery.initial,EdgeKinds.initial,ForwardEdge.initial,
    CutDriver.State.store,CutDriver.State.frame,CutDriver.State.registers,
    MatchingDriver.State.store,MatchingDriver.State.frame,MatchingDriver.State.registers,
    Search.State.store,Search.State.frame,Search.State.registers,Search.State.parent,
    Exploration.State.store,Exploration.State.frame,Exploration.State.registers,
    Extraction.State.store,Extraction.State.frame,Extraction.State.registers,Extraction.State.parent,
    Eligibility.State.store,Eligibility.State.frame,ParentQuery.State.store,ParentQuery.State.frame,
    ParentQuery.State.registers,EdgeKinds.State.store,EdgeKinds.State.frame,
    ForwardEdge.State.store,ForwardEdge.State.frame,Registers.store,initialRegisters,
    Frame.join,Store.get,Store.indexCases]
  all_goals rfl
theorem initial_input (input : BitString) : (initial input).registers.input = input := rfl
theorem loaded_initial (input : BitString) : loaded (initial input) = ready input := by
  have value := loaded_result (initial input)
  rw [initial_input] at value
  exact value.trans (initial_replace input (checkerInput input) (originalHeader input).target)
theorem loader_exec (input : BitString) :
    Exec block (initial input).store (fuel (initial input)) (ready input).store := by
  rw [← loaded_initial]
  exact block_exec (initial input)
theorem initial_bounded (input : BitString) : (initial input).store.Bounded input.length :=
  OutputBranches.extend_bounded (CutDriver.initial input) [] input.length
    (CutDriver.initial_bounded input) (Nat.zero_le _)
theorem initial_output (input : BitString) : (initial input).registers.output = [] := rfl

theorem originalHeader_canonical (width : Nat) (F : CNFFormula) :
    originalHeader (NANDFrontend.recordData width F) =
      TableInit.canonicalHeader width (CNFRegisterDecoder.formulaData F) :=
  BatchPacket.header_canonical width (CNFRegisterDecoder.formulaData F)
theorem frontendHeader_canonical (width : Nat) (F : CNFFormula) :
    frontendHeader (NANDFrontend.recordData width F) =
      TableInit.canonicalHeader F.variableCount (GraphQuery.clauseData F.clauses) := by
  rw [frontendHeader,originalHeader_canonical]
  exact BatchPacket.header_canonical F.variableCount (GraphQuery.clauseData F.clauses)
theorem checkerInput_canonical (width : Nat) (F : CNFFormula) :
    checkerInput (NANDFrontend.recordData width F) = MatchingDriver.encode F.variableCount F.clauses := by
  rw [checkerInput,frontendHeader_canonical]
  simp only [TableInit.canonicalHeader,List.length_replicate]
  rfl
theorem ready_canonical (width : Nat) (F : CNFFormula) :
    ready (NANDFrontend.recordData width F) =
      OutputBranches.extend (CutDriver.initial (MatchingDriver.encode F.variableCount F.clauses))
        (List.replicate width true) := by
  rw [ready,checkerInput_canonical,originalHeader_canonical]
  rfl

end PNP.Concrete.NormalizerBlocks.OutputLoader
