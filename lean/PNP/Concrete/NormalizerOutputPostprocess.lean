/-
Copyright (c) 2026 PNP Labs.

One finite routine consumes the actual frontend record, preserves its original
width, checks the transformed formula and emits the selected complete packet.
Invalid frontend records produce the malformed tag, not a substituted problem.
-/
import PNP.Concrete.NormalizerOutputLoaderCanonical

namespace PNP.Concrete.NormalizerBlocks.OutputPostprocess
open BitRegister Occurrence
open OutputBranches (State)

abbrev initial := OutputLoader.initial
def width (input : BitString) : BitString := (OutputLoader.originalHeader input).target
def checker (input : BitString) : CutDriver.State := SourceCheck.result (OutputLoader.checkerInput input)
def checked (input : BitString) : State := OutputBranches.extend (checker input) (width input)
def check : Block 38 := OutputBranches.liftCheck SourceCheck.block
theorem check_exec (input : BitString) :
    Exec check (OutputLoader.ready input).store
      (SourceCheck.sourceSteps (OutputLoader.checkerInput input)) (checked input).store :=
  OutputBranches.liftCheck_exec _ _ _ _ _ (SourceCheck.block_exec (OutputLoader.checkerInput input))

def valid : Block 38 := .seq OutputLoader.block (.seq check OutputBranches.dispatch)
def validResult (input : BitString) : State := OutputBranches.dispatched (checker input) (width input)
def validSteps (input : BitString) : Nat :=
  OutputLoader.fuel (initial input) +
    (SourceCheck.sourceSteps (OutputLoader.checkerInput input) +
      OutputBranches.dispatchFuel (checker input) (width input))
theorem valid_exec (input : BitString) :
    Exec valid (initial input).store (validSteps input) (validResult input).store :=
  Exec.seq (OutputLoader.loader_exec input)
    (Exec.seq (check_exec input) (OutputBranches.dispatch_exec (checker input) (width input)))

def invalid : Block 38 := OutputBranches.liftPacket PacketFrame.malformed
def invalidResult (input : BitString) : State :=
  (initial input).withRegisters (PacketFrame.malformedResult (initial input).registers)
theorem invalid_exec (input : BitString) :
    Exec invalid (initial input).store 4 (invalidResult input).store :=
  OutputBranches.liftPacket_exec _ _ _ _ (PacketFrame.malformed_exec (initial input).registers)
theorem invalid_output (input : BitString) :
    (invalidResult input).registers.output = [false,false,false] := rfl

def block : Block 38 := .branch 0 invalid invalid valid
def program : Program 38 := block.program 0 8
def result (input : BitString) : State :=
  if input.headD false then validResult input else invalidResult input
def sourceSteps (input : BitString) : Nat := 1+if input.headD false then validSteps input else 4

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(initial input).store⟩ := by
  have core : (Store.empty 36).set (0 : Fin 36) input = (CutDriver.initial input).store := by
    simpa only [BitRegister.initial,CutDriver.program,Block.program] using
      congrArg BitRegister.Configuration.store (CutDriver.initial_registers input)
  change ⟨.running 0,(Store.empty 38).set (0 : Fin 38) input⟩ =
    (⟨.running 0,(OutputBranches.extend (CutDriver.initial input) []).store⟩ : BitRegister.Configuration 38)
  rw [OutputBranches.extend_store,← core]
  rfl
theorem store_input (r : State) : r.store.get (0 : Fin 38) = r.registers.input := rfl
theorem store_output (r : State) : r.store.get (8 : Fin 38) = r.registers.output := rfl
theorem initial_input (input : BitString) : (initial input).store.get (0 : Fin 38) = input :=
  (store_input (initial input)).trans (OutputLoader.initial_input input)
attribute [local irreducible] CutDriver.State.store SystemAssembly.State.store

theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store := by
  have work := EdgeKinds.branch_head (0 : Fin 38) (initial input).store invalid valid
    4 (validSteps input) (invalidResult input).store (validResult input).store
    (invalid_exec input) (valid_exec input)
  rw [initial_input] at work
  cases tag : input.headD false <;>
    simpa only [block,sourceSteps,result,tag,Bool.false_eq_true,ite_false,ite_true] using work
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input+1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem malformed_output (input : BitString) (invalidTag : input.headD false = false) :
    (result input).registers.output = [false,false,false] := by
  rw [result,invalidTag]
  exact invalid_output input
theorem canonical_result (width : Nat) (F : CNFFormula) :
    result (NANDFrontend.recordData width F) =
      OutputBranches.dispatched (SourceCheck.result (MatchingDriver.encode F.variableCount F.clauses))
        (List.replicate width true) := by
  have tag : (NANDFrontend.recordData width F).headD false = true := rfl
  simp only [result,tag,ite_true,validResult,checker,OutputPostprocess.width,
    OutputLoader.checkerInput_canonical,OutputLoader.originalHeader_canonical,TableInit.canonicalHeader]

end PNP.Concrete.NormalizerBlocks.OutputPostprocess
