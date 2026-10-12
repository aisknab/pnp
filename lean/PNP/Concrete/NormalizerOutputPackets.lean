/-
Copyright (c) 2026 PNP Labs.

Lift exact output framing into the completed assembly state. The equation
branch keeps the actual row count while constructing every b/A/E payload;
the model framer preserves the recovered assignment verbatim.
-/
import PNP.Concrete.NormalizerOutputState
import PNP.Concrete.NormalizerPacketFrame

namespace PNP.Concrete.NormalizerBlocks.OutputBranches
open BitRegister Occurrence
open SystemAssembly (Routine)

def liftPacket (body : Block 9) : Block 38 :=
  SystemAssembly.liftRows (SystemRows.liftCore (Coefficient.liftCore body))
theorem liftPacket_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body r.registers.store fuel after.store) :
    Exec (liftPacket body) r.store fuel (r.withRegisters after).store :=
  SystemAssembly.liftRows_exec _ r _ _
    (SystemRows.liftCore_exec _ r.core _ _ (Coefficient.liftCore_exec _ r.core.core _ _ checked))

def modelPacket : Routine where
  block := liftPacket PacketFrame.model
  result r := r.withRegisters (PacketFrame.modelResult r.registers)
  fuel r := PacketFrame.modelFuel r.registers
  bound := .linear 3 6
  exec r := liftPacket_exec _ r _ _ (PacketFrame.model_exec r.registers)
  cost r n bounded := by
    have size := Store.get_length_le r.store (8 : Fin 38) bounded
    change r.registers.output.length ≤ n at size
    change 3*r.registers.output.length+6 ≤ 3*n+6
    omega
theorem modelPacket_output (r : State) :
    (modelPacket.result r).registers.output = [false,false,true] ++ BitString.frame r.registers.output :=
  PacketFrame.model_output r.registers

def loadCount : Routine where
  block := .action (.copy 3 24)
  result r := r.withRegisters {r.registers with excess := r.core.rows}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def systemPacket : Routine where
  block := liftPacket PacketFrame.system
  result r := r.withRegisters (PacketFrame.systemResult r.registers)
  fuel r := PacketFrame.systemFuel r.registers
  bound := .linear 3 5
  exec r := liftPacket_exec _ r _ _ (PacketFrame.system_exec r.registers)
  cost r n bounded := by
    have size := Store.get_length_le r.store (3 : Fin 38) bounded
    change r.registers.excess.length ≤ n at size
    change 3*r.registers.excess.length+5 ≤ 3*n+5
    omega
def frameSystem : Routine := Routine.seq loadCount systemPacket
theorem frameSystem_output (r : State) :
    (frameSystem.result r).registers.output = [false,true,false] ++
      (List.replicate r.core.rows.length true ++ false::r.registers.output) :=
  PacketFrame.system_output {r.registers with excess := r.core.rows}

theorem assembly_rows (r : State) : (SystemAssembly.result r).core.rows = r.core.rows := by
  have join : ∀ s : State, (SystemAssembly.joinPackets.result s).core.rows = s.core.rows := by
    intro s
    exact (SystemAssembly.prepend_rows .b _).trans (SystemAssembly.prepend_rows .a s)
  have construction := SystemAssembly.afterE_rows r
  rw [← SystemAssembly.construction_result] at construction
  exact (join (SystemAssembly.construction.result r)).trans construction
theorem failure_rows (r : State) : (SourceAssembly.failureResult r).core.rows = r.core.rows :=
  (assembly_rows (SourceAssembly.migrated r)).trans (SourceAssembly.migrated_frame r).1

def failureRoutine : Routine where
  block := SourceAssembly.failureBlock
  result := SourceAssembly.failureResult
  fuel := SourceAssembly.failureSteps
  bound := SourceAssembly.failureBound
  exec := SourceAssembly.failure_exec
  cost := SourceAssembly.failureSteps_bound
def equation : Routine := Routine.seq failureRoutine frameSystem
theorem equation_exec (r : State) : Exec equation.block r.store (equation.fuel r) (equation.result r).store :=
  equation.exec r
theorem equation_output (r : State) :
    (equation.result r).registers.output = [false,true,false] ++
      (List.replicate r.core.rows.length true ++ false::(SourceAssembly.failureResult r).registers.output) := by
  have output := frameSystem_output (SourceAssembly.failureResult r)
  rw [failure_rows] at output
  exact output
theorem equation_fuel_bound (r : State) (n : Nat) (bounded : r.store.Bounded n) :
    equation.fuel r ≤ equation.bound.eval n := equation.cost r n bounded

def success : Block 38 := .seq recover modelPacket.block
def succeeded (r : CutDriver.State) (width : BitString) : State := modelPacket.result (recovered r width)
def successFuel (r : CutDriver.State) (width : BitString) : Nat :=
  recoveryFuel r width+modelPacket.fuel (recovered r width)
def successBound : NatPolynomial :=
  .add recoveryBound (modelPacket.bound.substitute (.add .variable recoveryBound))
theorem success_exec (r : CutDriver.State) (width : BitString) :
    Exec success (extend r width).store (successFuel r width) (succeeded r width).store :=
  Exec.seq (recover_exec r width) (modelPacket.exec (recovered r width))
theorem success_output (r : CutDriver.State) (width : BitString) :
    (succeeded r width).registers.output =
      [false,false,true] ++ BitString.frame (SourceRecovery.called (requested r width)).registers.output := by
  rw [succeeded,modelPacket_output,recovered_output]
theorem successFuel_bound (r : CutDriver.State) (width : BitString) (n : Nat)
    (bounded : (extend r width).store.Bounded n) :
    successFuel r width ≤ successBound.eval n := by
  have first := recoveryFuel_bound r width n bounded
  have after : (recovered r width).store.Bounded (n+recoveryBound.eval n) :=
    Store.bounded_mono ((recover_exec r width).bounded n bounded) (Nat.add_le_add_left first n)
  have last := modelPacket.cost (recovered r width) _ after
  change recoveryFuel r width+modelPacket.fuel (recovered r width) ≤
    recoveryBound.eval n+(modelPacket.bound.substitute (.add .variable recoveryBound)).eval n
  rw [NatPolynomial.eval_substitute]
  exact Nat.add_le_add first last

end PNP.Concrete.NormalizerBlocks.OutputBranches
