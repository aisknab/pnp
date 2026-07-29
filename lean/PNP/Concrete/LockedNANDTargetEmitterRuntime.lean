/-
Copyright (c) 2026 PNP Labs.

Canonical logical workspace for the grammar-only locked-NAND target emitter.

The finite controller's local machines materialize and erase exterior blank
cells as they move.  `logicalConfiguration` deliberately omits those
representation-only tails.  Exact local traces are transported to and from
this canonical view through `WorkConfiguration.BlankEquivalent`.
-/

import PNP.Concrete.LockedNANDTargetEmitterCheckStack
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.LockedNAND.TargetEmitterRuntime

open PNP.Concrete

def logicalLeftWorkspace (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) : List WorkSymbol :=
  TargetEmitter.sourceLeftBoundary ::
    (TargetEmitterCheckStack.scratchWord capacity scratch ++
      TargetEmitterLedger.ledgerBoundary ::
        (TargetEmitterLedger.slotBank capacity registers ++
          TargetEmitterCheckStack.stackWord checks))

def logicalWord (source : List WorkSymbol)
    (target : List Token) : List WorkSymbol :=
  source ++
    (TargetEmitter.sourceTargetBoundary ::
      SourceParser.packedTokenCells target)

def logicalConfiguration (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) : WorkConfiguration :=
  TargetEmitter.configAtWord state
    (logicalLeftWorkspace capacity scratch registers checks)
    (logicalWord source target)

def logicalTape (capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) : WorkTape :=
  (logicalConfiguration 0 capacity scratch registers checks
    source target).tape

/-- Representation invariant carried between exact local controller runs. -/
def Represents (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (actual : WorkConfiguration) : Prop :=
  WorkConfiguration.BlankEquivalent actual
    (logicalConfiguration state capacity scratch registers
      checks source target)

theorem logicalWord_ne_nil
    (source : List WorkSymbol) (target : List Token) :
    logicalWord source target ≠ [] := by
  simp [logicalWord]

theorem logicalConfiguration_state
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) :
    (logicalConfiguration state capacity scratch registers
      checks source target).state = state := by
  unfold logicalConfiguration
  cases source <;> rfl

theorem Represents.state_eq
    {state capacity scratch : Nat}
    {registers : TargetEmitter.UnaryRegisters}
    {checks : List Nat} {source : List WorkSymbol}
    {target : List Token} {actual : WorkConfiguration}
    (represents :
      Represents state capacity scratch registers checks
        source target actual) :
    actual.state = state := by
  exact represents.state.trans
    (logicalConfiguration_state state capacity scratch registers
      checks source target)

theorem logicalConfiguration_tape
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) :
    (logicalConfiguration state capacity scratch registers
      checks source target).tape =
        logicalTape capacity scratch registers checks source target := by
  unfold logicalTape logicalConfiguration
  cases source <;> rfl

/-- A padded finite window and the canonical logical workspace denote the
same infinite blank work configuration. -/
theorem padded_blankEquivalent
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (leftPadding rightPadding : Nat) :
    WorkConfiguration.BlankEquivalent
      (TargetEmitter.configAtWord state
        (logicalLeftWorkspace capacity scratch registers checks ++
          List.replicate leftPadding WorkSymbol.blank)
        (logicalWord source target ++
          List.replicate rightPadding WorkSymbol.blank))
      (logicalConfiguration state capacity scratch registers
        checks source target) := by
  refine ⟨?_, ?_⟩
  · unfold logicalConfiguration
    cases source <;> rfl
  · cases source with
    | nil =>
        simpa [logicalTape, logicalConfiguration, logicalWord,
          TargetEmitter.configAtWord, List.append_assoc] using
          (WorkTape.blankEquivalent_of_padding
            { left :=
                logicalLeftWorkspace capacity scratch registers checks
              head := TargetEmitter.sourceTargetBoundary
              right := SourceParser.packedTokenCells target }
            leftPadding rightPadding)
    | cons head rest =>
        simpa [logicalTape, logicalConfiguration, logicalWord,
          TargetEmitter.configAtWord, List.append_assoc] using
          (WorkTape.blankEquivalent_of_padding
            { left :=
                logicalLeftWorkspace capacity scratch registers checks
              head := head
              right :=
                rest ++
                  TargetEmitter.sourceTargetBoundary ::
                    SourceParser.packedTokenCells target }
            leftPadding rightPadding)

theorem padded_blankEquivalent_symm
    (state capacity scratch : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (checks : List Nat) (source : List WorkSymbol)
    (target : List Token) (leftPadding rightPadding : Nat) :
    WorkConfiguration.BlankEquivalent
      (logicalConfiguration state capacity scratch registers
        checks source target)
      (TargetEmitter.configAtWord state
        (logicalLeftWorkspace capacity scratch registers checks ++
          List.replicate leftPadding WorkSymbol.blank)
        (logicalWord source target ++
          List.replicate rightPadding WorkSymbol.blank)) := by
  exact WorkConfiguration.blankEquivalent_symm
    (padded_blankEquivalent state capacity scratch registers checks
      source target leftPadding rightPadding)

theorem targetCells_packed (tokens : List Token) :
    ∀ symbol,
      symbol ∈ SourceParser.packedTokenCells tokens →
        TargetEmitter.PackedSymbol symbol :=
  TargetEmitter.packedTokenCells_packed tokens

end PNP.Concrete.LockedNAND.TargetEmitterRuntime
