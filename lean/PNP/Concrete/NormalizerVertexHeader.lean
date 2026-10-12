/-
Copyright (c) 2026 PNP Labs.

Reload a range count while retaining the accumulated vertex bytes. The finite
reset touches only scratch registers; the header parser has the same exact
execution and count as the existing closed parser, regardless of buffer size.
-/

import PNP.Concrete.NormalizerVertexRange

namespace PNP.Concrete.NormalizerBlocks.SearchVertices

open BitRegister Occurrence

def buffered (input buffer : BitString) : Registers :=
  {initialRegisters input with excess := buffer}

def resetLeft : Block 9 :=
  .seq (.action (.clear 1)) (.seq (.action (.clear 2)) (.action (.clear 4)))
def leftReset (r : Registers) : Registers := {r with target := [], remaining := [], sign := []}

theorem resetLeft_exec (r : Registers) : Exec resetLeft r.store 3 (leftReset r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def resetRight : Block 9 :=
  .seq (.action (.clear 5)) <| .seq (.action (.clear 6)) <|
  .seq (.action (.clear 7)) (.action (.clear 8))
def rightReset (r : Registers) : Registers :=
  {r with mode := [], active := [], reserved := [], output := []}

theorem resetRight_exec (r : Registers) : Exec resetRight r.store 4 (rightReset r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def reset : Block 9 := .seq resetLeft resetRight

theorem reset_exec (r : Registers) : Exec reset r.store 7 (buffered r.input r.excess).store :=
  Exec.seq (resetLeft_exec r) (resetRight_exec (leftReset r))

theorem header_buffer (input : BitString) (r : Registers) (buffer : BitString) :
    headerResult input {r with excess := buffer} =
      ⟨(headerResult input r).fuel, {(headerResult input r).state with excess := buffer}⟩ := by
  cases r with
  | mk original target remaining excess sign mode active reserved output =>
      induction input generalizing target with
      | nil => cases active <;> rfl
      | cons first rest ih =>
          cases active with
          | nil => rfl
          | cons bit tail =>
              cases first with
              | false => rfl
              | true =>
                  simp only [headerResult]
                  rw [ih (true :: target)]

def readBuffered (input buffer : BitString) : Registers :=
  {(TableInit.readCount input).state with excess := buffer}

theorem buffered_header_exec (input buffer : BitString) :
    Exec TableInit.header (buffered input buffer).store (TableInit.headerFuel input)
      (readBuffered input buffer).store := by
  have start : Exec (.action (.push 6 true)) (buffered input buffer).store 1
      ({TableInit.seeded input with excess := buffer}).store := .action _ _
  have checked := Occurrence.header_exec input {TableInit.seeded input with excess := buffer}
  rw [header_buffer] at checked
  exact Exec.seq start checked

def prepare : Block 9 := .seq (.action (.copy 2 1)) (.action (.clear 1))
def prepared (r : Registers) : Registers := {r with remaining := r.target, target := []}

theorem prepare_exec (r : Registers) : Exec prepare r.store 2 (prepared r).store :=
  Exec.seq (.action _ _) (.action _ _)

theorem readBuffered_canonical (count : Nat) (suffix buffer : BitString) :
    readBuffered (TableInit.encodeCount count suffix) buffer =
      {TableInit.canonicalHeader count suffix with excess := buffer} := by
  rw [readBuffered, BatchPacket.header_canonical]

end PNP.Concrete.NormalizerBlocks.SearchVertices
