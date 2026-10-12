/-
Copyright (c) 2026 PNP Labs.

Finite instruction blocks for the exact circuit-to-formula frontend.
Code-segment hypotheses describe literal instruction placement only. The final
closed program must establish these placements internally.
-/

import PNP.Concrete.NANDFrontendData
import PNP.Concrete.BitRegisterProgram

namespace PNP.Concrete.NANDFrontend

open BitRegister

structure Registers where
  input : BitString
  inputs : BitString
  width : BitString
  gate : BitString
  left : BitString
  right : BitString
  temp : BitString
  reversed : BitString
  output : BitString
deriving Repr

def Registers.store (r : Registers) : Store 9 :=
  .cons r.input (.cons r.inputs (.cons r.width (.cons r.gate (.cons r.left
    (.cons r.right (.cons r.temp (.cons r.reversed (.cons r.output .nil))))))))

def Registers.state (r : Registers) (address : Nat) : BitRegister.Configuration 9 :=
  ⟨.running address, r.store⟩

inductive Operand where
  | left | right | gate
deriving DecidableEq, Repr

def Operand.slot : Operand → Fin 9
  | .left => 4
  | .right => 5
  | .gate => 3

def Operand.value : Operand → Registers → BitString
  | .left, r => r.left
  | .right, r => r.right
  | .gate, r => r.gate

theorem Operand.read (operand : Operand) (r : Registers) :
    r.store.get operand.slot = operand.value r := by
  cases operand <;> rfl

/-- A checked range of the actual finite instruction table. -/
def Segment (program : Program 9) (base : Nat) (code : List (Instruction 9)) : Prop :=
  ∀ offset, offset < code.length →
    BitRegister.lookup program.code (base + offset) = BitRegister.lookup code offset

theorem lookup_append_left {α : Type} (front back : List α) (index : Nat)
    (inside : index < front.length) :
    BitRegister.lookup (front ++ back) index = BitRegister.lookup front index := by
  induction front generalizing index with
  | nil => exact False.elim (Nat.not_lt_zero index inside)
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          exact ih index (Nat.lt_of_succ_lt_succ inside)

theorem lookup_append_skip {α : Type} (front back : List α) (index : Nat) :
    BitRegister.lookup (front ++ back) (front.length + index) = BitRegister.lookup back index := by
  induction front with
  | nil => simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons first rest ih =>
      simpa only [List.cons_append, List.length_cons, Nat.succ_add, BitRegister.lookup] using ih

theorem Segment.slice {program : Program 9} {base : Nat}
    (front code back : List (Instruction 9))
    (whole : Segment program base (front ++ code ++ back)) :
    Segment program (base + front.length) code := by
  intro offset inside
  have within : front.length + offset < (front ++ code ++ back).length := by
    simp only [List.length_append]
    omega
  calc
    BitRegister.lookup program.code (base + front.length + offset) =
        BitRegister.lookup program.code (base + (front.length + offset)) := by rw [Nat.add_assoc]
    _ = BitRegister.lookup (front ++ code ++ back) (front.length + offset) := whole _ within
    _ = BitRegister.lookup code offset := by
      rw [List.append_assoc, lookup_append_skip, lookup_append_left code back offset inside]

theorem Segment.full (program : Program 9) : Segment program 0 program.code := by
  intro offset _
  rw [Nat.zero_add]

def pairCode (base : Nat) (first second : Bool) (next : Nat) : List (Instruction 9) :=
  [.push 7 first (base + 1), .push 7 second next]

def literalCode (base : Nat) (operand : Operand) (positive : Bool) (next : Nat) :
    List (Instruction 9) :=
  [.push 7 positive (base + 1),
   .push 7 positive (base + 2),
   .copy 6 operand.slot (base + 3),
   .branch 6 (base + 7) (base + 4) (base + 4),
   .pop 6 (base + 5),
   .push 7 true (base + 6),
   .push 7 true (base + 3),
   .push 7 false (base + 8),
   .push 7 false next]

def clauseCode (base : Nat) (first second third : Operand × Bool) (next : Nat) :
    List (Instruction 9) :=
  pairCode base false true (base + 2) ++
    literalCode (base + 2) first.1 first.2 (base + 11) ++
    literalCode (base + 11) second.1 second.2 (base + 20) ++
    literalCode (base + 20) third.1 third.2 (base + 29) ++
    pairCode (base + 29) true false next

def unitCode (base : Nat) (operand : Operand) (positive : Bool) (next : Nat) :
    List (Instruction 9) :=
  clauseCode base (operand, positive) (operand, positive) (operand, positive) next

def gateCode (base next : Nat) : List (Instruction 9) :=
  clauseCode base (.left, false) (.right, false) (.gate, false) (base + 31) ++
    clauseCode (base + 31) (.left, true) (.gate, true) (.gate, true) (base + 62) ++
    clauseCode (base + 62) (.right, true) (.gate, true) (.gate, true) next

theorem pairCode_length (base : Nat) (first second : Bool) (next : Nat) :
    (pairCode base first second next).length = 2 := rfl

theorem literalCode_length (base : Nat) (operand : Operand) (positive : Bool) (next : Nat) :
    (literalCode base operand positive next).length = 9 := rfl

theorem clauseCode_length (base : Nat) (first second third : Operand × Bool) (next : Nat) :
    (clauseCode base first second third next).length = 31 := rfl

theorem unitCode_length (base : Nat) (operand : Operand) (positive : Bool) (next : Nat) :
    (unitCode base operand positive next).length = 31 := rfl

theorem gateCode_length (base next : Nat) : (gateCode base next).length = 93 := rfl

end PNP.Concrete.NANDFrontend
