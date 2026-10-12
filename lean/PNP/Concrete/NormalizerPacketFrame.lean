/-
Copyright (c) 2026 PNP Labs.

Exact final packet framing, using finite register operations. Model payloads
are length-framed; system payloads receive the retained row count. These
operations label bytes, not the mathematical truth of an unchecked payload.
-/
import PNP.Concrete.NormalizerClausePack
import PNP.Concrete.NormalizerRegisterFrame

namespace PNP.Concrete.NormalizerBlocks.PacketFrame
open BitRegister Occurrence

inductive Kind where
  | malformed | model | system
deriving Repr
def Kind.bits : Kind → BitString
  | .malformed => [false,false,false]
  | .model => [false,false,true]
  | .system => [false,true,false]
def tag : Kind → Block 9
  | .malformed => .seq (.action (.push 8 false)) (.seq (.action (.push 8 false)) (.action (.push 8 false)))
  | .model => .seq (.action (.push 8 true)) (.seq (.action (.push 8 false)) (.action (.push 8 false)))
  | .system => .seq (.action (.push 8 false)) (.seq (.action (.push 8 true)) (.action (.push 8 false)))
def tagged (kind : Kind) (r : Registers) : Registers := {r with output := kind.bits ++ r.output}
theorem tag_exec (kind : Kind) (r : Registers) : Exec (tag kind) r.store 3 (tagged kind r).store := by
  cases kind <;> exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def countStep : Block 9 := .seq (.action (.pop 3)) (.action (.push 8 true))
def countLoop : Block 9 := .loop 3 countStep
theorem count_step (r : Registers) (bit : Bool) (rest : BitString) :
    Exec countStep ({r with excess := bit::rest}).store 2
      ({r with excess := rest,output := true::r.output}).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem count_exec (r : Registers) (word : BitString) :
    Exec countLoop ({r with excess := word}).store (3*word.length+1)
      ({r with excess := [],output := List.replicate word.length true ++ r.output}).store := by
  induction word generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons bit rest ih =>
      have next := ih {r with output := true::r.output}
      have step := Exec.loopStep (source := (3 : Fin 9)) (body := countStep)
        (before := ({r with excess := bit::rest}).store) rfl (count_step r bit rest) next
      have cost : 3*(bit::rest).length+1 = 1+(2+(3*rest.length+1)) := by
        simp only [List.length_cons]
        omega
      have bits : List.replicate rest.length true ++ true::r.output =
          List.replicate (rest.length+1) true ++ r.output := by
        have appendOne : ∀ n : Nat, List.replicate n true ++ true::r.output =
            List.replicate (n+1) true ++ r.output := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih => exact congrArg (List.cons true) ih
        exact appendOne rest.length
      rw [cost]
      simpa only [countLoop,List.length_cons,bits] using step

def lengthPrefix : Block 9 := .seq (.action (.push 8 false)) countLoop
def prefixed (r : Registers) : Registers :=
  {r with excess := [],output := List.replicate r.excess.length true ++ false::r.output}
theorem lengthPrefix_exec (r : Registers) : Exec lengthPrefix r.store (3*r.excess.length+2) (prefixed r).store := by
  have loop := count_exec {r with output := false::r.output} r.excess
  have work := Exec.seq (Exec.action (.push 8 false) r.store) loop
  have cost : 3*r.excess.length+2 = 1+(3*r.excess.length+1) := by omega
  simpa only [lengthPrefix,prefixed,cost] using work

def model : Block 9 := .seq (.action (.copy 3 8)) (.seq lengthPrefix (tag .model))
def modelResult (r : Registers) : Registers := tagged .model (prefixed {r with excess := r.output})
def modelFuel (r : Registers) : Nat := 3*r.output.length+6
theorem model_exec (r : Registers) : Exec model r.store (modelFuel r) (modelResult r).store := by
  have work := Exec.seq (Exec.action (.copy 3 8) r.store)
    (Exec.seq (lengthPrefix_exec {r with excess := r.output}) (tag_exec .model (prefixed {r with excess := r.output})))
  have cost : modelFuel r = 1+((3*r.output.length+2)+3) := by unfold modelFuel; omega
  simpa only [model,modelResult,cost] using work
theorem model_output (r : Registers) :
    (modelResult r).output = [false,false,true] ++ BitString.frame r.output := rfl

def system : Block 9 := .seq lengthPrefix (tag .system)
def systemResult (r : Registers) : Registers := tagged .system (prefixed r)
def systemFuel (r : Registers) : Nat := 3*r.excess.length+5
theorem system_exec (r : Registers) : Exec system r.store (systemFuel r) (systemResult r).store := by
  have work := Exec.seq (lengthPrefix_exec r) (tag_exec .system (prefixed r))
  have cost : systemFuel r = (3*r.excess.length+2)+3 := by unfold systemFuel; omega
  simpa only [system,systemResult,cost] using work
theorem system_output (r : Registers) :
    (systemResult r).output = [false,true,false] ++
      (List.replicate r.excess.length true ++ false::r.output) := rfl

def malformed : Block 9 := .seq (.action (.clear 8)) (tag .malformed)
def malformedResult (r : Registers) : Registers := {r with output := [false,false,false]}
theorem malformed_exec (r : Registers) : Exec malformed r.store 4 (malformedResult r).store := by
  have cleared : Exec (.action (.clear 8)) r.store 1 ({r with output := []}).store := .action _ _
  have work := Exec.seq cleared (tag_exec .malformed {r with output := []})
  simpa only [malformed,malformedResult,tagged,Kind.bits,List.cons_append,List.nil_append] using work
theorem modelFuel_bound (r : Registers) (n : Nat) (bounded : r.store.Bounded n) :
    modelFuel r ≤ 3*n+6 := by
  have size := Store.get_length_le r.store (8 : Fin 9) bounded
  change r.output.length ≤ n at size
  unfold modelFuel
  omega
theorem systemFuel_bound (r : Registers) (n : Nat) (bounded : r.store.Bounded n) :
    systemFuel r ≤ 3*n+5 := by
  have size := Store.get_length_le r.store (3 : Fin 9) bounded
  change r.excess.length ≤ n at size
  unfold systemFuel
  omega

end PNP.Concrete.NormalizerBlocks.PacketFrame
