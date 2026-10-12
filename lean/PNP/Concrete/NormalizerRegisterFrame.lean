/-
Copyright (c) 2026 PNP Labs.

Finite register framing for reusing closed table blocks inside the matching
driver. Extra words hold pending work and are unchanged by every lifted
instruction. This changes finite register indices only, not the machine model.
-/

import PNP.Concrete.NormalizerBlockExecution

namespace PNP.Concrete.NormalizerBlocks.Frame

open BitRegister

def join {extra count : Nat} (core : Store count) (frame : Store extra) : Store (extra + count) :=
  match core with
  | .nil => frame
  | .cons first rest => .cons first (join rest frame)
termination_by structural core

def index (extra : Nat) {count : Nat} (source : Fin count) : Fin (extra + count) :=
  ⟨source.val, by have bound := source.isLt; omega⟩

def frameIndex (count : Nat) {extra : Nat} (source : Fin extra) : Fin (extra + count) :=
  ⟨count + source.val, by have bound := source.isLt; omega⟩

theorem get_core {extra count : Nat} (core : Store count) (frame : Store extra) (source : Fin count) :
    (join core frame).get (index extra source) = core.get source := by
  induction core with
  | nil => exact Fin.elim0 source
  | cons first rest ih =>
      exact Store.indexCases
        (motive := fun selected => (join (.cons first rest) frame).get (index extra selected) =
          (Store.cons first rest).get selected)
        rfl (fun selected => ih selected) source

theorem set_core {extra count : Nat} (core : Store count) (frame : Store extra)
    (destination : Fin count) (value : BitString) :
    (join core frame).set (index extra destination) value = join (core.set destination value) frame := by
  induction core with
  | nil => exact Fin.elim0 destination
  | cons first rest ih =>
      exact Store.indexCases
        (motive := fun selected => (join (.cons first rest) frame).set (index extra selected) value =
          join ((Store.cons first rest).set selected value) frame)
        rfl (fun selected => congrArg (Store.cons first) (ih selected)) destination

theorem get_frame {extra count : Nat} (core : Store count) (frame : Store extra) (source : Fin extra) :
    (join core frame).get (frameIndex count source) = frame.get source := by
  induction core with
  | nil =>
      have position : frameIndex 0 source = source := by apply Fin.ext; simp only [frameIndex, Nat.zero_add]
      rw [position]
      rfl
  | @cons count first rest ih =>
      have position : frameIndex (count + 1) source = (frameIndex count source).succ := by
        apply Fin.ext
        change count + 1 + source.val = count + source.val + 1
        omega
      rw [position]
      exact ih

theorem join_bounded {extra count bound : Nat} (core : Store count) (frame : Store extra)
    (coreBound : core.Bounded bound) (frameBound : frame.Bounded bound) :
    (join core frame).Bounded bound := by
  induction core with
  | nil => exact frameBound
  | cons first rest ih => exact ⟨coreBound.1, ih coreBound.2⟩

def action (extra : Nat) {count : Nat} : Action count → Action (extra + count)
  | .clear destination => .clear (index extra destination)
  | .copy destination source => .copy (index extra destination) (index extra source)
  | .push destination bit => .push (index extra destination) bit
  | .pop destination => .pop (index extra destination)

theorem action_update {extra count : Nat} (operation : Action count) (core : Store count) (frame : Store extra) :
    (action extra operation).update (join core frame) = join (operation.update core) frame := by
  cases operation <;>
    simp only [action, Action.update, Action.instruction, Instruction.update, get_core, set_core]

def block (extra : Nat) {count : Nat} : Block count → Block (extra + count)
  | .skip => .skip
  | .action operation => .action (action extra operation)
  | .seq first second => .seq (block extra first) (block extra second)
  | .branch source empty zero one =>
      .branch (index extra source) (block extra empty) (block extra zero) (block extra one)
  | .loop source body => .loop (index extra source) (block extra body)

theorem block_size (extra : Nat) {count : Nat} (body : Block count) : (block extra body).size = body.size := by
  induction body <;> simp only [block, Block.size, *]

theorem execution {extra count : Nat} {body : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec body before fuel after) (frame : Store extra) :
    Exec (block extra body) (join before frame) fuel (join after frame) := by
  induction checked with
  | skip store => exact Exec.skip _
  | action operation store =>
      simpa only [block, action_update] using Exec.action (action extra operation) (join store frame)
  | seq first second ihf ihs => exact Exec.seq ihf ihs
  | empty read checked ih => exact Exec.empty ((get_core _ _ _).trans read) ih
  | zero read checked ih => exact Exec.zero ((get_core _ _ _).trans read) ih
  | one read checked ih => exact Exec.one ((get_core _ _ _).trans read) ih
  | loopStop read => exact Exec.loopStop ((get_core _ _ _).trans read)
  | loopStep read first rest ihf ihr => exact Exec.loopStep ((get_core _ _ _).trans read) ihf ihr

end PNP.Concrete.NormalizerBlocks.Frame
