/-
Copyright (c) 2026 PNP Labs.

Reusable finite scratch-register reset. The proof is structural in the
register store, so reentrant calls do not expand an entire nested machine
state while clearing each register.
-/
import PNP.Concrete.NormalizerBlockExecution

namespace PNP.Concrete.NormalizerBlocks.RegisterReset
open BitRegister

def action {count : Nat} : Action count → Action (count + 1)
  | .clear target => .clear target.succ
  | .copy target source => .copy target.succ source.succ
  | .push target bit => .push target.succ bit
  | .pop target => .pop target.succ

theorem action_update {count : Nat} (operation : Action count) (first : BitString) (rest : Store count) :
    (action operation).update (.cons first rest) = .cons first (operation.update rest) := by
  cases operation <;> rfl

def shift {count : Nat} : Block count → Block (count + 1)
  | .skip => .skip
  | .action operation => .action (action operation)
  | .seq first second => .seq (shift first) (shift second)
  | .branch source empty zero one => .branch source.succ (shift empty) (shift zero) (shift one)
  | .loop source body => .loop source.succ (shift body)

theorem get_succ {count : Nat} (first : BitString) (rest : Store count) (source : Fin count) :
    (Store.cons first rest).get source.succ = rest.get source := rfl

theorem execution {count : Nat} {body : Block count} {before after : Store count} {fuel : Nat}
    (checked : Exec body before fuel after) (first : BitString) :
    Exec (shift body) (.cons first before) fuel (.cons first after) := by
  induction checked with
  | skip store => exact Exec.skip _
  | action operation store =>
      simpa only [shift, action_update] using Exec.action (action operation) (.cons first store)
  | seq front back ihf ihb => exact Exec.seq ihf ihb
  | empty read checked ih => exact Exec.empty ((get_succ _ _ _).trans read) ih
  | zero read checked ih => exact Exec.zero ((get_succ _ _ _).trans read) ih
  | one read checked ih => exact Exec.one ((get_succ _ _ _).trans read) ih
  | loopStop read => exact Exec.loopStop ((get_succ _ _ _).trans read)
  | loopStep read step rest ihs ihr => exact Exec.loopStep ((get_succ _ _ _).trans read) ihs ihr

def all : (count : Nat) → Block count
  | 0 => .skip
  | count + 1 => .seq (.action (.clear 0)) (shift (all count))

theorem all_exec {count : Nat} (store : Store count) :
    Exec (all count) store (count + 1) (Store.empty count) := by
  induction store with
  | nil => exact Exec.skip _
  | @cons count first rest ih =>
      have start : Exec (.action (.clear (0 : Fin (count + 1)))) (.cons first rest) 1 (.cons [] rest) :=
        Exec.action _ _
      have checked := Exec.seq start (execution ih [])
      have cost : count + 1 + 1 = 1 + (count + 1) := Nat.add_comm _ _
      rw [cost]
      exact checked

def keepFirst (count : Nat) : Block (count + 1) := shift (all count)
theorem keepFirst_exec {count : Nat} (store : Store (count + 1)) :
    Exec (keepFirst count) store (count + 1) (.cons (store.get 0) (Store.empty count)) := by
  cases store with
  | cons first rest => exact execution (all_exec rest) first

end PNP.Concrete.NormalizerBlocks.RegisterReset
