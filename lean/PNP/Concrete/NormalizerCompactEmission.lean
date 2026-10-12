/-
Copyright (c) 2026 PNP Labs.

Emit a compacted literal only when the internally executed lookup found its
variable. Both the original polarity and the returned dense position come
from stored machine data. Emission consumes unary scratch in finite control.
-/
import PNP.Concrete.NormalizerCompactLookup

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

def emitCore (positive : Bool) : Block 9 :=
  .seq (.action (.copy 4 1)) <| .seq (ClauseQuery.emit positive positive) <|
    .seq TableWrite.valueLoop (ClauseQuery.emit false false)
def emittedCore (positive : Bool) (r : Registers) : Registers :=
  {r with sign := [], excess := (NANDFrontend.literalBits positive r.target.length).reverse ++ r.excess}
theorem emitCore_exec (positive : Bool) (r : Registers) :
    Exec (emitCore positive) r.store (4 * r.target.length + 6) (emittedCore positive r).store := by
  have checked := Exec.seq (Exec.action (.copy 4 1) r.store)
    (Exec.seq (ClauseQuery.emit_exec positive positive {r with sign := r.target})
      (Exec.seq (TableWrite.value_exec r.target
        (ClauseQuery.emitted positive positive {r with sign := r.target}))
        (ClauseQuery.emit_exec false false _)))
  have cost : 4 * r.target.length + 6 = 1 + (2 + ((4 * r.target.length + 1) + 2)) := by omega
  rw [cost]
  simpa only [emitCore, emittedCore, ClauseQuery.emitted, TableWrite.valueResult,
    NANDFrontend.literalBits_reverse, List.append_assoc,
    List.cons_append, List.nil_append] using checked

def prepareEmit : Block 13 :=
  .seq (.action (.copy 1 8)) (.seq (.action (.pop 1)) (.action (.copy 3 11)))
def emitPrepared (r : State) : State :=
  r.withCore {r.core with target := r.core.output.tail, excess := r.buffer}
theorem prepareEmit_exec (r : State) : Exec prepareEmit r.store 3 (emitPrepared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def emitSign : Block 13 :=
  .branch 12 (liftCore (emitCore false)) (liftCore (emitCore false)) (liftCore (emitCore true))
def signEmitted (r : State) : State :=
  r.withCore (emittedCore (ForwardEdge.present r.positive) r.core)
theorem emitSign_exec (r : State) :
    Exec emitSign r.store (1 + (4 * r.core.target.length + 6)) (signEmitted r).store := by
  cases sign : r.positive with
  | nil =>
      simpa only [emitSign, signEmitted, ForwardEdge.present, sign, List.headD] using
        (Exec.empty (source := (12 : Fin 13)) (before := r.store) sign
          (liftCore_exec _ r _ _ (emitCore_exec false r.core)))
  | cons positive rest =>
      cases positive with
      | false =>
          simpa only [emitSign, signEmitted, ForwardEdge.present, sign, List.headD] using
            (Exec.zero (source := (12 : Fin 13)) (before := r.store) sign
              (liftCore_exec _ r _ _ (emitCore_exec false r.core)))
      | true =>
          simpa only [emitSign, signEmitted, ForwardEdge.present, sign, List.headD] using
            (Exec.one (source := (12 : Fin 13)) (before := r.store) sign
              (liftCore_exec _ r _ _ (emitCore_exec true r.core)))

def saveBuffer : Block 13 := .action (.copy 11 3)
def bufferSaved (r : State) : State := {r with buffer := r.core.excess}
theorem saveBuffer_exec (r : State) : Exec saveBuffer r.store 1 (bufferSaved r).store := .action _ _

def emit : Block 13 := .seq prepareEmit (.seq emitSign saveBuffer)
def emitted (r : State) : State := bufferSaved (signEmitted (emitPrepared r))
def emitFuel (r : State) : Nat := 3 + ((1 + (4 * r.core.output.tail.length + 6)) + 1)
theorem emit_exec (r : State) : Exec emit r.store (emitFuel r) (emitted r).store :=
  Exec.seq (prepareEmit_exec r) (Exec.seq (emitSign_exec (emitPrepared r)) (saveBuffer_exec _))

theorem emitted_buffer (r : State) :
    (emitted r).buffer =
      (NANDFrontend.literalBits (ForwardEdge.present r.positive) r.core.output.tail.length).reverse ++
        r.buffer := rfl
theorem emitted_fields (r : State) :
    (emitted r).pending = r.pending ∧
    (emitted r).variables = r.variables ∧
    (emitted r).positive = r.positive := ⟨rfl,rfl,rfl⟩

def choose : Block 13 := .branch 8 .skip .skip emit
def chosen (r : State) : State := if ForwardEdge.present r.core.output then emitted r else r
def chooseFuel (r : State) : Nat := if ForwardEdge.present r.core.output then 1 + emitFuel r else 2
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  cases found : r.core.output with
  | nil =>
      simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD,
        Bool.false_eq_true, ite_false] using
        (Exec.empty (source := (8 : Fin 13)) (before := r.store) found (Exec.skip r.store))
  | cons bit rest =>
      cases bit with
      | false =>
          simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD,
            Bool.false_eq_true, ite_false] using
            (Exec.zero (source := (8 : Fin 13)) (before := r.store) found (Exec.skip r.store))
      | true =>
          simpa only [choose, chosen, chooseFuel, ForwardEdge.present, found, List.headD,
            ite_true] using
            (Exec.one (source := (8 : Fin 13)) (before := r.store) found (emit_exec r))

theorem chosen_fields (r : State) :
    (chosen r).pending = r.pending ∧
    (chosen r).variables = r.variables ∧
    (chosen r).positive = r.positive := by
  cases found : ForwardEdge.present r.core.output with
  | false => simp only [chosen, found, Bool.false_eq_true, ite_false]; trivial
  | true => simpa only [chosen, found, ite_true] using emitted_fields r

theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 4 * r.core.output.length + 12 := by
  have tail := ParentQuery.input_tail_bound r.core.output
  cases found : ForwardEdge.present r.core.output <;>
    simp only [chooseFuel, emitFuel, found, Bool.false_eq_true, ite_false, ite_true] <;> omega

def compactLiteral (vertices : List CNFLiteral) (literal : CNFLiteral) : Option CNFLiteral :=
  (TableOwner.vertexOwner vertices literal.variableIndex).map
    (fun index => ⟨literal.positive,index⟩)

def literalOutput : Option CNFLiteral → BitString
  | none => []
  | some literal => NANDFrontend.literalBits literal.positive literal.variableIndex

theorem chosen_buffer (r : State) (positive : Bool) (owner : Option Nat)
    (sign : ForwardEdge.present r.positive = positive)
    (answer : r.core.output = TableOwner.answer owner) :
    (chosen r).buffer =
      (literalOutput (owner.map (fun index => ⟨positive,index⟩))).reverse ++ r.buffer := by
  cases owner with
  | none =>
      have absent : ForwardEdge.present r.core.output = false := by rw [answer]; rfl
      simp only [chosen, absent, Bool.false_eq_true, ite_false, Option.map_none,
        literalOutput, List.reverse_nil, List.nil_append]
  | some index =>
      have present : ForwardEdge.present r.core.output = true := by rw [answer]; rfl
      simp only [chosen, present, ite_true]
      rw [emitted_buffer, sign, answer]
      simp only [TableOwner.answer, List.tail_cons, List.length_replicate,
        Option.map_some, literalOutput]

end PNP.Concrete.NormalizerBlocks.CompactClause
