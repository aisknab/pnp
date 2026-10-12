/-
Copyright (c) 2026 PNP Labs.

A source-system A entry carries its row label before the complete coefficient
packet. The runtime unary index is traversed, not treated as a constant.
-/
import PNP.Concrete.NormalizerCoefficientScratch

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
attribute [local irreducible] aTerms

def prepareRowHeader (tag : Bool) : Routine where
  block := .seq (.action (.push 8 tag)) (.seq (.action (.push 8 false)) (.action (.copy 3 22)))
  result r := r.withRegisters {r.registers with excess := r.row,output := false::tag::r.registers.output}
  fuel _ := 3
  bound := .constant 3
  exec _ := Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  cost _ _ _ := Nat.le_refl 3
def rowHeader (tag : Bool) : Routine := Routine.seq (prepareRowHeader tag) reverseRoutine
theorem rowHeader_result (tag : Bool) (r : State) :
    (rowHeader tag).result r = r.withRegisters {r.registers with excess := [],output := r.row.reverse ++ false::tag::r.registers.output} := rfl
theorem rowHeader_output (tag : Bool) (r : State) :
    ((rowHeader tag).result r).registers.output = r.row.reverse ++ false::tag::r.registers.output := rfl
theorem rowHeader_data (tag : Bool) (r : State) : ((rowHeader tag).result r).data = r.data := rfl

def entry (tag : Bool) : Routine := Routine.seq (packet (aTerms tag)) (rowHeader tag)
theorem entry_data (tag : Bool) (r : State) : ((entry tag).result r).data = r.data :=
  Routine.seq_data _ _ (packet_data _ (aTerms_data tag)) (rowHeader_data tag) r
theorem entry_output (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) (r : State)
    (encoded : ctx.Encoded r) (rowRead : r.row = List.replicate row true) :
    ((entry tag).result r).registers.output = CoefficientRow.bits row tag ++
      encodeRows ((row,tag)::ctx.companionRows anchor literals tag) := by
  have kept := packet_data (aTerms tag) (aTerms_data tag) r
  have selected : ((packet (aTerms tag)).result r).row = List.replicate row true :=
    (congrArg Data.row kept).trans rowRead
  have emitted := aTerms_emits ctx anchor row literals tag (started r)
    (encoded.transport (start_data r)) rowRead
  have packetBytes := packet_output (aTerms tag) r _ emitted
  change ((rowHeader tag).result ((packet (aTerms tag)).result r)).registers.output = _
  rw [rowHeader_output,selected,reverse_replicate,packetBytes]
  simp only [CoefficientRow.bits,List.append_assoc,List.cons_append,List.nil_append]

end PNP.Concrete.NormalizerBlocks.Coefficient
