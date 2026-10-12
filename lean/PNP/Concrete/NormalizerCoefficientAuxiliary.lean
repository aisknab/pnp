/-
Copyright (c) 2026 PNP Labs.

The auxiliary coefficient list is selected from the actual mode table.
All row indices and the middle literal are runtime data.
-/
import PNP.Concrete.NormalizerCoefficientLiteral

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
attribute [local irreducible] auxiliaryRow literalTerms

def copyAuxiliary : Routine where
  block := .action (.copy 23 22)
  result r := {r with auxiliary := r.row}
  fuel _ := 1
  bound := .constant 1
  exec _ := .action _ _
  cost _ _ _ := Nat.le_refl 1
def currentAuxiliary : Routine := Routine.seq copyAuxiliary auxiliaryRow
theorem currentAuxiliary_data (r : State) : (currentAuxiliary.result r).data = r.data :=
  Routine.seq_data _ _ (by intro r; rfl) auxiliaryRow_data r
theorem currentAuxiliary_emits (ctx : Context) (r : State) (encoded : ctx.Encoded r)
    (row : Nat) (rowRead : r.row = List.replicate row true) :
    Emits r (currentAuxiliary.result r)
      [(row,!OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row))] := by
  have emitted := auxiliaryRow_emits (copyAuxiliary.result r) ctx.modes row encoded.modes rowRead
  exact emits_trans r (copyAuxiliary.result r) (currentAuxiliary.result r) [] _
    (emits_none _ _ rfl rfl) emitted

attribute [local irreducible] currentAuxiliary

def extendedAuxiliary : Routine := Routine.seq currentAuxiliary (literalTerms 1)
def auxiliaryTerms : Routine :=
  Routine.seq (queryOrdinal .mode .row 2) (Routine.choose 8 currentAuxiliary extendedAuxiliary)
def Context.auxiliaryRows (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    {row : Nat} (middle : ctx.Literal row 1) : List Row :=
  (row,!OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row))::
    (if OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row)
    then ctx.literalRows anchor middle else [])

theorem extendedAuxiliary_data (r : State) : (extendedAuxiliary.result r).data = r.data :=
  Routine.seq_data _ _ currentAuxiliary_data (literalTerms_data 1) r
theorem auxiliaryTerms_data (r : State) : (auxiliaryTerms.result r).data = r.data :=
  Routine.seq_data _ _ (queryOrdinal_data .mode .row 2)
    (Routine.choose_data 8 _ _ currentAuxiliary_data extendedAuxiliary_data) r
theorem extendedAuxiliary_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (r : State) (encoded : ctx.Encoded r) (row : Nat) (middle : ctx.Literal row 1)
    (rowRead : r.row = List.replicate row true) :
    Emits r (extendedAuxiliary.result r)
      ((row,!OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row))::
        ctx.literalRows anchor middle) := by
  have first := currentAuxiliary_emits ctx r encoded row rowRead
  have kept := currentAuxiliary_data r
  have second := literalTerms_emits ctx anchor (currentAuxiliary.result r)
    (encoded.transport kept) row 1 middle ((congrArg Data.row kept).trans rowRead)
  exact emits_trans r (currentAuxiliary.result r) (extendedAuxiliary.result r) _ _ first second

theorem auxiliaryTerms_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (r : State) (encoded : ctx.Encoded r) (row : Nat) (middle : ctx.Literal row 1)
    (rowRead : r.row = List.replicate row true) :
    Emits r (auxiliaryTerms.result r) (ctx.auxiliaryRows anchor middle) := by
  let before := (queryOrdinal .mode .row 2).result r
  have read := queryOrdinal_output .mode .row 2 r ctx.modes row encoded.modes rowRead
  have flag : ForwardEdge.present before.registers.output =
      OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row) := by
    rw [read]
    rfl
  have kept := queryOrdinal_data .mode .row 2 r
  have next := encoded.transport kept
  have rowNext := (congrArg Data.row kept).trans rowRead
  have quietFields := queryOrdinal_buffers .mode .row 2 r
  have quiet : Emits r before [] := emits_none _ _ quietFields.1 quietFields.2
  change Emits r ((Routine.choose 8 currentAuxiliary extendedAuxiliary).result before) _
  rw [choose_output_result,flag]
  cases h : OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row)
  · simp only [Bool.false_eq_true,ite_false,Context.auxiliaryRows,h]
    have emitted := currentAuxiliary_emits ctx before next row rowNext
    rw [h] at emitted
    exact emits_trans r before (currentAuxiliary.result before) [] _ quiet emitted
  · simp only [ite_true,Context.auxiliaryRows,h]
    have emitted := extendedAuxiliary_emits ctx anchor before next row middle rowNext
    rw [h] at emitted
    exact emits_trans r before (extendedAuxiliary.result before) [] _ quiet emitted

end PNP.Concrete.NormalizerBlocks.Coefficient
