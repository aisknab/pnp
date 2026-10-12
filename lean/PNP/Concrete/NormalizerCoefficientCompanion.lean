/-
Copyright (c) 2026 PNP Labs.

Companion, A and E coefficient rows. Each branch reads the stored mode;
the complete source row formulas are finite compositions of checked blocks.
-/
import PNP.Concrete.NormalizerCoefficientAuxiliary

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
attribute [local irreducible] literalTerms auxiliaryTerms

def EmitsAt (ctx : Context) (row : Nat) (routine : Routine) (rows : List Row) : Prop :=
  ∀ r, ctx.Encoded r → r.row = List.replicate row true → Emits r (routine.result r) rows
theorem emitsAt_seq (ctx : Context) (row : Nat) (first second : Routine) (xs ys : List Row)
    (kept : ∀ r, (first.result r).data = r.data)
    (hx : EmitsAt ctx row first xs) (hy : EmitsAt ctx row second ys) :
    EmitsAt ctx row (Routine.seq first second) (xs++ys) := by
  intro r encoded selected
  exact emits_trans r (first.result r) (second.result (first.result r)) xs ys
    (hx r encoded selected)
    (hy (first.result r) (encoded.transport (kept r)) ((congrArg Data.row (kept r)).trans selected))

def modeChoose (value : Nat) (onFalse onTrue : Routine) : Routine :=
  Routine.seq (queryOrdinal .mode .row value) (Routine.choose 8 onFalse onTrue)
theorem modeChoose_data (value : Nat) (onFalse onTrue : Routine)
    (hf : ∀ r, (onFalse.result r).data = r.data) (ht : ∀ r, (onTrue.result r).data = r.data) (r : State) :
    ((modeChoose value onFalse onTrue).result r).data = r.data :=
  Routine.seq_data _ _ (queryOrdinal_data .mode .row value)
    (Routine.choose_data 8 _ _ hf ht) r
theorem modeChoose_emits (ctx : Context) (row value : Nat)
    (onFalse onTrue : Routine) (xs ys : List Row)
    (hf : EmitsAt ctx row onFalse xs) (ht : EmitsAt ctx row onTrue ys) :
    EmitsAt ctx row (modeChoose value onFalse onTrue)
      (if OrdinalTest.ordinalMatches value (MatchingTable.read ctx.modes row) then ys else xs) := by
  intro r encoded rowRead
  let before := (queryOrdinal .mode .row value).result r
  have read := queryOrdinal_output .mode .row value r ctx.modes row encoded.modes rowRead
  have flag : ForwardEdge.present before.registers.output =
      OrdinalTest.ordinalMatches value (MatchingTable.read ctx.modes row) := by
    rw [read]
    rfl
  have kept := queryOrdinal_data .mode .row value r
  have next := encoded.transport kept
  have rowNext := (congrArg Data.row kept).trans rowRead
  have quietFields := queryOrdinal_buffers .mode .row value r
  have quiet : Emits r before [] := emits_none _ _ quietFields.1 quietFields.2
  change Emits r ((Routine.choose 8 onFalse onTrue).result before) _
  rw [choose_output_result,flag]
  cases OrdinalTest.ordinalMatches value (MatchingTable.read ctx.modes row)
  · simp only [Bool.false_eq_true,ite_false]
    exact emits_trans r before (onFalse.result before) [] _ quiet (hf before next rowNext)
  · simp only [ite_true]
    exact emits_trans r before (onTrue.result before) [] _ quiet (ht before next rowNext)

attribute [local irreducible] modeChoose
def expandedCompanion : Routine := Routine.seq (literalTerms 1) auxiliaryTerms
def falseCompanion : Routine :=
  modeChoose 1 (modeChoose 2 expandedCompanion (literalTerms 0)) (literalTerms 0)
def trueCompanion : Routine := modeChoose 2 (literalTerms 2) auxiliaryTerms
def companionTerms (tag : Bool) : Routine := if tag then trueCompanion else falseCompanion

structure Context.RowLiterals (ctx : Context) (row : Nat) where
  first : ctx.Literal row 0
  middle : ctx.Literal row 1
  last : ctx.Literal row 2
def Context.companionRows (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    {row : Nat} (literals : ctx.RowLiterals row) (tag : Bool) : List Row :=
  if tag then
    if OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row)
    then ctx.auxiliaryRows anchor literals.middle else ctx.literalRows anchor literals.last
  else if OrdinalTest.ordinalMatches 1 (MatchingTable.read ctx.modes row)
    then ctx.literalRows anchor literals.first
    else if OrdinalTest.ordinalMatches 2 (MatchingTable.read ctx.modes row)
      then ctx.literalRows anchor literals.first
      else ctx.literalRows anchor literals.middle ++ ctx.auxiliaryRows anchor literals.middle

theorem expandedCompanion_data (r : State) : (expandedCompanion.result r).data = r.data :=
  Routine.seq_data _ _ (literalTerms_data 1) auxiliaryTerms_data r
theorem falseCompanion_data (r : State) : (falseCompanion.result r).data = r.data :=
  modeChoose_data 1 _ _ (modeChoose_data 2 _ _ expandedCompanion_data (literalTerms_data 0))
    (literalTerms_data 0) r
theorem trueCompanion_data (r : State) : (trueCompanion.result r).data = r.data :=
  modeChoose_data 2 _ _ (literalTerms_data 2) auxiliaryTerms_data r
theorem companionTerms_data (tag : Bool) (r : State) : ((companionTerms tag).result r).data = r.data := by
  cases tag
  · exact falseCompanion_data r
  · exact trueCompanion_data r

theorem companionTerms_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) :
    EmitsAt ctx row (companionTerms tag) (ctx.companionRows anchor literals tag) := by
  have first : EmitsAt ctx row (literalTerms 0) (ctx.literalRows anchor literals.first) :=
    fun r encoded selected => literalTerms_emits ctx anchor r encoded row 0 literals.first selected
  have middle : EmitsAt ctx row (literalTerms 1) (ctx.literalRows anchor literals.middle) :=
    fun r encoded selected => literalTerms_emits ctx anchor r encoded row 1 literals.middle selected
  have last : EmitsAt ctx row (literalTerms 2) (ctx.literalRows anchor literals.last) :=
    fun r encoded selected => literalTerms_emits ctx anchor r encoded row 2 literals.last selected
  have auxiliary : EmitsAt ctx row auxiliaryTerms (ctx.auxiliaryRows anchor literals.middle) :=
    fun r encoded selected => auxiliaryTerms_emits ctx anchor r encoded row literals.middle selected
  have expanded : EmitsAt ctx row expandedCompanion
      (ctx.literalRows anchor literals.middle ++ ctx.auxiliaryRows anchor literals.middle) :=
    emitsAt_seq ctx row _ _ _ _ (literalTerms_data 1) middle auxiliary
  cases tag
  · exact modeChoose_emits ctx row 1 _ _ _ _
      (modeChoose_emits ctx row 2 _ _ _ _ expanded first) first
  · exact modeChoose_emits ctx row 2 _ _ _ _ last auxiliary

attribute [local irreducible] companionTerms
def aTerms (tag : Bool) : Routine := Routine.seq (emitIndexRoutine .row tag) (companionTerms tag)
def imageTerms : Routine := Routine.seq (emitIndexRoutine .row false) (literalTerms 0)
theorem aTerms_data (tag : Bool) (r : State) : ((aTerms tag).result r).data = r.data :=
  Routine.seq_data _ _ (by intro r; rfl) (companionTerms_data tag) r
theorem imageTerms_data (r : State) : (imageTerms.result r).data = r.data :=
  Routine.seq_data _ _ (by intro r; rfl) (literalTerms_data 0) r
theorem currentRow_emits (ctx : Context) (row : Nat) (tag : Bool) :
    EmitsAt ctx row (emitIndexRoutine .row tag) [(row,tag)] := by
  intro r _ selected
  have emitted := indexEmitted_buffers .row tag r
  change (indexEmitted .row tag r).count = true::r.count ∧
    (indexEmitted .row tag r).buffer =
      (CoefficientRow.bits r.row.length tag).reverse ++ r.buffer at emitted
  rw [selected,List.length_replicate] at emitted
  exact emits_one _ _ _ emitted.1 emitted.2
theorem aTerms_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (literals : ctx.RowLiterals row) (tag : Bool) :
    EmitsAt ctx row (aTerms tag) ((row,tag)::ctx.companionRows anchor literals tag) :=
  emitsAt_seq ctx row _ _ _ _ (by intro r; rfl)
    (currentRow_emits ctx row tag) (companionTerms_emits ctx anchor row literals tag)
theorem imageTerms_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (row : Nat) (first : ctx.Literal row 0) :
    EmitsAt ctx row imageTerms ((row,false)::ctx.literalRows anchor first) :=
  emitsAt_seq ctx row _ _ _ _ (by intro r; rfl) (currentRow_emits ctx row false)
    (fun r encoded selected => literalTerms_emits ctx anchor r encoded row 0 first selected)

end PNP.Concrete.NormalizerBlocks.Coefficient
