/-
Copyright (c) 2026 PNP Labs.

Exact coefficient lists for an arbitrary stored literal. Representation
predicates below describe bytes; they are not arguments to the finite program.
A false literal appends the anchor terms, while a true literal does not.
-/
import PNP.Concrete.NormalizerCoefficientTruth

namespace PNP.Concrete.NormalizerBlocks.Coefficient
open BitRegister Occurrence
attribute [local irreducible] ellTerms bTerms literalTruth

structure Context where
  formula : List (List CNFLiteral)
  owners : MatchingTable.Entries
  slots : MatchingTable.Entries
  modes : MatchingTable.Entries
  assignment : BitString
  failed : Nat

structure Context.Encoded (ctx : Context) (r : State) : Prop where
  formula : r.core.core.formula = GraphQuery.clauseData ctx.formula
  owners : r.core.matching = MatchingTable.encode ctx.owners
  slots : r.core.counter = MatchingTable.encode ctx.slots
  modes : r.core.target = MatchingTable.encode ctx.modes
  assignment : r.assignment = ctx.assignment
  failed : r.failed = List.replicate ctx.failed true

theorem Context.Encoded.transport {ctx : Context} {before after : State}
    (encoded : ctx.Encoded before) (kept : after.data = before.data) : ctx.Encoded after :=
  ⟨(congrArg Data.literals kept).trans encoded.formula,
   (congrArg Data.owners kept).trans encoded.owners,
   (congrArg Data.slots kept).trans encoded.slots,
   (congrArg Data.modes kept).trans encoded.modes,
   (congrArg Data.assignment kept).trans encoded.assignment,
   (congrArg Data.failed kept).trans encoded.failed⟩

/-- A decoded lookup witness, never an execution input. -/
structure Context.Literal (ctx : Context) (row position : Nat) where
  leading : List CNFLiteral
  lit : CNFLiteral
  rest : List CNFLiteral
  owner : Nat
  position_eq : leading.length = position
  clause_eq : ctx.formula[row]?.getD [] = leading ++ lit::rest
  owner_eq : MatchingTable.read ctx.owners lit.variableIndex = some owner

def Context.Literal.ell {ctx : Context} {row position : Nat} (literal : ctx.Literal row position) : List Row :=
  ellRows literal.owner (MatchingTable.read ctx.slots literal.lit.variableIndex)
    (MatchingTable.read ctx.modes literal.owner)
def Context.anchorRows (ctx : Context) (anchor : ctx.Literal ctx.failed 0) : List Row :=
  (ctx.failed,false)::anchor.ell
def Context.literalRows (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    {row position : Nat} (literal : ctx.Literal row position) : List Row :=
  if ctx.assignment[literal.lit.variableIndex]?.getD false = literal.lit.positive
  then literal.ell else literal.ell ++ ctx.anchorRows anchor

theorem anchor_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (r : State) (encoded : ctx.Encoded r) :
    Emits r (bTerms.result r) (ctx.anchorRows anchor) := by
  have leading : anchor.leading = [] := by
    have length := anchor.position_eq
    cases h : anchor.leading with
    | nil => rfl
    | cons first rest =>
        rw [h,List.length_cons] at length
        omega
  have clause := anchor.clause_eq
  rw [leading,List.nil_append] at clause
  exact bTerms_emits r ctx.formula ctx.owners ctx.slots ctx.modes ctx.failed anchor.owner
    anchor.lit anchor.rest encoded.formula encoded.owners encoded.slots encoded.modes
    encoded.failed clause anchor.owner_eq

def falseLiteralTerms : Routine := Routine.seq ellTerms bTerms
def literalTerms (position : Nat) : Routine :=
  Routine.seq (literalTruth position) (Routine.choose 8 falseLiteralTerms ellTerms)
theorem falseLiteralTerms_data (r : State) : (falseLiteralTerms.result r).data = r.data :=
  Routine.seq_data _ _ ellTerms_data bTerms_data r
theorem literalTerms_data (position : Nat) (r : State) :
    ((literalTerms position).result r).data = r.data :=
  Routine.seq_data _ _ (literalTruth_data position)
    (Routine.choose_data 8 _ _ falseLiteralTerms_data ellTerms_data) r

theorem literalTerms_emits (ctx : Context) (anchor : ctx.Literal ctx.failed 0)
    (r : State) (encoded : ctx.Encoded r) (row position : Nat)
    (literal : ctx.Literal row position) (rowRead : r.row = List.replicate row true) :
    Emits r ((literalTerms position).result r) (ctx.literalRows anchor literal) := by
  let before := (literalTruth position).result r
  have selected := literalTruth_canonical r ctx.formula row literal.leading literal.lit literal.rest
    encoded.formula rowRead literal.clause_eq
  rw [literal.position_eq,encoded.assignment] at selected
  have flag : ForwardEdge.present before.registers.output =
      decide (ctx.assignment[literal.lit.variableIndex]?.getD false = literal.lit.positive) := by
    rw [selected.2]
    rfl
  have kept := literalTruth_data position r
  have next := encoded.transport kept
  have quietFields := literalTruth_buffers position r
  have quiet : Emits r before [] := emits_none _ _ quietFields.1 quietFields.2
  have first : Emits before (ellTerms.result before) literal.ell :=
    ellTerms_emits before ctx.owners ctx.slots ctx.modes literal.lit.variableIndex literal.owner
      next.owners next.slots next.modes selected.1 literal.owner_eq
  change Emits r ((Routine.choose 8 falseLiteralTerms ellTerms).result before) _
  rw [choose_output_result,flag]
  by_cases equal : ctx.assignment[literal.lit.variableIndex]?.getD false = literal.lit.positive
  · simp only [equal,decide_true,ite_true,Context.literalRows]
    exact emits_trans r before (ellTerms.result before) [] _ quiet first
  · simp only [equal,decide_false,Bool.false_eq_true,ite_false,Context.literalRows]
    have final := anchor_emits ctx anchor (ellTerms.result before)
      (next.transport (ellTerms_data before))
    exact emits_trans r before (falseLiteralTerms.result before) [] _ quiet
      (emits_trans before (ellTerms.result before) (falseLiteralTerms.result before) _ _ first final)

end PNP.Concrete.NormalizerBlocks.Coefficient
