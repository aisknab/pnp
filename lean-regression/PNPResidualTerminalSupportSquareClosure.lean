import PNP.ResidualTerminalSupportSquareClosure

namespace PNP
namespace DirectWire

abbrev squareRecord := TerminalPrimitiveRecord 1 4 1 2

def squareInput0 : Fin 1 := ⟨0, by decide⟩
def squareGate0 : Fin 4 := ⟨0, by decide⟩
def squareGate1 : Fin 4 := ⟨1, by decide⟩
def squareGate2 : Fin 4 := ⟨2, by decide⟩
def squareGate3 : Fin 4 := ⟨3, by decide⟩
def squareProfile0 : Fin 2 := ⟨0, by decide⟩
def squareProfile1 : Fin 2 := ⟨1, by decide⟩

def squareProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input squareInput0
      right := .input squareInput0 }

def squareProgram1 : Program 1 2 :=
  .snoc squareProgram0
    { left := .gate ⟨0, by decide⟩
      right := .gate ⟨0, by decide⟩ }

def squareProgram2 : Program 1 3 :=
  .snoc squareProgram1
    { left := .input squareInput0
      right := .input squareInput0 }

def squareProgram : Program 1 4 :=
  .snoc squareProgram2
    { left := .gate ⟨1, by decide⟩
      right := .gate ⟨2, by decide⟩ }

def squareWord : DirectWireWord 1 4 1 :=
  ⟨fun _output => .gate squareGate3⟩

def squareCandidate : Candidate 1 4 1 :=
  Candidate.ofDirectWireWord squareProgram squareWord

def squareGate0Record : squareRecord := .gate squareGate0
def squareGate1Record : squareRecord := .gate squareGate1
def squareGate2Record : squareRecord := .gate squareGate2
def squareProfile0Record : squareRecord := .profile squareProfile0
def squareProfile1Record : squareRecord := .profile squareProfile1

def squareProfileSystem : TerminalProfileSystem 1 1 2 :=
  { role := fun coordinate =>
      if coordinate.val = 0 then .origin else .charge
    observe := fun _implementation coordinate =>
      decide (coordinate.val = 1) }

def squareSaturationSystem : TerminalSaturationSystem 1 4 1 2 :=
  { profileSystem := squareProfileSystem
    requires := fun kind dependent required => decide (
      (kind = .gateSource ∧ dependent = squareGate1Record ∧
        required = squareGate0Record) ∨
      (kind = .origin ∧ dependent = squareGate1Record ∧
        required = squareProfile0Record) ∨
      (kind = .charge ∧ dependent = squareGate2Record ∧
        required = squareProfile0Record) ∨
      (kind = .direction ∧ dependent = squareGate2Record ∧
        required = squareProfile1Record)) }

def square : TerminalSaturatedSupportSquare squareSaturationSystem :=
  terminalSaturatedSupportSquare squareSaturationSystem
    [squareGate1Record] [squareGate2Record]

/-- The two sides saturate through distinct physical records and one shared
    profile coordinate. -/
example : square.leftRecords =
    [squareProfile0Record, squareGate0Record, squareGate1Record] := by
  decide

example : square.rightRecords =
    [squareProfile1Record, squareProfile0Record, squareGate2Record] := by
  decide

/-- Meet is canonical-universe ordered; join follows deterministic saturation
    visitation order. -/
example : square.meetRecords = [squareProfile0Record] := by decide

example : square.joinRecords =
    [squareProfile1Record, squareProfile0Record, squareGate2Record,
      squareGate1Record, squareGate0Record] := by
  decide

example (record : squareRecord) :
    record ∈ square.meetRecords ↔
      record ∈ square.leftRecords ∧ record ∈ square.rightRecords :=
  square.mem_meetRecords_iff record

example (record : squareRecord) :
    record ∈ square.joinRecords ↔
      record ∈ square.leftRecords ∨ record ∈ square.rightRecords :=
  square.mem_joinRecords_iff record

example (corner : TerminalSupportSquareCorner) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.records corner)
      squareSaturationSystem :=
  square.records_closed corner

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.meetRecords)
    (fun record => record ∈ square.leftRecords) :=
  square.meetRecords_subset_left

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.meetRecords)
    (fun record => record ∈ square.rightRecords) :=
  square.meetRecords_subset_right

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.leftRecords)
    (fun record => record ∈ square.joinRecords) :=
  square.leftRecords_subset_join

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.rightRecords)
    (fun record => record ∈ square.joinRecords) :=
  square.rightRecords_subset_join

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.meetRecords)
    (fun record => record ∈ square.meetRecords) :=
  square.meetRecords_greatest
    (fun record => record ∈ square.meetRecords)
    square.meetRecords_subset_left square.meetRecords_subset_right

example : TerminalRawSupport.Subset
    (fun record => record ∈ square.joinRecords)
    (fun record => record ∈ square.joinRecords) :=
  square.joinRecords_least
    (fun record => record ∈ square.joinRecords)
    square.leftRecords_subset_join square.rightRecords_subset_join

/-! Empty, identical, duplicate, and reordered seed boundaries. -/

def emptySquare : TerminalSaturatedSupportSquare squareSaturationSystem :=
  terminalSaturatedSupportSquare squareSaturationSystem [] []

example : emptySquare.meetRecords = [] := by decide
example : emptySquare.leftRecords = [] := by decide
example : emptySquare.rightRecords = [] := by decide
example : emptySquare.joinRecords = [] := by decide

def identicalSquare : TerminalSaturatedSupportSquare squareSaturationSystem :=
  terminalSaturatedSupportSquare squareSaturationSystem
    [squareGate1Record] [squareGate1Record]

example (record : squareRecord) :
    record ∈ identicalSquare.meetRecords ↔
      record ∈ identicalSquare.joinRecords := by
  rw [identicalSquare.mem_meetRecords_iff,
    identicalSquare.mem_joinRecords_iff]
  constructor
  · exact fun both => Or.inl both.1
  · intro either
    cases either with
    | inl member => exact ⟨member, member⟩
    | inr member => exact ⟨member, member⟩

def duplicateReorderedSquare :
    TerminalSaturatedSupportSquare squareSaturationSystem :=
  terminalSaturatedSupportSquare squareSaturationSystem
    [squareProfile0Record, squareGate1Record, squareGate1Record]
    [squareProfile1Record, squareGate2Record, squareGate2Record]

def reorderedSquare :
    TerminalSaturatedSupportSquare squareSaturationSystem :=
  terminalSaturatedSupportSquare squareSaturationSystem
    [squareGate1Record, squareProfile0Record]
    [squareGate2Record, squareProfile1Record]

example (corner : TerminalSupportSquareCorner) (record : squareRecord) :
    record ∈ duplicateReorderedSquare.records corner ↔
      record ∈ reorderedSquare.records corner := by
  apply duplicateReorderedSquare.records_congr reorderedSquare
  · intro candidate
    change candidate ∈
        [squareProfile0Record, squareGate1Record, squareGate1Record] ↔
      candidate ∈ [squareGate1Record, squareProfile0Record]
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
    exact or_comm
  · intro candidate
    change candidate ∈
        [squareProfile1Record, squareGate2Record, squareGate2Record] ↔
      candidate ∈ [squareGate2Record, squareProfile1Record]
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
    exact or_comm

/-! Exact physical completion of all four corners. -/

example : (square.completed squareCandidate .meet).boundary = [] := by decide
example : (square.completed squareCandidate .meet).interface = [] := by decide

example : (square.completed squareCandidate .left).boundary =
    [.input squareInput0] := by
  decide

example : (square.completed squareCandidate .left).interface =
    [squareGate1] := by
  decide

example : (square.completed squareCandidate .right).boundary =
    [.input squareInput0] := by
  decide

example : (square.completed squareCandidate .right).interface =
    [squareGate2] := by
  decide

example : (square.completed squareCandidate .join).boundary =
    [.input squareInput0] := by
  decide

example : (square.completed squareCandidate .join).interface =
    [squareGate1, squareGate2] := by
  decide

example (corner : TerminalSupportSquareCorner) :
    (square.completed squareCandidate corner).Compatible :=
  square.physically_compatible squareCandidate corner

example : (square.extracted squareCandidate .meet).gateCount = 0 := by decide
example : (square.extracted squareCandidate .left).gateCount = 2 := by decide
example : (square.extracted squareCandidate .right).gateCount = 1 := by decide
example : (square.extracted squareCandidate .join).gateCount = 3 := by decide

def squareBoundaryFalse : Valuation 1 :=
  (BoolTuple.cons false .nil).toValuation

def squareBoundaryTrue : Valuation 1 :=
  (BoolTuple.cons true .nil).toValuation

/-- Left computes `x`, right computes `not x`, and join exposes both in the
    canonical physical interface order. -/
example :
    (square.extracted squareCandidate .left).extractedCandidate.semantics
      squareBoundaryFalse ⟨0, by decide⟩ = false := by
  decide

example :
    (square.extracted squareCandidate .left).extractedCandidate.semantics
      squareBoundaryTrue ⟨0, by decide⟩ = true := by
  decide

example :
    (square.extracted squareCandidate .right).extractedCandidate.semantics
      squareBoundaryFalse ⟨0, by decide⟩ = true := by
  decide

example :
    (square.extracted squareCandidate .right).extractedCandidate.semantics
      squareBoundaryTrue ⟨0, by decide⟩ = false := by
  decide

example :
    (square.extracted squareCandidate .join).extractedCandidate.semantics
      squareBoundaryTrue ⟨0, by decide⟩ = true := by
  decide

example :
    (square.extracted squareCandidate .join).extractedCandidate.semantics
      squareBoundaryTrue ⟨1, by decide⟩ = false := by
  decide

/-- The universal semantics and induced-boundary theorems remain attached to
    every corner, beyond the concrete truth-table checks. -/
example (corner : TerminalSupportSquareCorner)
    (boundary : Valuation
      (terminalBoundaryPorts squareCandidate.program
        (square.records corner)).length)
    (output : Fin
      (terminalInterfacePorts squareCandidate
        (square.records corner)).length) :
    (square.extracted squareCandidate corner).extractedCandidate.semantics
        boundary output =
      terminalOpenSupportSemantics squareCandidate (square.records corner)
        boundary output :=
  square.extracted_semantics squareCandidate corner boundary output

example (corner : TerminalSupportSquareCorner)
    (input : Valuation 1)
    (output : Fin
      (terminalInterfacePorts squareCandidate
        (square.records corner)).length) :
    (square.extracted squareCandidate corner).extractedCandidate.semantics
        (terminalInducedBoundaryValuation squareCandidate
          (square.records corner) input) output =
      squareCandidate.program.eval input
        ((terminalInterfacePorts squareCandidate
          (square.records corner)).get output) :=
  square.extracted_induced squareCandidate corner input output

end DirectWire
end PNP
