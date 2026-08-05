/-
Copyright (c) 2026 PNP Labs.

Saturated meet/join squares for finite terminal supports.  Two arbitrary seed
lists are saturated by the existing executable work list.  Their meet is the
canonical intersection of the saturated record sets, and their join is the
executable saturation of their union.  The four resulting corners are closed,
form the expected lower/upper bounds extensionally, and admit the existing
computed physical completion and exact open-support extraction.

This reconstructs the algebraic and physical part of the pinned manuscript's
Section 3 saturated support-square closure theorem.  The terminal dependency
system remains explicit data.  No profile-frontier pushout, projection
compatibility, positivity-preservation, route, BCELReady, ZeroSlack, PCCMin,
polynomial-runtime, or P = NP claim is made.
-/

import PNP.ResidualTerminalProperSupport

namespace PNP
namespace DirectWire

/-- The four positions in a saturated support square. -/
inductive TerminalSupportSquareCorner where
  | meet
  | left
  | right
  | join
  deriving Repr, DecidableEq

/-- A pair of finite terminal seeds governed by one explicit saturation
    system.  The four square corners are computed from these seeds; callers do
    not supply corner lists or closure certificates. -/
structure TerminalSaturatedSupportSquare
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  leftSeed : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  rightSeed : List
    (TerminalPrimitiveRecord inputs gates outputs profileWidth)

/-- Build the exact support-square input from two finite seed lists. -/
def terminalSaturatedSupportSquare
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (leftSeed rightSeed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    TerminalSaturatedSupportSquare system :=
  { leftSeed := leftSeed
    rightSeed := rightSeed }

/-- Executable saturation of the left seed. -/
def TerminalSaturatedSupportSquare.leftRecords
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  terminalSaturateRecords system square.leftSeed

/-- Executable saturation of the right seed. -/
def TerminalSaturatedSupportSquare.rightRecords
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  terminalSaturateRecords system square.rightSeed

/-- Canonically ordered intersection of the two saturated sides. -/
def TerminalSaturatedSupportSquare.meetRecords
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (allTerminalPrimitiveRecords inputs gates outputs profileWidth).filter
    (fun record => decide
      (record ∈ square.leftRecords ∧ record ∈ square.rightRecords))

/-- Executable saturation of the union of the two saturated sides. -/
def TerminalSaturatedSupportSquare.joinRecords
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  terminalSaturateRecords system (square.leftRecords ++ square.rightRecords)

/-- Select one of the four exact computed record lists. -/
def TerminalSaturatedSupportSquare.records
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalSupportSquareCorner ->
      List (TerminalPrimitiveRecord inputs gates outputs profileWidth)
  | .meet => square.meetRecords
  | .left => square.leftRecords
  | .right => square.rightRecords
  | .join => square.joinRecords

/-- Exact membership specification for the saturated meet. -/
theorem TerminalSaturatedSupportSquare.mem_meetRecords_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ square.meetRecords ↔
      record ∈ square.leftRecords ∧ record ∈ square.rightRecords := by
  unfold meetRecords
  constructor
  · intro member
    have checked := (List.mem_filter.mp member).2
    exact of_decide_eq_true checked
  · intro both
    exact List.mem_filter.mpr
      ⟨mem_allTerminalPrimitiveRecords record, decide_eq_true both⟩

/-- The left corner is closed under every governed dependency. -/
theorem TerminalSaturatedSupportSquare.leftRecords_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.leftRecords) system :=
  terminalSaturateRecords_closed system square.leftSeed

/-- The right corner is closed under every governed dependency. -/
theorem TerminalSaturatedSupportSquare.rightRecords_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.rightRecords) system :=
  terminalSaturateRecords_closed system square.rightSeed

/-- Intersecting two closed terminal record sets remains closed. -/
theorem TerminalSaturatedSupportSquare.meetRecords_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.meetRecords) system := by
  intro kind dependent required dependentMember edge
  have both := (square.mem_meetRecords_iff dependent).1 dependentMember
  apply (square.mem_meetRecords_iff required).2
  exact ⟨
    square.leftRecords_closed kind dependent required both.1 edge,
    square.rightRecords_closed kind dependent required both.2 edge⟩

private theorem sideUnion_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Closed
      (fun record =>
        record ∈ square.leftRecords ∨ record ∈ square.rightRecords) system := by
  intro kind dependent required dependentMember edge
  cases dependentMember with
  | inl leftMember =>
      exact Or.inl
        (square.leftRecords_closed kind dependent required leftMember edge)
  | inr rightMember =>
      exact Or.inr
        (square.rightRecords_closed kind dependent required rightMember edge)

/-- Exact membership specification for the saturated join.  Because the
    dependency relation is unary and both sides are already closed, their
    union is closed and the final saturation adds no new member. -/
theorem TerminalSaturatedSupportSquare.mem_joinRecords_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ square.joinRecords ↔
      record ∈ square.leftRecords ∨ record ∈ square.rightRecords := by
  constructor
  · intro member
    have generated :=
      (mem_terminalSaturateRecords_iff system
        (square.leftRecords ++ square.rightRecords) record).1 member
    apply terminalSaturate_least system
      (fun candidate =>
        candidate ∈ square.leftRecords ++ square.rightRecords)
      (fun candidate =>
        candidate ∈ square.leftRecords ∨ candidate ∈ square.rightRecords)
      (fun candidate candidateMember =>
        List.mem_append.mp candidateMember)
      (sideUnion_closed square)
      record generated
  · intro member
    apply terminalSaturateRecords_extensive system
      (square.leftRecords ++ square.rightRecords) record
    exact List.mem_append.mpr member

/-- The join corner is closed under every governed dependency. -/
theorem TerminalSaturatedSupportSquare.joinRecords_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.joinRecords) system :=
  terminalSaturateRecords_closed system
    (square.leftRecords ++ square.rightRecords)

/-- Every one of the four computed square corners is closed. -/
theorem TerminalSaturatedSupportSquare.records_closed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (corner : TerminalSupportSquareCorner) :
    TerminalRawSupport.Closed
      (fun record => record ∈ square.records corner) system := by
  cases corner with
  | meet => exact square.meetRecords_closed
  | left => exact square.leftRecords_closed
  | right => exact square.rightRecords_closed
  | join => exact square.joinRecords_closed

/-- The meet is contained in the left side. -/
theorem TerminalSaturatedSupportSquare.meetRecords_subset_left
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Subset
      (fun record => record ∈ square.meetRecords)
      (fun record => record ∈ square.leftRecords) := by
  intro record member
  exact (square.mem_meetRecords_iff record).1 member |>.1

/-- The meet is contained in the right side. -/
theorem TerminalSaturatedSupportSquare.meetRecords_subset_right
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Subset
      (fun record => record ∈ square.meetRecords)
      (fun record => record ∈ square.rightRecords) := by
  intro record member
  exact (square.mem_meetRecords_iff record).1 member |>.2

/-- The left side is contained in the join. -/
theorem TerminalSaturatedSupportSquare.leftRecords_subset_join
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Subset
      (fun record => record ∈ square.leftRecords)
      (fun record => record ∈ square.joinRecords) := by
  intro record member
  exact (square.mem_joinRecords_iff record).2 (Or.inl member)

/-- The right side is contained in the join. -/
theorem TerminalSaturatedSupportSquare.rightRecords_subset_join
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) :
    TerminalRawSupport.Subset
      (fun record => record ∈ square.rightRecords)
      (fun record => record ∈ square.joinRecords) := by
  intro record member
  exact (square.mem_joinRecords_iff record).2 (Or.inr member)

/-- The computed meet is the greatest support contained in both sides. -/
theorem TerminalSaturatedSupportSquare.meetRecords_greatest
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (support : TerminalRawSupport inputs gates outputs profileWidth)
    (withinLeft : TerminalRawSupport.Subset support
      (fun record => record ∈ square.leftRecords))
    (withinRight : TerminalRawSupport.Subset support
      (fun record => record ∈ square.rightRecords)) :
    TerminalRawSupport.Subset support
      (fun record => record ∈ square.meetRecords) := by
  intro record member
  exact (square.mem_meetRecords_iff record).2
    ⟨withinLeft record member, withinRight record member⟩

/-- The computed join is the least support containing both sides.  Together
    with `joinRecords_closed`, this is the least closed upper-bound law. -/
theorem TerminalSaturatedSupportSquare.joinRecords_least
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (support : TerminalRawSupport inputs gates outputs profileWidth)
    (containsLeft : TerminalRawSupport.Subset
      (fun record => record ∈ square.leftRecords) support)
    (containsRight : TerminalRawSupport.Subset
      (fun record => record ∈ square.rightRecords) support) :
    TerminalRawSupport.Subset
      (fun record => record ∈ square.joinRecords) support := by
  intro record member
  cases (square.mem_joinRecords_iff record).1 member with
  | inl leftMember => exact containsLeft record leftMember
  | inr rightMember => exact containsRight record rightMember

/-- Executable saturation depends only on seed membership, not seed order or
    duplicate occurrences. -/
theorem terminalSaturateRecords_mem_congr
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (leftSeed rightSeed : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (sameMembers : ∀ record, record ∈ leftSeed ↔ record ∈ rightSeed)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ terminalSaturateRecords system leftSeed ↔
      record ∈ terminalSaturateRecords system rightSeed := by
  rw [mem_terminalSaturateRecords_iff, mem_terminalSaturateRecords_iff]
  constructor
  · exact terminalSaturate_monotone system
      (fun candidate => candidate ∈ leftSeed)
      (fun candidate => candidate ∈ rightSeed)
      (fun candidate member => (sameMembers candidate).1 member)
      record
  · exact terminalSaturate_monotone system
      (fun candidate => candidate ∈ rightSeed)
      (fun candidate => candidate ∈ leftSeed)
      (fun candidate member => (sameMembers candidate).2 member)
      record

/-- Every square corner is extensionally invariant under reordering or
    duplication of either seed. -/
theorem TerminalSaturatedSupportSquare.records_congr
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalSaturatedSupportSquare system)
    (leftSame : ∀ record, record ∈ left.leftSeed ↔ record ∈ right.leftSeed)
    (rightSame : ∀ record, record ∈ left.rightSeed ↔ record ∈ right.rightSeed)
    (corner : TerminalSupportSquareCorner)
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ left.records corner ↔ record ∈ right.records corner := by
  have leftRecordsSame := terminalSaturateRecords_mem_congr system
    left.leftSeed right.leftSeed leftSame
  have rightRecordsSame := terminalSaturateRecords_mem_congr system
    left.rightSeed right.rightSeed rightSame
  cases corner with
  | meet =>
      change record ∈ left.meetRecords ↔ record ∈ right.meetRecords
      rw [left.mem_meetRecords_iff, right.mem_meetRecords_iff]
      exact and_congr (leftRecordsSame record) (rightRecordsSame record)
  | left => exact leftRecordsSame record
  | right => exact rightRecordsSame record
  | join =>
      change record ∈ left.joinRecords ↔ record ∈ right.joinRecords
      rw [left.mem_joinRecords_iff, right.mem_joinRecords_iff]
      exact or_congr (leftRecordsSame record) (rightRecordsSame record)

/-- Compute the physical boundary and interface of one square corner from the
    actual direct-wire candidate. -/
def TerminalSaturatedSupportSquare.completed
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    TerminalPhysicalCompletedSupport (profileWidth := profileWidth) candidate :=
  completeTerminalPhysicalSupport candidate (square.records corner)

/-- Every computed corner has the exact incoming/outgoing compatibility
    required by open-support extraction. -/
theorem TerminalSaturatedSupportSquare.physically_compatible
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    (square.completed candidate corner).Compatible :=
  completeTerminalPhysicalSupport_compatible candidate (square.records corner)

/-- Extract one exact open direct-wire candidate from a square corner. -/
def TerminalSaturatedSupportSquare.extracted
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    TerminalExtractedSupport (profileWidth := profileWidth) candidate :=
  extractTerminalSupport candidate (square.records corner)

/-- Every extracted corner has exactly one NAND gate per selected ambient
    gate. -/
theorem TerminalSaturatedSupportSquare.extracted_gateCount
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner) :
    (square.extracted candidate corner).gateCount =
      (terminalSelectedGates (square.records corner)).length :=
  extractTerminalSupport_gateCount candidate (square.records corner)

/-- Every extracted corner denotes its independently defined open-support
    function for every boundary valuation and interface coordinate. -/
theorem TerminalSaturatedSupportSquare.extracted_semantics
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner)
    (boundaryValuation : Valuation
      (terminalBoundaryPorts candidate.program
        (square.records corner)).length)
    (output : Fin
      (terminalInterfacePorts candidate (square.records corner)).length) :
    (square.extracted candidate corner).extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics candidate (square.records corner)
        boundaryValuation output :=
  extractTerminalSupport_semantics candidate (square.records corner)
    boundaryValuation output

/-- On whole-circuit-induced boundaries, every extracted corner recovers the
    original gate value at its ordered interface. -/
theorem TerminalSaturatedSupportSquare.extracted_induced
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (corner : TerminalSupportSquareCorner)
    (input : Valuation inputs)
    (output : Fin
      (terminalInterfacePorts candidate (square.records corner)).length) :
    (square.extracted candidate corner).extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate
          (square.records corner) input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate
          (square.records corner)).get output) :=
  extractTerminalSupport_induced candidate (square.records corner) input output

end DirectWire
end PNP
