import PNP.ResidualTerminalProperSupport

namespace PNP
namespace DirectWire

abbrev properRecord := TerminalPrimitiveRecord 1 3 1 0

def properInput0 : Fin 1 := ⟨0, by decide⟩
def properGate0 : Fin 3 := ⟨0, by decide⟩
def properGate1 : Fin 3 := ⟨1, by decide⟩
def properGate2 : Fin 3 := ⟨2, by decide⟩

def properProgram0 : Program 1 1 :=
  .snoc .empty
    { left := .input properInput0
      right := .input properInput0 }

def properProgram1 : Program 1 2 :=
  .snoc properProgram0
    { left := .input properInput0
      right := .input properInput0 }

def properProgram : Program 1 3 :=
  .snoc properProgram1
    { left := .gate ⟨1, by decide⟩
      right := .gate ⟨1, by decide⟩ }

def properWord : DirectWireWord 1 3 1 :=
  ⟨fun _output => .gate properGate2⟩

def properCandidate : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord properProgram properWord

def properGate0Record : properRecord := .gate properGate0
def properGate1Record : properRecord := .gate properGate1
def properGate2Record : properRecord := .gate properGate2

def properProfileSystem : TerminalProfileSystem 1 1 0 :=
  { role := fun coordinate => Fin.elim0 coordinate
    observe := fun _implementation coordinate => Fin.elim0 coordinate }

def properSaturationSystem : TerminalSaturationSystem 1 3 1 0 :=
  { profileSystem := properProfileSystem
    requires := fun _kind _dependent _required => false }

def properSeed : List properRecord :=
  [properGate1Record, properGate2Record]

def properSeedSelector : properRecord -> Bool :=
  fun record => decide (record = properGate1Record ∨ record = properGate2Record)

/-- Five primitive records give all 32 canonical subsets. -/
example : (allTerminalSupportSeeds 1 3 1 0).length = 32 := by decide

/-- Boolean selection produces the expected canonical gate order. -/
example : canonicalTerminalSupportSeed 1 3 1 0 properSeedSelector = properSeed := by
  decide

example : properSeed ∈ allTerminalSupportSeeds 1 3 1 0 := by decide

example :
    (extractSaturatedTerminalSupport properCandidate properSaturationSystem
      properSeed).gateCount = 2 := by
  decide

/-- The selected two-gate double negation is a nonempty strict subset of the
    three-gate ambient circuit. -/
example : TerminalSupportProper properCandidate properSaturationSystem properSeed := by
  unfold TerminalSupportProper
  decide

/-- The selected support computes the identity, whose exact open minimum is
    the zero-gate direct boundary projection. -/
example :
    terminalSupportLocalGain properCandidate properSaturationSystem properSeed = 2 := by
  decide

example : TerminalSupportPositive properCandidate properSaturationSystem properSeed := by
  unfold TerminalSupportPositive
  decide

example :
    terminalProperPositiveSupportBool properCandidate properSaturationSystem
      properSeed = true := by
  decide

def properWitness :
    TerminalProperPositiveSupport properCandidate properSaturationSystem :=
  { seed := properSeed
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

example : properWitness.saturatedRecords = properSeed.reverse := by decide

example : properWitness.extractedSupport.gateCount = 2 := by decide

example : properWitness.extractedSupport.boundary = [.input properInput0] := by
  decide

example : properWitness.extractedSupport.interface = [properGate2] := by decide

def properBoundaryFalse : Valuation 1 :=
  (BoolTuple.cons false .nil).toValuation

def properBoundaryTrue : Valuation 1 :=
  (BoolTuple.cons true .nil).toValuation

example :
    properWitness.extractedSupport.extractedCandidate.semantics
      properBoundaryFalse ⟨0, by decide⟩ = false := by
  decide

example :
    properWitness.extractedSupport.extractedCandidate.semantics
      properBoundaryTrue ⟨0, by decide⟩ = true := by
  decide

/-- The universal open-semantics theorem remains attached to the search
    result, not merely to the concrete truth-table example. -/
example (boundary : Valuation 1) (output : Fin 1) :
    properWitness.extractedSupport.extractedCandidate.semantics boundary output =
      terminalOpenSupportSemantics properCandidate properWitness.saturatedRecords
        boundary output :=
  properWitness.extracted_semantics boundary output

example : properWitness.minimumReplacement.program.size = 0 := by decide

example :
    properWitness.minimumReplacement.program.size <
      properWitness.extractedSupport.extractedCandidate.program.size :=
  properWitness.minimumReplacement_size_lt

def properSearchFound : Bool :=
  match findTerminalProperPositiveSupport properCandidate properSaturationSystem with
  | none => false
  | some _found => true

def properSearchFirstSeedMatches : Bool :=
  match findTerminalProperPositiveSupport properCandidate properSaturationSystem with
  | none => false
  | some found => decide (found.seed = properSeed)

/-- The exhaustive search succeeds and deterministically selects the first
    qualifying canonical seed. -/
example : properSearchFound = true := by decide
example : properSearchFirstSeedMatches = true := by decide

example :
    ∃ found,
      findTerminalProperPositiveSupport properCandidate properSaturationSystem =
        some found :=
  findTerminalProperPositiveSupport_exists_of_seed properCandidate
    properSaturationSystem (seed := properSeed) (by decide)
      (by unfold TerminalSupportProper; decide)
      (by unfold TerminalSupportPositive; decide)

/-! A one-gate ambient carrier has no nonempty strict gate subset. -/

abbrev noProperRecord := TerminalPrimitiveRecord 1 1 1 0

def noProperProgram : Program 1 1 :=
  .snoc .empty
    { left := .input properInput0
      right := .input properInput0 }

def noProperWord : DirectWireWord 1 1 1 :=
  ⟨fun _output => .gate ⟨0, by decide⟩⟩

def noProperCandidate : Candidate 1 1 1 :=
  Candidate.ofDirectWireWord noProperProgram noProperWord

def noProperSaturationSystem : TerminalSaturationSystem 1 1 1 0 :=
  { profileSystem := properProfileSystem
    requires := fun _kind _dependent _required => false }

def noProperSearchFound : Bool :=
  match findTerminalProperPositiveSupport noProperCandidate
      noProperSaturationSystem with
  | none => false
  | some _found => true

example : noProperSearchFound = false := by decide

/-- The exact negative specification is universal over all canonical seeds. -/
example :
    findTerminalProperPositiveSupport noProperCandidate
        noProperSaturationSystem = none ↔
      ∀ seed,
        seed ∈ allTerminalSupportSeeds 1 1 1 0 ->
        ¬(TerminalSupportProper noProperCandidate noProperSaturationSystem seed ∧
          TerminalSupportPositive noProperCandidate noProperSaturationSystem seed) :=
  findTerminalProperPositiveSupport_eq_none_iff noProperCandidate
    noProperSaturationSystem

end DirectWire
end PNP
