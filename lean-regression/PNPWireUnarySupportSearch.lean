import PNP

namespace PNP.DirectWire.WireUnarySupportSearch.Regression

def dropAll {fields : Nat} : Fin fields → Bool := fun _ => false

def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

def freeFields : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 3 0)
      (⟨fun _ => .input 2⟩ : DirectWireWord 3 0 1)).toImplementation
    source := fun field => if field.val = 0 then .input 1
      else if field.val = 1 then .constant false else .constant true }

def oneNand : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 3 0).snoc ⟨.input 0, .input 2⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 3 1 1)).toImplementation
    source := Fin.elim0 }

def doubleNotProgram : Program 3 2 :=
  ((.empty : Program 3 0).snoc ⟨.input 2, .input 2⟩).snoc
    ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩

def wholeOnly : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord doubleNotProgram
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := Fin.elim0 }

def constantGain : WireCarrier 3 1 2 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.constant true, .constant true⟩).snoc
        ⟨.input 2, .input 2⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := fun field => .gate ⟨field.val, field.isLt⟩ }

def primaryProgram : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 2, .input 2⟩).snoc ⟨.input 2, .gate ⟨1, by decide⟩⟩

def primaryCarrier (hiddenNegation : Bool) : WireCarrier 3 1 2 :=
  { implementation := (Candidate.ofDirectWireWord primaryProgram
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩
      else if hiddenNegation then .gate ⟨1, by decide⟩ else .constant true }

-- The only available gain requires an external gate, not a primary input.
def externalProgram : Program 3 4 :=
  ((((.empty : Program 3 0).snoc ⟨.input 0, .input 2⟩).snoc
    ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩).snoc
      ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩).snoc
        ⟨.input 1, .input 1⟩

def externalCarrier : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord externalProgram
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 4 1)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨0, by decide⟩
      else if field.val = 1 then .gate ⟨1, by decide⟩ else .gate ⟨3, by decide⟩ }

-- An early selected constant also feeds the exterior boundary gate.
def interleavedProgram (earlyValue : Bool) : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.constant true, .constant (!earlyValue)⟩).snoc
    ⟨.gate ⟨0, by decide⟩, .input 2⟩).snoc ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

def interleaved (earlyValue : Bool) : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord (interleavedProgram earlyValue)
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun field => .gate ⟨field.val, field.isLt⟩ }

def fieldsOnly : WireCarrier 3 0 2 :=
  { implementation := (Candidate.ofDirectWireWord
      (doubleNotProgram.snoc ⟨.input 0, .input 0⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 3 3 0)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨1, by decide⟩
      else .gate ⟨2, by decide⟩ }

-- A two-input duplicate has a global one-gate implementation, but no proper
-- zero/unary support gain. A negative answer must not be called global minimality.
def twoBoundaryDuplicate : WireCarrier 3 2 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 0, .input 1⟩).snoc ⟨.input 0, .input 1⟩)
      (⟨fun output => .gate ⟨output.val, output.isLt⟩⟩ : DirectWireWord 3 2 2)).toImplementation
    source := Fin.elim0 }

def duplicateReference : Implementation 3 2 :=
  (Candidate.ofDirectWireWord ((.empty : Program 3 0).snoc ⟨.input 0, .input 1⟩)
    (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 3 1 2)).toImplementation

def unusedInputs : WireCarrier 64 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 64 0).snoc ⟨.input 63, .input 63⟩).snoc
        ⟨.constant true, .constant true⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 64 2 1)).toImplementation
    source := Fin.elim0 }

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (proper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier records)
    (other : Implementation (WireUnaryArbitrarySupport.pulled carrier records).boundary.length
      (WireUnaryArbitrarySupport.pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics)
    (smaller : other.gateCount < (WireUnaryArbitrarySupport.pulled carrier records).gateCount) :
    (findGain carrier).isSome = true :=
  findGain_complete carrier records small proper other sameOpen smaller

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (result : GainResult carrier) (found : findGain carrier = some result) :
    result.records.length ≤ carrier.implementation.gateCount :=
  findGain_records_bound carrier result found

example {inputs outputs fields : Nat} (carrier replacement : WireCarrier inputs outputs fields)
    (found : findReplacement carrier = some replacement) :
    StrictEquivalentGain carrier.implementation replacement.implementation ∧
      (∀ valuation field, replacement.fieldValue valuation field =
        carrier.fieldValue valuation field) :=
  findReplacement_sound carrier replacement found

def checkSearch {inputs outputs fields : Nat} (name : String)
    (carrier : WireCarrier inputs outputs fields) (expected : Bool) : IO Unit := do
  let gates := carrier.implementation.gateCount
  if inputs > 3 || outputs > 2 || fields > 3 || gates > 4 then
    throw (IO.userError "fixture exceeds the guarded runtime dimensions")
  let family := candidateFamily (outputs := outputs + fields) (profileWidth := 0)
    carrier.exposed.candidate.program
  if family.length > (2 * gates + 1) * gates + gates then
    throw (IO.userError (name ++ ": physical candidate bound failed"))
  for records in family do
    if records.length > gates then
      throw (IO.userError (name ++ ": candidate record bound failed"))
  for choice in boundaryChoices carrier.exposed.candidate.program do
    for omitted in allFin gates do
      let records := candidateRecords (outputs := outputs + fields) (profileWidth := 0)
        carrier.exposed.candidate.program choice omitted
      if (WireUnaryArbitrarySupport.pulled carrier records).boundary.length > 1 ||
          WireUnaryArbitrarySupport.exteriorCharge carrier records == 0 then
        throw (IO.userError (name ++ ": generated maximal support is not proper zero/unary"))
  let answer := findGain carrier
  if answer.isSome != expected then
    throw (IO.userError (name ++ ": source-derived search classification changed"))
  -- This powerset is bounded regression evidence only, never the production algorithm.
  let reference := (List.range (2 ^ gates)).any fun mask =>
    let records : List (TerminalPrimitiveRecord inputs gates (outputs + fields) 0) :=
      ((allFin gates).filter (fun index => (mask / 2 ^ index.val) % 2 == 1)).map
        TerminalPrimitiveRecord.gate
    (WireUnaryArbitrarySupport.checkedProperGain carrier records).isSome
  if answer.isSome != reference then
    throw (IO.userError (name ++ ": search differs from guarded exhaustive reference"))
  match answer with
  | none => pure ()
  | some result =>
      let built := result.expanded
      let support := WireUnaryArbitrarySupport.pulled carrier result.records
      let localCount :=
        (WireUnaryArbitrarySupport.replacement carrier result.records result.gain.small).gateCount
      let exterior := WireUnaryArbitrarySupport.exteriorCharge carrier result.records
      if support.boundary.length > 1 || exterior == 0 ||
          built.implementation.gateCount >= gates ||
          built.implementation.gateCount != localCount + exterior then
        throw (IO.userError (name ++ ": accepted result lost properness, charge or strict saving"))
      for mask in List.range (2 ^ inputs) do
        let valuation : Valuation inputs := fun index => (mask / 2 ^ index.val) % 2 == 1
        for output in allFin outputs do
          if built.implementation.candidate.semantics valuation output !=
              carrier.implementation.candidate.semantics valuation output then
            throw (IO.userError (name ++ ": ordinary output changed"))
        for field in allFin fields do
          if built.fieldValue valuation field != carrier.fieldValue valuation field then
            throw (IO.userError (name ++ ": selected or exterior field changed"))
          let creation := WireObligationRestoration.createR5 carrier dropAll field rfl
          let witness := result.dischargeR7 dropAll creation
          if witness.actualSource ≠ built.source field then
            throw (IO.userError (name ++ ": R7 source is not the actual expanded source"))
          if witness.actualSource.eval valuation
              (built.implementation.candidate.program.eval valuation) !=
                carrier.fieldValue valuation field then
            throw (IO.userError (name ++ ": full-value R7 discharge failed"))
  IO.println ("M258_FIXTURE_GREEN=" ++ name)

def checkEarlyConstant (earlyValue : Bool) : IO Unit := do
  let carrier := interleaved earlyValue
  let choice : BoundaryChoice 3 3 := some (.gate ⟨1, by decide⟩)
  let records : List (TerminalPrimitiveRecord 3 3 4 0) :=
    candidateRecords carrier.exposed.candidate.program choice ⟨1, by decide⟩
  if choice ∉ boundaryChoices carrier.exposed.candidate.program then
    throw (IO.userError "actual external boundary absent from computed choices")
  let support := WireUnaryArbitrarySupport.pulled carrier records
  if support.boundary.length != 1 || support.gateCount != 2 ||
      WireUnaryArbitrarySupport.exteriorCharge carrier records != 1 then
    throw (IO.userError "early-constant maximal candidate changed")
  match WireUnaryArbitrarySupport.checkedProperGain carrier records with
  | none => throw (IO.userError "early-constant external-boundary candidate was rejected")
  | some gain =>
      let result : GainResult carrier := ⟨records, gain⟩
      let built := result.expanded
      if built.implementation.gateCount != 2 then
        throw (IO.userError "early constant incorrectly introduced a boundary dependency")
      for mask in List.range 8 do
        let valuation : Valuation 3 := fun index => (mask / 2 ^ index.val) % 2 == 1
        for field in allFin 3 do
          if built.fieldValue valuation field != carrier.fieldValue valuation field then
            throw (IO.userError "early-constant expanded field changed")
  IO.println ("M258_FIXTURE_GREEN=early-constant-" ++ toString earlyValue)

def checkRepeatedRecords : IO Unit := do
  let carrier := primaryCarrier true
  let records : List (TerminalPrimitiveRecord 3 3 3 0) :=
    [.gate ⟨2, by decide⟩, .boundary 0, .gate ⟨1, by decide⟩,
      .gate ⟨2, by decide⟩, .interface 0]
  if !(WireUnaryArbitrarySupport.checkedProperGain carrier records).isSome ||
      !(findGain carrier).isSome then
    throw (IO.userError "duplicate or metadata records hid a proper gain")
  let generated : List (TerminalPrimitiveRecord 3 3 3 0) :=
    candidateRecords carrier.exposed.candidate.program
      (supportChoice carrier.exposed.candidate.program records) ⟨0, by decide⟩
  for index in allFin 3 do
    if terminalGateSelected records index && !terminalGateSelected generated index then
      throw (IO.userError "actual maximal candidate omitted a selected gate")
  let repeatedSources := (consumedWires primaryProgram).filter
    (fun wire => decide (wire = .input (2 : Fin 3)))
  if repeatedSources.length != 3 then
    throw (IO.userError "consumed-source occurrence semantics changed")
  IO.println "M258_FIXTURE_GREEN=repeated-and-metadata-records"

def checkUnusedInputs : IO Unit := do
  let program := unusedInputs.exposed.candidate.program
  if consumedWires program ≠ [.input (63 : Fin 64), .input (63 : Fin 64)] then
    throw (IO.userError "unused declared inputs entered candidate enumeration")
  if (boundaryChoices program).length != 3 ||
      (candidateFamily (outputs := 1) (profileWidth := 0) program).length != 8 then
    throw (IO.userError "candidate family depends on declared input arity")
  -- The wide case is never passed through valuation enumeration.
  let rejected ← try
    checkSearch "wide-guard" unusedInputs false
    pure false
  catch _ => pure true
  if !rejected then
    throw (IO.userError "guard accepted an unbounded valuation fixture")
  IO.println "M258_FIXTURE_GREEN=unused-inputs-and-runtime-guard"

def checkOutOfScopeSaving : IO Unit := do
  if duplicateReference.gateCount >= twoBoundaryDuplicate.implementation.gateCount then
    throw (IO.userError "out-of-scope reference is not a strict saving")
  for mask in List.range 8 do
    let valuation : Valuation 3 := fun index => (mask / 2 ^ index.val) % 2 == 1
    for output in allFin 2 do
      if duplicateReference.candidate.semantics valuation output !=
          twoBoundaryDuplicate.implementation.candidate.semantics valuation output then
        throw (IO.userError "two-boundary reference does not preserve outputs")
  IO.println "M258_FIXTURE_GREEN=negative-result-is-not-global-minimality"

def checkPublicReplacement : IO Unit := do
  let carrier := primaryCarrier true
  match findReplacement carrier with
  | none => throw (IO.userError "public replacement lost a found gain")
  | some replacement =>
      if replacement.implementation.gateCount != 2 then
        throw (IO.userError "public replacement did not return the expanded carrier")
  IO.println "M258_FIXTURE_GREEN=public-computed-replacement"

-- These finite checks supplement, and never replace, the general kernel theorems.
#eval show IO Unit from do
  checkSearch "empty-dimensions" emptyCarrier false
  checkSearch "free-input-and-constant-fields" freeFields false
  checkSearch "single-two-input-nand" oneNand false
  checkSearch "whole-support-only-gain" wholeOnly false
  checkSearch "singleton-constant-gain" constantGain true
  checkSearch "primary-boundary-and-omitted-gate" (primaryCarrier false) true
  checkSearch "hidden-selected-and-exterior-fields" (primaryCarrier true) true
  checkSearch "sole-external-gate-boundary" externalCarrier true
  checkSearch "interleaved-live-boundary" (interleaved true) true
  checkSearch "interleaved-unrealizable-bit" (interleaved false) true
  checkSearch "fields-without-ordinary-outputs" fieldsOnly true
  checkSearch "two-boundary-no-eligible-gain" twoBoundaryDuplicate false
  checkEarlyConstant true
  checkEarlyConstant false
  checkRepeatedRecords
  checkUnusedInputs
  checkOutOfScopeSaving
  checkPublicReplacement
  IO.println "M258_COMPUTED_UNARY_SUPPORT_SEARCH_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireUnarySupportSearch.Regression
