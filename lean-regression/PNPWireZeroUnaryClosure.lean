import PNP

namespace PNP.DirectWire.WireZeroUnaryClosure.Regression

open WireUnaryArbitrarySupport

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

def minimalNot : WireCarrier 1 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 1 1 1)).toImplementation
    source := Fin.elim0 }

def wholeTautology : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 2, .input 2⟩).snoc
        ⟨.input 2, .gate ⟨0, by decide⟩⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := Fin.elim0 }

def wholeDoubleNot : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 2, .input 2⟩).snoc
        ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := Fin.elim0 }

def properProgram : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 2, .input 2⟩).snoc ⟨.input 2, .gate ⟨1, by decide⟩⟩

def properCarrier (hiddenNegation : Bool) : WireCarrier 3 1 2 :=
  { implementation := (Candidate.ofDirectWireWord properProgram
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨0, by decide⟩
      else if hiddenNegation then .gate ⟨1, by decide⟩ else .constant true }

def mixedNormalization : WireCarrier 3 1 2 :=
  { implementation := (Candidate.ofDirectWireWord
      (properProgram.snoc ⟨.input 0, .input 0⟩)
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 4 1)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨3, by decide⟩ }

def twoSequentialGains : WireCarrier 3 2 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
        ⟨.input 0, .gate ⟨0, by decide⟩⟩).snoc ⟨.input 2, .input 2⟩).snoc
          ⟨.input 2, .gate ⟨2, by decide⟩⟩)
      (⟨fun output => if output.val = 0 then .gate ⟨1, by decide⟩
        else .gate ⟨3, by decide⟩⟩ : DirectWireWord 3 4 2)).toImplementation
    source := Fin.elim0 }

def gainThenConstants : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
        ⟨.input 0, .gate ⟨0, by decide⟩⟩).snoc
          ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩).snoc
            ⟨.input 2, .gate ⟨2, by decide⟩⟩)
      (⟨fun _ => .gate ⟨3, by decide⟩⟩ : DirectWireWord 3 4 1)).toImplementation
    source := Fin.elim0 }

def fieldsOnly : WireCarrier 3 0 2 :=
  { implementation := (Candidate.ofDirectWireWord properProgram
      (⟨Fin.elim0⟩ : DirectWireWord 3 3 0)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨2, by decide⟩ else .gate ⟨0, by decide⟩ }

def constantsOnly : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 1 0).snoc ⟨.input 0, .constant false⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def deadOnly : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
        ⟨.input 1, .input 1⟩)
      (⟨fun _ => .input 2⟩ : DirectWireWord 3 2 1)).toImplementation
    source := Fin.elim0 }

-- x OR (x AND y) is x. Its three-gate word is a common fixed point for the
-- implemented pass family, although a zero-gate equivalent word exists.
def nonminimum : WireCarrier 2 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      ((((.empty : Program 2 0).snoc ⟨.input 0, .input 1⟩).snoc
        ⟨.input 0, .input 0⟩).snoc ⟨.gate ⟨1, by decide⟩, .gate ⟨0, by decide⟩⟩)
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 2 3 1)).toImplementation
    source := Fin.elim0 }

def smallerReference : Implementation 2 1 :=
  (Candidate.ofDirectWireWord (.empty : Program 2 0)
    (⟨fun _ => .input 0⟩ : DirectWireWord 2 0 1)).toImplementation

example : StrictEquivalentGain nonminimum.implementation smallerReference :=
  strictEquivalentGainBool_sound (by decide)

example : 0 < residualSlack nonminimum.implementation :=
  Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack smallerReference))
    (strictEquivalentGainBool_sound (by decide :
      strictEquivalentGainBool nonminimum.implementation smallerReference = true)).strictResidualDescent

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields) :
    (run (run carrier).result).result = (run carrier).result :=
  run_idempotent carrier

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields) :
    residualSlack carrier.implementation =
      residualSlack (run carrier).result.implementation + (run carrier).trace.savedGates :=
  run_residualSlack carrier

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields) :
    (run carrier).trace.searchCalls ≤ residualSlack carrier.implementation + 1 :=
  run_searchCalls_le_residualSlack carrier

def branchNames {inputs outputs fields : Nat}
    {current final : WireCarrier inputs outputs fields} : Trace current final → List String
  | .done _ _ => []
  | .step _ gain _ tail =>
      (match gain with | .proper _ => "proper" | .wholeSpan _ => "whole-span") ::
        branchNames tail

def assertQuiet {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) : IO Unit := do
  for pass in [PhysicalNormalizationPass.constants, .sharing, .pruning] do
    if physicalNormalizationPassSavings pass carrier.exposed != 0 then
      throw (IO.userError "final carrier is not quiet for all three physical passes")
  if (WireUnarySupportSearch.findGain carrier).isSome || (wholeGain carrier).isSome ||
      (nextGain carrier).isSome then
    throw (IO.userError "a proper or whole-span zero/unary gain remains")

def checkClosure {inputs outputs fields : Nat} (name : String)
    (carrier : WireCarrier inputs outputs fields) (expectedGates expectedIterations : Nat)
    (expectedBranches : List String) : IO Unit := do
  let gates := carrier.implementation.gateCount
  if inputs > 3 || outputs > 2 || fields > 3 || gates > 4 then
    throw (IO.userError "fixture exceeds the guarded runtime dimensions")
  let execution := run carrier
  let final := execution.result
  if final.implementation.gateCount != expectedGates ||
      execution.trace.gainIterations != expectedIterations ||
      branchNames execution.trace != expectedBranches ||
      execution.trace.searchCalls != expectedBranches.length + 1 then
    throw (IO.userError (name ++ ": computed result or trace classification changed"))
  if final.implementation.gateCount + execution.trace.savedGates != gates ||
      execution.trace.gainIterations > execution.trace.savedGates ||
      execution.trace.searchCalls > execution.trace.gainIterations + 1 then
    throw (IO.userError (name ++ ": exact physical accounting failed"))
  assertQuiet final
  let repeated := run final
  if repeated.result.implementation.gateCount != expectedGates ||
      repeated.trace.savedGates != 0 || repeated.trace.gainIterations != 0 ||
      repeated.trace.searchCalls != 1 || branchNames repeated.trace != [] then
    throw (IO.userError (name ++ ": common fixed point was not operationally idempotent"))
  for mask in List.range (2 ^ inputs) do
    let valuation : Valuation inputs := fun index => (mask / 2 ^ index.val) % 2 == 1
    for output in allFin outputs do
      if final.implementation.candidate.semantics valuation output !=
          carrier.implementation.candidate.semantics valuation output then
        throw (IO.userError (name ++ ": ordinary output changed"))
    for field in allFin fields do
      if final.fieldValue valuation field != carrier.fieldValue valuation field then
        throw (IO.userError (name ++ ": complete computational field changed"))
  -- Guarded exhaustive support comparison is regression evidence only.
  -- The production closure neither enumerates this powerset nor calls a semantic minimum.
  let finalGates := final.implementation.gateCount
  for mask in List.range (2 ^ finalGates) do
    let records : List (TerminalPrimitiveRecord inputs finalGates (outputs + fields) 0) :=
      ((allFin finalGates).filter (fun index => (mask / 2 ^ index.val) % 2 == 1)).map
        TerminalPrimitiveRecord.gate
    if small : (pulled final records).boundary.length ≤ 1 then
      if (replacement final records small).gateCount < (pulled final records).gateCount then
        throw (IO.userError (name ++ ": guarded reference found a missed zero/unary gain"))
  IO.println ("M259_FIXTURE_GREEN=" ++ name)

def unusedInputs : WireCarrier 64 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 64 0).snoc ⟨.input 63, .input 63⟩).snoc
        ⟨.input 63, .gate ⟨0, by decide⟩⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 64 2 1)).toImplementation
    source := Fin.elim0 }

def checkUnusedInputs : IO Unit := do
  let execution := run unusedInputs
  if execution.result.implementation.gateCount != 0 ||
      branchNames execution.trace != ["whole-span"] ||
      execution.trace.savedGates != 2 || execution.trace.searchCalls != 2 then
    throw (IO.userError "unused declared inputs changed the whole-span descent")
  for value in [false, true] do
    let valuation : Valuation 64 := fun _ => value
    if execution.result.implementation.candidate.semantics valuation 0 != true then
      throw (IO.userError "unused-input fixture lost its constant output")
  assertQuiet execution.result
  IO.println "M259_FIXTURE_GREEN=unused-declared-inputs"

#eval (show IO Unit from do
  checkClosure "empty-dimensions" emptyCarrier 0 0 []
  checkClosure "free-ordered-fields" freeFields 0 0 []
  checkClosure "two-boundary-nand" oneNand 1 0 []
  checkClosure "minimal-negation" minimalNot 1 0 []
  checkClosure "whole-span-tautology" wholeTautology 0 1 ["whole-span"]
  checkClosure "whole-span-double-negation" wholeDoubleNot 0 1 ["whole-span"]
  checkClosure "proper-tautology-exterior-field" (properCarrier false) 1 1 ["proper"]
  checkClosure "hidden-selected-negation" (properCarrier true) 2 1 ["proper"]
  checkClosure "sharing-then-proper-gain" mixedNormalization 1 2 ["proper"]
  checkClosure "proper-then-whole-span" twoSequentialGains 0 2 ["proper", "whole-span"]
  checkClosure "gain-restarts-constant-propagation" gainThenConstants 0 2 ["proper"]
  checkClosure "no-ordinary-outputs" fieldsOnly 1 1 ["proper"]
  checkClosure "constant-normalization-only" constantsOnly 0 1 []
  checkClosure "dead-support-normalization-only" deadOnly 0 1 []
  checkClosure "nonminimum-common-fixed-point" nonminimum 3 0 []
  checkUnusedInputs
  IO.println "computed-zero-unary-descent-closure-fixtures: passed"
  IO.println "M259_COMPUTED_ZERO_UNARY_CLOSURE_RUNTIME_FIXTURES_GREEN")

end PNP.DirectWire.WireZeroUnaryClosure.Regression
