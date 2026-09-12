import PNP

namespace PNP.DirectWire.WireFrontierLift.Regression

def tautologyProgram : Program 1 2 :=
  ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .gate ⟨0, by decide⟩⟩

def properCarrier : WireCarrier 1 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (tautologyProgram.snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 3 1)).toImplementation
    source := fun field => if field.val = 0 then .gate ⟨1, by decide⟩ else .gate ⟨2, by decide⟩ }

def wholeCarrier : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord tautologyProgram
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 2 1)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

def frontierCarrier : WireCarrier 1 1 1 :=
  { implementation := properCarrier.implementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def properReplacement : Candidate
    (pulled properCarrier (fun _ => false)).boundary.length 0
    (pulled properCarrier (fun _ => false)).interface.length :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .constant true⟩

def wholeReplacement : Candidate
    (pulled wholeCarrier (fun _ => false)).boundary.length 0
    (pulled wholeCarrier (fun _ => false)).interface.length :=
  Candidate.ofDirectWireWord .empty ⟨fun _ => .constant true⟩

def wrongFrontier : Candidate
    (pulled frontierCarrier (fun _ => false)).boundary.length 0
    (pulled frontierCarrier (fun _ => false)).interface.length :=
  Candidate.ofDirectWireWord .empty
    ⟨fun output => .constant (output.val != 0)⟩

-- Finite equivalence checking here is kernel-reduced fixture evidence only.
-- The general construction does not enumerate valuations or replacements.
theorem properAgreement :
    properReplacement.semantics =
      (pulled properCarrier (fun _ => false)).extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool properReplacement
      (pulled properCarrier (fun _ => false)).extractedCandidate = true) input output

theorem wholeAgreement :
    wholeReplacement.semantics =
      (pulled wholeCarrier (fun _ => false)).extractedCandidate.semantics := by
  funext input output
  exact equivalentBool_sound (by decide :
    equivalentBool wholeReplacement
      (pulled wholeCarrier (fun _ => false)).extractedCandidate = true) input output

example : (pulled properCarrier (fun _ => false)).interface.map Fin.val = [1] := by decide
example : (pulled frontierCarrier (fun _ => false)).interface.map Fin.val = [0, 1] := by decide
example : exteriorCharge properCarrier (fun _ => false) = 1 := by decide

-- The wrong replacement matches the ordinary true output, but not the
-- forgotten retained predecessor that the completed full frontier exports.
example (input : Valuation (pulled frontierCarrier (fun _ => false)).boundary.length) :
    wrongFrontier.semantics input ⟨1, by decide⟩ = true := by
  unfold wrongFrontier
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

example : ¬(wrongFrontier.semantics =
    (pulled frontierCarrier (fun _ => false)).extractedCandidate.semantics) := by
  intro same
  have bad := congrFun (congrFun same (fun _ => false)) ⟨0, by decide⟩
  change false = true at bad
  cases bad

def repeated : WireCarrier 1 1 4 :=
  { implementation := properCarrier.implementation
    source := fun field => if field.val = 1 || field.val = 3 then .gate ⟨1, by decide⟩ else .gate ⟨2, by decide⟩ }

def freeFields : WireCarrier 1 1 4 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .input 0⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun field =>
      if field.val = 1 then .constant false
      else if field.val = 3 then .constant true else .input 0 }

def fieldsOnly : WireCarrier 1 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨Fin.elim0⟩ : DirectWireWord 1 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def empty : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0)
        (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  expanded_field carrier keep replacement sameOpen valuation field

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length) :
    (carrier.implementation.gateCount : Int) - (pulled carrier keep).gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacementGates :=
  matched_original_charge carrier keep replacement

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : Candidate (pulled carrier keep).boundary.length replacementGates
      (pulled carrier keep).interface.length)
    (sameOpen : replacement.semantics =
      (pulled carrier keep).extractedCandidate.semantics) :
    (checkedProperGain carrier keep replacement sameOpen).isSome = true ↔
      (pulled carrier keep).gateCount < carrier.implementation.gateCount ∧
        replacementGates < (pulled carrier keep).gateCount :=
  checkedProperGain_isSome_iff carrier keep replacement sameOpen

-- These bounded runs are regressions, not authority for the general theorems.
#eval show IO Unit from do
  let support := pulled properCarrier (fun _ => false)
  let saved := expanded properCarrier (fun _ => false) properReplacement
  if support.gateCount != 2 || exteriorCharge properCarrier (fun _ => false) != 1 ||
      saved.implementation.gateCount != 1 ||
      !(checkedProperGain properCarrier (fun _ => false) properReplacement
        properAgreement).isSome then
    throw (IO.userError "proper gain did not retain the original exterior exactly once")
  if (checkedProperGain properCarrier (fun _ => false)
      support.extractedCandidate rfl).isSome then
    throw (IO.userError "nonstrict replacement fabricated a proper gain")
  let whole := expanded wholeCarrier (fun _ => false) wholeReplacement
  if whole.implementation.gateCount != 0 ||
      exteriorCharge wholeCarrier (fun _ => false) != 0 ||
      (checkedProperGain wholeCarrier (fun _ => false) wholeReplacement
        wholeAgreement).isSome then
    throw (IO.userError "whole-support saving was incorrectly called a proper gain")
  let keptSupport := pulled properCarrier (fun _ => true)
  let kept := expanded properCarrier (fun _ => true) keptSupport.extractedCandidate
  if keptSupport.gateCount != 3 || exteriorCharge properCarrier (fun _ => true) != 0 ||
      kept.implementation.gateCount != 3 then
    throw (IO.userError "all-kept cone lost a computational source")
  let repeatedKeep : Fin 4 → Bool := fun field => field.val == 1
  let repeatedSupport := pulled repeated repeatedKeep
  let repeatedResult := expanded repeated repeatedKeep repeatedSupport.extractedCandidate
  if repeatedSupport.gateCount != 2 || exteriorCharge repeated repeatedKeep != 1 ||
      repeatedResult.implementation.gateCount != 3 then
    throw (IO.userError "ordered repeated fields duplicated physical ownership")
  let freeKeep : Fin 4 → Bool := fun field => field.val == 1 || field.val == 3
  let free := expanded freeFields freeKeep (pulled freeFields freeKeep).extractedCandidate
  if free.implementation.gateCount != 0 then
    throw (IO.userError "free input and constant fields allocated a gate")
  let only := expanded fieldsOnly (fun _ => false)
    (pulled fieldsOnly (fun _ => false)).extractedCandidate
  if (pulled fieldsOnly (fun _ => false)).gateCount != 0 ||
      exteriorCharge fieldsOnly (fun _ => false) != 1 ||
      only.implementation.gateCount != 1 then
    throw (IO.userError "field-only exterior was omitted")
  let emptyResult := expanded empty (fun _ => false)
    (pulled empty (fun _ => false)).extractedCandidate
  if emptyResult.implementation.gateCount != 0 ||
      (checkedProperGain empty (fun _ => false)
        (pulled empty (fun _ => false)).extractedCandidate rfl).isSome then
    throw (IO.userError "empty dimensions fabricated a gain")
  let creation := WireObligationRestoration.createR5
    properCarrier (fun _ => false) ⟨0, by decide⟩ rfl
  let witness := discharge properCarrier (fun _ => false)
    properReplacement properAgreement creation
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    if saved.implementation.candidate.semantics valuation 0 != true ||
        saved.fieldValue valuation 0 != true || saved.fieldValue valuation 1 != !value then
      throw (IO.userError "proper gain changed an ordinary or forgotten observation")
    if witness.actualSource.eval valuation
        (saved.implementation.candidate.program.eval valuation) != true then
      throw (IO.userError "discharge was not bound to the actual expanded source")
    if whole.implementation.candidate.semantics valuation 0 != true ||
        whole.fieldValue valuation 0 != true then
      throw (IO.userError "shared whole-support observation changed")
    if kept.fieldValue valuation 0 != true || kept.fieldValue valuation 1 != !value then
      throw (IO.userError "kept field value changed")
    if (List.finRange 4).map (repeatedResult.fieldValue valuation) !=
        [!value, true, !value, true] then
      throw (IO.userError "reordered repeated fields changed")
    if free.implementation.candidate.semantics valuation 0 != value ||
        (List.finRange 4).map (free.fieldValue valuation) !=
          [value, false, value, true] then
      throw (IO.userError "free mixed-mask field order changed")
    if only.fieldValue valuation 0 != !value then
      throw (IO.userError "forgotten field-only value changed")
  IO.println "M253_ORIGINAL_ACCOUNTED_FRONTIER_LIFT_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireFrontierLift.Regression
