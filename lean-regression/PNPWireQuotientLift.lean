import PNP

namespace PNP.DirectWire.WireQuotientLift.Regression

def tautologyProgram : Program 1 2 :=
  ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .gate ⟨0, by decide⟩⟩

def noNetGain : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord tautologyProgram
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 2 1)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

def nonzeroSuccess : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (tautologyProgram.snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 3 1)).toImplementation
    source := fun _ => .gate ⟨2, by decide⟩ }

def shared : WireCarrier 1 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def trueReplacement (fields : Nat) : WireCarrier 1 1 fields :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant false }

private theorem trueReplacement_output (fields : Nat)
    (valuation : Valuation 1) (output : Fin 1) :
    (trueReplacement fields).implementation.candidate.semantics valuation output = true := by
  unfold trueReplacement
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

private theorem shared_output (valuation : Valuation 1) (output : Fin 1) :
    shared.implementation.candidate.semantics valuation output = true := by
  unfold shared
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  rfl

private theorem noNetGain_output (valuation : Valuation 1) (output : Fin 1) :
    noNetGain.implementation.candidate.semantics valuation output = true := by
  unfold noNetGain
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  change boolNand (valuation 0) (boolNand (valuation 0) (valuation 0)) = true
  cases valuation 0 <;> rfl

private theorem nonzeroSuccess_output (valuation : Valuation 1) (output : Fin 1) :
    nonzeroSuccess.implementation.candidate.semantics valuation output = true := by
  unfold nonzeroSuccess
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics]
  change boolNand (valuation 0) (boolNand (valuation 0) (valuation 0)) = true
  cases valuation 0 <;> rfl

private def trueAgreement {fields : Nat} (carrier : WireCarrier 1 1 fields)
    (outputTrue : ∀ valuation output,
      carrier.implementation.candidate.semantics valuation output = true) :
    QuotientAgreement carrier (fun _ => false) (trueReplacement fields) where
  output := by
    intro valuation output
    rw [WireObligationRestoration.projected_output, trueReplacement_output]
    exact (outputTrue valuation output).symm
  keptField := by
    intro _valuation _field kept
    cases kept

def noNetAgreement :=
  trueAgreement noNetGain noNetGain_output

def successAgreement :=
  trueAgreement nonzeroSuccess nonzeroSuccess_output

def sharedAgreement :=
  trueAgreement shared shared_output

def freeFields : WireCarrier 1 1 4 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .input 0⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun field =>
      if field.val = 1 then .constant false
      else if field.val = 3 then .constant true else .input 0 }

def freeKeep (field : Fin 4) : Bool :=
  field.val == 1 || field.val == 3

private def maskedAgreement {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    QuotientAgreement carrier keep (WireObligationRestoration.masked carrier keep) where
  output := fun valuation output =>
    ((WireObligationRestoration.masked carrier keep).normalize_output valuation output).symm
  keptField := fun valuation field _kept =>
    ((WireObligationRestoration.masked carrier keep).normalize_field valuation field).symm

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

def wrongOutput : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .constant false⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant false }

example : ¬QuotientAgreement noNetGain (fun _ => false) wrongOutput := by
  intro same
  have bad := same.output (fun _ => false) 0
  rw [WireObligationRestoration.projected_output] at bad
  change false = true at bad
  cases bad

example : ¬QuotientAgreement noNetGain (fun _ => true) (trueReplacement 1) := by
  intro same
  have bad := same.keptField (fun _ => false) 0 rfl
  rw [WireObligationRestoration.projected_kept_field
    noNetGain (fun _ => true) (fun _ => false) 0 rfl] at bad
  change false = true at bad
  cases bad

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  expanded_field carrier keep replacement same valuation field

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    ((referenceLift carrier keep).implementation.gateCount : Int) -
        (WireObligationRestoration.projected carrier keep).implementation.gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacement.implementation.gateCount :=
  matched_materializer_charge carrier keep replacement

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement) :
    (checkedGain carrier keep replacement same).isSome = true ↔
      replacement.implementation.gateCount + charge carrier keep <
        carrier.implementation.gateCount :=
  checkedGain_isSome_iff carrier keep replacement same

-- These bounded computations are regression evidence, not theorem authority.
#eval show IO Unit from do
  let quotient := WireObligationRestoration.projected noNetGain (fun _ => false)
  let reference := referenceLift noNetGain (fun _ => false)
  let restored := expanded noNetGain (fun _ => false) (trueReplacement 1)
  if quotient.implementation.gateCount != 2 ||
      charge noNetGain (fun _ => false) != 2 ||
      reference.implementation.gateCount != 4 ||
      restored.implementation.gateCount != 2 then
    throw (IO.userError "relative saving must keep the actual shared materializer charge")
  if (checkedGain noNetGain (fun _ => false) (trueReplacement 1) noNetAgreement).isSome then
    throw (IO.userError "a saving against the lifted reference was misreported as an original gain")
  let paid := expanded nonzeroSuccess (fun _ => false) (trueReplacement 1)
  if charge nonzeroSuccess (fun _ => false) != 1 ||
      paid.implementation.gateCount != 1 ||
      !(checkedGain nonzeroSuccess (fun _ => false) (trueReplacement 1)
        successAgreement).isSome then
    throw (IO.userError "nonzero-cost original gain did not pay exactly its materializer")
  let repeated := expanded shared (fun _ => false) (trueReplacement 2)
  if charge shared (fun _ => false) != 1 || repeated.implementation.gateCount != 1 then
    throw (IO.userError "one shared materializer was charged once per repeated field")
  let kept := expanded noNetGain (fun _ => true)
    (WireObligationRestoration.projected noNetGain (fun _ => true))
  if charge noNetGain (fun _ => true) != 0 || kept.implementation.gateCount != 2 then
    throw (IO.userError "all-kept projection fabricated a restoration charge")
  let free := expanded freeFields freeKeep (WireObligationRestoration.masked freeFields freeKeep)
  if charge freeFields freeKeep != 0 || free.implementation.gateCount != 0 then
    throw (IO.userError "input and constant fields must remain zero-gate data")
  let only := expanded fieldsOnly (fun _ => false)
    (WireObligationRestoration.projected fieldsOnly (fun _ => false))
  if only.implementation.gateCount != 1 then
    throw (IO.userError "zero ordinary outputs erased a lost field's materializer")
  let emptyResult := expanded empty (fun _ => false)
    (WireObligationRestoration.projected empty (fun _ => false))
  if emptyResult.implementation.gateCount != 0 ||
      (checkedGain empty (fun _ => false)
        (WireObligationRestoration.projected empty (fun _ => false))
        (referenceAgreement empty (fun _ => false))).isSome then
    throw (IO.userError "empty dimensions fabricated a strict gain")
  let creation := WireObligationRestoration.createR5
    noNetGain (fun _ => false) ⟨0, by decide⟩ rfl
  let witness := discharge noNetGain (fun _ => false) (trueReplacement 1) creation
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    if (trueReplacement 1).fieldValue valuation 0 != false ||
        restored.implementation.candidate.semantics valuation 0 != true ||
        restored.fieldValue valuation 0 != true then
      throw (IO.userError "forgotten replacement data was not repaired from the original source")
    if witness.actualSource.eval valuation
        (restored.implementation.candidate.program.eval valuation) != true then
      throw (IO.userError "full discharge referred to the wrong expanded source")
    if paid.implementation.candidate.semantics valuation 0 != true ||
        paid.fieldValue valuation 0 != !value then
      throw (IO.userError "the paid strict gain changed a complete observation")
    if repeated.fieldValue valuation 0 != !value ||
        repeated.fieldValue valuation 1 != !value then
      throw (IO.userError "shared forgotten fields were not restored in order")
    if kept.fieldValue valuation 0 != true then
      throw (IO.userError "a kept field changed")
    if free.implementation.candidate.semantics valuation 0 != value ||
        free.fieldValue valuation 0 != value ||
        free.fieldValue valuation 1 != false ||
        free.fieldValue valuation 2 != value ||
        free.fieldValue valuation 3 != true then
      throw (IO.userError "mixed kept, forgotten, repeated or ordered free fields changed")
    if only.fieldValue valuation 0 != !value then
      throw (IO.userError "the field-only expansion changed its hidden value")
  IO.println "M252_QUOTIENT_REPLACEMENT_LIFT_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireQuotientLift.Regression
