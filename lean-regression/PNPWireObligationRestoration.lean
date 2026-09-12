import PNP

namespace PNP.DirectWire.WireObligationRestoration.Regression

def nandProgram : Program 2 1 :=
  .snoc .empty ⟨.input 0, .input 1⟩

def single : WireCarrier 2 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord nandProgram
        (⟨fun _ => .constant false⟩ : DirectWireWord 2 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def shared : WireCarrier 2 1 2 :=
  { implementation := single.implementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def duplicates : WireCarrier 2 1 2 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (nandProgram.snoc ⟨.input 0, .input 1⟩)
        (⟨fun _ => .constant false⟩ : DirectWireWord 2 2 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨1, by decide⟩ }

def fieldsOnly : WireCarrier 2 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord nandProgram
        (⟨Fin.elim0⟩ : DirectWireWord 2 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def empty : WireCarrier 0 0 0 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0)
        (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

def freeFields : WireCarrier 1 1 3 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .input 0⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .input 0
      else if field.val = 1 then .constant true else .constant false }

def mixed : WireCarrier 1 1 3 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
        (⟨fun _ => .input 0⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .constant true
      else if field.val = 1 then .gate ⟨0, by decide⟩ else .input 0 }

example : single.fieldValue (fun _ => false) 0 = true := rfl
example : (masked single (fun _ => false)).fieldValue (fun _ => false) 0 = false := rfl

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (restored carrier keep).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  restored_output carrier keep valuation output

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (valuation : Valuation inputs) (field : Fin fields) :
    (restored carrier keep).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  restored_field carrier keep valuation field

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    (restored carrier keep).implementation.gateCount =
      (projected carrier keep).implementation.gateCount +
      (materializer carrier keep).implementation.gateCount :=
  restored_exact_gate_charge carrier keep

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    replay [] (events carrier keep) = some [] :=
  replay_closed carrier keep

example {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (creation : R5Creation carrier keep) (valuation : Valuation inputs) :
    (dischargeR8 carrier keep creation).restoredSource.eval valuation
        ((restored carrier keep).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  dischargeR8_full_value carrier keep creation valuation

-- Guarded runtime fixtures exercise the computations. The theorems above, not
-- native execution of these fixtures, provide proof authority.
#eval show IO Unit from do
  let hiddenQ := projected single (fun _ => false)
  let hiddenM := materializer single (fun _ => false)
  let paidSingle := restored single (fun _ => false)
  if hiddenQ.implementation.gateCount != 0 ||
      hiddenM.implementation.gateCount != 1 ||
      paidSingle.implementation.gateCount != 1 then
    throw (IO.userError "a lost NAND value must pay its actual materializer")
  if (gain? single (fun _ => false)).isSome then
    throw (IO.userError "projected saving is not a fully charged strict gain")
  let sharedResult := restored shared (fun _ => false)
  if sharedResult.implementation.gateCount != 1 then
    throw (IO.userError "shared materializer was counted more than once")
  if (createdCoordinates (events shared (fun _ => false))).map Fin.val != [0, 1] ||
      (dischargedCoordinates (events shared (fun _ => false))).map Fin.val != [0, 1] then
    throw (IO.userError "lost coordinates must be created and discharged exactly once")
  if replay [] (events shared (fun _ => false)) != some [] then
    throw (IO.userError "generated lifecycle left an open obligation")
  if (restored duplicates (fun _ => false)).implementation.gateCount != 1 ||
      !(gain? duplicates (fun _ => false)).isSome then
    throw (IO.userError "actual shared saving was not surfaced after paying restoration")
  if (materializer shared (fun _ => true)).implementation.gateCount != 0 ||
      (restored shared (fun _ => true)).implementation.gateCount != 1 ||
      !(events shared (fun _ => true)).isEmpty then
    throw (IO.userError "all-kept mask created unnecessary obligations or charges")
  if (restored fieldsOnly (fun _ => false)).implementation.gateCount != 1 then
    throw (IO.userError "zero ordinary outputs lost a computational field")
  if (restored empty (fun _ => false)).implementation.gateCount != 0 ||
      !(events empty (fun _ => false)).isEmpty ||
      (gain? empty (fun _ => false)).isSome then
    throw (IO.userError "empty dimensions must close without a fictional gain")
  for a in [false, true] do
    for b in [false, true] do
      let valuation : Valuation 2 := fun input => if input.val = 0 then a else b
      if paidSingle.implementation.candidate.semantics valuation 0 != false ||
          paidSingle.fieldValue valuation 0 != PNP.boolNand a b then
        throw (IO.userError "ordinary output or restored hidden NAND value changed")
      if sharedResult.fieldValue valuation 0 != PNP.boolNand a b ||
          sharedResult.fieldValue valuation 1 != PNP.boolNand a b then
        throw (IO.userError "repeated computational fields were not restored")
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    let free := restored freeFields (fun field => field.val == 1)
    if free.implementation.gateCount != 0 ||
        free.implementation.candidate.semantics valuation 0 != value ||
        free.fieldValue valuation 0 != value ||
        free.fieldValue valuation 1 != true ||
        free.fieldValue valuation 2 != false then
      throw (IO.userError "actual input and constant fields must remain free data")
    let reordered := restored mixed (fun field => field.val == 0)
    if reordered.implementation.gateCount != 1 ||
        reordered.implementation.candidate.semantics valuation 0 != value ||
        reordered.fieldValue valuation 0 != true ||
        reordered.fieldValue valuation 1 != !value ||
        reordered.fieldValue valuation 2 != value then
      throw (IO.userError "field order or mixed kept/lost values changed")
  let first := createR5 shared (fun _ => false) ⟨0, by decide⟩ rfl
  let second := createR5 shared (fun _ => false) ⟨1, by decide⟩ rfl
  let firstPaid := dischargeR8 shared (fun _ => false) first
  let orphan : List (Event shared (fun _ => false)) := [.dischargeR8 first firstPaid]
  if (replay [] orphan).isSome then
    throw (IO.userError "discharge without creation was accepted")
  let duplicate : List (Event shared (fun _ => false)) :=
    [.createR5 first, .createR5 first]
  if (replay [] duplicate).isSome then
    throw (IO.userError "duplicate creation was accepted")
  let reused : List (Event shared (fun _ => false)) :=
    [.createR5 first, .dischargeR8 first firstPaid,
      .createR5 first, .dischargeR8 first firstPaid]
  if (replay [] reused).isSome then
    throw (IO.userError "an already discharged identity was created again")
  let wrongOrder : List (Event shared (fun _ => false)) :=
    [.createR5 first, .createR5 second, .dischargeR8 first firstPaid]
  if (replay [] wrongOrder).isSome then
    throw (IO.userError "a discharge closed the wrong pending coordinate")
  IO.println "M251_WIRE_OBLIGATION_RESTORATION_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireObligationRestoration.Regression
