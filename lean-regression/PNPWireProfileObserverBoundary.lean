import PNP

/-
Independent observer-domain obstruction regression; no global proof credit.
The existing implementation-only profile observer cannot represent arbitrary
actual wire bindings, even with an arbitrary finite encoding and decoder.
This does not refute the manuscript's route; it identifies a domain mismatch.
-/


namespace PNP.DirectWire.WireProfileObserverBoundary

variable {inputs outputs fields : Nat}

def constantCarrier (implementation : Implementation inputs outputs) (value : Bool) :
    WireCarrier inputs outputs fields :=
  { implementation := implementation
    source := fun _ => .constant value }

theorem equal_implementation_does_not_determine_profile
    (implementation : Implementation inputs outputs) (field : Fin fields) :
    ∃ left right : WireCarrier inputs outputs fields,
      left.implementation = right.implementation ∧
      ¬ WireProfile.FullEquivalent left right := by
  refine ⟨constantCarrier implementation false, constantCarrier implementation true, rfl, ?_⟩
  intro equivalent
  have same := ((WireProfile.full_iff _ _).1 equivalent).2
    (fun _ => false) field
  change true = false at same
  cases same

theorem no_implementation_observer
    (implementation : Implementation inputs outputs) (field : Fin fields)
    (observe : Implementation inputs outputs → Valuation inputs → Fin fields → Bool) :
    ¬ (∀ carrier : WireCarrier inputs outputs fields,
      ∀ valuation coordinate,
        observe carrier.implementation valuation coordinate =
          carrier.fieldValue valuation coordinate) := by
  intro represents
  have left := represents (constantCarrier implementation false) (fun _ => false) field
  have right := represents (constantCarrier implementation true) (fun _ => false) field
  change observe implementation (fun _ => false) field = false at left
  change observe implementation (fun _ => false) field = true at right
  have contradiction : false = true := left.symm.trans right
  cases contradiction

theorem no_encoded_terminal_observer {profileWidth : Nat}
    (implementation : Implementation inputs outputs) (field : Fin fields)
    (system : TerminalProfileSystem inputs outputs profileWidth)
    (decode : TerminalProfile profileWidth → Valuation inputs → Fin fields → Bool) :
    ¬ (∀ carrier : WireCarrier inputs outputs fields,
      ∀ valuation coordinate,
        decode (system.observe carrier.implementation) valuation coordinate =
          carrier.fieldValue valuation coordinate) :=
  no_implementation_observer implementation field
    (fun candidate valuation coordinate =>
      decode (system.observe candidate) valuation coordinate)

end PNP.DirectWire.WireProfileObserverBoundary

#print axioms PNP.DirectWire.WireProfileObserverBoundary.equal_implementation_does_not_determine_profile
#print axioms PNP.DirectWire.WireProfileObserverBoundary.no_implementation_observer
#print axioms PNP.DirectWire.WireProfileObserverBoundary.no_encoded_terminal_observer
