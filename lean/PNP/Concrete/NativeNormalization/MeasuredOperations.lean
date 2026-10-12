import PNP.Concrete.NativeNormalization.MeasuredChoice

namespace PNP.Concrete.NativeNormalization.MeasuredOperations

open PNP.Concrete MeasuredReach NativeContext NativeSource NativeBasis

/-- Generic accounting interface. The source constructor below supplies every field and proof. -/
structure Operations (S : Selection n c) where
  literal : Fin c → Slot → Measured (Literal n)
  literal_eq : ∀ i s, (literal i s).value = S.literal i s
  owner : Fin n → Measured (Fin c)
  owner_eq : ∀ v, (owner v).value = S.owner v
  slot : Fin n → Measured Slot
  slot_eq : ∀ v, (slot v).value = S.slot v
  mode : Fin c → Measured (Option Slot)
  mode_eq : ∀ i, (mode i).value = S.mode i

def Bounded {S : Selection n c} (ops : Operations S) (L O D M : Nat) : Prop :=
  (∀ i s, (ops.literal i s).cost ≤ L) ∧
  (∀ v, (ops.owner v).cost ≤ O) ∧
  (∀ v, (ops.slot v).cost ≤ D) ∧
  (∀ i, (ops.mode i).cost ≤ M)

def source {F : CNFFormula} (C : Prepared F) (three : ThreeCore F) :
    Operations (C.rawSelection three) :=
  { literal := MeasuredAccess.literal C three
    literal_eq := MeasuredAccess.literal_value C three
    owner := MeasuredChoice.partner C.toCutData
    owner_eq := MeasuredChoice.partner_value C.toCutData
    slot := MeasuredChoice.slot C three
    slot_eq := MeasuredChoice.slot_value C three
    mode := MeasuredChoice.mode C three
    mode_eq := MeasuredChoice.mode_value C three }

theorem source_bounded {F : CNFFormula} (C : Prepared F) (three : ThreeCore F)
    (B : Nat) (size : F.clauses.length+F.variableCount ≤ B) :
    Bounded (source C three) (B+4) (MeasuredChoice.partnerBound B)
      (MeasuredChoice.slotBound B) (6*B+16) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i s
    have h := MeasuredAccess.literal_cost C three i s
    change (MeasuredAccess.literal C three i s).cost ≤ B+4
    omega
  · exact MeasuredChoice.partner_cost C.toCutData B size
  · exact MeasuredChoice.slot_cost C three B size
  · exact MeasuredChoice.mode_cost C three B size

def transport {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    {S : Selection n c} (ops : Operations S) :
    Operations (NativeDimensionCache.transportSelection hn hc S) := by
  cases hn
  cases hc
  exact ops

theorem transport_bounded {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    {S : Selection n c} (ops : Operations S) (L O D M : Nat)
    (h : Bounded ops L O D M) :
    Bounded (transport hn hc ops) L O D M := by
  cases hn
  cases hc
  exact h

theorem transport_roundtrip {n c n' c' : Nat} (hn : n = n') (hc : c = c')
    (S : Selection n c) :
    NativeDimensionCache.transportSelection hn.symm hc.symm
      (NativeDimensionCache.transportSelection hn hc S) = S := by
  cases hn
  cases hc
  rfl


end PNP.Concrete.NativeNormalization.MeasuredOperations
