import PNP.ResidualTerminalPacketChargeSurplus

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-! A concrete occurrence ledger has two weight-preserving matches and one
    unmatched positive support charge. -/

def terminalPacketChargeSurplusExample :
    TerminalPacketChargeSurplus [1, 2, 3] [1, 2]
      (fun charge : Nat => charge) (fun charge : Nat => charge) where
  pairing := [(1, 1), (2, 2)]
  unmatched := [3]
  supportExact := by simp
  replacementExact := by simp
  weightPreserved := by
    intro entry member
    simp at member
    rcases member with rfl | rfl <;> rfl
  positiveUnmatched := ⟨3, by simp, by decide⟩

example : [1, 2].length < [1, 2, 3].length := by
  exact terminalPacketChargeSurplusExample
    |>.replacementLength_lt_supportLength

example :
    ([1, 2].map (fun charge : Nat => charge)).sum <
      ([1, 2, 3].map (fun charge : Nat => charge)).sum := by
  exact terminalPacketChargeSurplusExample
    |>.replacementWeight_lt_supportWeight

/-! Exact occurrence accounting rejects both a missing unmatched charge and
    attempted duplicate use of one support occurrence. -/

theorem terminalPacketChargeSurplus_requires_unmatchedOccurrence :
    ¬Nonempty (TerminalPacketChargeSurplus [1] [1]
      (fun charge : Nat => charge) (fun charge : Nat => charge)) := by
  rintro ⟨surplus⟩
  have strict := surplus.replacementLength_lt_supportLength
  simp at strict

theorem terminalPacketChargeSurplus_rejects_duplicateSupportReuse :
    ¬Nonempty (TerminalPacketChargeSurplus [1] [1, 1]
      (fun charge : Nat => charge) (fun charge : Nat => charge)) := by
  rintro ⟨surplus⟩
  have strict := surplus.replacementLength_lt_supportLength
  simp at strict

/-! The weighted ledger composes with exact gate accounting and separately
    proved semantics, without accepting a strict inequality or gain premise. -/

variable {SupportCharge ReplacementCharge : Type}
variable {inputs outputs : Nat}
variable {current next : Implementation inputs outputs}
variable {support : List SupportCharge}
variable {replacement : List ReplacementCharge}
variable {supportWeight : SupportCharge -> Nat}
variable {replacementWeight : ReplacementCharge -> Nat}

example (realization : TerminalPacketChargeSurplusRealization current next
    support replacement supportWeight replacementWeight) :
    StrictEquivalentGain current next :=
  realization.strictEquivalentGain

example (realization : TerminalPacketChargeSurplusRealization current next
    support replacement supportWeight replacementWeight) :
    residualSlack next < residualSlack current :=
  realization.strictResidualDescent

end DirectWire
end PNP
