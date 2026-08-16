/-
Copyright (c) 2026 PNP Labs.

Executable reconstruction of the selector-silence induction named in the
pinned manuscript's Section 15.  The checker accepts only when the existing
faithful-row validator accepts and every canonical realizer claim is a typed
bottom constructor.  Checked HB active-dependency closure removes HN and
budget bottoms, while strong induction removes faithful strictly lower-rank
seeds.  Thus no faithful selector remains.

Unlike the preceding conditional closure, this result does not assume global
semantic exclusion of every strict equivalent gain or a supplied gain-coverage
certificate.  A gain row is rejected by the exhaustive selector-silence check
itself.  The grouped family, rank and faithfulness tables, realizer claims,
blocker activity, dependency rows, and finite-to-exact rank map remain explicit
data inputs.  This module does not construct them from terminal data, establish
selector faithfulness or compatibility, prove blocker semantics or semantic
dependency completeness, establish the full unconditional HB negative closure,
prove ZeroSlack or PCCMin, establish encoded-size or polynomial-runtime bounds,
put SAT in P, remove a project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalHBActiveDependencyClosure

namespace PNP
namespace DirectWire

/-! ## Exact data-only bottom recognition -/

/-- A realizer claim is syntactically one of the three typed bottom forms. -/
def TerminalPacketTypedRealizerClaim.isBotBool
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) : Bool :=
  match claim with
  | .gain _blueprint => false
  | .bot _reason => true

/-- Bottom recognition accepts exactly a typed bottom constructor and rejects
    every gain constructor, whether or not its blueprint is valid. -/
theorem TerminalPacketTypedRealizerClaim.isBotBool_eq_true_iff
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount) :
    claim.isBotBool = true ↔
      ∃ reason : TerminalPacketTypedRealizerBot Selector rankCount,
        claim = .bot reason := by
  cases claim with
  | gain blueprint =>
      constructor
      · intro checked
        cases checked
      · rintro ⟨reason, equation⟩
        cases equation
  | bot reason =>
      constructor
      · intro _checked
        exact ⟨reason, rfl⟩
      · intro _exists
        rfl

/-! ## Exhaustive canonical selector-silence check -/

/-- Validate every faithful realizer row and require every canonical handle's
    recorded claim to be a typed bottom rather than a gain. -/
def TerminalPacketTypedRealizerTable.checkSelectorSilent
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  table.checkFaithful && family.packetSelectorHandles.all fun handle =>
    (table.claim handle).isBotBool

/-- Selector-silence acceptance is exactly the existing faithful-row validity
    check together with an exact typed-bottom equation for every canonical
    handle. -/
theorem TerminalPacketTypedRealizerTable.checkSelectorSilent_eq_true_iff
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkSelectorSilent = true ↔
      table.checkFaithful = true ∧
        ∀ handle : family.PacketSelectorHandle,
          ∃ reason : TerminalPacketTypedRealizerBot
              family.PacketSelectorHandle rankCount,
            table.claim handle = .bot reason := by
  constructor
  · intro accepted
    have checks : table.checkFaithful = true ∧
        family.packetSelectorHandles.all (fun handle =>
          (table.claim handle).isBotBool) = true := by
      simpa only [TerminalPacketTypedRealizerTable.checkSelectorSilent,
        Bool.and_eq_true] using accepted
    refine ⟨checks.1, ?_⟩
    intro handle
    have rowChecked := (List.all_eq_true.mp checks.2) handle
      (family.mem_packetSelectorHandles handle)
    exact ((table.claim handle).isBotBool_eq_true_iff).1 rowChecked
  · rintro ⟨faithfulAccepted, allBots⟩
    have botsAccepted : family.packetSelectorHandles.all (fun handle =>
        (table.claim handle).isBotBool) = true := by
      apply List.all_eq_true.mpr
      intro handle handleMember
      exact ((table.claim handle).isBotBool_eq_true_iff).2
        (allBots handle)
    simpa only [TerminalPacketTypedRealizerTable.checkSelectorSilent,
      Bool.and_eq_true] using And.intro faithfulAccepted botsAccepted

/-- Accepted selector silence retains the existing exhaustive faithful-row
    validation. -/
theorem TerminalPacketTypedRealizerTable.checkFaithful_of_selectorSilent
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkSelectorSilent = true) :
    table.checkFaithful = true :=
  (table.checkSelectorSilent_eq_true_iff.mp accepted).1

/-- Accepted selector silence gives an exact bottom equation for every
    canonical handle, not merely for a caller-selected sublist. -/
theorem TerminalPacketTypedRealizerTable.claim_eq_bot_of_selectorSilent
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (accepted : table.checkSelectorSilent = true)
    (handle : family.PacketSelectorHandle) :
    ∃ reason : TerminalPacketTypedRealizerBot
        family.PacketSelectorHandle rankCount,
      table.claim handle = .bot reason :=
  (table.checkSelectorSilent_eq_true_iff.mp accepted).2 handle

/-! ## Manuscript selector-silence induction -/

/-- Exhaustive checked bottom rows, checked HB activity closure, and strict
    lower-seed ranks imply that every canonical selector is nonfaithful.  No
    global semantic no-gain premise occurs in this theorem. -/
theorem TerminalPacketTypedRealizerTable.noFaithful_of_selectorSilent
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false := by
  have realizerAccepted : realizerTable.checkFaithful = true :=
    realizerTable.checkFaithful_of_selectorSilent silenceAccepted
  have everyClaimBot : ∀ handle : family.PacketSelectorHandle,
      ∃ reason : TerminalPacketTypedRealizerBot
          family.PacketSelectorHandle rankCount,
        realizerTable.claim handle = .bot reason :=
    (realizerTable.checkSelectorSilent_eq_true_iff.mp silenceAccepted).2
  intro handle
  have noFaithfulAtRank :
      ∀ rankValue : Nat,
        ∀ candidate : family.PacketSelectorHandle,
          (realizerTable.environment.rankOf candidate).val = rankValue →
            realizerTable.environment.faithful candidate = false := by
    intro rankValue
    refine Nat.strongRecOn rankValue ?_
    intro rankValue lowerRanks candidate candidateRank
    cases faithful : realizerTable.environment.faithful candidate with
    | false => rfl
    | true =>
        have outcome :=
          (realizerTable.checkFaithful_handle
            realizerAccepted candidate faithful).hbActiveClosureSound
              dependencyTable closureAccepted
        rcases outcome with gain | lowerSeed
        · obtain ⟨blueprint, claimEquation, _valid, _verified⟩ := gain
          obtain ⟨reason, botEquation⟩ := everyClaimBot candidate
          rw [botEquation] at claimEquation
          cases claimEquation
        · obtain ⟨lower, _claimEquation, rankStrict, lowerFaithful,
              _exactStrict⟩ := lowerSeed
          have lowerRank :
              (realizerTable.environment.rankOf lower).val < rankValue := by
            rw [← candidateRank]
            exact rankStrict
          have lowerInactive :
              realizerTable.environment.faithful lower = false :=
            lowerRanks _ lowerRank lower rfl
          rw [lowerInactive] at lowerFaithful
          contradiction
  exact noFaithfulAtRank _ handle rfl

/-- Explicit rank-indexed form of the Section 15 conclusion. -/
theorem TerminalPacketTypedRealizerTable.noFaithfulAtOrBelow_of_selectorSilent
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (rank : Fin rankCount) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.rankOf handle ≤ rank →
        realizerTable.environment.faithful handle = false := by
  intro handle _rankBound
  exact realizerTable.noFaithful_of_selectorSilent dependencyTable
    silenceAccepted closureAccepted handle

/-! ## Canonical Packet interface -/

/-- Named finite Packet interface: executable all-row selector silence and
    checked HB activity closure jointly yield rank-complete selector silence,
    exact all-row bottom equations, HN/BUD silence, and well-foundedness. -/
theorem terminalBN6_packet_typed_realizer_hb_selector_silence_induction_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) :
    (∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      (∀ handle : family.PacketSelectorHandle,
        ∃ reason : TerminalPacketTypedRealizerBot
            family.PacketSelectorHandle rankCount,
          realizerTable.claim handle = .bot reason) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends := by
  have closureValid :=
    (dependencyTable.checkNoOutcomeActiveClosure_eq_true_iff
      realizerTable.environment).mp closureAccepted
  have tableAccepted : dependencyTable.check = true :=
    (dependencyTable.check_eq_true_iff).mpr closureValid.1
  exact
    ⟨realizerTable.noFaithful_of_selectorSilent dependencyTable
        silenceAccepted closureAccepted,
      (realizerTable.checkSelectorSilent_eq_true_iff.mp silenceAccepted).2,
      closureValid,
      dependencyTable.noActive_of_noOutcomeActiveClosure
        realizerTable.environment closureAccepted,
      dependencyTable.depends_wellFounded tableAccepted⟩

end DirectWire
end PNP
