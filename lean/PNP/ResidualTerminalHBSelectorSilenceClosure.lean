/-
Copyright (c) 2026 PNP Labs.

Rank-complete selector silence for the supplied finite Packet typed-realizer
interface.  The preceding checked HB active-dependency closure removes every
HN and budget bot.  If every strict equivalent gain from the current
implementation is also excluded, each faithful selector could therefore name
only a faithful selector at a strictly lower finite rank.  Strong induction on
that rank proves that no faithful canonical selector remains.

The global no-gain proposition is an explicit proof-bearing premise.  A
specialization derives it from the existing explicit Packet gain-coverage
certificate and source-cell no-gain evidence.  The grouped family, rank and
faithfulness tables, realizer claims, blocker activity, dependency rows, and
finite-to-exact rank map remain supplied inputs.  This module does not derive
gain exclusion from ordinary family-local silence, establish selector
faithfulness or compatibility, construct sidecars from terminal data, prove
blocker semantics or semantic dependency completeness, establish the
unconditional HB negative closure, prove ZeroSlack or PCCMin, establish
encoded-size or polynomial-runtime bounds, put SAT in P, remove a project
assumption, or prove P = NP.
-/

import PNP.ResidualTerminalHBActiveDependencyClosure
import PNP.ResidualTerminalPacketSelectorGainCoverage

namespace PNP
namespace DirectWire

/-! ## Strong finite-rank selector-silence induction -/

/-- Once genuine gains and active HN/BUD bots are excluded, a faithful
    selector would require a faithful selector at strictly lower finite rank.
    Strong induction therefore eliminates every faithful canonical handle. -/
theorem TerminalPacketTypedRealizerTable.noFaithful_of_noStrictEquivalentGain
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false := by
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
        · obtain ⟨blueprint, _claimEquation, _valid, verified⟩ := gain
          exact False.elim (noGain blueprint.next verified)
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

/-- The existing explicit gain-coverage certificate upgrades exact no-gain in
    every canonical source cell to the global premise needed by the selector
    rank induction. -/
theorem TerminalPacketTypedRealizerTable.noFaithful_of_gainCoverageNoGain
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (sourceNoGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
        ¬StrictEquivalentGain current atom.payload) :
    ∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false :=
  realizerTable.noFaithful_of_noStrictEquivalentGain dependencyTable
    realizerAccepted closureAccepted
      (coverage.noStrictEquivalentGain sourceNoGain)

/-! ## Canonical Packet interface -/

/-- Named finite Packet interface: explicit semantic gain exclusion, checked
    typed-realizer rows, and checked HB activity closure jointly yield
    all-handle selector silence, all-node HN/BUD silence, and the retained
    exact-rank dependency facts. -/
theorem terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain current next) :
    (∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends := by
  have closureValid :=
    (dependencyTable.checkNoOutcomeActiveClosure_eq_true_iff
      realizerTable.environment).mp closureAccepted
  have tableAccepted : dependencyTable.check = true :=
    (dependencyTable.check_eq_true_iff).mpr closureValid.1
  exact ⟨realizerTable.noFaithful_of_noStrictEquivalentGain dependencyTable
      realizerAccepted closureAccepted noGain,
    closureValid,
    dependencyTable.noActive_of_noOutcomeActiveClosure
      realizerTable.environment closureAccepted,
    dependencyTable.depends_wellFounded tableAccepted⟩

/-- Coverage-specialized canonical interface.  The coverage certificate and
    exhaustive source-cell no-gain evidence remain explicit premises. -/
theorem terminalBN6_packet_typed_realizer_hb_selector_silence_gain_coverage_contract
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (Implementation inputs outputs)}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (coverage : TerminalPacketSelectorGainCoverage family current)
    (sourceNoGain : ∀ handle : family.PacketSelectorHandle,
      ∀ atom, atom ∈ (family.packetSelectorCell handle).atoms →
        ¬StrictEquivalentGain current atom.payload) :
    (∀ handle : family.PacketSelectorHandle,
      realizerTable.environment.faithful handle = false) ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends :=
  terminalBN6_packet_typed_realizer_hb_selector_silence_closure_contract
    realizerTable dependencyTable realizerAccepted closureAccepted
      (coverage.noStrictEquivalentGain sourceNoGain)

end DirectWire
end PNP
