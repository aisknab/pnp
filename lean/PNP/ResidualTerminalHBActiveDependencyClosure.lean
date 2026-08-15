/-
Copyright (c) 2026 PNP Labs.

Checked no-outcome activity closure for the supplied finite HN/BUD dependency
table.  The existing typed-realizer environment supplies the HN and budget
activity bits, and the existing total dependency table supplies every row.
The local checker requires every active node to name an active dependency in
its own row.  The table checker independently requires every such dependency
to descend the exact ten-coordinate terminal residual rank.

Well-founded induction then proves that no supplied HN or budget activity bit
can remain true.  Composition with the checked Packet typed-realizer contract
therefore eliminates the HN and budget bot branches, leaving only a verified
gain or a faithful strictly lower-rank selector.

The activity bits, dependency rows, rank mapping, selector family,
faithfulness predicate, and realizer claims remain explicit inputs.  The local
closure check does not derive blocker activity or dependency semantics from
terminal data, establish semantic dependency completeness, construct the
selector family, exclude gain or lower-seed branches, prove rank-complete
selector silence or the full HB negative closure, establish polynomial size
or runtime, prove unconditional ZeroSlack or PCCMin, put SAT in P, remove a
project assumption, or prove P = NP.
-/

import PNP.ResidualTerminalHBDependencyTableClosure

namespace PNP
namespace DirectWire

/-! ## Activity projection and local no-outcome closure -/

/-- The activity bit for either closed HB node, projected directly from the
    existing typed-realizer environment. -/
def TerminalPacketTypedRealizerEnvironment.hbActive
    {Selector : Type} {rankCount : Nat}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    TerminalPacketHBNode rankCount -> Bool
  | .hn rank => environment.hnActive rank
  | .budget rank => environment.budgetActive rank

/-- Exact local no-outcome premise: every supplied active node names an active
    dependency in its own total table row. -/
def TerminalPacketHBDependencyTable.ActiveDependencyClosed
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    Prop :=
  ∀ node, environment.hbActive node = true →
    ∃ dependency,
      table.Depends dependency node ∧
        environment.hbActive dependency = true

/-- Exhaustively check the local no-outcome premise for every HN and budget
    node.  No local-validity or silence field is accepted. -/
def TerminalPacketHBDependencyTable.checkActiveDependencyClosed
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    Bool :=
  (allTerminalPacketHBNodes rankCount).all (fun node =>
    !environment.hbActive node ||
      (table.dependencies node).any (fun dependency =>
        environment.hbActive dependency))

/-- The local Boolean scan recognizes exactly active-to-active dependency
    closure over every row in the total finite HB domain. -/
theorem TerminalPacketHBDependencyTable.checkActiveDependencyClosed_eq_true_iff
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    table.checkActiveDependencyClosed environment = true ↔
      table.ActiveDependencyClosed environment := by
  constructor
  · intro accepted node active
    have rowChecked :=
      (List.all_eq_true.mp accepted) node
        (mem_allTerminalPacketHBNodes node)
    have dependencyChecked :
        (table.dependencies node).any (fun dependency =>
          environment.hbActive dependency) = true := by
      simpa [active] using rowChecked
    obtain ⟨dependency, dependencyMember, dependencyActive⟩ :=
      List.any_eq_true.mp dependencyChecked
    exact ⟨dependency, dependencyMember, dependencyActive⟩
  · intro closed
    apply List.all_eq_true.mpr
    intro node _nodeMember
    cases active : environment.hbActive node with
    | false => simp
    | true =>
        obtain ⟨dependency, dependencyMember, dependencyActive⟩ :=
          closed node active
        have dependencyChecked :
            (table.dependencies node).any (fun candidate =>
              environment.hbActive candidate) = true :=
          List.any_eq_true.mpr
            ⟨dependency, dependencyMember, dependencyActive⟩
        simp [dependencyChecked]

/-! ## Combined exact-rank and local-closure checker -/

/-- Complete proposition enforced by the combined no-outcome HB checker. -/
def TerminalPacketHBDependencyTable.NoOutcomeActiveClosureValid
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    Prop :=
  table.Valid ∧ table.ActiveDependencyClosed environment

/-- Check both exact-rank descent for every total row and the local
    active-to-active dependency condition. -/
def TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    Bool :=
  table.check && table.checkActiveDependencyClosed environment

/-- Combined acceptance is exactly ranked-table validity plus the exhaustive
    local active-dependency proposition. -/
theorem TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure_eq_true_iff
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount) :
    table.checkNoOutcomeActiveClosure environment = true ↔
      table.NoOutcomeActiveClosureValid environment := by
  simp only [TerminalPacketHBDependencyTable.checkNoOutcomeActiveClosure,
    TerminalPacketHBDependencyTable.NoOutcomeActiveClosureValid,
    Bool.and_eq_true, table.check_eq_true_iff,
    table.checkActiveDependencyClosed_eq_true_iff]

/-! ## Well-founded active-chain contradiction -/

/-- If every active node requires a lower active dependency, exact-rank
    well-foundedness forces every supplied HN/BUD activity bit to be false. -/
theorem TerminalPacketHBDependencyTable.noActive_of_noOutcomeActiveClosure
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (accepted : table.checkNoOutcomeActiveClosure environment = true) :
    ∀ node, environment.hbActive node = false := by
  have valid :=
    (table.checkNoOutcomeActiveClosure_eq_true_iff environment).mp accepted
  have tableAccepted : table.check = true :=
    (table.check_eq_true_iff).mpr valid.1
  apply table.depends_induction tableAccepted
    (motive := fun node => environment.hbActive node = false)
  intro node dependencyInactive
  cases active : environment.hbActive node with
  | false => rfl
  | true =>
      obtain ⟨dependency, depends, dependencyActive⟩ :=
        valid.2 node active
      have inactive := dependencyInactive dependency depends
      rw [inactive] at dependencyActive
      contradiction

/-- Specialized HN consequence of checked no-outcome active closure. -/
theorem TerminalPacketHBDependencyTable.hnActive_eq_false
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (accepted : table.checkNoOutcomeActiveClosure environment = true)
    (rank : Fin rankCount) :
    environment.hnActive rank = false := by
  exact table.noActive_of_noOutcomeActiveClosure environment accepted (.hn rank)

/-- Specialized budget consequence of checked no-outcome active closure. -/
theorem TerminalPacketHBDependencyTable.budgetActive_eq_false
    {Selector : Type} {rankCount : Nat}
    (table : TerminalPacketHBDependencyTable rankCount)
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (accepted : table.checkNoOutcomeActiveClosure environment = true)
    (rank : Fin rankCount) :
    environment.budgetActive rank = false := by
  exact table.noActive_of_noOutcomeActiveClosure environment accepted
    (.budget rank)

/-! ## Composition with the checked Packet typed-realizer table -/

/-- Public meaning of a checked typed-realizer claim after HN/BUD activity is
    eliminated: either a verified strict gain or a faithful strictly
    lower-rank seed remains. -/
def TerminalPacketTypedRealizerClaim.HBActiveClosureSound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (environment : TerminalPacketTypedRealizerEnvironment Selector rankCount)
    (selector : Selector)
    (claim : TerminalPacketTypedRealizerClaim current Selector rankCount)
    (table : TerminalPacketHBDependencyTable rankCount) : Prop :=
  (∃ blueprint : TerminalPacketUnitChargeBlueprint current,
    claim = .gain blueprint ∧ blueprint.Valid ∧
      StrictEquivalentGain current blueprint.next) ∨
  (∃ lower : Selector,
    claim = .bot (.lowerSeed lower) ∧
      environment.rankOf lower < environment.rankOf selector ∧
      environment.faithful lower = true ∧
      (table.rankTuple (environment.rankOf lower)).LexLT
        (table.rankTuple (environment.rankOf selector)))

/-- Checked typed-realizer evidence composes with the no-outcome activity
    closure: HN and budget evidence contradict the derived all-node silence. -/
theorem TerminalPacketTypedRealizerEvidence.hbActiveClosureSound
    {Selector : Type} {rankCount inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {environment : TerminalPacketTypedRealizerEnvironment Selector rankCount}
    {selector : Selector}
    {claim : TerminalPacketTypedRealizerClaim current Selector rankCount}
    (evidence : TerminalPacketTypedRealizerEvidence
      current environment selector claim)
    (table : TerminalPacketHBDependencyTable rankCount)
    (closureAccepted :
      table.checkNoOutcomeActiveClosure environment = true) :
    claim.HBActiveClosureSound environment selector table := by
  unfold TerminalPacketTypedRealizerClaim.HBActiveClosureSound
  cases evidence with
  | gain blueprint claimEquation valid =>
      exact Or.inl ⟨blueprint, claimEquation, valid,
        valid.chargeSurplusRealization.strictEquivalentGain⟩
  | hn rank _claimEquation _rankBound active =>
      have inactive := table.hnActive_eq_false environment closureAccepted rank
      rw [inactive] at active
      contradiction
  | budget rank _claimEquation _rankBound active =>
      have inactive :=
        table.budgetActive_eq_false environment closureAccepted rank
      rw [inactive] at active
      contradiction
  | lowerSeed lower claimEquation rankStrict faithful =>
      have closureValid :=
        (table.checkNoOutcomeActiveClosure_eq_true_iff environment).mp
          closureAccepted
      have exactStrict :
          (table.rankTuple (environment.rankOf lower)).LexLT
            (table.rankTuple (environment.rankOf selector)) :=
        closureValid.1.1 (environment.rankOf lower)
          (environment.rankOf selector) rankStrict
      exact Or.inr
        ⟨lower, claimEquation, rankStrict, faithful, exactStrict⟩

/-- Named finite Packet interface: every faithful canonical handle in an
    accepted table yields either a checked strict gain or a faithful exact-rank
    lower seed, while every supplied HN/BUD activity bit is false. -/
theorem terminalBN6_packet_typed_realizer_hb_active_dependency_closure_contract
    {Atom Payload : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom Payload}
    (realizerTable : TerminalPacketTypedRealizerTable current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (realizerAccepted : realizerTable.checkFaithful = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true)
    (handle : family.PacketSelectorHandle)
    (faithful : realizerTable.environment.faithful handle = true) :
    (realizerTable.claim handle).HBActiveClosureSound
        realizerTable.environment handle dependencyTable ∧
      dependencyTable.NoOutcomeActiveClosureValid realizerTable.environment ∧
      (∀ node, realizerTable.environment.hbActive node = false) ∧
      WellFounded dependencyTable.Depends := by
  have evidence := realizerTable.checkFaithful_handle
    realizerAccepted handle faithful
  exact ⟨evidence.hbActiveClosureSound dependencyTable closureAccepted,
    (dependencyTable.checkNoOutcomeActiveClosure_eq_true_iff
      realizerTable.environment).mp closureAccepted,
    dependencyTable.noActive_of_noOutcomeActiveClosure
      realizerTable.environment closureAccepted,
    dependencyTable.depends_wellFounded
      ((dependencyTable.check_eq_true_iff).mpr
        ((dependencyTable.checkNoOutcomeActiveClosure_eq_true_iff
          realizerTable.environment).mp closureAccepted).1)⟩

end DirectWire
end PNP
