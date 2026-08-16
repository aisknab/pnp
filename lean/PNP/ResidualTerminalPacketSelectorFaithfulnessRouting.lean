/-
Copyright (c) 2026 PNP Labs.

Executable reconstruction of the first-failure Packet selector-faithfulness
boundary named by the pinned manuscript's Pair packet seed,
Balanced-triple seed, Full-span spine seed, and patched BCEL seed theorems.
Every canonical handle selects its existing canonical positive source payload.
The payload is faithful only when every named data-only field check succeeds
and its finite rank tag equals the handle's supplied canonical rank.  Otherwise
the classifier exposes the first typed route in a fixed fail-closed order.

An exhaustive binding check prevents the existing HB environment from
silently supplying a different faithfulness table.  Consequently a positive
BN6 Packet with route-clear payloads supplies a faithful canonical handle,
which contradicts accepted executable HB selector silence.

The grouped BN6 family, payload field Booleans, rank tags, realizer claims,
blocker activity, dependency rows, and finite-to-exact rank map remain explicit
inputs.  This module does not derive those data from a terminal candidate or
prove their external manuscript semantics.  It does not construct positive
residual slack, SaturatePositive, BCELReady, the grouped family, or the
no-lower ledger; prove unconditional ZeroSlack or PCCMin; establish encoded
size or polynomial runtime; put SAT in P; remove a project assumption; or
prove P = NP.
-/

import PNP.ResidualTerminalHBExecutableSelectorSilenceInduction

namespace PNP
namespace DirectWire

/-! ## Closed typed first-failure surface -/

/-- Exact public route names checked before one Packet payload may be treated
    as faithful.  The constructor order below is also the executable priority
    order of `firstRoute`. -/
inductive TerminalPacketSelectorFaithfulnessRoute where
  | colour
  | frontier
  | charge
  | obligation
  | activation
  | direction
  | budget
  | rank
  | exactRoute
  | descent
  deriving Repr, DecidableEq

/-- Data-only Packet payload checks.  There is deliberately no caller-supplied
    `faithful` field: faithfulness is the conjunction computed below. -/
structure TerminalPacketSelectorFaithfulnessPayload (rankCount : Nat) where
  colourChecked : Bool
  frontierChecked : Bool
  chargeChecked : Bool
  obligationChecked : Bool
  activationChecked : Bool
  directionChecked : Bool
  budgetChecked : Bool
  rankTag : Fin rankCount
  exactRouteClear : Bool
  strictDescentClear : Bool
  deriving Repr, DecidableEq

/-- Exact proposition recognized for one payload at one canonical handle rank. -/
def TerminalPacketSelectorFaithfulnessPayload.Valid
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) : Prop :=
  payload.colourChecked = true ∧
    payload.frontierChecked = true ∧
    payload.chargeChecked = true ∧
    payload.obligationChecked = true ∧
    payload.activationChecked = true ∧
    payload.directionChecked = true ∧
    payload.budgetChecked = true ∧
    payload.rankTag = expectedRank ∧
    payload.exactRouteClear = true ∧
    payload.strictDescentClear = true

/-- Fail-closed data-only faithfulness checker. -/
def TerminalPacketSelectorFaithfulnessPayload.check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) : Bool :=
  payload.colourChecked &&
    payload.frontierChecked &&
    payload.chargeChecked &&
    payload.obligationChecked &&
    payload.activationChecked &&
    payload.directionChecked &&
    payload.budgetChecked &&
    decide (payload.rankTag = expectedRank) &&
    payload.exactRouteClear &&
    payload.strictDescentClear

/-- The checker accepts exactly all named field checks plus the exact finite
    rank equality. -/
theorem TerminalPacketSelectorFaithfulnessPayload.check_eq_true_iff
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    payload.check expectedRank = true ↔ payload.Valid expectedRank := by
  simp [TerminalPacketSelectorFaithfulnessPayload.check,
    TerminalPacketSelectorFaithfulnessPayload.Valid, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

/-- Return the first failed field in the manuscript order, or `none` only
    after traversing the complete payload boundary. -/
def TerminalPacketSelectorFaithfulnessPayload.firstRoute
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  if payload.colourChecked = true then
    if payload.frontierChecked = true then
      if payload.chargeChecked = true then
        if payload.obligationChecked = true then
          if payload.activationChecked = true then
            if payload.directionChecked = true then
              if payload.budgetChecked = true then
                if payload.rankTag = expectedRank then
                  if payload.exactRouteClear = true then
                    if payload.strictDescentClear = true then
                      none
                    else some .descent
                  else some .exactRoute
                else some .rank
              else some .budget
            else some .direction
          else some .activation
        else some .obligation
      else some .charge
    else some .frontier
  else some .colour

/-- An accepted payload has no typed failure route. -/
theorem TerminalPacketSelectorFaithfulnessPayload.firstRoute_eq_none_of_check
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (accepted : payload.check expectedRank = true) :
    payload.firstRoute expectedRank = none := by
  rcases (payload.check_eq_true_iff expectedRank).mp accepted with
    ⟨colour, frontier, charge, obligation, activation, direction, budget,
      rank, exactRoute, descent⟩
  simp [TerminalPacketSelectorFaithfulnessPayload.firstRoute, colour,
    frontier, charge, obligation, activation, direction, budget, rank,
    exactRoute, descent]

/-- A reported typed route is incompatible with payload acceptance. -/
theorem TerminalPacketSelectorFaithfulnessPayload.check_eq_false_of_firstRoute
    {rankCount : Nat}
    (payload : TerminalPacketSelectorFaithfulnessPayload rankCount)
    (expectedRank : Fin rankCount)
    (route : TerminalPacketSelectorFaithfulnessRoute)
    (found : payload.firstRoute expectedRank = some route) :
    payload.check expectedRank = false := by
  cases accepted : payload.check expectedRank with
  | false => rfl
  | true =>
      have noRoute := payload.firstRoute_eq_none_of_check expectedRank accepted
      rw [noRoute] at found
      cases found

/-! ## Canonical payload computation and exhaustive route clearance -/

/-- Compute faithfulness from the canonical first positive source payload of
    one exact input-relative handle. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFaithful
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) : Bool :=
  (family.packetSelectorPayloadAtom handle).payload.check (rankOf handle)

/-- Expose the exact first route for the same canonical payload and rank. -/
def TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    Option TerminalPacketSelectorFaithfulnessRoute :=
  (family.packetSelectorPayloadAtom handle).payload.firstRoute (rankOf handle)

/-- Computed handle faithfulness is exactly validity of the canonical source
    payload at the supplied handle rank. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFaithful_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle) :
    family.packetSelectorPayloadFaithful rankOf handle = true ↔
      (family.packetSelectorPayloadAtom handle).payload.Valid
        (rankOf handle) :=
  (family.packetSelectorPayloadAtom handle).payload.check_eq_true_iff
    (rankOf handle)

/-- Accepted computed faithfulness has no first route. -/
theorem TerminalBN6GroupedFamily.packetSelectorPayloadFirstRoute_eq_none
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount)
    (handle : family.PacketSelectorHandle)
    (accepted : family.packetSelectorPayloadFaithful rankOf handle = true) :
    family.packetSelectorPayloadFirstRoute rankOf handle = none :=
  (family.packetSelectorPayloadAtom handle).payload
    |>.firstRoute_eq_none_of_check (rankOf handle) accepted

/-- Exhaustively require route-clear computed payload faithfulness for every
    canonical handle in the arbitrary finite grouped family. -/
def TerminalBN6GroupedFamily.checkPacketSelectorRoutesClear
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    family.packetSelectorPayloadFaithful rankOf handle

/-- Route-clear acceptance covers every canonical handle exactly. -/
theorem TerminalBN6GroupedFamily.checkPacketSelectorRoutesClear_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    {rankCount : Nat}
    (family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount))
    (rankOf : family.PacketSelectorHandle -> Fin rankCount) :
    family.checkPacketSelectorRoutesClear rankOf = true ↔
      ∀ handle : family.PacketSelectorHandle,
        family.packetSelectorPayloadFaithful rankOf handle = true := by
  constructor
  · intro accepted handle
    exact (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
  · intro everyHandle
    apply List.all_eq_true.mpr
    intro handle _handleMember
    exact everyHandle handle

/-! ## Exact binding to the existing HB table -/

/-- Check every existing HB faithfulness bit against the computed canonical
    payload result. -/
def TerminalPacketTypedRealizerTable.checkPacketSelectorFaithfulnessBinding
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) : Bool :=
  family.packetSelectorHandles.all fun handle =>
    decide (table.environment.faithful handle =
      family.packetSelectorPayloadFaithful table.environment.rankOf handle)

/-- Binding acceptance is exact equality on every canonical handle. -/
theorem TerminalPacketTypedRealizerTable.checkPacketSelectorFaithfulnessBinding_eq_true_iff
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (table : TerminalPacketTypedRealizerTable current family rankCount) :
    table.checkPacketSelectorFaithfulnessBinding = true ↔
      ∀ handle : family.PacketSelectorHandle,
        table.environment.faithful handle =
          family.packetSelectorPayloadFaithful
            table.environment.rankOf handle := by
  constructor
  · intro accepted handle
    have rowChecked := (List.all_eq_true.mp accepted) handle
      (family.mem_packetSelectorHandles handle)
    simpa only [decide_eq_true_eq] using rowChecked
  · intro everyHandle
    apply List.all_eq_true.mpr
    intro handle _handleMember
    simpa only [decide_eq_true_eq] using everyHandle handle

/-! ## Positive Packet witness and HB contradiction -/

/-- Every exact positive Packet branch contains at least one canonical handle.
    The balanced-triple branch deterministically selects the first two carrier
    atoms; the existing branch theorem supplies that pair's handle. -/
theorem TerminalPacketSelectorHandleConclusion.existsHandle
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalPacketSelectorHandleConclusion family) :
    Nonempty family.PacketSelectorHandle := by
  cases conclusion with
  | pair _carrierLength _fullPositive selector =>
      obtain ⟨handle, _decode⟩ := selector
      exact ⟨handle⟩
  | fullSpan _carrierLength _fullPositive selector =>
      obtain ⟨handle, _decode⟩ := selector
      exact ⟨handle⟩
  | balancedTriple carrierLength _pairMass _pairPositive _everyPair selectors =>
      let footprint := family.carrier.take 2
      have footprintSublist : footprint.Sublist family.carrier := by
        exact List.take_sublist 2 family.carrier
      have footprintLength : footprint.length = 2 := by
        simp [footprint, List.length_take, carrierLength]
      obtain ⟨handle, _decode⟩ :=
        selectors footprint footprintSublist footprintLength
      exact ⟨handle⟩

/-- Every BN6 Packet conclusion therefore contains a canonical handle through
    the existing seed, universe, and handle construction chain. -/
theorem TerminalBN6PacketConclusion.existsPacketSelectorHandle
    {Atom Payload : Type} [DecidableEq Atom]
    {family : TerminalBN6GroupedFamily Atom Payload}
    (conclusion : TerminalBN6PacketConclusion family) :
    Nonempty family.PacketSelectorHandle :=
  conclusion.selectorHandles.existsHandle

/-- A positive Packet, exhaustive route clearance, and exact HB-table binding
    produce a genuinely computed faithful canonical handle. -/
theorem TerminalBN6PacketConclusion.existsFaithfulHandle_of_routesClear
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (table : TerminalPacketTypedRealizerTable current family rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      table.environment.rankOf = true)
    (bindingAccepted :
      table.checkPacketSelectorFaithfulnessBinding = true) :
    ∃ handle : family.PacketSelectorHandle,
      table.environment.faithful handle = true := by
  let ⟨handle⟩ := conclusion.existsPacketSelectorHandle
  have computedFaithful :=
    (family.checkPacketSelectorRoutesClear_eq_true_iff
      table.environment.rankOf).mp routesClear handle
  have binding :=
    (table.checkPacketSelectorFaithfulnessBinding_eq_true_iff).mp
      bindingAccepted handle
  exact ⟨handle, binding.trans computedFaithful⟩

/-- Named Packet-to-HB contradiction: a route-clear positive Packet cannot
    coexist with executable all-row selector silence and accepted HB
    active-dependency closure when the HB faithfulness table is bound to the
    computed canonical payload checks. -/
theorem terminalBN6_packet_selector_faithfulness_hb_contradiction
    {Atom : Type} [DecidableEq Atom]
    {inputs outputs rankCount : Nat}
    {current : Implementation inputs outputs}
    {family : TerminalBN6GroupedFamily Atom
      (TerminalPacketSelectorFaithfulnessPayload rankCount)}
    (conclusion : TerminalBN6PacketConclusion family)
    (realizerTable : TerminalPacketTypedRealizerTable
      current family rankCount)
    (dependencyTable : TerminalPacketHBDependencyTable rankCount)
    (routesClear : family.checkPacketSelectorRoutesClear
      realizerTable.environment.rankOf = true)
    (bindingAccepted :
      realizerTable.checkPacketSelectorFaithfulnessBinding = true)
    (silenceAccepted : realizerTable.checkSelectorSilent = true)
    (closureAccepted : dependencyTable.checkNoOutcomeActiveClosure
      realizerTable.environment = true) : False := by
  obtain ⟨handle, faithful⟩ :=
    conclusion.existsFaithfulHandle_of_routesClear realizerTable
      routesClear bindingAccepted
  have notFaithful :=
    realizerTable.noFaithful_of_selectorSilent dependencyTable
      silenceAccepted closureAccepted handle
  rw [notFaithful] at faithful
  contradiction

end DirectWire
end PNP
