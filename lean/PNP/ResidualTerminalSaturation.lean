/-
Copyright (c) 2026 PNP Labs.

Finite terminal support saturation for the direct-wire residual calculus.  A
primitive-record universe contains the actual gate, boundary, interface, and
computed profile coordinates of one finite carrier shape.  An explicit
Boolean dependency system labels every required closure edge by the rule kind
named in the pinned manuscript.  Saturation is the reflexive transitive
closure generated from a raw support.

This reconstructs the manuscript's Section 3 saturation-closure theorem: the
generated support is extensive, closed, least, monotone, and idempotent.  The
dependency relation is explicit data at this boundary.  No claim is made that
it has already been extracted from an arbitrary program, and no completion,
frontier, proper-support, square-legitimacy, projection-compatibility,
SaturatePositive, route, BCELReady, ZeroSlack, PCCMin, or polynomial-runtime
result is asserted.
-/

import PNP.ResidualTerminalProjectionTransfer

namespace PNP
namespace DirectWire

/-- The finite primitive records available to a terminal support: physical
    NAND gates, incoming boundary coordinates, outgoing interface coordinates,
    and the computed profile coordinates introduced by the mode firewall. -/
inductive TerminalPrimitiveRecord
    (inputs gates outputs profileWidth : Nat) where
  | gate (index : Fin gates)
  | boundary (index : Fin inputs)
  | interface (index : Fin outputs)
  | profile (index : Fin profileWidth)
  deriving Repr, DecidableEq

/-- Canonical enumeration of the complete finite primitive-record universe. -/
def allTerminalPrimitiveRecords
    (inputs gates outputs profileWidth : Nat) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (allFin gates).map (fun index =>
      (TerminalPrimitiveRecord.gate index :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)) ++
  (allFin inputs).map (fun index =>
      (TerminalPrimitiveRecord.boundary index :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)) ++
  (allFin outputs).map (fun index =>
      (TerminalPrimitiveRecord.interface index :
        TerminalPrimitiveRecord inputs gates outputs profileWidth)) ++
  (allFin profileWidth).map (fun index =>
      (TerminalPrimitiveRecord.profile index :
        TerminalPrimitiveRecord inputs gates outputs profileWidth))

/-- Every primitive record occurs in the canonical finite enumeration. -/
theorem mem_allTerminalPrimitiveRecords
    {inputs gates outputs profileWidth : Nat}
    (record : TerminalPrimitiveRecord inputs gates outputs profileWidth) :
    record ∈ allTerminalPrimitiveRecords inputs gates outputs profileWidth := by
  cases record with
  | gate index =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact mem_map_of_mem TerminalPrimitiveRecord.gate (mem_allFin index)
  | boundary index =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact mem_map_of_mem TerminalPrimitiveRecord.boundary (mem_allFin index)
  | interface index =>
      apply List.mem_append_left
      apply List.mem_append_right
      exact mem_map_of_mem TerminalPrimitiveRecord.interface (mem_allFin index)
  | profile index =>
      apply List.mem_append_right
      exact mem_map_of_mem TerminalPrimitiveRecord.profile (mem_allFin index)

/-- The ten closure mechanisms named by the manuscript's terminal support
    calculus.  A dependency is oriented from an included record to a record it
    requires. -/
inductive TerminalSaturationRuleKind where
  | gateSource
  | interfaceConsumer
  | origin
  | kernel
  | obligation
  | prefixTail
  | budget
  | saturation
  | direction
  | charge
  deriving Repr, DecidableEq

/-- Explicit finite governance for terminal saturation.  `requires kind from
    to = true` means that inclusion of `from` requires inclusion of `to` by the
    named closure rule.  The profile system is the same computed observer used
    by the full/quotient terminal boundary; it is data, not a soundness
    certificate for the dependency relation. -/
structure TerminalSaturationSystem
    (inputs gates outputs profileWidth : Nat) where
  profileSystem : TerminalProfileSystem inputs outputs profileWidth
  requires : TerminalSaturationRuleKind →
    TerminalPrimitiveRecord inputs gates outputs profileWidth →
    TerminalPrimitiveRecord inputs gates outputs profileWidth → Bool

/-- A raw support is a subset of an intrinsically finite primitive universe. -/
abbrev TerminalRawSupport
    (inputs gates outputs profileWidth : Nat) :=
  TerminalPrimitiveRecord inputs gates outputs profileWidth → Prop

namespace TerminalRawSupport

/-- Pointwise inclusion of raw supports. -/
def Subset
    {inputs gates outputs profileWidth : Nat}
    (left right : TerminalRawSupport inputs gates outputs profileWidth) : Prop :=
  ∀ record, left record → right record

/-- A support is closed when it contains every record required by any record
    it already contains. -/
def Closed
    {inputs gates outputs profileWidth : Nat}
    (support : TerminalRawSupport inputs gates outputs profileWidth)
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) : Prop :=
  ∀ kind dependent required,
    support dependent → system.requires kind dependent required = true →
      support required

end TerminalRawSupport

/-- Membership generated from a seed support by zero or more explicitly
    governed saturation edges. -/
inductive TerminalSaturationGenerated
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    TerminalPrimitiveRecord inputs gates outputs profileWidth → Prop where
  | seed {record} (member : seed record) :
      TerminalSaturationGenerated system seed record
  | close {kind dependent required}
      (present : TerminalSaturationGenerated system seed dependent)
      (edge : system.requires kind dependent required = true) :
      TerminalSaturationGenerated system seed required

/-- Saturate a raw support by taking the reflexive transitive closure of every
    rule-tagged dependency edge. -/
def terminalSaturate
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    TerminalRawSupport inputs gates outputs profileWidth :=
  fun record => TerminalSaturationGenerated system seed record

/-- Saturation contains every record in the seed support. -/
theorem terminalSaturate_extensive
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    seed.Subset (terminalSaturate system seed) := by
  intro record member
  exact TerminalSaturationGenerated.seed member

/-- The generated saturation is closed under every governed dependency. -/
theorem terminalSaturate_closed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    (terminalSaturate system seed).Closed system := by
  intro kind dependent required present edge
  exact TerminalSaturationGenerated.close present edge

/-- Saturation is the least closed support containing the seed. -/
theorem terminalSaturate_least
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed support : TerminalRawSupport inputs gates outputs profileWidth)
    (seedWithin : seed.Subset support)
    (supportClosed : support.Closed system) :
    (terminalSaturate system seed).Subset support := by
  intro record generated
  induction generated with
  | seed member => exact seedWithin _ member
  | close present edge ih => exact supportClosed _ _ _ ih edge

/-- Enlarging a seed cannot shrink its saturated closure. -/
theorem terminalSaturate_monotone
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (left right : TerminalRawSupport inputs gates outputs profileWidth)
    (within : left.Subset right) :
    (terminalSaturate system left).Subset (terminalSaturate system right) := by
  intro record generated
  induction generated with
  | seed member =>
      exact TerminalSaturationGenerated.seed (within _ member)
  | close present edge ih =>
      exact TerminalSaturationGenerated.close ih edge

/-- Repeating saturation adds nothing: the closure operator is idempotent. -/
theorem terminalSaturate_idempotent
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    terminalSaturate system (terminalSaturate system seed) =
      terminalSaturate system seed := by
  apply funext
  intro record
  apply propext
  constructor
  · exact terminalSaturate_least system
      (terminalSaturate system seed) (terminalSaturate system seed)
      (fun _ member => member) (terminalSaturate_closed system seed) record
  · exact terminalSaturate_extensive system (terminalSaturate system seed) record

/-- A raw support is a saturation fixed point exactly when it is dependency
    closed. -/
theorem terminalSaturate_fixed_iff_closed
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (support : TerminalRawSupport inputs gates outputs profileWidth) :
    terminalSaturate system support = support ↔ support.Closed system := by
  constructor
  · intro fixed
    intro kind dependent required present edge
    have dependentGenerated : terminalSaturate system support dependent := by
      rw [fixed]
      exact present
    have requiredGenerated : terminalSaturate system support required :=
      terminalSaturate_closed system support kind dependent required
        dependentGenerated edge
    rw [fixed] at requiredGenerated
    exact requiredGenerated
  · intro closed
    apply funext
    intro record
    apply propext
    constructor
    · exact terminalSaturate_least system support support
        (fun _ member => member) closed record
    · exact terminalSaturate_extensive system support record

/-- A support packaged with the exact saturation fixed-point law. -/
structure TerminalSaturatedSupport
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth) where
  records : TerminalRawSupport inputs gates outputs profileWidth
  fixed : terminalSaturate system records = records

/-- Canonically package the saturation of any seed as a saturated support. -/
def saturateSupport
    {inputs gates outputs profileWidth : Nat}
    (system : TerminalSaturationSystem inputs gates outputs profileWidth)
    (seed : TerminalRawSupport inputs gates outputs profileWidth) :
    TerminalSaturatedSupport system :=
  { records := terminalSaturate system seed
    fixed := terminalSaturate_idempotent system seed }

end DirectWire
end PNP
