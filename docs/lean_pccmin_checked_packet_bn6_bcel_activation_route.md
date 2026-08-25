# Same-candidate BCEL activation-route classifier

M195 removes M194's opaque positive-slack-to-constant-activation callback from
the new theorem surface. It binds a supplied grouped BN6 Packet family directly
to the checked finite BCEL-ready nucleus for the same candidate and saturation
model. No independent carrier map or bijection is accepted.

The total finite classifier compares, in order:

1. the Packet carrier with the computed BCEL nucleus carrier;
2. the Packet cut value with the computed BCEL projection defect; and
3. every canonical nonempty proper Packet cut's activation weight with that
   same defect.

A failed comparison returns a proof-bearing carrier mismatch, cut-value
mismatch, or the first proper-cut activation mismatch. If every comparison
passes, the coherent branch derives the exact constant-activation premise used
by M194 and identifies the activation value with the BCEL projection excess.
Under complete checked selector silence, the existing Packet/HB contradiction
then derives conditional ZeroSlack. The public endpoint is
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_activation_route_or_zeroslack_checked_complete`.

## Exact claim boundary

The terminal finite SaturatePositive problem, its positive premise, the checked
BCEL-ready certificate, grouped Packet family, payloads, claim table, rank map,
route-clear equation, dependency table, and checked HB closure remain supplied.
HResolve, BudgetResolve, the normalizer, and encoded-size bounds also remain
open. The mismatch outcomes are typed diagnostics; M195 does not yet turn them
into strict gains or prove that they decrease the complete global rank.

The classifier enumerates the finite powerset of the supplied carrier, so M195
does not establish polynomial runtime. It is not manuscript-wide
`SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`, complete executable
polynomial PCCMin, deterministic CNFSAT in P, the eligible root theorem, or a
proof that P equals NP. No fixed risk-weighted checkpoint or global gate closes.
The risk-weighted proof-completion estimate remains 35 percent with a 20 to 40
percent uncertainty range; formal artefact coverage becomes 171 of 173 current
scoped rows.

## Verification

The focused checks are:

```text
lake build PNP.PCCMinCheckedPacketBN6BCELActivationRoute
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELActivationRouteAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELActivationRoute.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-activation-route0.test.mjs
```

The fifteen-declaration axiom transcript must contain no project-specific
axiom, `sorryAx`, or `Classical.choice`. The regression covers all three mismatch
routes, total classifier exhaustiveness, coherent carrier size, derived constant
activation, the projection-excess identity, the M194 adapter, and conditional
ZeroSlack. The hostile audit rejects a supplied coherence callback, erased
routes, hidden choice or exhaustive-minimum shortcuts, fixed carriers, and
unearned unconditional or polynomial claims.
