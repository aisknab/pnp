# M182 same-family Selector/HB, Packet, and BCEL ZeroSlack coherence

## Evidence-led selection

The pinned manuscript's Sections 14--16 use one BN6 family, one selector and
realizer environment, and one HB dependency system from Packet extraction
through the no-lower contradiction. M179 made the report-facing Selector/HB
boundary proof-bearing, M180 made the Packet/budget no-lower boundary
proof-bearing, and M181 tied the BCEL contradiction to the exact M180
certificate. The current `ZeroSlackCertificate`, however, can still store an
independent M179 certificate beside M180. Those two certificates may describe
different families, tables, environments, or dependency systems even though
the M180 checker already recomputes selector silence and HB closure internally.

M182 removes that detached duplicate. It derives the Selector/HB sidecar from
the exact computed table and dependency data accepted by M180, and makes both
`ZeroSlackCertificate` and `PCCOracleCertificate` expose that derived value
rather than accept a second caller-supplied certificate.

## Legacy anchor and dependency edge

- Legacy anchor: report Sections 14--16, especially the single-family path
  from BN6 Packet payloads through Selector/Realizer and HB negative closure to
  the final no-lower contradiction.
- Closed edge: accepted same-candidate Packet/budget checker -> its exact
  computed selector-silence and HB-closure rows -> the report-facing
  Selector/HB sidecar -> the same-family BCEL contradiction.
- Unbounded abstraction: arbitrary natural dimensions and rank counts, and an
  arbitrary finite supplied grouped BN6 family, typed-realizer table, HB
  dependency table, and residual-rank maps.

## Exact theorem target

For every accepted `PacketBudgetNoLowerZeroSlackSidecarCertificate`, construct
`selectorHB` from its exact family, its table after the existing executable
payload-faithfulness completion, and its exact dependency table. Prove the
named endpoint
`PNP.zeroslack_packet_selector_hb_bcel_coherent_checked_complete` for every
`ZeroSlackCertificate`: the derived Selector/HB boundary has no faithful
canonical selector, retains valid no-outcome HB closure and no active HB node,
the exact M180 family has no positive Packet, and the dependent M181 boundary
rules out constant activation on that same family.

Neither report-facing certificate may retain an independent
`selectorHBClosure` field. The accessor must be definitionally derived from
M180, so family/table/dependency coherence is structural rather than a caller
equality or digest assertion.

## Claim boundary and downstream blockers

All terminal, budget, grouped-family, payload, realizer, activity, dependency,
and rank data retained by M180 remain supplied. M182 does not derive that data
from a terminal candidate, construct a faithful selector or BCELReady, derive
constant activation from positive residual slack, complete the manuscript
no-lower ledger, establish unconditional ZeroSlack, prove PCCMin exactness or
polynomial runtime, put SAT in P, remove a project assumption, or prove
`P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every new public declaration;
- a generic regression proving the derived family/table/dependency identities,
  Selector/HB consequences, Packet exclusion, BCEL exclusion, and named
  endpoint;
- hostile mutations rejecting a retained independent sidecar, equality or
  digest-only coherence, caller success flags, duplicated family/table data,
  fixed dimensions, assumptions, and widened claims;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback. On the
configured remote builder, compile the changed dependency and root once, run
the axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction. Do not
rerun a targeted command already covered by an unchanged broader suite unless
diagnosing a failure. PNPLabs imports the exact verified core artifacts and
must not invoke Lean, Lake, Elan, or the core proof suite.
