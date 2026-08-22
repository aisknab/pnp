# M181 proof-bearing BCEL/Packet no-lower contradiction sidecar

## Evidence-led selection

The pinned manuscript's Section 16 closes the positive-slack branch by
constructing a BCEL-ready constant-cut nucleus, extracting a positive BN6
Packet, and contradicting the rank-complete no-lower and selector/HB ledgers.
M180 now provides the checked same-family Packet/budget ledger and proves that
its accepted branch contains no positive Packet, but `ZeroSlack.lean` still
stores the BCEL contradiction as five uninterpreted strings.

M181 replaces that opaque bundle with one dependent proof-bearing boundary.
It reuses the exact M180 certificate, checks from its family data that the BN6
carrier contains at least two anchors, invokes the existing arbitrary-finite
constant-cut hypergraph theorem, and derives that the same family cannot
satisfy BCEL constant activation.

## Legacy anchor and dependency edge

- Legacy anchor: report Section 16, especially the step from a BCEL-ready
  positive nucleus through BN6 packet extraction to the no-lower
  contradiction.
- Closed edge: same-family BCEL constant activation -> checked positive BN6
  Packet construction -> accepted Packet/budget no-lower exclusion.
- Unbounded abstraction: arbitrary natural dimensions and rank counts, and an
  arbitrary finite supplied grouped BN6 family whose carrier passes the exact
  lower-bound check.

## Exact theorem target

For every `BCELContradictionCertificate packetBudgetNoLower`, prove
`PNP.bcel_packet_no_lower_zeroslack_sidecar_checked_complete`: the family has
at least two anchors, the linked checked no-lower certificate excludes a
positive Packet conclusion, and the family cannot satisfy
`TerminalBN6GroupedFamily.ConstantActivation`.

The certificate must not store strings, a caller success Boolean, a supplied
Packet exclusion, a supplied contradiction, or an independent copy of the
M180 evidence. Its only field is the exact decidable carrier-bound equation,
and its type binds it to the existing M180 certificate.

## Claim boundary and downstream blockers

The grouped family, candidate, budget and saturation data, Packet payloads,
rank and realizer tables, activity environment, dependency rows, and rank maps
remain supplied through M180. M181 does not derive a grouped family or constant
activation from a terminal candidate or positive residual slack, construct
BCELReady, prove the complete manuscript no-lower ledger, establish
unconditional ZeroSlack, prove PCCMin exactness or polynomial runtime, put SAT
in P, remove a project assumption, or prove `P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every public declaration;
- a generic regression retaining the checked carrier premise, Packet
  exclusion, constant-activation exclusion, dependent ZeroSlack binding, and
  named endpoint;
- hostile mutations for strings, caller flags, supplied conclusions, detached
  M180 evidence, omitted BN6 construction, fixed dimensions, assumptions, and
  claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback. On the
configured remote builder, compile the new dependency and root once, run its
axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction. Do not
rerun a targeted command already covered by an unchanged broader suite unless
diagnosing a failure. PNPLabs imports the exact verified core artifacts and
must not invoke Lean, Lake, Elan, or the core proof suite.
