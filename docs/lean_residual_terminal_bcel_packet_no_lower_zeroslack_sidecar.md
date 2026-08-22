# Proof-bearing BCEL/Packet no-lower contradiction sidecar

`PNP.ResidualTerminalBCELPacketNoLowerZeroSlackSidecar` replaces the five
string fields formerly stored in `BCELContradictionCertificate` with a checked
boundary tied to the exact M180 Packet/budget no-lower certificate.

The certificate stores one equation:

```lean
decide (2 ≤ packetBudgetNoLower.family.carrier.length) = true
```

That equation is reflected to the domain premise of
`terminalBN6_hypergraph_packet`. If the supplied grouped family also satisfied
`TerminalBN6GroupedFamily.ConstantActivation`, the existing arbitrary-finite
BN6 theorem would construct a positive `TerminalBN6PacketConclusion`. The
linked M180 checker proves that no such conclusion exists for the same family.
Lean therefore derives `¬ packetBudgetNoLower.family.ConstantActivation`.

The named endpoint is
`PNP.bcel_packet_no_lower_zeroslack_sidecar_checked_complete`. It returns the
carrier lower bound, positive-Packet exclusion, and constant-activation
exclusion. The dedicated axiom transcript covers every public declaration and
must contain only the repository's allowed Lean standard axioms.

This is a finite, same-family contradiction boundary. The grouped family and
all data inherited from M180 remain supplied. The theorem does not derive the
family or BCEL constant activation from positive residual slack, construct
BCELReady from terminal data, complete the no-lower ledger, prove unconditional
ZeroSlack or polynomial PCCMin, remove a project assumption, put SAT in P, or
prove `P = NP`.
