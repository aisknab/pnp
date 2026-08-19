# Checked Packet descent no-lower binding

`PNP.ResidualTerminalPacketDescentNoLowerBinding` adds one executable local
row toward the pinned manuscript's no-lower ledger. It is deliberately a
bounded claim: it connects the fully computed Packet first-route classifier
to the already checked positive-Packet boundary, but it does not claim the
complete ZeroSlack argument.

For an arbitrary finite grouped BN6 family, arbitrary finite selector-rank
carrier, authoritative rank map, and supplied before/after residual ranks,
`TerminalBN6GroupedFamily.PacketDescentNoLower` says that no canonical handle
has `.descent` as its fully computed first failed route.
`checkPacketDescentNoLower` scans the exact canonical handle list and decides
that proposition at every handle. The theorem
`checkPacketDescentNoLower_eq_true_iff` proves exact Boolean reflection in both
directions; there is no caller-supplied success flag or fixed family bound.

The preceding Packet milestone already proves that the following explicit
checked premises force some canonical handle's first route to be `.descent`:

- a positive `TerminalBN6PacketConclusion`;
- the semantic/HN activity-binding checker;
- the budget/HB activity-binding checker;
- executable selector silence; and
- the supplied well-founded HB no-outcome closure checker.

`checkPacketDescentNoLower_eq_false_of_selectorSilence` consumes exactly those
premises and the prior existential witness. If the exhaustive no-lower checker
were true, reflection would exclude `.descent` at that witness, contradicting
the computed route. The named endpoint
`terminalBN6_packet_descent_no_lower_rejected` therefore returns checker
rejection. A companion theorem exposes the same result as `False` when an
accepted local row is also supplied.

This proves one local incompatibility: the checked positive-Packet boundary
cannot coexist with an accepted Packet-descent no-lower row for the same
family, table, and ranks. It does not construct any of those inputs from
terminal data. It does not build the manuscript's complete no-lower ledger,
cover HResolve, BudgetResolve, normalization, named descent routes,
saturation, or replay, derive unconditional HB closure, or prove the remaining
ZeroSlack obligations. It does not establish PCCMin, encoded-size or
polynomial-runtime bounds, SAT in P, remove a project axiom, or prove P = NP.

## Review surfaces

- Source: `lean/PNP/ResidualTerminalPacketDescentNoLowerBinding.lean`
- Axiom transcript:
  `lean-audit/PNPResidualTerminalPacketDescentNoLowerBindingAxiomAudit.lean`
- Executable regression:
  `lean-regression/PNPResidualTerminalPacketDescentNoLowerBinding.lean`
- Hostile audit:
  `audits/lean-residual-terminal-packet-descent-no-lower-binding0.test.mjs`

The compiled axiom transcript must contain only the repository's approved
Lean standard allowlist (`propext` and `Quot.sound` where required), with no
`Classical.choice`, `sorryAx`, or project-specific axiom.
