# Lean canonical Packet faithfulness-table construction

This milestone closes one supplied-data compatibility gap at the existing
Packet-to-HB boundary. The previous checker computed faithfulness from the
canonical positive source payload behind each handle, but an independently
supplied typed-realizer table could still contain a different faithfulness
function. Composition therefore required a separate exhaustive binding
premise.

`ResidualTerminalPacketSelectorFaithfulnessTable` constructs the table used by
the downstream selector-silence checker. For every arbitrary finite grouped
BN6 family and finite rank carrier, it replaces only the free faithfulness
function with

```text
family.packetSelectorPayloadFaithful table.environment.rankOf
```

and preserves the rank assignment, HN activity, budget activity, and every
realizer claim exactly. The exhaustive binding checker then accepts by
construction. A route-clear positive Packet supplies a faithful handle in this
canonicalized table, while accepted executable HB selector silence proves that
same handle nonfaithful. The resulting contradiction no longer accepts an
independent binding hypothesis.

## Manuscript anchor and theorem boundary

The pinned manuscript anchors are the Section 13 Pair packet seed,
Balanced-triple seed, Full-span spine seed, and patched BCEL seed, composed with
the Section 14 Selector realization contract and Section 15 selector-silence
induction. The unbounded abstraction formalized here is an arbitrary finite
grouped BN6 family and arbitrary finite rank count; no fixed carrier prefix or
fixed rank bound is used.

The named endpoint is:

```text
PNP.DirectWire.terminalBN6_packet_computed_faithfulness_hb_contradiction
```

Its theorem interface retains route clearance, selector-silence acceptance,
and HB active-dependency closure, but contains no caller-supplied
faithfulness-binding premise.

## Kernel-checked surface

The source is
[`lean/PNP/ResidualTerminalPacketSelectorFaithfulnessTable.lean`](../lean/PNP/ResidualTerminalPacketSelectorFaithfulnessTable.lean).
It provides:

- `withComputedPacketSelectorFaithfulness`, the canonical table constructor;
- exact preservation theorems for rank, HN activity, budget activity, and
  realizer claims;
- an exact equation identifying every rebuilt faithfulness entry with the
  canonical source-payload computation;
- `withComputedPacketSelectorFaithfulness_binding`, which proves exhaustive
  binding acceptance without a premise;
- `existsFaithfulHandle_of_computedTable`, the binding-free positive Packet
  witness; and
- the named binding-free Packet-to-HB contradiction.

The regression and axiom audit are:

```text
lean-regression/PNPResidualTerminalPacketSelectorFaithfulnessTable.lean
lean-audit/PNPResidualTerminalPacketSelectorFaithfulnessTableAxiomAudit.lean
audits/lean-residual-terminal-packet-selector-faithfulness-table0.test.mjs
```

## Claim boundary

This construction removes the independently supplied Boolean faithfulness
function and the separate binding premise from this finite composition. It does
not prove the manuscript's full external selector compatibility claim. The
grouped family, ten payload-field Booleans, finite rank tags and rank map,
route-clear acceptance, realizer claims, HN/BUD activity, dependency rows, and
finite-to-exact rank embedding remain explicit inputs. Their semantics and
derivation from a terminal candidate remain open.

Accordingly, this milestone does not derive positive residual slack,
`SaturatePositive`, `BCELReady`, complete route silence, unconditional HB
negative closure, global `ZeroSlack`, polynomial PCCMin, encoded-size or
polynomial-runtime bounds, SAT in P, or `P = NP`.
