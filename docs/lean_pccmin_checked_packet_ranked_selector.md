# Checked Packet-backed rank-selector construction

M192 narrows the selector-stage input accepted by the M191 rank-ordered
PCCOracle. M191 allowed a caller to supply arbitrary selector rows and a
proof-bearing realizer. M192 instead requires one explicit
`TerminalPacketTypedRealizerTable` over every canonical handle of a supplied
finite grouped Packet family.

`TerminalPacketTypedRealizerTable.checkEveryClaim` executes the data-only
claim checker at every handle in `packetSelectorHandles`. Acceptance is
equivalent to validity of every claim. Only after that complete check does
`checkedOutcome` construct an M191 outcome:

- a gain blueprint must pass the existing occurrence-ledger, semantic, and
  exact gate-accounting validator before it yields `StrictEquivalentGain`;
- an HN claim retains an active bounded-rank hereditary blocker;
- a budget claim retains an active bounded-rank budget blocker; and
- a lower-seed claim retains a faithful selector at a strictly lower rank.

The caller no longer supplies `selectorsAt`. `selectorsAtRank` filters the
complete canonical handle list by equality with the table-owned `rankOf`, and
`mem_selectorsAtRank_iff` proves that membership is exactly the assigned-rank
equation. Consequently every canonical handle occurs in its assigned row.

`PCCMinCheckedPacketSelectorData.toRankedSelectorPlan` exposes those derived
rows and checked outcomes to M191. The total
`PCCMinCheckedPacketRankOrderedOracleBuilder` permits the Atom and Payload
carriers to depend on the current implementation, converts each checked plan
to the M191 builder, and reuses the M190 normalization composition plus M189
well-founded exact loop. The public endpoint is
`PNP.DirectWire.pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete`.

## Exact claim boundary

The grouped Packet family, finite rank assignment, claim table, HResolve,
BudgetResolve, normalizer, blocker meanings, and the implication from complete
typed silence to ZeroSlack remain explicit supplied inputs. The construction
does not derive these objects from an arbitrary terminal implementation.

The regression's total builder uses exhaustive reference minimization only as
a semantic fixture. It is not a polynomial PCCMin construction. M192 proves no
encoded-size enumeration or runtime bound, unconditional ZeroSlack,
deterministic SAT algorithm, or root theorem. It closes no fixed risk-weighted
checkpoint and no global gate.

## Verification

The focused checks are:

```text
lake build PNP.PCCMinCheckedPacketRankedSelector
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketRankedSelectorAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketRankedSelector.lean
node --test audits/lean-pccmin-checked-packet-ranked-selector0.test.mjs
```

The regression covers accepted data-only gain, HN, budget, and lower-seed
claims; a rejected malformed gain; exact row membership; a gain reached only
at a later rank; complete checked silence and its explicit ZeroSlack closure;
and total-loop composition. The fifteen-declaration focused axiom transcript
contains no project-specific axiom, `sorryAx`, or `Classical.choice`; it uses
only Lean's standard `propext` and `Quot.sound` foundations where required.
