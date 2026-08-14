# Lean Packet typed-realizer contract

`lean/PNP/ResidualTerminalPacketTypedRealizerContract.lean` reconstructs a
finite, input-relative interface for the pinned manuscript's Section 14
obligations `realizerBotTyped` and
`realizerBotOnlyHNBUDBlockedOrLowerRank`.

The result is deliberately conditional on explicit executable tables. It does
not construct a selector, blocker, replacement, or rank system from a terminal
candidate.

## Data-only inputs

`TerminalPacketTypedRealizerEnvironment Selector rankCount` contains four
functions:

- `rankOf`, assigning each selector a canonical `Fin rankCount` index;
- `faithful`, an executable Boolean predicate on selectors;
- `hnActive`, an executable hereditary-blocker activity table; and
- `budgetActive`, an executable budget-blocker activity table.

The finite indices provide an exact order for this supplied table. They are not
claimed to be the manuscript's full tuple-valued packet ranks.

`TerminalPacketTypedRealizerClaim` is data only. Its gain constructor contains
one `TerminalPacketUnitChargeBlueprint`; its bot constructor contains exactly
one of:

- `hn rank`;
- `budget rank`; or
- `lowerSeed selector`.

No constructor stores a validity proof, semantic proof, gain proof, activity
proof, faithfulness proof, or rank inequality.

## Exact checks

The gain branch delegates to the existing unit-charge blueprint checker. That
checker verifies exact gate-occurrence multiplicity, a nonempty unmatched
current-gate remainder, and semantic equivalence before Lean derives strict
charge surplus and `StrictEquivalentGain`.

The bot checker accepts:

- `hn rank` only when `rank ≤ rankOf current` and `hnActive rank = true`;
- `budget rank` only when `rank ≤ rankOf current` and
  `budgetActive rank = true`; and
- `lowerSeed lower` only when `rankOf lower < rankOf current` and
  `faithful lower = true`.

The two `check_eq_true_iff` theorems prove that these Boolean checks recognize
their propositions exactly. `evidenceOfCheck` reconstructs proof-bearing
evidence only after a data row has passed. The evidence retains an equality to
the exact checked claim, so it cannot silently substitute a different gain or
bot.

`TerminalPacketTypedRealizerEvidence.sound` exposes one of four results:

1. the exact blueprint is valid and gives a genuine charge-derived strict
   equivalent gain;
2. the exact HN rank is active and no greater than the current rank;
3. the exact budget rank is active and no greater than the current rank; or
4. the exact lower selector is faithful at a strictly smaller rank.

## Finite faithful-table coverage

`checkTerminalPacketFaithfulRealizerClaims` checks an arbitrary finite selector
list. A nonfaithful row lies outside this conditional obligation. Every row
whose supplied faithfulness predicate is true must pass the complete
gain-or-typed-bot checker.

`checkTerminalPacketFaithfulRealizerClaims_sound` proves the four-way result for
every faithful member of an accepted list. The specialization
`terminalBN6_packet_typed_realizer_contract` instantiates that result over
`family.packetSelectorHandles`. The existing `mem_packetSelectorHandles`
theorem ensures that every canonical handle in the supplied grouped BN6 family
is covered.

## Axiom audit

The focused transcript audits 20 public declarations:

- 10 have empty axiom closure;
- 5 depend only on `propext`; and
- 5 depend only on `propext` and `Quot.sound`.

No audited declaration reaches `Classical.choice`, `sorryAx`, or a
project-specific axiom.

Run the focused checks with:

```text
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketTypedRealizerContractAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketTypedRealizerContract.lean
node --test audits/lean-residual-terminal-packet-typed-realizer-contract0.test.mjs
```

## Boundary

The family, ranks, faithfulness predicate, HN and budget activity tables, and
realizer claims remain supplied inputs. An invalid faithful row is rejected; it
is not reinterpreted as a bot. This milestone does not prove that supplied HN
or budget entries have the manuscript's full semantics, establish the HB
blocker graph or its acyclicity, construct blueprints, derive the grouped family
from terminal data, prove selector faithfulness or compatibility, establish
encoded-circuit-size or polynomial-runtime bounds, or derive global selector
silence.

Accordingly this is not unconditional `ZeroSlack`, polynomial PCCMin,
`CNFSAT ∈ P`, or `P = NP`, and it removes no project assumption.
