# Residual terminal Packet charge-surplus plan

## Legacy anchor

Pinned manuscript Section 14, `R-ChargeSurplus`, requires a faithful Packet
selector realizer to inject every replacement charge into a support charge of
the same weight while leaving at least one positive support charge unmatched.
The current finite Packet milestones enumerate, decode, materialize, and scan
payloads, but do not formalize this arithmetic step from a realizer witness to
a strict equivalent gain.

## Unbounded abstraction

Work over arbitrary support- and replacement-charge types, arbitrary finite
charge ledgers, arbitrary natural-valued weight functions, and arbitrary
direct-wire circuit arities and gate counts. Represent the occurrence-level
injection by an exact list of matched pairs: permutation identities require
every replacement occurrence to appear exactly once and partition every
support occurrence into a matched occurrence or an unmatched remainder.
Duplicated charge values therefore cannot reuse one support occurrence.

## Exact theorem boundary

If every matched pair preserves weight and the unmatched remainder contains a
positive-weight support charge, Lean derives that replacement total weight is
strictly smaller than support total weight. If those totals account exactly for
the replacement and current NAND gate counts, and semantic equivalence is
proved independently, Lean constructs a genuine `StrictEquivalentGain` and
strict reference-residual descent. Neither the total-weight inequality nor the
strict gain is accepted as an input field.

## Remaining downstream blockers

The finite ledgers, exact pairing, gate accounting, semantic equivalence,
grouped BN6 family, and candidate implementations remain explicit inputs. The
milestone does not construct a replacement from a Packet blueprint, derive the
charge ledger from terminal data, prove selector faithfulness or compatibility,
produce `BotHN`, `BotBUD`, or lower-rank `BotSeed`, close the HB blocker graph,
establish encoded-size or polynomial-runtime bounds, or prove unconditional
ZeroSlack or PCCMin. It does not put CNF-SAT in P, remove a project assumption,
or prove `P = NP`.

## Required evidence

- A Lean theorem module over arbitrary finite charge ledgers and circuit
  arities.
- A source-derived axiom audit and generic regression covering exact matching,
  strict total weight, strict equivalent gain, residual descent, duplicate-use
  rejection, and the necessity of an unmatched positive charge.
- A hostile JavaScript audit rejecting missing multiplicity accounting,
  weakened weight preservation, absent positive surplus, assumed inequalities
  or gains, fixed bounds, forbidden shortcuts, and unconditional overclaims.
- Synchronized theorem inventory, publication map, status payloads, report,
  documentation, and durable read-only workflow checks.
