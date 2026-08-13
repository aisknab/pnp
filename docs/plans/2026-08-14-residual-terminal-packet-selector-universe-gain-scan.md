# Residual terminal Packet selector-universe gain-scan plan

## Legacy anchor

Pinned manuscript Sections 14 and 15 require the rank-ordered selector oracle to
run every selector before recording selector silence. The preceding milestone
checks every candidate payload in one decoded source cell, but its no-gain result
is local to that one selector.

## Unbounded abstraction

Work over every arbitrary finite explicit grouped BN6 family, every atom type,
and every direct-wire input/output arity. Enumerate every canonical input-relative
selector handle in that family, run the existing proof-bearing source-cell scan
at each handle, and stop only on a genuine source-atom strict equivalent gain.
Do not fix a carrier cardinality, selector count, cell count, candidate-list
length, or circuit arity.

## Exact theorem boundary

Define a total scan whose only outcomes are:

- a canonical selector handle and an original atom in its exact source cell,
  together with a kernel-checked `StrictEquivalentGain`; or
- proof that no original candidate payload in any canonical selector source
  cell of the explicit family is a strict equivalent gain.

Prove that every handle is covered exactly by the finite enumeration, every gain
has a canonical accepted code and strictly decreases residual slack, and the
pair, positive balanced-triple, and full-span Packet alternatives remain intact
while sharing the same exhaustive family scan.

## Remaining downstream blockers

The grouped BN6 family and candidate implementations remain explicit inputs.
Family-wide no-gain is silence only for that supplied input-relative selector
universe. It is not a manuscript `BotHN`, `BotBUD`, or lower-rank `BotSeed`, does
not establish selector faithfulness or compatibility, and does not imply global
minimality or ZeroSlack. The milestone does not construct replacement
candidates, connect payload mass to charge surplus, derive or group survivors
from terminal data, bound the family by encoded circuit size, prove polynomial
enumeration or runtime, complete PkgC, ZeroSlack, or PCCMin, put CNF-SAT in P,
remove a project assumption, or prove `P = NP`.

## Required evidence

- Lean theorem module over arbitrary finite grouped families and circuit arities.
- Axiom audit whose expected declaration count is derived from the source.
- Generic regression covering exhaustive handle membership, both universe
  outcomes, exact source membership, canonical coding, strict descent, and every
  Packet branch.
- Hostile JavaScript audit rejecting skipped handles, invented atoms, proof-free
  gains, globalized family silence, fixed bounds, missing branch coverage, and
  overclaims.
- Synchronized theorem inventory, publication map, status payloads, report,
  documentation, and durable read-only workflow checks.
