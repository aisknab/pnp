# Residual terminal Packet selector-codec plan

## Legacy anchor

Pinned manuscript Sections 13--14 require Packet selectors to have an encoded
interface before a selector realizer can consume them. The preceding milestone
assigns every exact grouped-footprint payload selector a unique position in the
explicit grouped BN6 family, but deliberately stops before any bit encoding.

## Unbounded abstraction

Work over every arbitrary finite explicit grouped BN6 family and arbitrary atom
and payload types. Encode the canonical finite position itself, without fixing
the carrier size, selector count, or a sample family. Decode every bitstring
totally and fail closed on missing delimiters, trailing data, or out-of-range
positions.

## Exact theorem boundary

Define a canonical unary bitstring codec for the existing input-relative handle.
Prove exact round trip, encoding injectivity, canonical re-encoding of every
successful decode, and an exact length formula bounded by the explicit family's
grouped-footprint count. Prove every successfully decoded handle retains exact
payload-selector, carrier-containment, nontrivial-size, grouped-cell, and atom
evidence. Prove every payload selector has one unique accepted bitstring and
upgrade the pair, positive balanced-triple, and full-span Packet branches.

## Remaining downstream blockers

The bound is relative to the explicit grouped-family list. The milestone does
not bound that list by the encoded circuit size, prove polynomial enumeration or
runtime, encode atom or payload data, prove manuscript-level selector
faithfulness or compatibility, construct a selector realizer or route, derive or
group BN6 survivors from a terminal candidate, complete PkgC, ZeroSlack, or
PCCMin, put CNF-SAT in P, remove a project assumption, or prove `P = NP`.

## Required evidence

- Lean theorem module over arbitrary finite grouped families.
- Axiom audit with an exact public declaration list.
- Generic regression covering round trip, malformed-input rejection,
  canonicality, length, retained evidence, uniqueness, and every Packet branch.
- Hostile JavaScript audit rejecting fixed bounds, permissive trailing data,
  missing range checks, noncanonical decoding, weakened branch coverage, and
  overclaims.
- Synchronized theorem inventory, publication map, status payloads, report,
  documentation, and durable read-only workflow checks.
