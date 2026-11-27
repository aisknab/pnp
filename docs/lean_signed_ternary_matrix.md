# Strict CNFSAT as a signed ternary matrix problem

For every input bit string, the original CNF predicate is true exactly when the constructed square matrix has a signed solution. The target does not know the original formula: it parses its **own** input, obtains a matrix `A` over the field of three elements, and asks for a **single** vector `x` such that every entry of both `x` and `A x` is nonzero. Here “signed” means +1 or −1 (the two nonzero field elements).

In [the public entry module](../lean/PNP/SignedTernary/Encoding.lean), the kernel-checked interface is:

```lean
PNP.SignedTernary.Encoding.matrixSAT_encodeCNFMatrix_iff (raw : BitString) :
  MatrixSAT (encodeCNFMatrix raw) ↔ CNFSAT raw
```

There is no well-formedness premise. Malformed source words map to negative instances, an empty conjunction maps to a positive one, and literals outside the declared variable range are false under the source semantics. Malformed **target** encodings are rejected. In particular, a nonzero row considered on its own need not have the same witness as another row. The [regression examples](../lean-regression/PNPSignedTernaryMatrix.lean) include a matrix where this difference changes the answer.

The construction proceeds in three verifiable steps:

1. The [CNF semantics](../lean/PNP/SignedTernary/CNF/Source.lean) turn literal evaluation and clause satisfaction into nonzero tests of homogeneous ternary forms. Auxiliary sites are constructed in the forward proof; they are not supplied as correctness evidence.
2. The [network](../lean/PNP/SignedTernary/Network/Signed.lean) turns those tests into sign constraints on one square linear map. [Linearity and basis recovery](../lean/PNP/SignedTernary/Matrix/Basis.lean) prove that ordinary multiplication by the stated row matrix agrees with that map on every field vector. Evaluating basis vectors alone would not establish this for a nonlinear map.
3. The [codec](../lean/PNP/SignedTernary/Codec.lean) writes a positive dimension in unary followed by exactly two bits per ternary entry, in row order. The trits 0, +1, and −1 use `00`, `01`, and `10` respectively. The tag `11`, a truncated row, zero dimension, and trailing bits are invalid. `canonical_unpack` recovers the matrix actually constructed.

For a source of length `r` the matrix dimension is at most `13*r + 30`; its encoding has exactly `N + 1 + 2*N*N` **bits**, with no byte padding. This bounds **output length**. It is not an execution-time bound for constructing the matrix in the project's finite-machine model, an algorithm for finding a signed solution, or a proof that CNFSAT is in P. The existing binary linear-system solver addresses a different predicate: these ternary nonzero-coordinate constraints cannot simply be dropped.

This representation does not activate the final theorem or earn a weighted proof checkpoint. Current [formal artefact coverage and risk-weighted proof status](../status/PROOF_PROGRESS.json) remain separately governed by the core ledger.
