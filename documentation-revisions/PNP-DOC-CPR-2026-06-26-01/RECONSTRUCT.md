# Exact reconstruction

The revised payload is derived from the unmodified canonical report at documentation base commit `f52e04b9963ea2f10cfccafbf705b9e316ed25a6`.

Required base-file hashes:

```text
d5559b4d0ca59b9c08d180cd802652159da75e58291aa293e539776207865b21  canonical_proof_report.tex
e134c92d74eb4fdbe4e86814d8c0a86fa49768f2036cb98b5fc9f8da906c44c2  canonical_proof_report.pdf
```

Reconstruction steps:

1. Check out the base commit and verify the two base-file hashes above.
2. Apply `canonical_proof_report.tex.patch` to `canonical_proof_report.tex` to obtain the revised TeX payload.
3. Concatenate `canonical_proof_report.pdf.zstpatch.b64.part*`, decode the base64 stream, and use the resulting zstd patch with the base PDF as the patch source to obtain the revised PDF payload.
4. In this revision directory, run `sha256sum -c SHA256SUMS` and `sha256sum -c PATCH_SHA256SUMS`.

The PDF delta is an exact binary patch, not a source-level approximation. Successful verification produces the payload hashes recorded in `SHA256SUMS`.