# Exact reconstruction

The revised TeX payload is derived from the unmodified canonical report at documentation base commit `f52e04b9963ea2f10cfccafbf705b9e316ed25a6`.

Required base-file hashes:

```text
d5559b4d0ca59b9c08d180cd802652159da75e58291aa293e539776207865b21  canonical_proof_report.tex
e134c92d74eb4fdbe4e86814d8c0a86fa49768f2036cb98b5fc9f8da906c44c2  canonical_proof_report.pdf
```

Reconstruction steps:

1. Check out the base commit and verify the two base-file hashes above.
2. Apply `canonical_proof_report.tex.patch` to `canonical_proof_report.tex` to obtain the revised TeX payload.
3. Verify the revised TeX hash using `SHA256SUMS`.
4. Build or receive the revised PDF payload under a controlled publication build and verify it against the PDF hash recorded in `SHA256SUMS`.
5. Verify the transport file using `PATCH_SHA256SUMS`.

`SHA256SUMS` binds both revised payload hashes. `PATCH_SHA256SUMS` binds the TeX transport patch supplied in this directory. The PDF hash is a publication-coordinate identity hash; the sealed `7072f8d` PDF remains the base artefact and is not overwritten by this revision.