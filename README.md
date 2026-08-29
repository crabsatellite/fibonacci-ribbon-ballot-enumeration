# Ballot-Admissible Fibonacci Ribbon Tableaux

This repository contains the public manuscript and complete Lean 4
kernel-only formalization for:

> Alex Chengyu Li, *Exact Enumeration and Fixed-Rank Asymptotics of
> Ballot-Admissible Fibonacci Ribbon Tableaux* (2026).

The versioned public preprint is maintained under
[Zenodo concept DOI 10.5281/zenodo.22103759](https://doi.org/10.5281/zenodo.22103759).

## Formalized result

For every fixed alphabet size `n >= 3`, the Lean development proves the
paper's exact enumeration, generating-function identities, Regev leading
term, fixed-rank ribbon asymptotic, density asymptotic, and both iterated
density limits. The exact `n = 2` clause is also proved. All 47 numbered
manuscript labels have explicit entries in
`lean4/FibonacciRibbonKernel/ManuscriptFormulaMap.lean`.

The publication root is
`lean4/FibonacciRibbonKernel/KernelPublicationRoot.lean`; the executable
root is `lean4/FibonacciRibbonKernel/CurrentKernelRoot.lean`. The latter
imports the theorem map, manuscript-label map, and axiom audit.

The source contains no project axiom, `sorry`, `admit`, explicit `opaque` or
`unsafe` declaration, `native_decide`, or `ofReduceBool`. The trust-zero
axiom surface is limited to Lean's standard `propext`, `Classical.choice`,
and `Quot.sound`.

## Version relationship

The repository PDF is the 29 August 2026 formalization-complete revision. The
exact enumeration and every theorem statement are unchanged from the earlier
priority record. Release v1.2.0 replaces the compressed singularity-transfer
argument for the fixed-rank theorem with the exact Weyl-moment and Gaussian
transport route consumed by the Lean publication root. It also cites this
repository directly from the manuscript.

## Build from source

Use the pinned Lean toolchain and dependency revisions:

```powershell
cd lean4
lake exe cache get
lake build FibonacciRibbonKernel.CurrentKernelRoot
python verify-formula-map.py
```

Do not run `lake update`; `lake-manifest.json` pins all dependency revisions.
The complete build is intentionally large. A verified Windows x86-64 `.olean`
cache is attached to the GitHub release.

## Use the release cache

Download the cache archive, `olean-cache-manifest.json`, and
`SHA256SUMS.txt` from the matching release. Verify and restore it with:

```powershell
.\scripts\restore-olean-cache.ps1 `
  -Archive .\fibonacci-ribbon-ballot-enumeration-olean-cache-lean-4.32.0-rc1-windows-x86_64.zip `
  -Manifest .\olean-cache-manifest.json
```

The cache is a derived convenience artifact, not proof authority. The Lean
source and a `--trust=0` kernel build remain canonical.

## Contents

- `paper/`: current TeX, bibliography, and repository PDF.
- `lean4/FibonacciRibbonKernel/`: complete proof source.
- `FORMULA_MAP.md`: one-to-one map for all 47 manuscript labels.
- `scripts/restore-olean-cache.ps1`: hash-checked cache restoration.

## Licensing

See `LICENSE.md`. Lean source and repository documentation are Apache-2.0;
the manuscript source and PDF are CC BY 4.0.
