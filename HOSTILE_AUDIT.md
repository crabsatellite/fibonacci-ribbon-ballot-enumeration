# Hostile paper-to-kernel audit

Date: 29 August 2026

This audit attempts to falsify the manuscript and its claim of complete
kernel-only coverage. It distinguishes theorem truth, paper-to-Lean carrier
fidelity, release reproducibility, and the convenience cache.

## Audit target

- Manuscript: the 29 August 2026 repository PDF and TeX.
- Formal root: `FibonacciRibbonKernel.CurrentKernelRoot`.
- Publication surface: `KernelPublicationRoot.lean`, `KernelTheoremMap.lean`,
  `ManuscriptFormulaMap.lean`, and `KernelAxiomAudit.lean`.
- Release cache: the Windows x86-64 `.olean` archive attached to `v1.0.1`.

## Adversarial checks performed

1. Parsed all 47 TeX labels and compared them with the 47 explicit kernel
   mappings. There were no missing, extra, or duplicate labels. Multi-clause
   theorem and corollary labels were checked against every supporting
   endpoint, not only one representative endpoint.
2. Compared all 433 module sources and the package root byte-for-byte with
   the signed trust-zero build inputs. No source mismatch was found.
3. Searched the complete Lean tree for project axioms, `sorry`, `admit`,
   explicit `opaque` or `unsafe` declarations, `native_decide`,
   `ofReduceBool`, compiler trust escapes, and conditional literature adapters.
   None was found.
4. Compared the 129 publication theorem checks with the 129 axiom-audit
   declarations. The two sets are identical. The accepted dependencies are
   only `propext`, `Classical.choice`, and `Quot.sound`.
5. Restored all 434 release `.olean` files into the public relative build
   path, verified every byte count and SHA-256, and imported the global
   asymptotic and noncommuting-limit endpoints with `--trust=0` without
   rebuilding the proof cache.
6. Recomputed the dominant-walk counts, hook sums, inclusion-exclusion,
   Schur endpoint multiplicities, height-five and height-six recurrences,
   stable involutions, factorial moments, and near-stable defects for
   `2 <= n <= 8` and `0 <= k <= 24`.
7. Independently generated bounded-height tableau counts by Young-lattice
   dynamic programming through `k = 80`, applied the ribbon convolution, and
   compared the results with both Regev and transferred ribbon leading terms
   for `3 <= n <= 8`. Every normalized ratio moved toward `1`; no parity
   oscillation or wrong constant was detected.

## Carrier and normalization attacks

- The paper's alphabet size `n` is Lean's internal rank plus one:
  `b_(n,k) = ribbonCount (n-1) k` and
  `u_(n,k) = unrestrictedCount (n-1) k`. This shift is used consistently in
  the exact, stable, and asymptotic endpoints.
- Reversal changes the source's forbidden left-to-right parameter pair
  `(n,1)` into the paper's reading-order pair `(1,n)`. Both column parities
  concatenate to the literal full word `12...n`.
- The mixed defining/dual operators prove both `AB = BA` and
  `A 1 = B 1`. The exceptional off-diagonal interaction `x = y+1` is handled
  explicitly; it is not silently treated as independent.
- The fixed-rank exponent is exactly `n(n-1)/4`; the transferred constant is
  exactly
  `C_n * alpha_n/n * (sqrt(n^2-4)/n)^(beta_n-1)`.
- The one-dimensional `n = 3` tail is not obtained by applying the invalid
  coarse arbitrary-rank bound. It is split into two strict subdominant
  regions and proved separately.
- Even-rank negative endpoint contributions and middle spectral tails are
  consumed before the all-rank theorem is assembled.
- The forward and reverse iterated density limits use the literal finite-rank
  density, with the inner limits proved in the stated quantifier order.

## Attempts to find counterexamples

- Boundary cases `n = 2`, `k = 0`, empty inclusion-exclusion ranges, and the
  threshold `n = k` were replayed.
- The tempting direct model "no adjacent transposition and longest decreasing
  subsequence at most `n`" was rejected by exact counterexamples; it is not
  used by the paper or Lean proof.
- The stable walled-Brauer shortcut was likewise rejected on exact small
  cases and is not used.
- No mismatch was found in the displayed `n = 4,5,6` constants or
  recurrences, the four near-stable strips, or the Poisson factorial moment
  normalization.

## Findings and repairs

- A release-only defect was found: the initial public `lakefile.toml` used
  Git URLs with a trailing `.git`, while the pinned manifest used canonical
  URLs without it. Lake therefore warned that the manifest was stale. The
  URLs were made byte-identical to the lock file without changing either
  dependency revision.
- The first public formula table listed only one representative endpoint for
  several multi-clause theorem labels. The table now lists all supporting
  endpoints. This was a documentation defect, not an unproved theorem.
- The fixed-rank endpoint is proved through an exact Weyl-integral route,
  while the manuscript presents a Bessel/singularity route. The Lean project
  separately formalizes the Bessel systems, scale separation, local
  substitution geometry, actual Gessel bridges, and the same final literal
  count and constant. Thus the theorem carrier is identical, although the
  final kernel proof is not a line-by-line transcription of the prose proof.

## Verdict

No mathematical counterexample, false theorem, hidden premise, carrier
substitution, or kernel escape was found. The current result is **GO** as a
public kernel-only formalization. This is not a substitute for independent
peer review, and the platform-specific `.olean` archive remains a derived
cache rather than proof authority.
