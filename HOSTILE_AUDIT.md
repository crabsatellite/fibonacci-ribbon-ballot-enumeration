# Hostile mathematical audit — updated 29 August 2026

This audit treats the paper as a human proof.  Incomplete formalization is not
evidence against the mathematics, and finite replay is not evidence for an
unquantified theorem.

## Submission hostile rerun

- The existing Proof Engine build was run without clearing caches or forcing
  a fresh proof run.  The v2.5.27 release gate, graph, registered replay, and
  paper build all passed; `target_closed=false` remains unchanged.
- A separate local-state probe checked `AB=BA` for every state in
  `{0,1,2}^(n-1)` for `2<=n<=8`, not merely equality of total path counts.
- Endpoint multiplicities were compared with their Schur--Pieri realization
  for `2<=n<=6`, `0<=k<=10`.  Near-stable defects were compared with the
  tableau-tail formula for `1<=r<=8`, `k<=24`.
- At `k=800`, the exact-value-to-claimed-leading-asymptotic ratios for
  `n=3,4,5,6` were respectively approximately
  `0.99698, 0.99036, 0.97686, 0.95300`; these stress probes support but do not
  replace the analytic proof.
- The attack found and repaired one genuine exposition defect: the
  near-stable proof had grammatically assigned the summed leading coefficient
  `I_s/s!` to an individual hook-length polynomial.  The paper now states the
  individual coefficient `f^nu/t!` before summing over `nu`.
- The Poisson argument now gives an explicit uniform-integrability bound and
  obtains the zero-mass limit at the continuity point `1/2`.  The transfer
  step now cites the power--logarithm theorem directly.

Result: the fresh hostile review found repairable exposition obligations but
no counterexample or broken theorem.

## Literal source carrier

- The source labels columns from the left and uses
  `T_(j+1) != T_j+1`.  Writing `T_j=(j-1)n+a_j` shows that the unique bad
  left-to-right pair is `(n,1)`.  Reversal to the source's linear-word reading
  order makes it `(1,n)`, exactly as used in the paper.
- The rightmost column has height one.  After reversal, odd columns are
  singleton `a_c`, and even columns omit `n+1-a_c`.  No parity or complement
  convention is changed.
- A tall column is read in increasing order.  Omitting `y` has net difference
  step `-v_y`; the only possible internal-prefix failure is the same
  coordinate required by endpoint nonnegativity.

Result: the column-to-walk carrier passes.

## Mixed branching

- For `x != y`, compare `v_x,-v_y` in both orders.  The only nontrivial
  interaction is `x=y+1`; both orders are valid exactly when `d_y>=2`.
  Otherwise their validity conditions are independent.  The manuscript now
  states this exceptional case explicitly rather than incorrectly saying that
  only the diagonal case can couple the two validity tests.
- Zero displacement forces `x=y`.  Defining and dual outdegrees both equal
  `1+#{i:d_i>0}`.  Hence the diagonal coefficients of `AB` and `BA` agree as
  well as the off-diagonal coefficients.
- The proof uses `AB=BA` and `A 1=B 1`; it does not claim the mixed tensor is
  literally `V^tensor-k`.  That stronger statement is false at finite rank.
- Exact replay agrees with the bounded-height hook sum for
  `2<=n<=8`, `0<=k<=24`.

Result: the unrestricted finite-rank bridge passes.

## Inclusion-exclusion

- A bad pair is `1 | 2...n` or `1...(n-1) | n`, depending on parity.  Both
  concatenate to the same literal word `12...n`.
- The block is ballot-neutral at every starting dominant weight and deleting
  two columns preserves the parity of every remaining column.
- Bad locations cannot overlap.  Their `j`-subsets are exactly the
  `j`-matchings of a path on `k` vertices, counted by `binom(k-j,j)`.
- The contracted object is deliberately unrestricted; no new neighbor
  condition is silently imposed after deletion.

Result: the main formula passes.

## Highest-weight refinement

- The endpoint difference vector is normalized to the unique partition
  `mu` with last part zero; determinant twists are not counted as distinct
  `SL_n` weights.
- The dual defining module is replaced only by the literal `SL_n` identity
  `V^* = exterior^(n-1) V`.  Homogeneous degree fixes the determinant shift
  `q` uniquely, so the Schur coefficient neither omits nor duplicates a
  finite-rank constituent.
- Deleting a bad pair removes one defining and one dual factor and has zero
  difference displacement.  Inclusion--exclusion therefore holds at each
  endpoint, not only after summing endpoints.
- Registered replay agrees for all endpoints with `2<=n<=5`, `0<=k<=8`;
  the submission stress probe extends this to `2<=n<=6`, `0<=k<=10`.

Result: the highest-weight Schur refinement passes.

## Stable range and probability

- Stability is used only for `n>=k`, where every partition of every
  `k-2j` has at most `n` rows.
- Robinson--Schensted is used only for the total tableau sum.  The paper does
  not claim that the ordinary longest-decreasing-subsequence statistic gives
  a direct finite-rank model for the restricted ribbons.
- Prescribed adjacent transpositions are simultaneously possible exactly at
  path-matching locations, and leave an arbitrary involution on the remaining
  labels.
- The factorial-moment identity contains the ordered factor `r!`.  Moser--
  Wyman gives `I_(k-2r)/I_k~k^(-r)` for fixed `r`, so every fixed factorial
  moment tends to one.  Bounded next factorial moments supply uniform
  integrability in the standard method-of-moments argument.

Result: the stable involution interpretation and Poisson limit pass.

## Near-stable strips

- At `n=k-r`, the defect from stability in the term of residual size
  `m=k-2j` is nonzero exactly when `2j<r`; no omitted tail is extended beyond
  its legal range.
- Conjugation changes "more than `k-r` rows" into the literal first-row
  condition `m-lambda_1<=r-2j-1` and preserves `f^lambda`.
- For fixed tail size, the hook-length dimensions are eventually polynomial;
  the leading sum is `I_s/s!`, so later inclusion-exclusion terms cannot
  cancel the degree-`r-1` leading term.
- The registered replay covers `1<=r<=6,k<=16`; the submission stress probe
  extends the general identity to `1<=r<=8,k<=24`.  The four displayed strips
  agree exactly throughout their full legal ranges in those windows.

Result: the near-stable defect theorem passes.

## Four-letter asymptotic

- The height-four tableau formulas have the same leading constant on even and
  odd indices: `u_(4,m)~(32/pi)4^m m^(-3)`.
- The exact even Weyl moment replaces the geometric kernel `S^k` by the
  Fibonacci kernel `P_k(S)` on the same weight.  At the positive endpoint the
  Gaussian rate changes from `1/4` to `1/sqrt(12)`, while the homogeneous Weyl
  weight has total scaling exponent `beta_4=3`.
- The all-minus endpoint has the same absolute scale, but the even Weyl factor
  `prod_i(1+cos(theta_i))` vanishes there and makes its contribution lower
  order.  Gaussian transport therefore produces the ratio `(sqrt(3)/2)^3`;
  the exact `P_k(4)` normalization supplies the remaining factor and gives
  `6(2+sqrt(3))/pi`.

Result: the `n=4` formula and asymptotic pass.

## Five-letter asymptotic

- The height-five recurrence is the exact Bergeron--Gascon recurrence and is
  independently replayed against the hook sum through `k=24`.
- The odd Weyl scale `1+2 sum cos(theta_i)` has unique absolute maximum `5` at
  the all-plus endpoint.  The Fibonacci kernel changes the local Gaussian rate
  from `1/5` to `1/sqrt(21)` on the same homogeneous weight.
- Gaussian transport gives `(sqrt(21)/5)^5`; the exact
  `P_k(5)~alpha_5^(k+1)/sqrt(21)` factor reduces this to the displayed
  constant `1323*alpha_5/(8*pi)`.

Result: the `n=5` recurrence and asymptotic pass.

## All fixed ranks and the six-letter recurrence

- Gessel's Weyl moment represents `u_(n,k)` as the integral of `S_n^k` and the
  exact generating substitution represents `b_(n,k)` on the same measure by
  the Fibonacci polynomial `P_k(S_n)`.
- Under `theta=x/sqrt(k)`, the geometric and Fibonacci kernels converge to
  Gaussian factors with rates `1/n` and `1/sqrt(n^2-4)`.  The even and odd Weyl
  weights, together with the Jacobian, scale as `k^(-beta_n)` and have the same
  nonnegative homogeneous limit polynomial.
- Away from the all-plus endpoint the contribution is exponentially smaller;
  in even rank the all-minus Weyl factor vanishes to higher order.  The
  `n=3` negative endpoint has absolute scale `1<3` and is handled separately.
- Homogeneous Gaussian transport gives
  `(sqrt(n^2-4)/n)^beta_n`.  Combining this with
  `P_k(n)~alpha_n^(k+1)/sqrt(n^2-4)` yields exactly
  `C_n*(alpha_n/n)*(sqrt(n^2-4)/n)^(beta_n-1)`.
- The Bessel system remains in the paper for D-finiteness and the explicit
  special-rank recurrences; it is no longer used as an abbreviated singularity
  argument for the all-rank asymptotic.
- The height-six recurrence is obtained by literal coefficient extraction
  from the Bergeron--Gascon `Y_6` differential equation and is independently
  replayed through `k=24`.

Result: the all-fixed-rank leading asymptotic and `n=6` specialization pass.

## Direct finite-rank involution boundary

- The ordinary candidate "no adjacent transposition and LDS at most `n`"
  is false: it gives `5` versus `4` at `(n,k)=(3,4)`, `32` versus `31` at
  `(4,6)`, and `356` versus `355` at `(6,8)`.
- Deleting a prescribed adjacent transposition does not preserve ordinary
  Robinson--Schensted height.  Thus the neutral-block contraction cannot be
  transported through that statistic.
- The stable walled-Brauer shortcut fails independently at `(2,4)` and
  `(3,5)`.  Both negative routes are exact finite-rank obstructions, not a
  lack of literature search.

Result: the two obvious direct-involution transports are retired; a positive
model would require a new statistic carried by the alternating crystal.

## Kernel correspondence rerun — 29 August 2026

- All 47 TeX labels have explicit publication mappings; there are no missing,
  extra, or duplicate labels.
- All 433 module sources and the package root match the signed trust-zero
  build inputs. The 129 theorem-map endpoints and 129 axiom-audit endpoints
  are identical sets.
- The all-rank actual Gessel bridges, even/odd Weyl carriers, `n=3` tail,
  all fixed-rank asymptotics, density asymptotic, and forward iterated limit
  are now kernel closed.
- The public cache contains 434 source-bound `.olean` files and passed a
  hash-checked restore plus `--trust=0` import smoke test. It is treated only
  as derived cache evidence.
- Independent Young-lattice dynamic programming through `k=80` for
  `3<=n<=8` found no wrong Regev constant, transferred ribbon constant, or
  parity oscillation.
- The adversarial rerun found and repaired two release-documentation defects:
  noncanonical dependency URL spellings and under-specified multi-endpoint
  mappings. Neither defect changed a mathematical theorem.

## Publication boundary

The paper closes the source enumeration for all `n>=4` and proves independent
stable results.  It does not claim:

- a direct finite-rank arc-diagram model;
- an asymptotic uniform in simultaneously growing `n` and `k`.

The Lean formalization is complete and independent of the separate legacy
Proof Engine graph. The manuscript disclosure identifies OpenAI Codex as the
active replaceable component and cites the framework paper.

**Verdict:** **GO as a human-proof paper with complete kernel-only statement
coverage.** External peer review remains independent.
