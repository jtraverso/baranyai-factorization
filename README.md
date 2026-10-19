# Baranyai's theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

All statements are in the namespace `BaranyaiTheorem`:

1. `rounding`, **Baranyai's rounding lemma**. Every real `m × n` matrix can be rounded entrywise
   (each entry to its floor or its ceiling) to an integer matrix whose row sums, column sums and
   total sum are also roundings (floor or ceiling) of the corresponding sums of the original
   matrix.
2. `baranyai`, **Baranyai's theorem (1975)**. If `0 < k` and `k ∣ n`, the `k`-subsets of
   `Fin n` can be partitioned into `(n-1).choose (k-1)` *parallel classes*, each a partition of
   `Fin n` into `n / k` blocks of size `k` (`BaranyaiTheorem.IsParallelClass`), with every
   `k`-subset in exactly one class. In other words the complete `k`-uniform hypergraph `K_n^(k)`
   has a 1-factorization.

The definition `IsParallelClass` is stated in `Challenge.lean`; `comparator.json` selects only the
theorems, and the definition enters the check only as part of the theorem statement that uses it.
Mathlib has neither result.

## Files

- [`Challenge.lean`](Challenge.lean): the definition and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean), [`BaranyaiLib/`](BaranyaiLib) and
  [`FlowLib/MaxFlowMinCut.lean`](FlowLib/MaxFlowMinCut.lean): the proofs. `FlowLib` is the
  author's finite max-flow/min-cut theorem from the registered entry
  [PALOMAR-2026-10-15-000008](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000008&version=1),
  included unchanged.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Integral flows** (`IntegralFlow.lean`). A network with integer capacities has an integral
  flow whose value is at least that of every real flow. Take an integral flow of largest value;
  if the sink were still reachable in the residual graph, pushing one unit along an augmenting
  path would give a larger one, so the reachable set is a saturated cut and the flow is maximum
  by the max-flow/min-cut theorem of `FlowLib`.
* **Rounding** (`Rounding.lean`). A nonnegative matrix with integer entry bounds and integer line
  sums is replaced by an integral one through the network source → rows → columns → sink. For a
  general matrix, a slack row and a slack column make every line sum an integer; the fractional
  parts are rounded this way and the slack row and column are dropped.
* **Baranyai** (`BaranyaiAux.lean`). Write `n = k a` and `N = (n-1).choose (k-1)`. By induction
  on `m ≤ n`, there is an `N × a` array of subsets of `{0, …, m-1}` in which every row is a
  partition and every set `S` with `|S| ≤ k` occurs exactly `(n - m).choose (k - |S|)` times. To
  add the element `m`, the matrix `x(i, S)` = (number of cells of row `i` equal to `S`) ·
  `(k - |S|) / (n - m)` has row sums `1` and integer column sums; the rounding lemma chooses one
  cell per row, and Pascal's rule restores the invariant. At `m = n` every cell is a `k`-set and
  every `k`-set occurs exactly once.

## Sources

* Zs. Baranyai, *On the factorization of the complete uniform hypergraph*, in: Infinite and
  Finite Sets (Proc. Colloq. Keszthely, 1973), Colloq. Math. Soc. János Bolyai 10, North-Holland
  (1975) 91–108.
* J. H. van Lint, R. M. Wilson, *A Course in Combinatorics*, 2nd ed., Cambridge University Press
  (2001), doi:10.1017/CBO9780511987045 (Chapter 38).
* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956)
  399–404, doi:10.4153/CJM-1956-045-5.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude
Code. Harmonic's Aristotle produced the proofs (including the integral flow theorem, which the
reused max-flow library did not contain), which were audited and rebuilt locally. Lean checks
everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
