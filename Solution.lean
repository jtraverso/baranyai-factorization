/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BaranyaiLib.Baranyai

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `BaranyaiLib/` (namespace `Baranyai`), on top of the author's finite
max-flow/min-cut theorem (`FlowLib/MaxFlowMinCut.lean`, from the registered entry
PALOMAR-2026-10-15-000008, included unchanged). `IntegralFlow.lean` proves that a network with
integer capacities has an integral maximum flow (Ford–Fulkerson with unit augmentations);
`Rounding.lean` derives the rounding lemma from it (a transportation network, after adding a slack
row and column so that all line sums are integers); `BaranyaiAux.lean` proves Baranyai's theorem
by Baranyai's induction, adding one element at a time to an array of partial parallel classes and
choosing where it goes by the rounding lemma. The definition below is the same as
`Baranyai.IsParallelClass` in the library.
-/

@[expose] public section

namespace BaranyaiTheorem

/-- **Baranyai's rounding lemma.** A real `m × n` matrix can be rounded entrywise to an integer
matrix so that every row sum, every column sum and the total sum is rounded too. -/
theorem rounding {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    ∃ B : Fin m → Fin n → ℤ,
      (∀ i j, B i j = ⌊A i j⌋ ∨ B i j = ⌈A i j⌉) ∧
      (∀ i, ∑ j, B i j = ⌊∑ j, A i j⌋ ∨ ∑ j, B i j = ⌈∑ j, A i j⌉) ∧
      (∀ j, ∑ i, B i j = ⌊∑ i, A i j⌋ ∨ ∑ i, B i j = ⌈∑ i, A i j⌉) ∧
      (∑ i, ∑ j, B i j = ⌊∑ i, ∑ j, A i j⌋ ∨ ∑ i, ∑ j, B i j = ⌈∑ i, ∑ j, A i j⌉) :=
  Baranyai.rounding A

/-- `P` is a partition of `Fin n` into blocks of size `k`: every element lies in exactly one block
of `P`, and every block has `k` elements. -/
def IsParallelClass (n k : ℕ) (P : Finset (Finset (Fin n))) : Prop :=
  (∀ x : Fin n, ∃! s, s ∈ P ∧ x ∈ s) ∧ ∀ s ∈ P, s.card = k

/-- **Baranyai's theorem (1975).** If `0 < k` and `k ∣ n`, the `k`-subsets of `Fin n` split into
`(n-1).choose (k-1)` parallel classes: each class is a partition of `Fin n` into blocks of size `k`,
and every `k`-subset lies in exactly one class. -/
theorem baranyai {n k : ℕ} (hk : 0 < k) (hkn : k ∣ n) :
    ∃ P : Fin ((n - 1).choose (k - 1)) → Finset (Finset (Fin n)),
      (∀ i, IsParallelClass n k (P i)) ∧
      ∀ s : Finset (Fin n), s.card = k → ∃! i, s ∈ P i :=
  Baranyai.baranyai hk hkn

end BaranyaiTheorem
