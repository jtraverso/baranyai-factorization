/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BaranyaiLib.Rounding
public import BaranyaiLib.BaranyaiAux

/-!
# Baranyai's theorem

* `Baranyai.rounding`: **Baranyai's rounding lemma.** Every real matrix can be rounded entrywise
  (each entry to its floor or its ceiling) to an integer matrix whose row sums, column sums and
  total sum are also roundings (floor or ceiling) of the corresponding sums of the original matrix.
* `Baranyai.baranyai`: **Baranyai's theorem (1975).** If `0 < k` and `k ∣ n`, the `k`-subsets of an
  `n`-set can be partitioned into `(n-1).choose (k-1)` *parallel classes*, each of which is a
  partition of the whole set into `n / k` blocks of size `k`; in other words the complete
  `k`-uniform hypergraph `K_n^(k)` has a 1-factorization.
-/

@[expose] public section

namespace Baranyai

/-- **Baranyai's rounding lemma.** A real `m × n` matrix can be rounded entrywise to an integer
matrix so that every row sum, every column sum and the total sum is rounded too. -/
theorem rounding {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    ∃ B : Fin m → Fin n → ℤ,
      (∀ i j, B i j = ⌊A i j⌋ ∨ B i j = ⌈A i j⌉) ∧
      (∀ i, ∑ j, B i j = ⌊∑ j, A i j⌋ ∨ ∑ j, B i j = ⌈∑ j, A i j⌉) ∧
      (∀ j, ∑ i, B i j = ⌊∑ i, A i j⌋ ∨ ∑ i, B i j = ⌈∑ i, A i j⌉) ∧
      (∑ i, ∑ j, B i j = ⌊∑ i, ∑ j, A i j⌋ ∨ ∑ i, ∑ j, B i j = ⌈∑ i, ∑ j, A i j⌉) :=
  rounding_fintype A

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
      ∀ s : Finset (Fin n), s.card = k → ∃! i, s ∈ P i := by
  obtain ⟨A, hA⟩ := exists_good (ι := Fin ((n - 1).choose (k - 1))) (κ := Fin (n / k)) k hk
    (by simp [Nat.div_mul_cancel hkn]) (by simp) n le_rfl
  obtain ⟨h1, h2, h3⟩ := good_final hA
  exact ⟨fun i => Finset.univ.image (A i), fun i => ⟨h1 i, h2 i⟩, h3⟩

end Baranyai
