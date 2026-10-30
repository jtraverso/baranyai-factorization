/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import BaranyaiLib.Rounding
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Fin

/-!
# Auxiliary material for Baranyai's theorem

The inductive invariant of the standard proof: an array of subsets of `{0, …, m-1}` whose rows
are partitions and in which every set `S` occurs `(n - m).choose (k - #S)` times.
-/

@[expose] public section

namespace Baranyai

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}

/-- Number of cells of row `i` equal to `S`. -/
def mult (A : ι → κ → Finset (Fin n)) (i : ι) (S : Finset (Fin n)) : ℕ :=
  #{j | A i j = S}

/-- Number of cells of the whole array equal to `S`. -/
def cnt (A : ι → κ → Finset (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i, mult A i S

/-- The invariant of Baranyai's induction at stage `m`. -/
def Good (k m : ℕ) (A : ι → κ → Finset (Fin n)) : Prop :=
  (∀ i j, ∀ x ∈ A i j, x.val < m) ∧
  (∀ i j, (A i j).card ≤ k) ∧
  (∀ i (x : Fin n), x.val < m → ∃! j, x ∈ A i j) ∧
  (∀ S : Finset (Fin n), (∀ x ∈ S, x.val < m) → S.card ≤ k →
    cnt A S = (n - m).choose (k - S.card))

lemma choose_mul_div_eq (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    ((p.choose q : ℕ) : ℝ) * (q : ℝ) / (p : ℝ) = ((p - 1).choose (q - 1) : ℕ) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  simp only [zero_add, Nat.add_sub_cancel]
  have h := Nat.add_one_mul_choose_eq p q
  have h' : ((p + 1 : ℕ) : ℝ) * (p.choose q : ℝ) = ((p + 1).choose (q + 1) : ℝ) * (q + 1 : ℕ) := by
    exact_mod_cast h
  have hp' : ((p + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

lemma good_zero (k : ℕ) (hk : 0 < k) (hκ : Fintype.card κ * k = n)
    (hι : Fintype.card ι = (n - 1).choose (k - 1)) :
    Good (ι := ι) (κ := κ) k 0 (fun _ _ => (∅ : Finset (Fin n))) := by
  refine ⟨fun _ _ x hx => by simp at hx, fun _ _ => by simp, fun _ x hx => absurd hx (by omega),
    ?_⟩
  intro S hS _
  have hS0 : S = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]; intro x hx; have := hS x hx; omega
  subst hS0
  have hm : ∀ i : ι, mult (κ := κ) (fun _ _ => (∅ : Finset (Fin n))) i ∅ = Fintype.card κ :=
    fun i => by simp [mult]
  simp only [cnt, hm, Finset.card_univ, Finset.sum_const, smul_eq_mul,
    Finset.card_empty, Nat.sub_zero, hι]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : Fintype.card κ = 0 := by
      rcases Nat.mul_eq_zero.mp hκ with h | h
      · exact h
      · omega
    rw [this, Nat.choose_eq_zero_of_lt hk]; simp
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h := Nat.add_one_mul_choose_eq n' k'
    apply Nat.eq_of_mul_eq_mul_right (show 0 < k' + 1 by omega)
    rw [← h, ← hκ]; ring

lemma sum_card_row {k m : ℕ} {A : ι → κ → Finset (Fin n)} (hA : Good k m A) (hm : m ≤ n)
    (i : ι) : ∑ j, (A i j).card = m := by
  classical
  have hdisj : (↑(univ : Finset κ) : Set κ).PairwiseDisjoint (A i) := by
    intro j _ j' _ hjj'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j0, _, hu⟩ := hA.2.2.1 i x (hA.1 i j x hx)
    exact hjj' ((hu j hx).trans (hu j' hx').symm)
  rw [← Finset.card_biUnion hdisj]
  have : univ.biUnion (A i) = univ.filter (fun x : Fin n => (x : ℕ) < m) := by
    ext x
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨j, hj⟩; exact hA.1 i j x hj
    · intro hx; obtain ⟨j, hj, _⟩ := hA.2.2.1 i x hx; exact ⟨j, hj⟩
  rw [this, Fin.card_filter_val_lt]
  omega

lemma sum_deficit_row {k m : ℕ} {A : ι → κ → Finset (Fin n)} (hA : Good k m A) (hm : m ≤ n)
    (hκ : Fintype.card κ * k = n) (i : ι) : ∑ j, (k - (A i j).card) = n - m := by
  have h1 := sum_card_row hA hm i
  have h2 : ∑ j, (k - (A i j).card) + ∑ j, (A i j).card = n := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hA.2.1 i j)]
    simpa using hκ
  omega

omit [Fintype ι] in
lemma sum_mult_mul (A : ι → κ → Finset (Fin n)) (i : ι) (w : Finset (Fin n) → ℝ) :
    ∑ S, (mult A i S : ℝ) * w S = ∑ j, w (A i j) := by
  classical
  simp only [mult, Finset.card_filter]
  push_cast
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

lemma exists_selection {k m : ℕ} {A : ι → κ → Finset (Fin n)} (hA : Good k m A) (hm : m < n)
    (hκ : Fintype.card κ * k = n) :
    ∃ sel : ι → κ, (∀ i, (A i (sel i)).card < k) ∧
      ∀ S : Finset (Fin n), (∀ x ∈ S, x.val < m) → S.card < k →
        #{i | A i (sel i) = S} = (n - m - 1).choose (k - S.card - 1) := by
  classical
  have hpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - m)
  set x : ι → Finset (Fin n) → ℝ :=
    fun i S => (mult A i S : ℝ) * ((k - S.card : ℕ) : ℝ) / ((n - m : ℕ) : ℝ) with hx
  obtain ⟨B, hBe, hBr, hBc, -⟩ := rounding_fintype x
  have hx0 : ∀ i S, 0 ≤ x i S := fun i S => by positivity
  have hB0 : ∀ i S, 0 ≤ B i S := fun i S => by
    have h1 := Int.floor_nonneg.mpr (hx0 i S)
    have h2 := Int.floor_le_ceil (x i S)
    rcases hBe i S with h | h <;> omega
  have hBpos : ∀ i S, 1 ≤ B i S → 0 < x i S := by
    intro i S h1
    by_contra hneg
    have h0 : x i S = 0 := le_antisymm (not_lt.mp hneg) (hx0 i S)
    rcases hBe i S with h | h <;> rw [h0] at h <;> simp at h <;> omega
  have hxrow : ∀ i, ∑ S, x i S = 1 := by
    intro i
    simp only [hx]
    rw [← Finset.sum_div, sum_mult_mul A i (fun S => ((k - S.card : ℕ) : ℝ))]
    rw [← Nat.cast_sum, sum_deficit_row hA hm.le hκ i]
    exact div_self hpos.ne'
  have hBrow : ∀ i, ∑ S, B i S = 1 := by
    intro i
    have := hBr i
    rw [hxrow i] at this
    simpa using this
  have hchoice : ∀ i, ∃ j, (A i j).card < k ∧ ∀ S, B i S = if A i j = S then 1 else 0 := by
    intro i
    have hne : ∑ S, B i S ≠ 0 := by rw [hBrow]; norm_num
    obtain ⟨S, _, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hS1 : 1 ≤ B i S := by have := hB0 i S; omega
    have hxS := hBpos i S hS1
    have hmS : 0 < mult A i S := by
      rcases Nat.eq_zero_or_pos (mult A i S) with h | h
      · simp [hx, h] at hxS
      · exact h
    have hwS : 0 < k - S.card := by
      rcases Nat.eq_zero_or_pos (k - S.card) with h | h
      · simp [hx, h] at hxS
      · exact h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hmS
    simp only [mem_filter, mem_univ, true_and] at hj
    have hle : B i S ≤ 1 := hBrow i ▸ Finset.single_le_sum (fun S _ => hB0 i S) (mem_univ S)
    refine ⟨j, by rw [hj]; omega, fun S' => ?_⟩
    split_ifs with h
    · rw [← h, hj]; omega
    · have hSS : S ≠ S' := fun e => h (hj.trans e)
      have := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ {S, S'})
        (fun S _ _ => hB0 i S) (f := B i)
      rw [Finset.sum_pair hSS, hBrow i] at this
      have := hB0 i S'
      omega
  choose sel hsel1 hsel2 using hchoice
  refine ⟨sel, hsel1, fun S hS hSk => ?_⟩
  have hcol : ((#{i | A i (sel i) = S} : ℕ) : ℤ) = ∑ i, B i S := by
    rw [Finset.sum_congr rfl fun i _ => hsel2 i S, Finset.sum_boole]
  have hxcol : ∑ i, x i S = (((n - m - 1).choose (k - S.card - 1) : ℕ) : ℝ) := by
    simp only [hx]
    rw [← Finset.sum_div, ← Finset.sum_mul, ← Nat.cast_sum]
    change ((cnt A S : ℕ) : ℝ) * _ / _ = _
    rw [hA.2.2.2 S hS hSk.le]
    exact choose_mul_div_eq (n - m) (k - S.card) (by omega) (by omega)
  have h := hBc S
  rw [hxcol, Int.floor_natCast, Int.ceil_natCast, ← hcol] at h
  have h' : ((#{i | A i (sel i) = S} : ℕ) : ℤ) = (((n - m - 1).choose (k - S.card - 1) : ℕ) : ℤ) :=
    h.elim id id
  exact_mod_cast h'

lemma good_succ [DecidableEq κ] {k m : ℕ} {A : ι → κ → Finset (Fin n)} (hA : Good k m A)
    (hm : m < n)
    (sel : ι → κ) (hsel1 : ∀ i, (A i (sel i)).card < k)
    (hsel2 : ∀ S : Finset (Fin n), (∀ x ∈ S, x.val < m) → S.card < k →
        #{i | A i (sel i) = S} = (n - m - 1).choose (k - S.card - 1)) :
    Good k (m + 1) (fun i j => if j = sel i then insert ⟨m, hm⟩ (A i j) else A i j) := by
  set mm : Fin n := ⟨m, hm⟩ with hmm
  set A' : ι → κ → Finset (Fin n) := fun i j => if j = sel i then insert mm (A i j) else A i j
    with hA'
  have hmA : ∀ i j, mm ∉ A i j := fun i j h => by
    have := hA.1 i j mm h; simp [mm] at this
  have hmem : ∀ i j x, x ∈ A' i j ↔ x ∈ A i j ∨ (j = sel i ∧ x = mm) := by
    intro i j x
    by_cases h : j = sel i <;> simp [A', h, mem_insert, or_comm]
  have hval : ∀ x : Fin n, x.val < m + 1 → x ≠ mm → x.val < m := by
    intro x hx hne
    have : x.val ≠ m := fun h => hne (Fin.ext h)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j x hx
    rcases (hmem i j x).1 hx with h | ⟨_, rfl⟩
    · have := hA.1 i j x h; omega
    · simp [mm]
  · intro i j
    by_cases h : j = sel i
    · subst h
      simp only [A', ite_true]
      exact (card_insert_le _ _).trans (by have := hsel1 i; omega)
    · simp only [A', h, ite_false]; exact hA.2.1 i j
  · intro i x hx
    by_cases hxm : x = mm
    · refine ⟨sel i, (hmem _ _ _).2 (Or.inr ⟨rfl, hxm⟩), fun j' hj' => ?_⟩
      rcases (hmem _ _ _).1 hj' with h | ⟨h, _⟩
      · exact absurd (hxm ▸ h) (hmA i j')
      · exact h
    · obtain ⟨j, hj, hu⟩ := hA.2.2.1 i x (hval x hx hxm)
      refine ⟨j, (hmem _ _ _).2 (Or.inl hj), fun j' hj' => ?_⟩
      rcases (hmem _ _ _).1 hj' with h | ⟨_, h⟩
      · exact hu j' h
      · exact absurd h hxm
  -- counting
  have hrow1 : ∀ T, mm ∉ T → ∀ i,
      mult A' i T + (if A i (sel i) = T then 1 else 0) = mult A i T := by
    intro T hT i
    unfold mult
    have : ({j | A' i j = T} : Finset κ) = ({j | A i j = T} : Finset κ).erase (sel i) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_erase, A']
      by_cases h : j = sel i
      · subst h
        simp only [ite_true, ne_eq, not_true_eq_false, false_and, iff_false]
        intro heq; apply hT; rw [← heq]; exact mem_insert_self _ _
      · simp [h]
    rw [this]
    split_ifs with h
    · exact card_erase_add_one (by simp [h])
    · rw [erase_eq_of_notMem (by simp [h])]; simp
  have hrow2 : ∀ T, mm ∈ T → ∀ i,
      mult A' i T = if A i (sel i) = T.erase mm then 1 else 0 := by
    intro T hT i
    unfold mult
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨sel i, ?_⟩
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton, A']
      by_cases hj : j = sel i
      · subst hj; simp [h, insert_erase hT]
      · simp only [hj, ite_false, iff_false]
        intro heq; apply hmA i j; rw [heq]; exact hT
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro j _
      simp only [A']
      split_ifs with hj
      · subst hj; intro heq; apply h; rw [← heq, erase_insert (hmA i _)]
      · intro heq; apply hmA i j; rw [heq]; exact hT
  intro T hT hTk
  by_cases hmT : mm ∈ T
  · have hc : cnt A' T = #{i | A i (sel i) = T.erase mm} := by
      unfold cnt
      rw [Finset.sum_congr rfl fun i _ => hrow2 T hmT i]
      simp only [Finset.sum_boole, Nat.cast_id]
    have hTpos : 0 < T.card := card_pos.mpr ⟨mm, hmT⟩
    have hsub : ∀ x ∈ T.erase mm, x.val < m := by
      intro x hx
      obtain ⟨hne, hx⟩ := mem_erase.mp hx
      exact hval x (hT x hx) hne
    rw [hc, hsel2 _ hsub (by rw [card_erase_of_mem hmT]; omega), card_erase_of_mem hmT]
    congr 1
    omega
  · have hsub : ∀ x ∈ T, x.val < m := fun x hx =>
      hval x (hT x hx) (fun h => hmT (h ▸ hx))
    have hsum : cnt A' T + #{i | A i (sel i) = T} = cnt A T := by
      unfold cnt
      rw [← Finset.sum_congr rfl fun i _ => hrow1 T hmT i, Finset.sum_add_distrib]
      simp only [Finset.sum_boole, Nat.cast_id]
    rw [hA.2.2.2 T hsub hTk] at hsum
    rcases Nat.lt_or_ge T.card k with hlt | hge
    · rw [hsel2 T hsub hlt] at hsum
      obtain ⟨p, hp⟩ : ∃ p, n - m = p + 1 := ⟨n - m - 1, by omega⟩
      obtain ⟨q, hq⟩ : ∃ q, k - T.card = q + 1 := ⟨k - T.card - 1, by omega⟩
      rw [hp, hq, Nat.choose_succ_succ] at hsum
      have e1 : n - (m + 1) = p := by omega
      simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one] at hsum
      rw [e1, hq]
      omega
    · have hTk' : T.card = k := le_antisymm hTk hge
      have h0 : #{i | A i (sel i) = T} = 0 := by
        rw [card_eq_zero, filter_eq_empty_iff]
        intro i _ heq
        have := hsel1 i
        rw [heq] at this
        omega
      rw [h0, hTk', Nat.sub_self, Nat.choose_zero_right] at hsum
      rw [hTk', Nat.sub_self, Nat.choose_zero_right]
      omega

lemma exists_good (k : ℕ) (hk : 0 < k) (hκ : Fintype.card κ * k = n)
    (hι : Fintype.card ι = (n - 1).choose (k - 1)) :
    ∀ m ≤ n, ∃ A : ι → κ → Finset (Fin n), Good k m A := by
  classical
  intro m
  induction m with
  | zero => exact fun _ => ⟨_, good_zero k hk hκ hι⟩
  | succ m ih =>
    intro hm
    obtain ⟨A, hA⟩ := ih (by omega)
    obtain ⟨sel, h1, h2⟩ := exists_selection hA (by omega) hκ
    exact ⟨_, good_succ hA (by omega) sel h1 h2⟩

lemma good_final {k : ℕ} {A : ι → κ → Finset (Fin n)} (hA : Good k n A) :
    (∀ i (x : Fin n), ∃! s, s ∈ univ.image (A i) ∧ x ∈ s) ∧
    (∀ i, ∀ s ∈ univ.image (A i), s.card = k) ∧
    ∀ s : Finset (Fin n), s.card = k → ∃! i, s ∈ univ.image (A i) := by
  classical
  have hcnt : ∀ S : Finset (Fin n), S.card ≤ k → cnt A S = if S.card = k then 1 else 0 := by
    intro S hS
    rw [hA.2.2.2 S (fun x _ => x.isLt) hS, Nat.sub_self]
    split_ifs with h
    · rw [h, Nat.sub_self, Nat.choose_zero_right]
    · obtain ⟨d, hd⟩ : ∃ d, k - S.card = d + 1 := ⟨k - S.card - 1, by omega⟩
      rw [hd, Nat.choose_zero_succ]
  have hmult : ∀ i s, s ∈ univ.image (A i) → 1 ≤ mult A i s := by
    intro i s hs
    obtain ⟨j, _, rfl⟩ := mem_image.mp hs
    exact Finset.card_pos.mpr ⟨j, by simp⟩
  have hle : ∀ i s, mult A i s ≤ cnt A s := fun i s =>
    Finset.single_le_sum (f := fun i => mult A i s) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hcell : ∀ i j, (A i j).card = k := by
    intro i j
    have h1 := hmult i (A i j) (mem_image_of_mem _ (mem_univ _))
    have h2 := hle i (A i j)
    rw [hcnt _ (hA.2.1 i j)] at h2
    split_ifs at h2 with h
    · exact h
    · omega
  refine ⟨?_, ?_, ?_⟩
  · intro i x
    obtain ⟨j, hj, huniq⟩ := hA.2.2.1 i x x.isLt
    refine ⟨A i j, ⟨mem_image_of_mem _ (mem_univ _), hj⟩, ?_⟩
    rintro s ⟨hs, hxs⟩
    obtain ⟨j', _, rfl⟩ := mem_image.mp hs
    rw [huniq j' hxs]
  · intro i s hs
    obtain ⟨j, _, rfl⟩ := mem_image.mp hs
    exact hcell i j
  · intro s hs
    have hc : cnt A s = 1 := by rw [hcnt s hs.le]; simp [hs]
    have hne : ∑ i, mult A i s ≠ 0 := by rw [← cnt, hc]; omega
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hi)
    simp only [mem_filter, mem_univ, true_and] at hj
    refine ⟨i, hj ▸ mem_image_of_mem _ (mem_univ _), ?_⟩
    intro i' hi'
    by_contra hii
    have h1 := hmult i' s hi'
    have h2 := hmult i s (hj ▸ mem_image_of_mem _ (mem_univ _))
    have h3 : mult A i' s + mult A i s ≤ cnt A s := by
      rw [cnt, ← Finset.sum_pair (f := fun i => mult A i s) hii]
      exact Finset.sum_le_sum_of_subset (subset_univ _)
    omega

end Baranyai
