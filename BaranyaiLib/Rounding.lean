/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FlowLib.MaxFlowMinCut
public import BaranyaiLib.IntegralFlow

/-!
# Matrix rounding

Integrality of bipartite transportation problems (via integral maximum flows), and from it
Baranyai's rounding lemma for real matrices indexed by arbitrary finite types.
-/

@[expose] public section

namespace Baranyai

open Contrib.MaxFlowMinCut Finset

section Transport

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Integer capacities of the transportation network `s → rows → columns → t`. -/
def tCap (u : α → β → ℤ) (R : α → ℤ) (C : β → ℤ) :
    Unit ⊕ Unit ⊕ α ⊕ β → Unit ⊕ Unit ⊕ α ⊕ β → ℤ
  | .inl _, .inr (.inr (.inl i)) => R i
  | .inr (.inr (.inl i)), .inr (.inr (.inr j)) => u i j
  | .inr (.inr (.inr j)), .inr (.inl _) => C j
  | _, _ => 0

/-- Forward part of the real flow given by a real matrix. -/
def tFwd (a : α → β → ℝ) (R : α → ℤ) (C : β → ℤ) :
    Unit ⊕ Unit ⊕ α ⊕ β → Unit ⊕ Unit ⊕ α ⊕ β → ℝ
  | .inl _, .inr (.inr (.inl i)) => R i
  | .inr (.inr (.inl i)), .inr (.inr (.inr j)) => a i j
  | .inr (.inr (.inr j)), .inr (.inl _) => C j
  | _, _ => 0

/-- **Integral transportation.** A nonnegative real matrix with entrywise integer upper bounds
and integer row and column sums can be replaced by an integer matrix with the same bounds and
the same row and column sums. -/
theorem transport_integral (a : α → β → ℝ) (u : α → β → ℤ)
    (hau : ∀ i j, 0 ≤ a i j ∧ a i j ≤ u i j) (R : α → ℤ) (C : β → ℤ)
    (hR : ∀ i, ∑ j, a i j = R i) (hC : ∀ j, ∑ i, a i j = C j) :
    ∃ e : α → β → ℤ, (∀ i j, 0 ≤ e i j ∧ e i j ≤ u i j) ∧
      (∀ i, ∑ j, e i j = R i) ∧ ∀ j, ∑ i, e i j = C j := by
  classical
  have hR0 : ∀ i, 0 ≤ R i := fun i => by
    have : (0 : ℝ) ≤ R i := by rw [← hR]; exact Finset.sum_nonneg fun j _ => (hau i j).1
    exact_mod_cast this
  have hC0 : ∀ j, 0 ≤ C j := fun j => by
    have : (0 : ℝ) ≤ C j := by rw [← hC]; exact Finset.sum_nonneg fun i _ => (hau i j).1
    exact_mod_cast this
  have hu0 : ∀ i j, 0 ≤ u i j := fun i j => by
    have := (hau i j).1.trans (hau i j).2
    exact_mod_cast this
  have hcap0 : ∀ x y, 0 ≤ tCap u R C x y := by
    intro x y
    rcases x with _ | _ | i | j <;> rcases y with _ | _ | i' | j' <;>
      simp [tCap, hR0, hC0, hu0]
  let Net : Network (Unit ⊕ Unit ⊕ α ⊕ β) :=
    { cap := fun x y => tCap u R C x y
      capNonneg := fun x y => by exact_mod_cast hcap0 x y
      s := .inl ()
      t := .inr (.inl ())
      st := by simp }
  have hfwd0 : ∀ x y, 0 ≤ tFwd a R C x y := by
    intro x y
    rcases x with _ | _ | i | j <;> rcases y with _ | _ | i' | j' <;>
      simp [tFwd, hR0, hC0, (hau _ _).1]
  have hfwdc : ∀ x y, tFwd a R C x y ≤ tCap u R C x y := by
    intro x y
    rcases x with _ | _ | i | j <;> rcases y with _ | _ | i' | j' <;>
      simp [tFwd, tCap, (hau _ _).2]
  let F0 : Flow Net :=
    { f := fun x y => tFwd a R C x y - tFwd a R C y x
      skew := fun x y => by ring
      capacitated := fun x y => by
        change _ ≤ (tCap u R C x y : ℝ)
        linarith [hfwd0 y x, hfwdc x y]
      conserved := by
        intro x hxs hxt
        rcases x with _ | _ | i | j
        · exact absurd rfl hxs
        · exact absurd rfl hxt
        · simp [Fintype.sum_sum_type, tFwd, hR]
        · simp [Fintype.sum_sum_type, tFwd, hC] }
  have hF0 : F0.value = ∑ i, (R i : ℝ) := by
    simp [Flow.value, F0, Net, Fintype.sum_sum_type, tFwd]
  obtain ⟨F, g, hg, hmax⟩ := exists_integral_maxflow Net (tCap u R C) (fun _ _ => rfl)
  -- integer facts about `g`
  have gskew : ∀ x y, g x y = - g y x := by
    intro x y
    have := F.skew x y
    rw [hg, hg] at this
    exact_mod_cast this
  have gcap : ∀ x y, g x y ≤ tCap u R C x y := by
    intro x y
    have := F.capacitated x y
    rw [hg] at this
    have h' : (g x y : ℝ) ≤ (tCap u R C x y : ℝ) := this
    exact_mod_cast h'
  have gcons : ∀ x, x ≠ Net.s → x ≠ Net.t → ∑ y, g x y = 0 := by
    intro x h1 h2
    have := F.conserved x h1 h2
    simp only [hg] at this
    exact_mod_cast this
  have gzero : ∀ x y, tCap u R C x y = 0 → tCap u R C y x = 0 → g x y = 0 := by
    intro x y h1 h2
    have := gcap x y
    have := gcap y x
    have := gskew x y
    omega
  have gval : F.value = ∑ y, (g (.inl ()) y : ℝ) := by
    simp only [Flow.value, hg]; rfl
  -- the integer matrix
  refine ⟨fun i j => g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))), ?_, ?_⟩
  · intro i j
    refine ⟨?_, gcap _ _⟩
    have h1 := gskew (.inr (.inr (.inl i))) (.inr (.inr (.inr j)))
    have h2 := gcap (.inr (.inr (.inr j))) (.inr (.inr (.inl i)))
    simp only [tCap] at h2
    dsimp only
    omega
  -- row sums
  have hrow : ∀ i, ∑ j, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) =
      g (.inl ()) (.inr (.inr (.inl i))) := by
    intro i
    have h := gcons (.inr (.inr (.inl i))) (by simp [Net]) (by simp [Net])
    simp only [Fintype.sum_sum_type, Fintype.sum_unique] at h
    rw [gzero (.inr (.inr (.inl i))) (.inr (.inl ())) rfl rfl,
      Finset.sum_eq_zero (fun i' _ => gzero (.inr (.inr (.inl i))) (.inr (.inr (.inl i')))
        rfl rfl), gskew (.inr (.inr (.inl i))) (.inl ())] at h
    try simp only [PUnit.default_eq_unit] at h
    omega
  have hsrc : ∀ i, g (.inl ()) (.inr (.inr (.inl i))) ≤ R i := fun i => gcap _ _
  have hvalZ : ∑ i, R i ≤ ∑ i, g (.inl ()) (.inr (.inr (.inl i))) := by
    have hZ : ∑ y, g (.inl ()) y = ∑ i, g (.inl ()) (.inr (.inr (.inl i))) := by
      simp only [Fintype.sum_sum_type, Fintype.sum_unique]
      rw [gzero (.inl ()) (.inl ()) rfl rfl, gzero (.inl ()) (.inr (.inl ())) rfl rfl,
        Finset.sum_eq_zero (fun j _ => gzero (.inl ()) (.inr (.inr (.inr j))) rfl rfl)]
      simp
    have h := hmax F0
    rw [hF0, gval] at h
    have h' : ((∑ i, R i : ℤ) : ℝ) ≤ ((∑ y, g (.inl ()) y : ℤ) : ℝ) := by
      push_cast; exact h
    rw [hZ] at h'
    exact_mod_cast h'
  have hsat : ∀ i, g (.inl ()) (.inr (.inr (.inl i))) = R i := by
    have hle : ∑ i, (R i - g (.inl ()) (.inr (.inr (.inl i)))) ≤ 0 := by
      rw [Finset.sum_sub_distrib]; linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hsrc i))).mp
      (le_antisymm hle (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hsrc i)))
    intro i
    have := this i (Finset.mem_univ _)
    omega
  have hrow' : ∀ i, ∑ j, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) = R i :=
    fun i => (hrow i).trans (hsat i)
  refine ⟨hrow', ?_⟩
  -- column sums
  have hcol : ∀ j, ∑ i, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) =
      g (.inr (.inr (.inr j))) (.inr (.inl ())) := by
    intro j
    have h := gcons (.inr (.inr (.inr j))) (by simp [Net]) (by simp [Net])
    simp only [Fintype.sum_sum_type, Fintype.sum_unique] at h
    rw [gzero (.inr (.inr (.inr j))) (.inl ()) rfl rfl,
      Finset.sum_eq_zero (fun j' _ => gzero (.inr (.inr (.inr j))) (.inr (.inr (.inr j')))
        rfl rfl)] at h
    simp only [PUnit.default_eq_unit] at h
    have : ∑ i, g (.inr (.inr (.inr j))) (.inr (.inr (.inl i))) =
        - ∑ i, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => gskew _ _
    have e : g (.inr (.inr (.inr j))) (.inr (.inl PUnit.unit)) =
        g (.inr (.inr (.inr j))) (.inr (.inl ())) := rfl
    omega
  have hcolle : ∀ j, ∑ i, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) ≤ C j := by
    intro j; rw [hcol]; exact gcap _ _
  have hRC : ∑ i, R i = ∑ j, C j := by
    have : ((∑ i, R i : ℤ) : ℝ) = ((∑ j, C j : ℤ) : ℝ) := by
      push_cast
      simp_rw [← hR, ← hC]
      exact Finset.sum_comm
    exact_mod_cast this
  have htot : ∑ j, ∑ i, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j))) = ∑ j, C j := by
    rw [Finset.sum_comm, ← hRC]
    exact Finset.sum_congr rfl fun i _ => hrow' i
  have hle : ∑ j, (C j - ∑ i, g (.inr (.inr (.inl i))) (.inr (.inr (.inr j)))) ≤ 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hcolle j))).mp
    (le_antisymm hle (Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hcolle j)))
  intro j
  have := this j (Finset.mem_univ _)
  dsimp only
  omega

end Transport

section Round

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Rounding a real matrix whose row and column sums are integers, keeping these sums. -/
theorem round_integral_margins (A : α → β → ℝ) (R : α → ℤ) (C : β → ℤ)
    (hR : ∀ i, ∑ j, A i j = R i) (hC : ∀ j, ∑ i, A i j = C j) :
    ∃ B : α → β → ℤ, (∀ i j, B i j = ⌊A i j⌋ ∨ B i j = ⌈A i j⌉) ∧
      (∀ i, ∑ j, B i j = R i) ∧ ∀ j, ∑ i, B i j = C j := by
  obtain ⟨e, he, heR, heC⟩ := transport_integral (fun i j => A i j - ⌊A i j⌋)
    (fun i j => ⌈A i j⌉ - ⌊A i j⌋)
    (fun i j => by
      refine ⟨sub_nonneg.mpr (Int.floor_le _), ?_⟩
      push_cast
      linarith [Int.le_ceil (A i j)])
    (fun i => R i - ∑ j, ⌊A i j⌋) (fun j => C j - ∑ i, ⌊A i j⌋)
    (fun i => by push_cast; rw [Finset.sum_sub_distrib, hR])
    (fun j => by push_cast; rw [Finset.sum_sub_distrib, hC])
  refine ⟨fun i j => ⌊A i j⌋ + e i j, fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · have h1 := he i j
    have h2 := Int.ceil_le_floor_add_one (A i j)
    simp only at h1 ⊢
    omega
  · rw [Finset.sum_add_distrib, heR i]; ring
  · rw [Finset.sum_add_distrib, heC j]; ring

lemma floor_ceil_sub_self (x : ℝ) : ⌊(⌈x⌉ : ℝ) - x⌋ = 0 := by
  rw [sub_eq_add_neg, Int.floor_intCast_add, Int.floor_neg]; ring

lemma ceil_ceil_sub_self (x : ℝ) : ⌈(⌈x⌉ : ℝ) - x⌉ = ⌈x⌉ - ⌊x⌋ := by
  rw [sub_eq_add_neg, Int.ceil_intCast_add, Int.ceil_neg]; ring

lemma floor_sub_floor_self (x : ℝ) : ⌊x - ⌊x⌋⌋ = 0 := by
  rw [Int.floor_sub_intCast]; ring

lemma ceil_sub_floor_self (x : ℝ) : ⌈x - ⌊x⌋⌉ = ⌈x⌉ - ⌊x⌋ := by
  rw [Int.ceil_sub_intCast]

/-- **Baranyai's rounding lemma** for matrices indexed by arbitrary finite types. -/
theorem rounding_fintype (A : α → β → ℝ) :
    ∃ B : α → β → ℤ,
      (∀ i j, B i j = ⌊A i j⌋ ∨ B i j = ⌈A i j⌉) ∧
      (∀ i, ∑ j, B i j = ⌊∑ j, A i j⌋ ∨ ∑ j, B i j = ⌈∑ j, A i j⌉) ∧
      (∀ j, ∑ i, B i j = ⌊∑ i, A i j⌋ ∨ ∑ i, B i j = ⌈∑ i, A i j⌉) ∧
      (∑ i, ∑ j, B i j = ⌊∑ i, ∑ j, A i j⌋ ∨ ∑ i, ∑ j, B i j = ⌈∑ i, ∑ j, A i j⌉) := by
  set r : α → ℝ := fun i => ∑ j, A i j with hr
  set c : β → ℝ := fun j => ∑ i, A i j with hc
  set T : ℝ := ∑ i, ∑ j, A i j with hT
  have hTc : ∑ j, c j = T := by rw [hT, hc, Finset.sum_comm]
  have hTr : ∑ i, r i = T := rfl
  let A' : Option α → Option β → ℝ
    | some i, some j => A i j
    | some i, none => ⌈r i⌉ - r i
    | none, some j => ⌈c j⌉ - c j
    | none, none => T - ⌊T⌋
  let R' : Option α → ℤ
    | some i => ⌈r i⌉
    | none => ∑ j, ⌈c j⌉ - ⌊T⌋
  let C' : Option β → ℤ
    | some j => ⌈c j⌉
    | none => ∑ i, ⌈r i⌉ - ⌊T⌋
  obtain ⟨B', hB, hBR, hBC⟩ := round_integral_margins A' R' C'
    (by
      intro o
      rcases o with _ | i
      · simp only [Fintype.sum_option, A', R']
        push_cast
        rw [Finset.sum_sub_distrib, hTc]; ring
      · simp only [Fintype.sum_option, A', R']
        linarith [show r i = ∑ j, A i j from rfl])
    (by
      intro o
      rcases o with _ | j
      · simp only [Fintype.sum_option, A', C']
        push_cast
        rw [Finset.sum_sub_distrib, hTr]; ring
      · simp only [Fintype.sum_option, A', C']
        linarith [show c j = ∑ i, A i j from rfl])
  refine ⟨fun i j => B' (some i) (some j), fun i j => hB (some i) (some j), ?_, ?_, ?_⟩
  · intro i
    have h1 := hBR (some i)
    simp only [Fintype.sum_option, R'] at h1
    have h2 := hB (some i) none
    simp only [A', floor_ceil_sub_self, ceil_ceil_sub_self] at h2
    change ∑ j, B' (some i) (some j) = ⌊r i⌋ ∨ ∑ j, B' (some i) (some j) = ⌈r i⌉
    omega
  · intro j
    have h1 := hBC (some j)
    simp only [Fintype.sum_option, C'] at h1
    have h2 := hB none (some j)
    simp only [A', floor_ceil_sub_self, ceil_ceil_sub_self] at h2
    change ∑ i, B' (some i) (some j) = ⌊c j⌋ ∨ ∑ i, B' (some i) (some j) = ⌈c j⌉
    omega
  · have hrow : ∀ i, ∑ j, B' (some i) (some j) = ⌈r i⌉ - B' (some i) none := by
      intro i
      have h1 := hBR (some i)
      simp only [Fintype.sum_option, R'] at h1
      omega
    have h1 := hBC none
    simp only [Fintype.sum_option, C'] at h1
    have h2 := hB none none
    simp only [A', floor_sub_floor_self, ceil_sub_floor_self] at h2
    have h3 : ∑ i, ∑ j, B' (some i) (some j) = ∑ i, ⌈r i⌉ - ∑ i, B' (some i) none := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => hrow i
    change ∑ i, ∑ j, B' (some i) (some j) = ⌊T⌋ ∨ ∑ i, ∑ j, B' (some i) (some j) = ⌈T⌉
    omega

end Round

end Baranyai
