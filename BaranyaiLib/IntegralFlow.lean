/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import FlowLib.MaxFlowMinCut

/-!
# Integral maximum flows

For a network with integer capacities there is an integer-valued flow of maximum value
(Ford–Fulkerson with unit augmentations).
-/

@[expose] public section

namespace Baranyai

open Contrib.MaxFlowMinCut Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Unit augmentation of an integral flow that still has an augmenting path. -/
theorem integral_augment {Net : Network N} (c : N → N → ℤ)
    (hc : ∀ u v, Net.cap u v = c u v) (F : Flow Net) (g : N → N → ℤ)
    (hg : ∀ u v, F.f u v = g u v) (hreach : Reaches Net F Net.t) :
    ∃ (F' : Flow Net) (g' : N → N → ℤ), (∀ u v, F'.f u v = g' u v) ∧
      F'.value = F.value + 1 := by
  obtain ⟨P, δ, hδ, hres, hanti, hbal⟩ := augEdges_exists F hreach
  set push : N → N → ℤ :=
    fun u v => (if (u, v) ∈ P then 1 else 0) - (if (v, u) ∈ P then 1 else 0) with hpush
  have hrowsum : ∀ u, ∑ v, (push u v : ℝ)
      = (if u = Net.s then 1 else 0) - (if u = Net.t then 1 else 0) := by
    intro u
    simp only [hpush]
    push_cast
    rw [Finset.sum_sub_distrib]
    exact hbal u
  have cap' : ∀ u v, F.f u v + push u v ≤ Net.cap u v := by
    intro u v
    rw [hg, hc]
    simp only [hpush]
    by_cases huv : (u, v) ∈ P
    · have hvu : (v, u) ∉ P := hanti u v huv
      simp only [huv, hvu, ite_true, ite_false]
      have h1 := hres (u, v) huv
      simp only at h1
      rw [hg, hc] at h1
      have h2 : (0 : ℝ) < ((c u v - g u v : ℤ) : ℝ) := by push_cast; linarith
      have h3 : (0 : ℤ) < c u v - g u v := by exact_mod_cast h2
      exact_mod_cast (by push_cast; omega : g u v + ((1 : ℤ) - 0) ≤ c u v)
    · have hle : F.f u v ≤ Net.cap u v := F.capacitated u v
      rw [hg, hc] at hle
      have hle' : g u v ≤ c u v := by exact_mod_cast hle
      by_cases hvu : (v, u) ∈ P
      · simp only [huv, hvu, ite_true, ite_false]
        exact_mod_cast (by omega : g u v + ((0 : ℤ) - 1) ≤ c u v)
      · simp only [huv, hvu, ite_false]
        exact_mod_cast (by omega : g u v + ((0 : ℤ) - 0) ≤ c u v)
  have cons' : ∀ u, u ≠ Net.s → u ≠ Net.t → ∑ v, (F.f u v + push u v) = 0 := by
    intro u hus hut
    rw [Finset.sum_add_distrib, F.conserved u hus hut, hrowsum u]
    simp [hus, hut]
  let F' : Flow Net :=
    { f := fun u v => F.f u v + push u v
      skew := by
        intro u v; rw [F.skew u v]; simp only [hpush]; push_cast; ring
      capacitated := cap'
      conserved := cons' }
  refine ⟨F', fun u v => g u v + push u v, fun u v => ?_, ?_⟩
  · change F.f u v + (push u v : ℝ) = _
    rw [hg]; push_cast; ring
  · change ∑ v, (F.f Net.s v + (push Net.s v : ℝ)) = F.value + 1
    rw [Finset.sum_add_distrib, hrowsum Net.s, ite_eq_left rfl, ite_eq_right Net.st]
    simp only [Flow.value]
    ring

/-- **Integrality of maximum flows.** A network with integer capacities has an integer-valued
flow whose value is at least that of every flow. -/
theorem exists_integral_maxflow (Net : Network N) (c : N → N → ℤ)
    (hc : ∀ u v, Net.cap u v = c u v) :
    ∃ (F : Flow Net) (g : N → N → ℤ), (∀ u v, F.f u v = g u v) ∧
      ∀ F' : Flow Net, F'.value ≤ F.value := by
  classical
  let C0 : Cut Net := ⟨{Net.s}, by simp, by simp [Net.st.symm]⟩
  let Pr : ℤ → Prop := fun z =>
    ∃ (F : Flow Net) (g : N → N → ℤ), (∀ u v, F.f u v = g u v) ∧ F.value = z
  have hbdd : ∃ ub : ℤ, ∀ z, Pr z → z ≤ ub := by
    refine ⟨⌈C0.capacity⌉, fun z ⟨F, g, _, hv⟩ => ?_⟩
    have := value_le_capacity F C0
    rw [hv] at this
    exact Int.cast_le.mp (this.trans (Int.le_ceil _))
  have hex : ∃ z, Pr z := by
    refine ⟨0, ⟨fun _ _ => 0, fun _ _ => by simp, fun u v => by simpa using Net.capNonneg u v,
      fun _ _ _ => by simp⟩, fun _ _ => 0, fun _ _ => by simp, ?_⟩
    simp [Flow.value]
  obtain ⟨z0, ⟨F, g, hg, hv⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hex
  refine ⟨F, g, hg, ?_⟩
  have ht : Net.t ∉ reachableSet F := by
    rw [mem_reachableSet]
    intro hreach
    obtain ⟨F', g', hg', hv'⟩ := integral_augment c hc F g hg hreach
    have h1 := hmax (z0 + 1) ⟨F', g', hg', by rw [hv', hv]; push_cast; ring⟩
    omega
  have hs : Net.s ∈ reachableSet F := by
    rw [mem_reachableSet]; exact Relation.ReflTransGen.refl
  have hval := saturated_cut_value F (reachableSet F) hs ht
    (fun u hu v hv => reachable_saturates F hu hv)
  intro F'
  rw [hval]
  exact value_le_capacity F' _

end Baranyai
