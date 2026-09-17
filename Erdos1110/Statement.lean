/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Erdos1110.Providers
import Mathlib

namespace Erdos1110

/-- The natural-valued formulation from Formal Conjectures, Erdős Problem 1110.
The displayed set is exactly `Erdos246.Gamma p q` in that repository.
Source: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1110.lean -/
def PrimitiveRepresentable (p q n : ℕ) : Prop :=
  ∃ s : Finset ℕ,
    (s : Set ℕ) ⊆ {x | ∃ k l : ℕ, x = p ^ k * q ^ l} ∧
    _root_.IsAntichain (· ∣ ·) (s : Set ℕ) ∧
    s.sum id = n

private theorem term_injective_of_validBases {p q : ℕ} (hb : ValidBases p q) :
    Function.Injective (Term p q) := by
  intro x y h
  have hxy := term_dvd_coordLe hb.one_lt_p hb.one_lt_q hb.coprime
    (show Term p q x ∣ Term p q y from h ▸ dvd_refl _)
  have hyx := term_dvd_coordLe hb.one_lt_p hb.one_lt_q hb.coprime
    (show Term p q y ∣ Term p q x from h ▸ dvd_refl _)
  exact Prod.ext (Nat.le_antisymm hxy.1 hyx.1) (Nat.le_antisymm hxy.2 hyx.2)

theorem primitiveRepresentable_iff {p q n : ℕ} (hb : ValidBases p q) :
    PrimitiveRepresentable p q n ↔ Representable p q n := by
  classical
  constructor
  · rintro ⟨s, hs, ha, hn⟩
    have hex : ∀ m, m ∈ s → ∃ x : Point, Term p q x = m := by
      intro m hm
      rcases hs hm with ⟨k, l, h⟩
      exact ⟨(k, l), h.symm⟩
    let g : ℕ → Point := fun m => if h : m ∈ s then (hex m h).choose else (0, 0)
    have hg : ∀ m, m ∈ s → Term p q (g m) = m := by
      intro m hm
      simp only [g, dif_pos hm]
      exact (hex m hm).choose_spec
    have hginj : ∀ ⦃a⦄, a ∈ s.toList → ∀ ⦃b⦄, b ∈ s.toList → g a = g b → a = b := by
      intro a ha b hb hab
      have hga := hg a (Finset.mem_toList.mp ha)
      have hgb := hg b (Finset.mem_toList.mp hb)
      rw [hab] at hga
      exact hga.symm.trans hgb
    refine ⟨s.toList.map g, ⟨nodup_map_of_injective_on hginj s.nodup_toList, ?_⟩, ?_⟩
    · intro x hx y hy hne hcoord
      rcases List.mem_map.mp hx with ⟨a, ha', rfl⟩
      rcases List.mem_map.mp hy with ⟨b, hb', rfl⟩
      have haS := Finset.mem_toList.mp ha'
      have hbS := Finset.mem_toList.mp hb'
      have hab : a ≠ b := fun h => hne (congrArg g h)
      apply ha haS hbS hab
      simpa only [hg a haS, hg b hbS] using coordLe_term_dvd (p := p) (q := q) hcoord
    · have hmap : (s.toList.map g).map (Term p q) = s.toList := by
        rw [List.map_map]
        calc
          s.toList.map (Term p q ∘ g) = s.toList.map id := by
            apply List.map_congr_left
            intro m hm
            exact hg m (Finset.mem_toList.mp hm)
          _ = s.toList := List.map_id _
      change ((s.toList.map g).map (Term p q)).sum = n
      rw [hmap]
      have hsum : s.sum id = s.toList.sum := by
        simpa using List.sum_toFinset id s.nodup_toList
      exact hsum.symm.trans hn
  · rintro ⟨A, hA, hn⟩
    let l := A.map (Term p q)
    have hinj := term_injective_of_validBases hb
    have hl : l.Nodup := nodup_map_of_injective_on (fun _ _ _ _ h => hinj h) hA.1
    refine ⟨l.toFinset, ?_, ?_, ?_⟩
    · intro m hm
      rcases List.mem_map.mp (List.mem_toFinset.mp hm) with ⟨x, hx, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · intro a ha b hb' hab hdiv
      rcases List.mem_map.mp (List.mem_toFinset.mp ha) with ⟨x, hx, rfl⟩
      rcases List.mem_map.mp (List.mem_toFinset.mp hb') with ⟨y, hy, rfl⟩
      exact hA.2 hx hy (fun h => hab (congrArg (Term p q) h))
        (term_dvd_coordLe hb.one_lt_p hb.one_lt_q hb.coprime hdiv)
    · have hsum : l.toFinset.sum id = l.sum := by
        simpa using List.sum_toFinset id hl
      exact hsum.trans hn

/-- Convert the constructed sequence to the infinite-set formulation used by
Formal Conjectures, without strengthening the hypotheses on the bases. -/
theorem primitiveConclusion_of_conclusion {p q : ℕ} (hb : ValidBases p q)
    (h : Erdos1110Conclusion p q) :
    ∃ A : Set ℕ, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ PrimitiveRepresentable p q n := by
  rcases h with ⟨f, hf⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hc := hf.2 hne
    have hone : f j = 1 := by
      simpa [hij, Nat.Coprime] using hc
    have hgt := (hf.1 j).1
    omega
  refine ⟨Set.range f, Set.infinite_range_of_injective hinj, ?_, ?_⟩
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hne
    exact hf.2 (fun h => hne (congrArg f h))
  · rintro n ⟨i, rfl⟩ hn
    exact (hf.1 i).2.1 ((primitiveRepresentable_iff hb).mp hn)

end Erdos1110
