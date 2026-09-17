import Mathlib
import Erdos1110.Basic

namespace Erdos1110

noncomputable section
attribute [local instance] Classical.propDecidable

private def RectangleAntichain (s : Finset Point) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ CoordLe x y

private theorem projection_injective {s : Finset Point} (hs : RectangleAntichain s) :
    Set.InjOn Prod.fst (s : Set Point) ∧ Set.InjOn Prod.snd (s : Set Point) := by
  constructor
  · intro x hx y hy he
    by_contra hn
    rcases le_total x.2 y.2 with h | h
    · exact hs x hx y hy hn ⟨he.le, h⟩
    · exact hs y hy x hx (Ne.symm hn) ⟨he.ge, h⟩
  · intro x hx y hy he
    by_contra hn
    rcases le_total x.1 y.1 with h | h
    · exact hs x hx y hy hn ⟨h, he.le⟩
    · exact hs y hy x hx (Ne.symm hn) ⟨h, he.ge⟩

private theorem antichain_eq_of_projections {s t : Finset Point}
    (hs : RectangleAntichain s) (ht : RectangleAntichain t)
    (hf : s.image Prod.fst = t.image Prod.fst)
    (hg : s.image Prod.snd = t.image Prod.snd) : s = t := by
  classical
  have step : ∀ k : ℕ, ∀ x : Point, x.1 = k → (x ∈ s ↔ x ∈ t) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have direction : ∀ (u v : Finset Point),
          RectangleAntichain u → RectangleAntichain v →
          u.image Prod.fst = v.image Prod.fst →
          u.image Prod.snd = v.image Prod.snd →
          (∀ j < k, ∀ z : Point, z.1 = j → (z ∈ u ↔ z ∈ v)) →
          ∀ x : Point, x.1 = k → x ∈ u → x ∈ v := by
        intro u v hu hv hf hg hi x hxk hx
        have hxproj : x.1 ∈ v.image Prod.fst := by
          rw [← hf]
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
        obtain ⟨y, hy, hyf⟩ := Finset.mem_image.mp hxproj
        by_cases he : x = y
        · simpa [he] using hy
        have hneq : x.2 ≠ y.2 := by
          intro h
          exact he (Prod.ext hyf.symm h)
        rcases lt_or_gt_of_ne hneq with hxy | hyx
        · have hyp : y.2 ∈ u.image Prod.snd := by
            rw [hg]
            exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
          obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp hyp
          have hzf : z.1 < x.1 := by
            by_contra h
            exact hu x hx z hz (by intro e; simp_all) ⟨by omega, by omega⟩
          have hzv : z ∈ v := (hi z.1 (by omega) z rfl).mp hz
          have hzy := (projection_injective hv).2 hzv hy hzg
          subst z
          omega
        · have hxp : x.2 ∈ v.image Prod.snd := by
            rw [← hg]
            exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
          obtain ⟨z, hz, hzg⟩ := Finset.mem_image.mp hxp
          have hzf : z.1 < y.1 := by
            by_contra h
            exact hv y hy z hz (by intro e; simp_all) ⟨by omega, by omega⟩
          have hzu : z ∈ u := (hi z.1 (by omega) z rfl).mpr hz
          have hzx := (projection_injective hu).2 hzu hx hzg
          subst z
          omega
      intro x hx
      exact ⟨direction s t hs ht hf hg ih x hx,
        direction t s ht hs hf.symm hg.symm
          (fun j hj z hz => (ih j hj z hz).symm) x hx⟩
  exact Finset.ext (fun x => step x.1 x rfl)

private def antichainCode (A : ℕ) (s : Finset Point) : Finset ℕ :=
  (Finset.range A \ s.image Prod.fst) ∪ ((s.image Prod.snd).image (A + ·))

private theorem code_mem_low {A B i : ℕ} {s : Finset Point}
    (hs : ∀ x ∈ s, x.1 < A ∧ x.2 < B) (hi : i < A) :
    i ∈ antichainCode A s ↔ i ∉ s.image Prod.fst := by
  classical
  simp only [antichainCode, Finset.mem_union, Finset.mem_sdiff, Finset.mem_range,
    Finset.mem_image]
  constructor
  · rintro (⟨_, h⟩ | ⟨j, hj, he⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl ⟨hi, h⟩

private theorem code_mem_high {A B j : ℕ} {s : Finset Point}
    (hs : ∀ x ∈ s, x.1 < A ∧ x.2 < B) :
    A + j ∈ antichainCode A s ↔ j ∈ s.image Prod.snd := by
  classical
  simp [antichainCode, Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]

private theorem code_injective {A B : ℕ} {s t : Finset Point}
    (hs : RectangleAntichain s) (ht : RectangleAntichain t)
    (hbs : ∀ x ∈ s, x.1 < A ∧ x.2 < B)
    (hbt : ∀ x ∈ t, x.1 < A ∧ x.2 < B)
    (he : antichainCode A s = antichainCode A t) : s = t := by
  classical
  apply antichain_eq_of_projections hs ht
  · ext i
    by_cases hi : i < A
    · have hh := iff_of_eq (congrArg (fun c => i ∈ c) he)
      simpa only [code_mem_low hbs hi, code_mem_low hbt hi, not_iff_not] using hh
    · constructor <;> intro h
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
        exact False.elim (hi (hbs x hx).1)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
        exact False.elim (hi (hbt x hx).1)
  · ext j
    have hh := iff_of_eq (congrArg (fun c => A + j ∈ c) he)
    simpa only [code_mem_high hbs, code_mem_high hbt] using hh

private theorem code_mem_powerset {A B : ℕ} {s : Finset Point}
    (hs : RectangleAntichain s)
    (hb : ∀ x ∈ s, x.1 < A ∧ x.2 < B) :
    antichainCode A s ∈ (Finset.range (A + B)).powersetCard A := by
  classical
  have hf : s.image Prod.fst ⊆ Finset.range A := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hb x hx).1
  have hd : Disjoint (Finset.range A \ s.image Prod.fst)
      ((s.image Prod.snd).image (A + ·)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hil := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hj
    omega
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have hil := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (by have := (hb x hx).2; omega)
  · rw [antichainCode, Finset.card_union_of_disjoint hd,
      Finset.card_sdiff_of_subset hf, Finset.card_range,
      Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
      Finset.card_image_of_injOn (projection_injective hs).1,
      Finset.card_image_of_injOn (projection_injective hs).2]
    have hc : s.card ≤ A := by
      simpa [Finset.card_image_of_injOn (projection_injective hs).1] using
        Finset.card_le_card hf
    omega

private theorem sum_toFinset_terms {p q : ℕ} {L : List Point}
    (hL : L.Nodup) : ∑ x ∈ L.toFinset, Term p q x = SumTerms p q L := by
  classical
  induction L with
  | nil => simp [SumTerms]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hL
    simpa [SumTerms, hx, List.mem_toFinset] using
      congrArg (Term p q x + ·) (ih hxs)

theorem representable_count_le {p q n A B : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hnp : n ≤ p ^ A) (hnq : n ≤ q ^ B) :
    ((Finset.range n).filter (fun m => Representable p q m)).card ≤
      Nat.choose (A + B) A := by
  classical
  let R := (Finset.range n).filter (fun m => Representable p q m)
  have repr (m : R) : ∃ L : List Point, IsAntichain L ∧ SumTerms p q L = m :=
    (Finset.mem_filter.mp m.property).2
  let L (m : R) : List Point := Classical.choose (repr m)
  have hl (m : R) : IsAntichain (L m) ∧ SumTerms p q (L m) = m :=
    Classical.choose_spec (repr m)
  let S (m : R) : Finset Point := (L m).toFinset
  have ha (m : R) : RectangleAntichain (S m) := by
    intro x hx y hy hn
    exact (hl m).1.2 (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hn
  have hb (m : R) : ∀ x ∈ S m, x.1 < A ∧ x.2 < B := by
    intro x hx
    have ht : Term p q x ≤ m := by
      rw [← (hl m).2]
      exact mem_term_le_sum (List.mem_toFinset.mp hx)
    have hm : (m : ℕ) < n := Finset.mem_range.mp (Finset.mem_filter.mp m.property).1
    have hp0 : 0 < p := by omega
    have hq0 : 0 < q := by omega
    have hpp : 0 < p ^ x.1 := Nat.pow_pos hp0
    have hqq : 0 < q ^ x.2 := Nat.pow_pos hq0
    have hpterm : p ^ x.1 ≤ Term p q x := by
      dsimp [Term]
      nlinarith
    have hqterm : q ^ x.2 ≤ Term p q x := by
      dsimp [Term]
      nlinarith
    constructor
    · by_contra h
      have he := Nat.pow_le_pow_right hp0 (show A ≤ x.1 by omega)
      omega
    · by_contra h
      have he := Nat.pow_le_pow_right hq0 (show B ≤ x.2 by omega)
      omega
  let C := (Finset.range (A + B)).powersetCard A
  let f : R → C := fun m => ⟨antichainCode A (S m), code_mem_powerset (ha m) (hb m)⟩
  have hinj : Function.Injective f := by
    intro m k he
    have hs : S m = S k :=
      code_injective (ha m) (ha k) (hb m) (hb k) (congrArg Subtype.val he)
    apply Subtype.ext
    calc
      (m : ℕ) = ∑ x ∈ S m, Term p q x :=
        (hl m).2.symm.trans (sum_toFinset_terms (hl m).1.1).symm
      _ = ∑ x ∈ S k, Term p q x := by rw [hs]
      _ = (k : ℕ) := (sum_toFinset_terms (hl k).1.1).trans (hl k).2
  have hc : R.card ≤ C.card := Finset.card_le_card_of_injective hinj
  simpa [R, C] using hc

end
end Erdos1110
