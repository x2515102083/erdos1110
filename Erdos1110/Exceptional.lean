import Erdos1110.Amplification

/-!
# Exceptional seed certificates
-/

namespace Erdos1110

theorem corrected_embedding_bound_for_examples :
    (5 ^ 2 < 2 ^ 5 ∧ 3 * 2 ^ 5 < 4 * 5 ^ 2) ∧
    (9 ^ 2 < 2 ^ 7 ∧ 5 * 2 ^ 7 < 8 * 9 ^ 2) ∧
    (5 < 3 ^ 2 ∧ 3 ^ 2 < 2 * 5) := by
  decide

theorem supplied_embedding_bound_is_false_for_5_2 :
    ¬ (5 ^ 2 < 2 ^ 5 ∧ 4 * 2 ^ 5 < 3 * 5 ^ 2) := by
  decide

theorem supplied_embedding_bound_is_false_for_9_2 :
    ¬ (9 ^ 2 < 2 ^ 7 ∧ 8 * 2 ^ 7 < 5 * 9 ^ 2) := by
  decide

private theorem one_le_of_pos {n : Nat} (h : 0 < n) : 1 ≤ n :=
  h

private theorem first_coord_zero_of_small_term
    {p q c : Nat} {x : Point}
    (hp : 1 < p)
    (hq : 0 < q)
    (hcp : c < p)
    (hterm : Term p q x ≤ c) :
    x.1 = 0 := by
  by_cases hxzero : x.1 = 0
  · exact hxzero
  have hxpos : 0 < x.1 := Nat.pos_of_ne_zero hxzero
  have hile : 1 ≤ x.1 := one_le_of_pos hxpos
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hp_le_pow : p ≤ p ^ x.1 := by
    simpa using Nat.pow_le_pow_right hp_pos hile
  have hqpow_pos : 0 < q ^ x.2 := (Nat.pow_pos hq : 0 < q ^ x.2)
  have hp_le_term : p ≤ Term p q x := by
    exact Nat.le_trans hp_le_pow (Nat.le_mul_of_pos_right _ hqpow_pos)
  exact False.elim ((Nat.not_le_of_gt hcp) (Nat.le_trans hp_le_term hterm))

private theorem second_point_contradiction
    {A_tail : List Point} {x y : Point}
    (hanti : IsAntichain (x :: y :: A_tail))
    (hx0 : x.1 = 0)
    (hy0 : y.1 = 0) :
    False := by
  have hnodup : (x :: y :: A_tail).Nodup := hanti.1
  have hx_not_mem_tail : ¬ x ∈ y :: A_tail := (List.nodup_cons.mp hnodup).1
  have hxy_ne : x ≠ y := by
    intro hxy
    exact hx_not_mem_tail (by rw [hxy]; exact List.mem_cons_self)
  have hle_or : x.2 ≤ y.2 ∨ y.2 ≤ x.2 := Nat.le_total x.2 y.2
  cases hle_or with
  | inl hxy2 =>
      have hcoord : CoordLe x y := by
        constructor
        · rw [hx0, hy0]
          exact Nat.le_refl 0
        · exact hxy2
      exact hanti.2 List.mem_cons_self
        (List.mem_cons_of_mem x List.mem_cons_self) hxy_ne hcoord
  | inr hyx2 =>
      have hcoord : CoordLe y x := by
        constructor
        · rw [hx0, hy0]
          exact Nat.le_refl 0
        · exact hyx2
      exact hanti.2 (List.mem_cons_of_mem x List.mem_cons_self)
        List.mem_cons_self (fun hyx => hxy_ne hyx.symm) hcoord

theorem c_lt_p_and_not_q_power_nonrepresentable
    {p q c : Nat}
    (hp : 1 < p)
    (hq : 0 < q)
    (hcpos : 0 < c)
    (hcp : c < p)
    (hnotpow : ∀ j : Nat, c ≠ q ^ j) :
    Nonrepresentable p q c := by
  intro hrepr
  rcases hrepr with ⟨A, hA, hsum⟩
  cases A with
  | nil =>
      change 0 = c at hsum
      exact Nat.ne_of_gt hcpos hsum.symm
  | cons x xs =>
      have hx_mem : x ∈ x :: xs := List.mem_cons_self
      have hx_le_c : Term p q x ≤ c := by
        rw [← hsum]
        exact mem_term_le_sum hx_mem
      have hx0 : x.1 = 0 := first_coord_zero_of_small_term hp hq hcp hx_le_c
      cases xs with
      | nil =>
          change Term p q x = c at hsum
          have : c = q ^ x.2 := by
            rw [← hsum]
            dsimp [Term]
            rw [hx0]
            simp
          exact hnotpow x.2 this
      | cons y ys =>
          have hy_mem : y ∈ x :: y :: ys :=
            List.mem_cons_of_mem x List.mem_cons_self
          have hy_le_c : Term p q y ≤ c := by
            rw [← hsum]
            exact mem_term_le_sum hy_mem
          have hy0 : y.1 = 0 := first_coord_zero_of_small_term hp hq hcp hy_le_c
          exact second_point_contradiction hA hx0 hy0

private theorem two_pow_ne_three : ∀ j : Nat, 3 ≠ 2 ^ j
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      intro h
      have hle : 4 ≤ 2 ^ (n + 2) := by
        have hpow : 2 ^ 2 ≤ 2 ^ (n + 2) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by simp : 2 ≤ n + 2)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 4 ≤ 3) hle

private theorem two_pow_ne_five : ∀ j : Nat, 5 ≠ 2 ^ j
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
      intro h
      have hle : 8 ≤ 2 ^ (n + 3) := by
        have hpow : 2 ^ 3 ≤ 2 ^ (n + 3) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by simp : 3 ≤ n + 3)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 8 ≤ 5) hle

private theorem three_pow_ne_two : ∀ j : Nat, 2 ≠ 3 ^ j
  | 0 => by decide
  | n + 1 => by
      intro h
      have hle : 3 ≤ 3 ^ (n + 1) := by
        have hpow : 3 ^ 1 ≤ 3 ^ (n + 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 3) (by simp : 1 ≤ n + 1)
        simpa using hpow
      rw [← h] at hle
      exact (by decide : ¬ 3 ≤ 2) hle

theorem c3_nonrepresentable_5_2 : Nonrepresentable 5 2 3 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact two_pow_ne_three

theorem c5_nonrepresentable_9_2 : Nonrepresentable 9 2 5 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact two_pow_ne_five

theorem c2_nonrepresentable_5_3 : Nonrepresentable 5 3 2 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
  · decide
  · decide
  · decide
  · decide
  · exact three_pow_ne_two

theorem support_4_within_10 : SupportCoprimeWithin 4 10 := by
  intro D hD
  have hD10 : Nat.Coprime D (2 * 5) := by simpa using hD
  have hD2 : Nat.Coprime D 2 := (Nat.coprime_mul_iff_right.mp hD10).1
  have h2D : Nat.Coprime 2 D := Nat.Coprime.symm hD2
  simpa using h2D.pow_left 2

theorem support_6_within_18 : SupportCoprimeWithin 6 18 := by
  intro D hD
  have hD6 : Nat.Coprime D 6 := by
    have h : Nat.Coprime D (6 * 3) := by simpa using hD
    exact (Nat.coprime_mul_iff_right.mp h).1
  exact Nat.Coprime.symm hD6

theorem support_3_within_15 : SupportCoprimeWithin 3 15 := by
  intro D hD
  have hD3 : Nat.Coprime D 3 := by
    have h : Nat.Coprime D (3 * 5) := by simpa using hD
    exact (Nat.coprime_mul_iff_right.mp h).1
  exact Nat.Coprime.symm hD3

theorem validBases_5_2 : ValidBases 5 2 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem validBases_9_2 : ValidBases 9 2 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem validBases_5_3 : ValidBases 5 3 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem seed_5_2 : GoodSeed 5 2 3 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c3_nonrepresentable_5_2
  coprime_pq := by decide
  support_succ := by simpa using support_4_within_10

theorem seed_9_2 : GoodSeed 9 2 5 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c5_nonrepresentable_9_2
  coprime_pq := by decide
  support_succ := by simpa using support_6_within_18

theorem seed_5_3 : GoodSeed 5 3 2 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c2_nonrepresentable_5_3
  coprime_pq := by decide
  support_succ := by simpa using support_3_within_15

theorem exceptional_5_2_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  amplify validBases_5_2 seed_5_2

theorem exceptional_9_2_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  amplify validBases_9_2 seed_9_2

theorem exceptional_5_3_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  amplify validBases_5_3 seed_5_3

theorem exceptional_cases_from_goodSeed_amplification
    (amplify : GoodSeedAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) := by
  exact ⟨exceptional_5_2_from_goodSeed_amplification amplify,
    exceptional_9_2_from_goodSeed_amplification amplify,
    exceptional_5_3_from_goodSeed_amplification amplify⟩

theorem exceptional_5_2_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_9_2_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_5_3_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_cases_from_freshExtension_amplification
    (freshAmp : FreshExtensionAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_freshExtensionAmplification freshAmp)

theorem exceptional_5_2_from_period_window
    (period : PeriodProvider 5 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_5_2 seed_5_2 period window
    (embeddingProvider_core validBases_5_2 seed_5_2)

theorem exceptional_9_2_from_period_window
    (period : PeriodProvider 9 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_9_2 seed_9_2 period window
    (embeddingProvider_core validBases_9_2 seed_9_2)

theorem exceptional_5_3_from_period_window
    (period : PeriodProvider 5 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  goodSeedAmplification_of_period_window_embedding
    validBases_5_3 seed_5_3 period window
    (embeddingProvider_core validBases_5_3 seed_5_3)

theorem exceptional_cases_from_period_window
    (period_5_2 : PeriodProvider 5 2)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (period_9_2 : PeriodProvider 9 2)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (period_5_3 : PeriodProvider 5 3)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_period_window period_5_2 window_5_2,
    exceptional_9_2_from_period_window period_9_2 window_9_2,
    exceptional_5_3_from_period_window period_5_3 window_5_3⟩

theorem exceptional_5_2_from_basic_period_window
    (period : BasicPeriodProvider 5 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_9_2_from_basic_period_window
    (period : BasicPeriodProvider 9 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_5_3_from_basic_period_window
    (period : BasicPeriodProvider 5 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_basicPeriodProvider period) window

theorem exceptional_cases_from_basic_period_window
    (period_5_2 : BasicPeriodProvider 5 2)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (period_9_2 : BasicPeriodProvider 9 2)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (period_5_3 : BasicPeriodProvider 5 3)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_basic_period_window period_5_2 window_5_2,
    exceptional_9_2_from_basic_period_window period_9_2 window_9_2,
    exceptional_5_3_from_basic_period_window period_5_3 window_5_3⟩

theorem exceptional_5_2_from_base_period_window
    (period5 : CoprimeBasePeriodProvider 5)
    (period2 : CoprimeBasePeriodProvider 2)
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period5 period2) window

theorem exceptional_9_2_from_base_period_window
    (period9 : CoprimeBasePeriodProvider 9)
    (period2 : CoprimeBasePeriodProvider 2)
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period9 period2) window

theorem exceptional_5_3_from_base_period_window
    (period5 : CoprimeBasePeriodProvider 5)
    (period3 : CoprimeBasePeriodProvider 3)
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_coprimeBasePeriodProviders period5 period3) window

theorem exceptional_cases_from_base_period_window
    (period2 : CoprimeBasePeriodProvider 2)
    (period3 : CoprimeBasePeriodProvider 3)
    (period5 : CoprimeBasePeriodProvider 5)
    (period9 : CoprimeBasePeriodProvider 9)
    (window_5_2 : PowerWindowProvider 5 2 3)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_base_period_window period5 period2 window_5_2,
    exceptional_9_2_from_base_period_window period9 period2 window_9_2,
    exceptional_5_3_from_base_period_window period5 period3 window_5_3⟩

theorem exceptional_5_2_from_window
    (window : PowerWindowProvider 5 2 3) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_period_window
    (periodProvider_of_pos (p := 5) (q := 2) (by decide) (by decide))
    window

theorem exceptional_9_2_from_window
    (window : PowerWindowProvider 9 2 5) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_period_window
    (periodProvider_of_pos (p := 9) (q := 2) (by decide) (by decide))
    window

theorem exceptional_5_3_from_window
    (window : PowerWindowProvider 5 3 2) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_period_window
    (periodProvider_of_pos (p := 5) (q := 3) (by decide) (by decide))
    window

theorem exceptional_cases_from_window
    (window_5_2 : PowerWindowProvider 5 2 3)
    (window_9_2 : PowerWindowProvider 9 2 5)
    (window_5_3 : PowerWindowProvider 5 3 2) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  ⟨exceptional_5_2_from_window window_5_2,
    exceptional_9_2_from_window window_9_2,
    exceptional_5_3_from_window window_5_3⟩

theorem exceptional_cases_from_window_amplification
    (amp : WindowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_windowAmplification amp)

theorem exceptional_cases_from_periodWindow_amplification
    (amp : PeriodWindowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_periodWindowAmplification amp)

theorem exceptional_cases_from_periodWindowLowRow_amplification
    (amp : PeriodWindowLowRowAmplification) :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_goodSeed_amplification
    (goodSeedAmplification_of_periodWindowLowRowAmplification amp)

end Erdos1110
