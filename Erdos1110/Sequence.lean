import Erdos1110.Period
import Erdos1110.Embedding

/-!
# Infinite sequence construction and amplification bridges
-/

namespace Erdos1110

abbrev PQCoprimeState (p q : Nat) :=
  {D : Nat // Nat.Coprime D (p * q)}

noncomputable def nextFresh
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) : Nat :=
  Classical.choose (fresh D.1 D.2)

theorem nextFresh_spec
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    FreshExtension p q D.1 (nextFresh fresh D) :=
  Classical.choose_spec (fresh D.1 D.2)

theorem coprime_of_eq_seed_succ_add_mul
    {p q c D N k : Nat}
    (hs : GoodSeed p q c)
    (hD : Nat.Coprime D (p * q))
    (hN : N = (c + 1) + D * k) :
    Nat.Coprime N D := by
  have hseedD : Nat.Coprime (c + 1) D := hs.support_succ D hD
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [hN]
  rw [Nat.gcd_add_mul_left_left]
  exact Nat.Coprime.gcd_eq_one hseedD

theorem freshExtensionProvider_of_congruentExtensionProvider
    {p q c : Nat}
    (hs : GoodSeed p q c)
    (provider : CongruentExtensionProvider p q c) :
    FreshExtensionProvider p q c := by
  intro D hD
  rcases provider D hD with ⟨N, hN⟩
  rcases hN with ⟨hgt, hnrep, hcop_pq, k, hcong⟩
  exact ⟨N, hgt, hnrep, hcop_pq,
    coprime_of_eq_seed_succ_add_mul hs hD hcong⟩

theorem congruentExtensionProvider_of_period_window_embedding
    {p q c : Nat}
    (hb : ValidBases p q)
    (period : PeriodProvider p q)
    (window : PowerWindowProvider p q c)
    (embed : EmbeddingProvider p q c) :
    CongruentExtensionProvider p q c := by
  intro D hD
  rcases period D hD with ⟨L, hLpos, hp_period, hq_period⟩
  rcases window L hLpos with
    ⟨a, M, ha_pos, hM_pos, hLa, hLM, hleft, hright⟩
  let N := p ^ a + c * q ^ M
  have hemb := embed a M ha_pos hM_pos hleft hright
  rcases hp_period a hLa with ⟨rp, hp_cong⟩
  rcases hq_period M hLM with ⟨rq, hq_cong⟩
  refine ⟨N, ?_, ?_, ?_, rp + c * rq, ?_⟩
  · dsimp [N]
    have hpowa : 1 < p ^ a := Nat.one_lt_pow (Nat.ne_of_gt ha_pos) hb.one_lt_p
    exact Nat.lt_add_right (c * q ^ M) hpowa
  · simpa [N] using hemb.1
  · simpa [N] using hemb.2
  · dsimp [N]
    rw [hp_cong, hq_cong]
    simp [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]
    ac_rfl

theorem nextFresh_gt_one
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    1 < nextFresh fresh D :=
  (nextFresh_spec fresh D).1

theorem nextFresh_nonrep
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nonrepresentable p q (nextFresh fresh D) :=
  (nextFresh_spec fresh D).2.1

theorem nextFresh_coprime_pq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nat.Coprime (nextFresh fresh D) (p * q) :=
  (nextFresh_spec fresh D).2.2.1

theorem nextFresh_coprime_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (D : PQCoprimeState p q) :
    Nat.Coprime (nextFresh fresh D) D.1 :=
  (nextFresh_spec fresh D).2.2.2

noncomputable def states
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    Nat → PQCoprimeState p q
  | 0 => ⟨1, Nat.coprime_one_left (p * q)⟩
  | n + 1 =>
      let D := states fresh n
      let N := nextFresh fresh D
      ⟨D.1 * N, Nat.Coprime.mul_left D.2 (nextFresh_coprime_pq fresh D)⟩

noncomputable def nonrepSeq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) : Nat :=
  nextFresh fresh (states fresh n)

theorem nonrepSeq_gt_one
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    1 < nonrepSeq fresh n :=
  nextFresh_gt_one fresh (states fresh n)

theorem nonrepSeq_nonrep
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nonrepresentable p q (nonrepSeq fresh n) :=
  nextFresh_nonrep fresh (states fresh n)

theorem nonrepSeq_coprime_pq
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nat.Coprime (nonrepSeq fresh n) (p * q) :=
  nextFresh_coprime_pq fresh (states fresh n)

theorem nonrepSeq_coprime_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    Nat.Coprime (nonrepSeq fresh n) (states fresh n).1 :=
  nextFresh_coprime_state fresh (states fresh n)

theorem state_succ_val
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    (states fresh (n + 1)).1 = (states fresh n).1 * nonrepSeq fresh n := by
  rfl

theorem seq_dvd_state_succ
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    nonrepSeq fresh n ∣ (states fresh (n + 1)).1 := by
  rw [state_succ_val]
  exact Nat.dvd_mul_left _ _

theorem state_dvd_state_succ
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c)
    (n : Nat) :
    (states fresh n).1 ∣ (states fresh (n + 1)).1 := by
  rw [state_succ_val]
  exact Nat.dvd_mul_right _ _

theorem seq_dvd_later_state
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∀ {m n : Nat}, m < n → nonrepSeq fresh m ∣ (states fresh n).1
  | m, 0, h => False.elim ((Nat.not_lt_zero m) h)
  | m, n + 1, h => by
      have hmle : m ≤ n := Nat.le_of_lt_succ h
      cases Nat.lt_or_eq_of_le hmle with
      | inl hmn =>
          have hdiv : nonrepSeq fresh m ∣ (states fresh n).1 :=
            seq_dvd_later_state fresh hmn
          exact Nat.dvd_trans hdiv (state_dvd_state_succ fresh n)
      | inr hmn =>
          subst m
          exact seq_dvd_state_succ fresh n

theorem nonrepSeq_pairwise_coprime
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∀ ⦃m n : Nat⦄, m ≠ n → Nat.Coprime (nonrepSeq fresh m) (nonrepSeq fresh n) := by
  intro m n hne
  cases Nat.lt_or_ge m n with
  | inl hmn =>
      have hdiv : nonrepSeq fresh m ∣ (states fresh n).1 :=
        seq_dvd_later_state fresh hmn
      have hcop : Nat.Coprime (nonrepSeq fresh n) (states fresh n).1 :=
        nonrepSeq_coprime_state fresh n
      exact Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right hdiv hcop)
  | inr hge =>
      have hnm : n < m := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
      have hdiv : nonrepSeq fresh n ∣ (states fresh m).1 :=
        seq_dvd_later_state fresh hnm
      have hcop : Nat.Coprime (nonrepSeq fresh m) (states fresh m).1 :=
        nonrepSeq_coprime_state fresh m
      exact Nat.Coprime.coprime_dvd_right hdiv hcop

theorem infinite_pairwise_nonrep_of_freshExtensionProvider
    {p q c : Nat}
    (fresh : FreshExtensionProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f := by
  refine ⟨nonrepSeq fresh, ?_, ?_⟩
  · intro n
    exact ⟨nonrepSeq_gt_one fresh n, nonrepSeq_nonrep fresh n,
      nonrepSeq_coprime_pq fresh n⟩
  · exact nonrepSeq_pairwise_coprime fresh

theorem goodSeedAmplification_of_congruentExtensionProvider
    {p q c : Nat}
    (_hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (provider : CongruentExtensionProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  infinite_pairwise_nonrep_of_freshExtensionProvider
    (freshExtensionProvider_of_congruentExtensionProvider hs provider)

theorem goodSeedAmplification_of_period_window_embedding
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (period : PeriodProvider p q)
    (window : PowerWindowProvider p q c)
    (embed : EmbeddingProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  goodSeedAmplification_of_congruentExtensionProvider hb hs
    (congruentExtensionProvider_of_period_window_embedding hb period window embed)

theorem goodSeedAmplification_of_window
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (window : PowerWindowProvider p q c) :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f :=
  goodSeedAmplification_of_period_window_embedding hb hs
    (periodProvider_of_pos
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_p)
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_q))
    window
    (embeddingProvider_core hb hs)

theorem freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (amp : PeriodWindowEmbeddingAmplification) :
    FreshExtensionAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window, embed⟩
  exact freshExtensionProvider_of_congruentExtensionProvider hs
    (congruentExtensionProvider_of_period_window_embedding hb period window embed)

theorem periodWindowEmbeddingAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    PeriodWindowEmbeddingAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window⟩
  exact ⟨period, window, embeddingProvider_core hb hs⟩

theorem periodWindowAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    PeriodWindowAmplification := by
  intro p q c hb hs
  exact ⟨periodProvider_of_pos
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_p)
      (Nat.lt_trans Nat.zero_lt_one hb.one_lt_q),
    amp hb hs⟩

theorem periodWindowLowRowAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    PeriodWindowLowRowAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window⟩
  exact ⟨period, window, lowRowSyncProvider_core⟩

theorem periodWindowEmbeddingAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    PeriodWindowEmbeddingAmplification := by
  intro p q c hb hs
  rcases amp hb hs with ⟨period, window, sync⟩
  exact ⟨period, window, embeddingProvider_of_lowRowSync hb hs sync⟩

theorem freshExtensionAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (periodWindowEmbeddingAmplification_of_periodWindowAmplification amp)

theorem freshExtensionAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowAmplification
    (periodWindowAmplification_of_windowAmplification amp)

theorem freshExtensionAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    FreshExtensionAmplification :=
  freshExtensionAmplification_of_periodWindowEmbeddingAmplification
    (periodWindowEmbeddingAmplification_of_periodWindowLowRowAmplification amp)

theorem goodSeedAmplification_of_freshExtensionAmplification
    (freshAmp : FreshExtensionAmplification) :
    GoodSeedAmplification := by
  intro p q c hb hs
  exact infinite_pairwise_nonrep_of_freshExtensionProvider (freshAmp hb hs)

theorem goodSeedAmplification_of_periodWindowEmbeddingAmplification
    (amp : PeriodWindowEmbeddingAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowEmbeddingAmplification amp)

theorem goodSeedAmplification_of_periodWindowAmplification
    (amp : PeriodWindowAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowAmplification amp)

theorem goodSeedAmplification_of_windowAmplification
    (amp : WindowAmplification) :
    GoodSeedAmplification := by
  intro p q c hb hs
  exact goodSeedAmplification_of_window hb hs (amp hb hs)

theorem goodSeedAmplification_of_periodWindowLowRowAmplification
    (amp : PeriodWindowLowRowAmplification) :
    GoodSeedAmplification :=
  goodSeedAmplification_of_freshExtensionAmplification
    (freshExtensionAmplification_of_periodWindowLowRowAmplification amp)

end Erdos1110
