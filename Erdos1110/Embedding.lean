import Erdos1110.LowRowResidual

/-!
# Embedding providers
-/

namespace Erdos1110

def EmbeddingNonrepProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nonrepresentable p q (p ^ a + c * q ^ M)

def EmbeddingCoprimeProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nat.Coprime (p ^ a + c * q ^ M) (p * q)

def EmbeddingProvider (p q c : Nat) : Prop :=
  ∀ a M : Nat,
    0 < a → 0 < M →
    p ^ a < q ^ M →
    c * q ^ M < (p - 1) * p ^ a →
      Nonrepresentable p q (p ^ a + c * q ^ M) ∧
      Nat.Coprime (p ^ a + c * q ^ M) (p * q)

def PeriodWindowEmbeddingAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c ∧ EmbeddingProvider p q c

def PeriodWindowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c

def WindowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PowerWindowProvider p q c

def PeriodWindowLowRowAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      PeriodProvider p q ∧ PowerWindowProvider p q c ∧ LowRowSyncProvider p q

def FreshExtensionAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c → FreshExtensionProvider p q c

def GoodSeedAmplification : Prop :=
  ∀ ⦃p q c : Nat⦄,
    ValidBases p q → GoodSeed p q c →
      ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f

theorem lowRowSyncProvider_of_residual
    {p q : Nat}
    (residual : LowRowResidualProvider p q) :
    LowRowSyncProvider p q := by
  intro a M A hp hq hpq hM hpow hA hcol hrow hcong
  rcases exists_unique_second_zero_of_lowrow_congruence hq hpq hM hA hcong with
    ⟨x, hxA, hx0, huniq⟩
  cases x with
  | mk t j =>
      dsimp at hx0 huniq hxA hcol hrow
      subst j
      by_cases hta : t = a
      · subst t
        have huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0) := by
          intro y hy hy0
          exact huniq y hy hy0
        exact eq_singleton_of_zero_at_a_of_lowrow_congruence
          hq hpq hM hA hrow hxA huniq_zero hcong
      · have ht_le_a : t ≤ a := hcol (t, 0) hxA
        have ht_lt_a : t < a := Nat.lt_of_le_of_ne ht_le_a hta
        exact False.elim
          (residual a M A t hp hq hpq hM hpow hA hcol hrow hxA ht_lt_a hcong)

theorem lowRowSyncProvider_core
    {p q : Nat} :
    LowRowSyncProvider p q :=
  lowRowSyncProvider_of_residual lowRowResidualProvider_core

theorem embeddingProvider_of_nonrep_and_coprime
    {p q c : Nat}
    (hnrep : EmbeddingNonrepProvider p q c)
    (hcop : EmbeddingCoprimeProvider p q c) :
    EmbeddingProvider p q c := by
  intro a M ha hM hleft hright
  exact ⟨hnrep a M ha hM hleft hright, hcop a M ha hM hleft hright⟩

theorem embeddingNonrepProvider_of_lowRowSync
    {p q c : Nat}
    (hb : ValidBases p q)
    (sync : LowRowSyncProvider p q)
    (hc_nonrep : Nonrepresentable p q c) :
    EmbeddingNonrepProvider p q c := by
  intro a M ha hM hleft hright
  intro hrepr
  rcases hrepr with ⟨A, hA, hsum⟩
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hb.one_lt_p
  have hq_pos : 0 < q := Nat.lt_trans Nat.zero_lt_one hb.one_lt_q
  have hNlt : p ^ a + c * q ^ M < p ^ (a + 1) :=
    embedded_lt_pow_succ hp_pos hright
  have hcolA : ∀ x, x ∈ A → x.1 ≤ a := by
    intro x hx
    have hx_le_sum : Term p q x ≤ SumTerms p q A := mem_term_le_sum hx
    have hx_lt : Term p q x < p ^ (a + 1) := by
      rw [hsum] at hx_le_sum
      exact Nat.lt_of_le_of_lt hx_le_sum hNlt
    exact first_coord_le_of_term_lt_pow_succ hb.one_lt_p hq_pos hx_lt
  let Low := lowRows M A
  let HighShift := shiftedHighRows M A
  have hlow_anti : IsAntichain Low := by
    dsimp [Low]
    exact lowRows_antichain hA M
  have hlow_col : ∀ x, x ∈ Low → x.1 ≤ a := by
    intro x hx
    exact hcolA x (List.mem_filter.mp hx).1
  have hlow_row : ∀ x, x ∈ Low → x.2 < M := by
    intro x hx
    exact mem_lowRows_lt hx
  have hcong : ∃ u v : Nat,
      SumTerms p q Low + q ^ M * u = p ^ a + q ^ M * v := by
    refine ⟨SumTerms p q HighShift, c, ?_⟩
    dsimp [Low, HighShift]
    have hsplit := sumTerms_lowRows_add_highRows p q M A
    have hfactor := highRows_sum_factor p q M A
    calc
      SumTerms p q (lowRows M A) + q ^ M * SumTerms p q (shiftedHighRows M A)
          = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A) := by
              rw [hfactor]
      _ = SumTerms p q A := hsplit.symm
      _ = p ^ a + c * q ^ M := hsum
      _ = p ^ a + q ^ M * c := by rw [Nat.mul_comm c (q ^ M)]
  have hlow_eq : Low = [(a, 0)] :=
    sync a M Low hb.one_lt_p hb.one_lt_q hb.coprime hM
      hleft hlow_anti hlow_col hlow_row hcong
  have hhigh_sum_eq : SumTerms p q HighShift = c := by
    have hsplit := sumTerms_lowRows_add_highRows p q M A
    have hfactor := highRows_sum_factor p q M A
    dsimp [Low, HighShift] at hlow_eq ⊢
    have hmain :
        p ^ a + q ^ M * SumTerms p q (shiftedHighRows M A) =
          p ^ a + q ^ M * c := by
      calc
        p ^ a + q ^ M * SumTerms p q (shiftedHighRows M A)
            = SumTerms p q (lowRows M A) + q ^ M * SumTerms p q (shiftedHighRows M A) := by
                rw [hlow_eq]
                simp [SumTerms, Term]
        _ = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A) := by
                rw [hfactor]
        _ = SumTerms p q A := hsplit.symm
        _ = p ^ a + c * q ^ M := hsum
        _ = p ^ a + q ^ M * c := by rw [Nat.mul_comm c (q ^ M)]
    have hcancel_add :
        q ^ M * SumTerms p q (shiftedHighRows M A) = q ^ M * c :=
      Nat.add_left_cancel hmain
    have hqM_pos : 0 < q ^ M := (Nat.pow_pos hq_pos : 0 < q ^ M)
    exact Nat.mul_left_cancel hqM_pos hcancel_add
  exact hc_nonrep ⟨HighShift, shiftedHighRows_antichain hA M, hhigh_sum_eq⟩

theorem embeddingProvider_of_lowRowSync_and_coprime
    {p q c : Nat}
    (hb : ValidBases p q)
    (sync : LowRowSyncProvider p q)
    (hc_nonrep : Nonrepresentable p q c)
    (hcop : EmbeddingCoprimeProvider p q c) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_nonrep_and_coprime
    (embeddingNonrepProvider_of_lowRowSync hb sync hc_nonrep)
    hcop

theorem embeddingCoprimeProvider_of_goodSeed
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    EmbeddingCoprimeProvider p q c := by
  intro a M ha hM _hleft _hright
  apply Nat.coprime_mul_iff_right.mpr
  constructor
  · have hc_p : Nat.Coprime c p :=
      (Nat.coprime_mul_iff_right.mp hs.coprime_pq).1
    have hqM_p : Nat.Coprime (q ^ M) p :=
      hb.coprime.symm.pow_left M
    have hprod_p : Nat.Coprime (c * q ^ M) p :=
      Nat.Coprime.mul_left hc_p hqM_p
    rw [Nat.coprime_iff_gcd_eq_one]
    have hpow : p ^ a = p * p ^ (a - 1) := by
      have hsucc : (a - 1).succ = a := Nat.succ_pred_eq_of_pos ha
      rw [← hsucc, Nat.pow_succ]
      ac_rfl
    rw [hpow]
    rw [Nat.add_comm]
    rw [Nat.gcd_add_mul_left_left]
    exact Nat.Coprime.gcd_eq_one hprod_p
  · have hpowa_q : Nat.Coprime (p ^ a) q :=
      hb.coprime.pow_left a
    rw [Nat.coprime_iff_gcd_eq_one]
    have hqpow : q ^ M = q * q ^ (M - 1) := by
      have hsucc : (M - 1).succ = M := Nat.succ_pred_eq_of_pos hM
      rw [← hsucc, Nat.pow_succ]
      ac_rfl
    rw [hqpow]
    have hmul : c * (q * q ^ (M - 1)) = q * (c * q ^ (M - 1)) := by
      ac_rfl
    rw [hmul]
    rw [Nat.gcd_add_mul_left_left]
    exact Nat.Coprime.gcd_eq_one hpowa_q

theorem embeddingProvider_of_lowRowSync
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c)
    (sync : LowRowSyncProvider p q) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_lowRowSync_and_coprime hb sync hs.nonrep
    (embeddingCoprimeProvider_of_goodSeed hb hs)

theorem embeddingProvider_core
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    EmbeddingProvider p q c :=
  embeddingProvider_of_lowRowSync hb hs lowRowSyncProvider_core

end Erdos1110
