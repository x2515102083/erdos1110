import Erdos1110.Providers

/-!
# Finite-period providers
-/

namespace Erdos1110

theorem exists_duplicate_get_of_not_nodup {α : Type} :
    ∀ (l : List α), ¬ l.Nodup →
      ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j
  | [], hnot => by
      exact False.elim (hnot List.nodup_nil)
  | a :: as, hnot => by
      by_cases ha : a ∈ as
      · rcases List.get_of_mem ha with ⟨j, hj⟩
        refine ⟨0, j.succ, ?_, ?_⟩
        · intro hzero
          exact Fin.succ_ne_zero j hzero.symm
        · simpa [List.get_eq_getElem] using hj.symm
      · have hnot_as : ¬ as.Nodup := by
          intro has
          exact hnot ((List.nodup_cons).mpr ⟨ha, has⟩)
        rcases exists_duplicate_get_of_not_nodup as hnot_as with
          ⟨i, j, hij, hget⟩
        refine ⟨i.succ, j.succ, ?_, ?_⟩
        · intro hs
          exact hij ((Fin.succ_inj).mp hs)
        · simpa [List.get_eq_getElem] using hget

theorem not_mem_erase_self_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    {a : α} : ∀ {l : List α}, l.Nodup → ¬ a ∈ l.erase a
  | [], _ => by
      simp [List.erase]
  | x :: xs, hnod => by
      by_cases hxa : x = a
      · subst x
        rw [List.erase_cons_head]
        exact (List.nodup_cons.mp hnod).1
      · have hb : ¬ (x == a) = true := by
          intro hbtrue
          exact hxa ((beq_iff_eq.mp hbtrue))
        rw [List.erase_cons_tail hb]
        intro hmem
        cases List.mem_cons.mp hmem with
        | inl hx =>
            exact hxa hx.symm
        | inr htail =>
            exact not_mem_erase_self_of_nodup (List.nodup_cons.mp hnod).2 htail

theorem nodup_length_le_of_all_lt :
    ∀ (D : Nat) (l : List Nat), l.Nodup →
      (∀ x, x ∈ l → x < D) → l.length ≤ D
  | 0, [], _hnod, _hall => by
      simp
  | 0, x :: _xs, _hnod, hall => by
      have hx : x < 0 := hall x List.mem_cons_self
      omega
  | D + 1, l, hnod, hall => by
      by_cases hDmem : D ∈ l
      · have hnod_erase : (l.erase D).Nodup := List.Nodup.erase D hnod
        have hall_erase : ∀ x, x ∈ l.erase D → x < D := by
          intro x hx
          have hx_l : x ∈ l := List.mem_of_mem_erase hx
          have hx_lt_succ : x < D + 1 := hall x hx_l
          have hx_ne : x ≠ D := by
            intro hxeq
            subst x
            exact not_mem_erase_self_of_nodup hnod hx
          omega
        have hle : (l.erase D).length ≤ D :=
          nodup_length_le_of_all_lt D (l.erase D) hnod_erase hall_erase
        have hlen_eq : (l.erase D).length = l.length - 1 :=
          List.length_erase_of_mem hDmem
        have hlen_pos : 0 < l.length := List.length_pos_of_mem hDmem
        omega
      · have hall_lt : ∀ x, x ∈ l → x < D := by
          intro x hx
          have hx_lt_succ : x < D + 1 := hall x hx
          have hx_ne : x ≠ D := by
            intro hxeq
            subst x
            exact hDmem hx
          omega
        have hle : l.length ≤ D :=
          nodup_length_le_of_all_lt D l hnod hall_lt
        omega

theorem exists_duplicate_get_of_length_gt_bound
    {D : Nat} {l : List Nat}
    (hlen : D < l.length)
    (hall : ∀ x, x ∈ l → x < D) :
    ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j := by
  by_cases hnod : l.Nodup
  · have hle : l.length ≤ D := nodup_length_le_of_all_lt D l hnod hall
    omega
  · exact exists_duplicate_get_of_not_nodup l hnod

theorem get_power_residues {b D : Nat}
    (i : Fin ((List.range (D + 1)).map (fun n => b ^ n % D)).length) :
    ((List.range (D + 1)).map (fun n => b ^ n % D)).get i = b ^ i.1 % D := by
  rw [List.get_eq_getElem]
  rw [List.getElem_map]
  rw [List.getElem_range]

theorem exists_power_mod_repeat
    {b D : Nat} (hDpos : 0 < D) :
    ∃ i j : Nat, i < j ∧ j ≤ D ∧ b ^ i % D = b ^ j % D := by
  let residues := (List.range (D + 1)).map (fun n => b ^ n % D)
  have hlen : residues.length = D + 1 := by
    simp [residues, List.length_map, List.length_range]
  have hall : ∀ x, x ∈ residues → x < D := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨n, _hn, hnx⟩
    subst x
    exact Nat.mod_lt _ hDpos
  have hgt : D < residues.length := by
    omega
  rcases exists_duplicate_get_of_length_gt_bound hgt hall with ⟨i, j, hij, hget⟩
  have hi_get : residues.get i = b ^ i.1 % D := by
    simp [residues]
  have hj_get : residues.get j = b ^ j.1 % D := by
    simp [residues]
  have hmod : b ^ i.1 % D = b ^ j.1 % D := by
    rw [← hi_get, ← hj_get]
    exact hget
  have hval_ne : i.1 ≠ j.1 := by
    intro hval
    exact hij (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval_ne with
  | inl hlt =>
      refine ⟨i.1, j.1, hlt, ?_, hmod⟩
      have hj_lt : j.1 < D + 1 := by omega
      omega
  | inr hgtij =>
      refine ⟨j.1, i.1, hgtij, ?_, hmod.symm⟩
      have hi_lt : i.1 < D + 1 := by omega
      omega

theorem dvd_sub_of_mod_eq_of_le {D x y : Nat}
    (hyx : y ≤ x) (hmod : x % D = y % D) :
    D ∣ x - y := by
  rcases Nat.mod_eq_mod_iff.mp hmod with ⟨k1, k2, h⟩
  rcases Nat.exists_eq_add_of_le hyx with ⟨t, ht⟩
  subst x
  have hcancel : t + k1 * D = k2 * D := by
    omega
  have ht_eq : t = k2 * D - k1 * D := Nat.eq_sub_of_add_eq hcancel
  refine ⟨k2 - k1, ?_⟩
  rw [Nat.add_sub_cancel_left]
  rw [ht_eq]
  rw [← Nat.mul_sub_right_distrib]
  rw [Nat.mul_comm]

theorem one_plus_mul_of_dvd_sub_one {D x : Nat}
    (hx : 1 ≤ x) (hdiv : D ∣ x - 1) :
    ∃ r : Nat, x = 1 + D * r := by
  rcases hdiv with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have hx_eq : x = D * r + 1 := (Nat.sub_eq_iff_eq_add hx).mp hr
  rw [hx_eq, Nat.add_comm]

theorem dvd_pow_period_sub_one_of_mod_repeat
    {b D i j : Nat}
    (hcop : Nat.Coprime b D)
    (hbpos : 0 < b)
    (hij : i < j)
    (hmod : b ^ i % D = b ^ j % D) :
    D ∣ b ^ (j - i) - 1 := by
  have hile : i ≤ j := Nat.le_of_lt hij
  have hpow_le : b ^ i ≤ b ^ j := Nat.pow_le_pow_right hbpos hile
  have hdiv_diff : D ∣ b ^ j - b ^ i :=
    dvd_sub_of_mod_eq_of_le hpow_le hmod.symm
  have hdiff_eq : b ^ j - b ^ i = b ^ i * (b ^ (j - i) - 1) := by
    have hpow : b ^ (j - i) * b ^ i = b ^ j := Nat.pow_sub_mul_pow b hile
    calc
      b ^ j - b ^ i = b ^ (j - i) * b ^ i - 1 * b ^ i := by
        rw [hpow, Nat.one_mul]
      _ = (b ^ (j - i) - 1) * b ^ i := by
        rw [← Nat.mul_sub_right_distrib]
      _ = b ^ i * (b ^ (j - i) - 1) := by
        rw [Nat.mul_comm]
  rw [hdiff_eq] at hdiv_diff
  have hcop_factor : Nat.Coprime D (b ^ i) := hcop.symm.pow_right i
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop_factor hdiv_diff

theorem coprimeBasePeriodProvider_of_pos {b : Nat}
    (hbpos : 0 < b) :
    CoprimeBasePeriodProvider b := by
  intro D hcop
  by_cases hDzero : D = 0
  · subst D
    have hb_eq_one : b = 1 := by
      rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
      exact hcop
    subst b
    exact ⟨1, by decide, ⟨0, by simp⟩⟩
  · by_cases hDone : D = 1
    · subst D
      refine ⟨1, by decide, ⟨b - 1, ?_⟩⟩
      simp
      omega
    · have hDpos : 0 < D := Nat.pos_of_ne_zero hDzero
      rcases exists_power_mod_repeat (b := b) (D := D) hDpos with
        ⟨i, j, hij, _hjD, hmod⟩
      let L := j - i
      have hLpos : 0 < L := Nat.sub_pos_of_lt hij
      have hdiv : D ∣ b ^ L - 1 := by
        dsimp [L]
        exact dvd_pow_period_sub_one_of_mod_repeat hcop hbpos hij hmod
      have hone : 1 ≤ b ^ L := Nat.one_le_pow L b hbpos
      rcases one_plus_mul_of_dvd_sub_one hone hdiv with ⟨r, hr⟩
      exact ⟨L, hLpos, ⟨r, hr⟩⟩

theorem pow_one_plus_mul_congruent
    {D r k : Nat} :
    ∃ s : Nat, (1 + D * r) ^ k = 1 + D * s := by
  induction k with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      rcases ih with ⟨s, hs⟩
      refine ⟨r + s + D * r * s, ?_⟩
      rw [Nat.pow_succ, hs]
      simp [Nat.mul_add, Nat.add_mul]
      ac_rfl

theorem period_all_multiples_of_basic
    {b D L : Nat}
    (hL : ∃ r : Nat, b ^ L = 1 + D * r) :
    ∀ a : Nat, L ∣ a → ∃ r : Nat, b ^ a = 1 + D * r := by
  intro a hdiv
  rcases hdiv with ⟨k, hk⟩
  rcases hL with ⟨r, hr⟩
  rcases pow_one_plus_mul_congruent (D := D) (r := r) (k := k) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [hk, Nat.pow_mul, hr]
  exact hs

theorem periodProvider_of_basicPeriodProvider
    {p q : Nat}
    (basic : BasicPeriodProvider p q) :
    PeriodProvider p q := by
  intro D hD
  rcases basic D hD with ⟨L, hLpos, hpL, hqL⟩
  exact ⟨L, hLpos,
    period_all_multiples_of_basic hpL,
    period_all_multiples_of_basic hqL⟩

theorem basicPeriodProvider_of_coprimeBasePeriodProviders
    {p q : Nat}
    (p_period : CoprimeBasePeriodProvider p)
    (q_period : CoprimeBasePeriodProvider q) :
    BasicPeriodProvider p q := by
  intro D hD
  have hDp : Nat.Coprime D p := (Nat.coprime_mul_iff_right.mp hD).1
  have hDq : Nat.Coprime D q := (Nat.coprime_mul_iff_right.mp hD).2
  rcases p_period D hDp.symm with ⟨Lp, hLp_pos, hpLp⟩
  rcases q_period D hDq.symm with ⟨Lq, hLq_pos, hqLq⟩
  refine ⟨Lp * Lq, Nat.mul_pos hLp_pos hLq_pos, ?_, ?_⟩
  · exact period_all_multiples_of_basic hpLp (Lp * Lq) ⟨Lq, rfl⟩
  · exact period_all_multiples_of_basic hqLq (Lp * Lq)
      ⟨Lp, Nat.mul_comm Lp Lq⟩

theorem basicPeriodProvider_of_pos
    {p q : Nat}
    (hp_pos : 0 < p)
    (hq_pos : 0 < q) :
    BasicPeriodProvider p q :=
  basicPeriodProvider_of_coprimeBasePeriodProviders
    (coprimeBasePeriodProvider_of_pos hp_pos)
    (coprimeBasePeriodProvider_of_pos hq_pos)

theorem periodProvider_of_coprimeBasePeriodProviders
    {p q : Nat}
    (p_period : CoprimeBasePeriodProvider p)
    (q_period : CoprimeBasePeriodProvider q) :
    PeriodProvider p q :=
  periodProvider_of_basicPeriodProvider
    (basicPeriodProvider_of_coprimeBasePeriodProviders p_period q_period)

theorem periodProvider_of_pos
    {p q : Nat}
    (hp_pos : 0 < p)
    (hq_pos : 0 < q) :
    PeriodProvider p q :=
  periodProvider_of_basicPeriodProvider
    (basicPeriodProvider_of_pos hp_pos hq_pos)

end Erdos1110
