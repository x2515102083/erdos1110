import Erdos1110.Basic

/-!
# Low-row infrastructure
-/

namespace Erdos1110

def highRows (M : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (M ≤ x.2))

def lowRows (M : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.2 < M))

def shiftSecondDown (M : Nat) (x : Point) : Point :=
  (x.1, x.2 - M)

def shiftedHighRows (M : Nat) (A : List Point) : List Point :=
  (highRows M A).map (shiftSecondDown M)

theorem mem_highRows_le
    {M : Nat} {A : List Point} {x : Point}
    (hx : x ∈ highRows M A) :
    M ≤ x.2 :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem mem_lowRows_lt
    {M : Nat} {A : List Point} {x : Point}
    (hx : x ∈ lowRows M A) :
    x.2 < M :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem lowRows_one_eq_singleton_of_unique_second_zero
    {A : List Point} {x : Point}
    (hnodup : A.Nodup)
    (hx : x ∈ A)
    (hx0 : x.2 = 0)
    (huniq : ∀ y, y ∈ A → y.2 = 0 → y = x) :
    lowRows 1 A = [x] := by
  dsimp [lowRows]
  apply filter_eq_singleton_of_unique
  · exact hnodup
  · exact hx
  · exact decide_eq_true (by rw [hx0]; decide : x.2 < 1)
  · intro y hy hyP
    have hylt : y.2 < 1 := of_decide_eq_true hyP
    exact huniq y hy (Nat.lt_one_iff.mp hylt)

theorem lowRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (lowRows M A) :=
  antichain_filter hA (fun x => decide (x.2 < M))

theorem highRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (highRows M A) :=
  antichain_filter hA (fun x => decide (M ≤ x.2))

theorem shiftSecondDown_injective_on_high
    {M : Nat} {x y : Point}
    (hx : M ≤ x.2) (hy : M ≤ y.2)
    (h : shiftSecondDown M x = shiftSecondDown M y) :
    x = y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [shiftSecondDown] at h hx hy ⊢
          injection h with hfirst hsecond
          subst yi
          have hadd : xj - M + M = yj - M + M := by rw [hsecond]
          rw [Nat.sub_add_cancel hx, Nat.sub_add_cancel hy] at hadd
          rw [hadd]

theorem shiftSecondDown_reflects_coordLe_on_high
    {M : Nat} {x y : Point}
    (hx : M ≤ x.2) (hy : M ≤ y.2)
    (h : CoordLe (shiftSecondDown M x) (shiftSecondDown M y)) :
    CoordLe x y := by
  cases x with
  | mk xi xj =>
      cases y with
      | mk yi yj =>
          dsimp [CoordLe, shiftSecondDown] at hx hy h ⊢
          constructor
          · exact h.1
          · have hadd : xj - M + M ≤ yj - M + M :=
              Nat.add_le_add_right h.2 M
            rw [Nat.sub_add_cancel hx, Nat.sub_add_cancel hy] at hadd
            exact hadd

theorem nodup_map_of_injective_on
    {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y)
    (hnodup : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.map, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
        have hab : a = b :=
          hinj List.mem_cons_self (List.mem_cons_of_mem a hb) hfb.symm
        subst b
        exact hnodup.1 hb
      · apply ih
        · intro x hx y hy hxy
          exact hinj (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy) hxy
        · exact hnodup.2

theorem shiftedHighRows_antichain
    {A : List Point} (hA : IsAntichain A) (M : Nat) :
    IsAntichain (shiftedHighRows M A) := by
  let H := highRows M A
  have hH : IsAntichain H := antichain_filter hA (fun x => decide (M ≤ x.2))
  constructor
  · dsimp [shiftedHighRows]
    apply nodup_map_of_injective_on
    · intro x hx y hy hxy
      exact shiftSecondDown_injective_on_high
        (mem_highRows_le hx) (mem_highRows_le hy) hxy
    · exact hH.1
  · intro u hu v hv huv hcoord
    dsimp [shiftedHighRows] at hu hv
    rcases List.mem_map.mp hu with ⟨x, hxH, hxu⟩
    rcases List.mem_map.mp hv with ⟨y, hyH, hyv⟩
    subst u
    subst v
    have hxy_ne : x ≠ y := by
      intro hxy
      exact huv (by rw [hxy])
    have hxy_coord : CoordLe x y :=
      shiftSecondDown_reflects_coordLe_on_high
        (mem_highRows_le hxH) (mem_highRows_le hyH) hcoord
    exact hH.2 hxH hyH hxy_ne hxy_coord

theorem term_eq_qpow_mul_shifted
    {p q M : Nat} {x : Point}
    (hx : M ≤ x.2) :
    Term p q x = q ^ M * Term p q (shiftSecondDown M x) := by
  cases x with
  | mk i j =>
      dsimp [Term, shiftSecondDown] at hx ⊢
      have hadd : M + (j - M) = j := Nat.add_sub_of_le hx
      calc
        p ^ i * q ^ j = p ^ i * q ^ (M + (j - M)) := by rw [hadd]
        _ = q ^ M * (p ^ i * q ^ (j - M)) := by
          rw [Nat.pow_add]
          ac_rfl

theorem sumTerms_eq_qpow_mul_shifted
    {p q M : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → M ≤ x.2) →
      SumTerms p q A = q ^ M * SumTerms p q (A.map (shiftSecondDown M))
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : M ≤ x.2 := hall x List.mem_cons_self
      have hxs : ∀ y, y ∈ xs → M ≤ y.2 := by
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      have ih := sumTerms_eq_qpow_mul_shifted (p := p) (q := q) (M := M) hxs
      dsimp [SumTerms] at ih ⊢
      rw [List.map_map] at ih
      simp [List.map_map]
      rw [term_eq_qpow_mul_shifted hx, ih]
      rw [Nat.mul_add]

theorem highRows_sum_factor
    (p q M : Nat) (A : List Point) :
    SumTerms p q (highRows M A) =
      q ^ M * SumTerms p q (shiftedHighRows M A) := by
  exact sumTerms_eq_qpow_mul_shifted (p := p) (q := q) (M := M)
    (fun x hx => mem_highRows_le hx)

theorem term_first_zeroSecond
    (p q a : Nat) :
    Term p q (a, 0) = p ^ a := by
  simp [Term]

theorem sumTerms_lowRows_add_highRows
    (p q M : Nat) :
    ∀ A : List Point,
      SumTerms p q A = SumTerms p q (lowRows M A) + SumTerms p q (highRows M A)
  | [] => by
      simp [SumTerms, lowRows, highRows]
  | x :: xs => by
      have ih := sumTerms_lowRows_add_highRows p q M xs
      dsimp [SumTerms, lowRows, highRows] at ih
      by_cases hlow : x.2 < M
      · have hnot_high : ¬ M ≤ x.2 := Nat.not_le_of_gt hlow
        simp [SumTerms, lowRows, highRows, hlow, hnot_high]
        rw [ih]
        ac_rfl
      · have hhigh : M ≤ x.2 := Nat.le_of_not_gt hlow
        simp [SumTerms, lowRows, highRows, hlow, hhigh]
        rw [ih]
        ac_rfl

theorem sumTerms_eq_zeroSecond_term_add_highRows_one
    {p q : Nat} {A : List Point} {x : Point}
    (hnodup : A.Nodup)
    (hx : x ∈ A)
    (hx0 : x.2 = 0)
    (huniq : ∀ y, y ∈ A → y.2 = 0 → y = x) :
    SumTerms p q A = Term p q x + SumTerms p q (highRows 1 A) := by
  have hsplit := sumTerms_lowRows_add_highRows p q 1 A
  have hlow : lowRows 1 A = [x] :=
    lowRows_one_eq_singleton_of_unique_second_zero hnodup hx hx0 huniq
  rw [hsplit, hlow]
  simp [SumTerms]

theorem first_coord_le_of_term_lt_pow_succ
    {p q a : Nat} {x : Point}
    (hp : 1 < p) (hq : 0 < q)
    (hterm : Term p q x < p ^ (a + 1)) :
    x.1 ≤ a := by
  by_cases hxle : x.1 ≤ a
  · exact hxle
  have hax : a < x.1 := Nat.lt_of_not_ge hxle
  have hsucc_le : a + 1 ≤ x.1 := Nat.succ_le_of_lt hax
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hpow_le : p ^ (a + 1) ≤ p ^ x.1 :=
    Nat.pow_le_pow_right hp_pos hsucc_le
  have hqpow_pos : 0 < q ^ x.2 := (Nat.pow_pos hq : 0 < q ^ x.2)
  have hpx_le_term : p ^ x.1 ≤ Term p q x :=
    Nat.le_mul_of_pos_right _ hqpow_pos
  have hbad : p ^ (a + 1) < p ^ (a + 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hpow_le hpx_le_term) hterm
  exact False.elim ((Nat.lt_irrefl _) hbad)

theorem embedded_lt_pow_succ
    {p q c a M : Nat}
    (hp_pos : 0 < p)
    (hright : c * q ^ M < (p - 1) * p ^ a) :
    p ^ a + c * q ^ M < p ^ (a + 1) := by
  have h1 : p ^ a + c * q ^ M < p ^ a + (p - 1) * p ^ a :=
    Nat.add_lt_add_left hright (p ^ a)
  have hsum : p ^ a + (p - 1) * p ^ a = p * p ^ a := by
    have hp_eq : p = (p - 1) + 1 := by
      exact (Nat.succ_pred_eq_of_pos hp_pos).symm
    rw [hp_eq]
    simp [Nat.add_mul]
    ac_rfl
  have hpow : p ^ (a + 1) = p * p ^ a := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hsum, ← hpow] at h1
  exact h1

theorem q_dvd_term_of_second_pos
    {p q : Nat} {x : Point}
    (hpos : 0 < x.2) :
    q ∣ Term p q x := by
  have hq_dvd_qpow : q ∣ q ^ x.2 :=
    by simpa using Nat.pow_dvd_pow q hpos
  exact Nat.dvd_trans hq_dvd_qpow (Nat.dvd_mul_left _ _)

theorem dvd_sumTerms_of_dvd_each
    {p q d : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → d ∣ Term p q x) →
      d ∣ SumTerms p q A
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : d ∣ Term p q x := hall x List.mem_cons_self
      have hxs : d ∣ SumTerms p q xs := by
        apply dvd_sumTerms_of_dvd_each
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      change d ∣ Term p q x + SumTerms p q xs
      exact Nat.dvd_add hx hxs

theorem q_dvd_sumTerms_of_all_second_pos
    {p q : Nat} {A : List Point}
    (hall : ∀ x, x ∈ A → 0 < x.2) :
    q ∣ SumTerms p q A := by
  apply dvd_sumTerms_of_dvd_each
  intro x hx
  exact q_dvd_term_of_second_pos (hall x hx)

theorem not_dvd_coprime_pow
    {p q a : Nat}
    (hq : 1 < q) (hpq : Nat.Coprime p q) :
    ¬ q ∣ p ^ a := by
  intro hdiv
  have hcop : Nat.Coprime q (p ^ a) :=
    hpq.symm.pow_right a
  have hgcd_left : Nat.gcd q (p ^ a) = q :=
    Nat.gcd_eq_left hdiv
  have hgcd_one : Nat.gcd q (p ^ a) = 1 :=
    Nat.Coprime.gcd_eq_one hcop
  have hq_eq_one : q = 1 := hgcd_left.symm.trans hgcd_one
  rw [hq_eq_one] at hq
  exact (Nat.lt_irrefl 1) hq

theorem q_dvd_qpow_mul_of_pos
    {q M u : Nat}
    (hM : 0 < M) :
    q ∣ q ^ M * u := by
  have hq : q ∣ q ^ M := by
    simpa using Nat.pow_dvd_pow q hM
  exact Nat.dvd_trans hq (Nat.dvd_mul_right _ _)

theorem dvd_pow_of_lowrow_congruence_and_dvd_sum
    {p q a M S u v : Nat}
    (hM : 0 < M)
    (hS : q ∣ S)
    (heq : S + q ^ M * u = p ^ a + q ^ M * v) :
    q ∣ p ^ a := by
  have hqu : q ∣ q ^ M * u := q_dvd_qpow_mul_of_pos hM
  have hqv : q ∣ q ^ M * v := q_dvd_qpow_mul_of_pos hM
  have hleft : q ∣ S + q ^ M * u := Nat.dvd_add hS hqu
  have hright : q ∣ p ^ a + q ^ M * v := by
    rwa [heq] at hleft
  exact (Nat.dvd_add_left hqv).mp hright

theorem not_all_second_pos_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hall_pos : ∀ x, x ∈ A → 0 < x.2)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  rcases hcong with ⟨u, v, heq⟩
  have hS : q ∣ SumTerms p q A :=
    q_dvd_sumTerms_of_all_second_pos hall_pos
  have hdiv : q ∣ p ^ a :=
    dvd_pow_of_lowrow_congruence_and_dvd_sum hM hS heq
  exact not_dvd_coprime_pow hq hpq hdiv

theorem exists_second_zero_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ∃ x, x ∈ A ∧ x.2 = 0 := by
  by_cases hzero : ∃ x, x ∈ A ∧ x.2 = 0
  · exact hzero
  · have hall_pos : ∀ x, x ∈ A → 0 < x.2 := by
      intro x hx
      by_cases hx0 : x.2 = 0
      · exact False.elim (hzero ⟨x, hx, hx0⟩)
      · exact Nat.pos_of_ne_zero hx0
    exact False.elim
      (not_all_second_pos_of_lowrow_congruence hq hpq hM hall_pos hcong)

theorem second_zero_unique_of_antichain
    {A : List Point} (hA : IsAntichain A)
    {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A)
    (hx0 : x.2 = 0) (hy0 : y.2 = 0) :
    x = y := by
  apply antichain_same_second_eq hA hx hy
  rw [hx0, hy0]

theorem exists_unique_second_zero_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hA : IsAntichain A)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ∃ x, x ∈ A ∧ x.2 = 0 ∧
      ∀ y, y ∈ A → y.2 = 0 → y = x := by
  rcases exists_second_zero_of_lowrow_congruence hq hpq hM hcong with
    ⟨x, hx, hx0⟩
  refine ⟨x, hx, hx0, ?_⟩
  intro y hy hy0
  exact second_zero_unique_of_antichain hA hy hx hy0 hx0

theorem exists_min_positive_second :
    ∀ A : List Point,
      (∃ x, x ∈ A ∧ 0 < x.2) →
      ∃ x, x ∈ A ∧ 0 < x.2 ∧
        ∀ y, y ∈ A → 0 < y.2 → x.2 ≤ y.2
  | [], h => by
      rcases h with ⟨x, hx, _⟩
      exact False.elim (List.not_mem_nil hx)
  | z :: zs, h => by
      by_cases hzpos : 0 < z.2
      · by_cases htail : ∃ x, x ∈ zs ∧ 0 < x.2
        · rcases exists_min_positive_second zs htail with ⟨m, hm, hmpos, hmin⟩
          cases Nat.le_total z.2 m.2 with
          | inl hz_le_m =>
              refine ⟨z, List.mem_cons_self, hzpos, ?_⟩
              intro y hy hypos
              cases List.mem_cons.mp hy with
              | inl hyz =>
                  subst y
                  exact Nat.le_refl z.2
              | inr hyzs =>
                  exact Nat.le_trans hz_le_m (hmin y hyzs hypos)
          | inr hm_le_z =>
              refine ⟨m, List.mem_cons_of_mem z hm, hmpos, ?_⟩
              intro y hy hypos
              cases List.mem_cons.mp hy with
              | inl hyz =>
                  subst y
                  exact hm_le_z
              | inr hyzs =>
                  exact hmin y hyzs hypos
        · refine ⟨z, List.mem_cons_self, hzpos, ?_⟩
          intro y hy hypos
          cases List.mem_cons.mp hy with
          | inl hyz =>
              subst y
              exact Nat.le_refl z.2
          | inr hyzs =>
              exact False.elim (htail ⟨y, hyzs, hypos⟩)
      · have htail : ∃ x, x ∈ zs ∧ 0 < x.2 := by
          rcases h with ⟨x, hx, hxpos⟩
          cases List.mem_cons.mp hx with
          | inl hxz =>
              subst x
              exact False.elim (hzpos hxpos)
          | inr hxzs =>
              exact ⟨x, hxzs, hxpos⟩
        rcases exists_min_positive_second zs htail with ⟨m, hm, hmpos, hmin⟩
        refine ⟨m, List.mem_cons_of_mem z hm, hmpos, ?_⟩
        intro y hy hypos
        cases List.mem_cons.mp hy with
        | inl hyz =>
            subst y
            exact False.elim (hzpos hypos)
        | inr hyzs =>
            exact hmin y hyzs hypos

theorem qpow_dvd_term_of_second_ge
    {p q k : Nat} {x : Point}
    (hk : k ≤ x.2) :
    q ^ k ∣ Term p q x := by
  have hq : q ^ k ∣ q ^ x.2 := Nat.pow_dvd_pow q hk
  exact Nat.dvd_trans hq (Nat.dvd_mul_left _ _)

theorem qpow_dvd_sumTerms_of_all_second_ge
    {p q k : Nat} :
    ∀ {A : List Point},
      (∀ x, x ∈ A → k ≤ x.2) →
      q ^ k ∣ SumTerms p q A
  | [], _ => by
      simp [SumTerms]
  | x :: xs, hall => by
      have hx : q ^ k ∣ Term p q x :=
        qpow_dvd_term_of_second_ge (hall x List.mem_cons_self)
      have hxs : q ^ k ∣ SumTerms p q xs := by
        apply qpow_dvd_sumTerms_of_all_second_ge
        intro y hy
        exact hall y (List.mem_cons_of_mem x hy)
      change q ^ k ∣ Term p q x + SumTerms p q xs
      exact Nat.dvd_add hx hxs

theorem exists_qpow_factor_sumTerms_of_all_second_ge
    {p q k : Nat} {A : List Point}
    (hall : ∀ x, x ∈ A → k ≤ x.2) :
    ∃ U, SumTerms p q A = q ^ k * U := by
  rcases qpow_dvd_sumTerms_of_all_second_ge (p := p) (q := q) (k := k) hall with
    ⟨U, hU⟩
  exact ⟨U, hU⟩

theorem sumTerms_factor_at_strict_second_min
    {p q : Nat} :
    ∀ {A : List Point} {x : Point},
      A.Nodup →
      x ∈ A →
      (∀ y, y ∈ A → y ≠ x → x.2 < y.2) →
      ∃ U, SumTerms p q A = q ^ x.2 * (p ^ x.1 + q * U)
  | [], _, _, hx, _ => by
      exact False.elim (List.not_mem_nil hx)
  | z :: zs, x, hnodup, hx, hstrict => by
      have hz_not : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzs_nodup : zs.Nodup := (List.nodup_cons.mp hnodup).2
      cases List.mem_cons.mp hx with
      | inl hxz =>
          subst x
          have htail_ge : ∀ y, y ∈ zs → z.2 + 1 ≤ y.2 := by
            intro y hy
            have hy_ne : y ≠ z := by
              intro hyz
              subst y
              exact hz_not hy
            exact Nat.succ_le_of_lt (hstrict y (List.mem_cons_of_mem z hy) hy_ne)
          rcases exists_qpow_factor_sumTerms_of_all_second_ge
              (p := p) (q := q) (k := z.2 + 1) htail_ge with
            ⟨U, hU⟩
          refine ⟨U, ?_⟩
          change Term p q z + SumTerms p q zs = q ^ z.2 * (p ^ z.1 + q * U)
          rw [hU]
          dsimp [Term]
          rw [Nat.pow_succ]
          simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      | inr hxzs =>
          have hz_ne_x : z ≠ x := by
            intro hzx
            subst x
            exact hz_not hxzs
          have hz_ge : x.2 + 1 ≤ z.2 :=
            Nat.succ_le_of_lt (hstrict z List.mem_cons_self hz_ne_x)
          have hstrict_tail : ∀ y, y ∈ zs → y ≠ x → x.2 < y.2 := by
            intro y hy hyne
            exact hstrict y (List.mem_cons_of_mem z hy) hyne
          rcases sumTerms_factor_at_strict_second_min
              (p := p) (q := q) hzs_nodup hxzs hstrict_tail with
            ⟨U, hU⟩
          rcases qpow_dvd_term_of_second_ge
              (p := p) (q := q) (k := x.2 + 1) (x := z) hz_ge with
            ⟨V, hV⟩
          refine ⟨V + U, ?_⟩
          change Term p q z + SumTerms p q zs =
            q ^ x.2 * (p ^ x.1 + q * (V + U))
          rw [hV, hU]
          rw [Nat.pow_succ]
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          ac_rfl

theorem not_q_dvd_p_pow_add_q_mul
    {p q i U : Nat}
    (hq : 1 < q) (hpq : Nat.Coprime p q) :
    ¬ q ∣ p ^ i + q * U := by
  intro hdiv
  have hqU : q ∣ q * U := Nat.dvd_mul_right q U
  have hqpi : q ∣ p ^ i := (Nat.dvd_add_left hqU).mp hdiv
  have hcop : Nat.Coprime q (p ^ i) := hpq.symm.pow_right i
  have hgcd_left : Nat.gcd q (p ^ i) = q := Nat.gcd_eq_left hqpi
  have hgcd_one : Nat.gcd q (p ^ i) = 1 := Nat.Coprime.gcd_eq_one hcop
  have hqeq : q = 1 := hgcd_left.symm.trans hgcd_one
  rw [hqeq] at hq
  exact (Nat.lt_irrefl 1) hq

theorem not_qpow_succ_dvd_sumTerms_at_strict_second_min
    {p q : Nat} {A : List Point} {x : Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hnodup : A.Nodup) (hx : x ∈ A)
    (hstrict : ∀ y, y ∈ A → y ≠ x → x.2 < y.2) :
    ¬ q ^ (x.2 + 1) ∣ SumTerms p q A := by
  rcases sumTerms_factor_at_strict_second_min
      (p := p) (q := q) hnodup hx hstrict with
    ⟨U, hU⟩
  intro hdiv
  rw [hU] at hdiv
  rw [Nat.pow_succ] at hdiv
  have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
  have hqjpos : 0 < q ^ x.2 := (Nat.pow_pos hqpos : 0 < q ^ x.2)
  have hq_dvd : q ∣ p ^ x.1 + q * U :=
    (Nat.mul_dvd_mul_iff_left hqjpos).mp hdiv
  exact not_q_dvd_p_pow_add_q_mul hq hpq hq_dvd

theorem false_of_zero_at_a_and_positive_second_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (_hM : 0 < M)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hpos_exists : ∃ x, x ∈ A ∧ 0 < x.2)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  let Pos := highRows 1 A
  have hdecomp : SumTerms p q A = p ^ a + SumTerms p q Pos := by
    dsimp [Pos]
    rw [sumTerms_eq_zeroSecond_term_add_highRows_one hA.1 hzero rfl huniq_zero]
    simp [Term]
  have hqM_dvd_pos : q ^ M ∣ SumTerms p q Pos := by
    rcases hcong with ⟨u, v, heq⟩
    have heq' : p ^ a + (SumTerms p q Pos + q ^ M * u) =
        p ^ a + q ^ M * v := by
      rw [← Nat.add_assoc]
      rw [← hdecomp]
      exact heq
    have hcancel : SumTerms p q Pos + q ^ M * u = q ^ M * v :=
      Nat.add_left_cancel heq'
    have hleft : q ^ M ∣ SumTerms p q Pos + q ^ M * u := by
      rw [hcancel]
      exact Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp hleft
  have hpos_mem : ∃ x, x ∈ Pos ∧ 0 < x.2 := by
    rcases hpos_exists with ⟨x, hxA, hxpos⟩
    refine ⟨x, ?_, hxpos⟩
    dsimp [Pos, highRows]
    rw [List.mem_filter]
    exact ⟨hxA, decide_eq_true (Nat.succ_le_of_lt hxpos)⟩
  rcases exists_min_positive_second Pos hpos_mem with ⟨m, hmPos, hmpos, hmin⟩
  have hmA : m ∈ A := (List.mem_filter.mp hmPos).1
  have hstrict : ∀ y, y ∈ Pos → y ≠ m → m.2 < y.2 := by
    intro y hyPos hyne
    have hypos : 0 < y.2 :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (mem_highRows_le hyPos)
    have hmle : m.2 ≤ y.2 := hmin y hyPos hypos
    have hne_second : m.2 ≠ y.2 := by
      intro hsec
      have hyA : y ∈ A := (List.mem_filter.mp hyPos).1
      have hyeq : y = m := antichain_same_second_eq hA hyA hmA hsec.symm
      exact hyne hyeq
    exact Nat.lt_of_le_of_ne hmle hne_second
  have hnot : ¬ q ^ (m.2 + 1) ∣ SumTerms p q Pos :=
    not_qpow_succ_dvd_sumTerms_at_strict_second_min hq hpq
      (highRows_antichain hA 1).1 hmPos hstrict
  have hsucc_le_M : m.2 + 1 ≤ M := Nat.succ_le_of_lt (hrow m hmA)
  have hpow_dvd_qM : q ^ (m.2 + 1) ∣ q ^ M :=
    Nat.pow_dvd_pow q hsucc_le_M
  have hdiv : q ^ (m.2 + 1) ∣ SumTerms p q Pos :=
    Nat.dvd_trans hpow_dvd_qM hqM_dvd_pos
  exact hnot hdiv

theorem eq_singleton_of_zero_at_a_and_no_positive_second
    {a : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hno_pos : ¬ ∃ x, x ∈ A ∧ 0 < x.2) :
    A = [(a, 0)] := by
  apply list_eq_singleton_of_mem_unique hA.1 hzero
  intro y hy
  by_cases hy0 : y.2 = 0
  · exact huniq_zero y hy hy0
  · have hypos : 0 < y.2 := Nat.pos_of_ne_zero hy0
    exact False.elim (hno_pos ⟨y, hy, hypos⟩)

theorem eq_singleton_of_zero_at_a_of_lowrow_congruence
    {p q a M : Nat} {A : List Point}
    (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hM : 0 < M)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (a, 0) ∈ A)
    (huniq_zero : ∀ y, y ∈ A → y.2 = 0 → y = (a, 0))
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    A = [(a, 0)] := by
  by_cases hpos : ∃ x, x ∈ A ∧ 0 < x.2
  · exact False.elim
      (false_of_zero_at_a_and_positive_second_of_lowrow_congruence
        hq hpq hM hA hrow hzero huniq_zero hpos hcong)
  · exact eq_singleton_of_zero_at_a_and_no_positive_second
      hA hzero huniq_zero hpos

end Erdos1110
