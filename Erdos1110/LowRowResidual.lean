import Erdos1110.Providers

/-!
# Low-row residual induction
-/

namespace Erdos1110

def firstGE (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (i ≤ x.1))

def firstGT (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (i < x.1))

def firstLT (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.1 < i))

def firstEQ (i : Nat) (A : List Point) : List Point :=
  A.filter (fun x => decide (x.1 = i))

theorem mem_firstLT
    {i : Nat} {A : List Point} {x : Point}
    (hx : x ∈ firstLT i A) :
    x.1 < i :=
  of_decide_eq_true (List.mem_filter.mp hx).2

theorem firstGE_eq_firstEQ_add_firstGT_sum
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q (firstGE i A) =
        SumTerms p q (firstEQ i A) + SumTerms p q (firstGT i A)
  | [] => by
      simp [SumTerms, firstGE, firstEQ, firstGT]
  | x :: xs => by
      have ih := firstGE_eq_firstEQ_add_firstGT_sum p q i xs
      dsimp [SumTerms, firstGE, firstEQ, firstGT] at ih ⊢
      by_cases hlt : i < x.1
      · have hge : i ≤ x.1 := Nat.le_of_lt hlt
        have hne : ¬ x.1 = i := by
          intro h
          rw [h] at hlt
          exact (Nat.lt_irrefl i) hlt
        simp [hge, hlt, hne]
        rw [ih]
        ac_rfl
      · by_cases heq : x.1 = i
        · have _hge : i ≤ x.1 := by
            rw [heq]
            exact Nat.le_refl i
          simp [heq]
          rw [ih]
          ac_rfl
        · have hge_not : ¬ i ≤ x.1 := by
            intro hge
            have hle : x.1 ≤ i := Nat.le_of_not_gt hlt
            have hxeq : x.1 = i := Nat.le_antisymm hle hge
            exact heq hxeq
          simp [hge_not, hlt, heq]
          exact ih

theorem sumTerms_firstGE_zero
    (p q : Nat) (A : List Point) :
    SumTerms p q (firstGE 0 A) = SumTerms p q A := by
  induction A with
  | nil =>
      simp [SumTerms, firstGE]
  | cons x xs ih =>
      dsimp [SumTerms, firstGE] at ih ⊢
      simp
      simpa [firstGE] using ih

theorem sumTerms_firstGE_add_firstLT
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q A =
        SumTerms p q (firstGE i A) + SumTerms p q (firstLT i A)
  | [] => by
      simp [SumTerms, firstGE, firstLT]
  | x :: xs => by
      have ih := sumTerms_firstGE_add_firstLT p q i xs
      dsimp [SumTerms, firstGE, firstLT] at ih ⊢
      by_cases hge : i ≤ x.1
      · have hnlt : ¬ x.1 < i := Nat.not_lt_of_ge hge
        simp [hge, hnlt]
        rw [ih]
        ac_rfl
      · have hlt : x.1 < i := Nat.lt_of_not_ge hge
        simp [hge, hlt]
        rw [ih]
        ac_rfl

theorem sumTerms_firstGE_succ_eq_firstGT
    (p q i : Nat) :
    ∀ A : List Point,
      SumTerms p q (firstGE (i + 1) A) = SumTerms p q (firstGT i A)
  | [] => by
      simp [SumTerms, firstGE, firstGT]
  | x :: xs => by
      have ih := sumTerms_firstGE_succ_eq_firstGT p q i xs
      dsimp [SumTerms, firstGE, firstGT] at ih ⊢
      by_cases hx : i < x.1
      · have hs : i + 1 ≤ x.1 := Nat.succ_le_of_lt hx
        simp [hx, hs]
        exact ih
      · have hs : ¬ i + 1 ≤ x.1 := by
          intro h
          exact hx (Nat.lt_of_succ_le h)
        simp [hx, hs]
        exact ih

theorem firstEQ_eq_singleton_of_antichain
    {i : Nat} {A : List Point} {x : Point}
    (hA : IsAntichain A)
    (hx : x ∈ A)
    (hxfirst : x.1 = i) :
    firstEQ i A = [x] := by
  dsimp [firstEQ]
  apply filter_eq_singleton_of_unique
  · exact hA.1
  · exact hx
  · exact decide_eq_true hxfirst
  · intro y hy hyP
    have hyfirst : y.1 = i := of_decide_eq_true hyP
    exact antichain_same_first_eq hA hy hx (hyfirst.trans hxfirst.symm)

theorem firstEQ_eq_nil_of_no_first
    {i : Nat} {A : List Point}
    (hno : ∀ x, x ∈ A → x.1 ≠ i) :
    firstEQ i A = [] := by
  dsimp [firstEQ]
  apply filter_eq_nil_of_forall_not
  intro x hx hP
  exact hno x hx (of_decide_eq_true hP)

theorem firstGE_eq_nil_of_zero_before
    {a t : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hzero : (t, 0) ∈ A)
    (ht : t < a) :
    firstGE a A = [] := by
  dsimp [firstGE]
  apply filter_eq_nil_of_forall_not
  intro x hx hP
  have hage : a ≤ x.1 := of_decide_eq_true hP
  have hxa : x.1 = a := Nat.le_antisymm (hcol x hx) hage
  have hx_ne_zero : x ≠ (t, 0) := by
    intro h
    have hfirst : x.1 = t := by rw [h]
    rw [hxa] at hfirst
    rw [hfirst] at ht
    exact (Nat.lt_irrefl t) ht
  have hcoord : CoordLe (t, 0) x := by
    constructor
    · rw [hxa]
      exact Nat.le_of_lt ht
    · exact Nat.zero_le x.2
  exact hA.2 hzero hx (fun h => hx_ne_zero h.symm) hcoord

def ResidualInvariant (p q a : Nat) (A : List Point) (i : Nat) : Prop :=
  ∃ X : Nat, 0 < X ∧ p ^ i * X + SumTerms p q (firstGE i A) = p ^ a

theorem residualInvariant_top
    {p q a t : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hzero : (t, 0) ∈ A)
    (ht : t < a) :
    ResidualInvariant p q a A a := by
  refine ⟨1, by decide, ?_⟩
  rw [firstGE_eq_nil_of_zero_before hA hcol hzero ht]
  simp [SumTerms]

theorem residualInvariant_step_empty
    {p q a i : Nat} {A : List Point}
    (hp_pos : 0 < p)
    (hinv : ResidualInvariant p q a A (i + 1))
    (hno : ∀ x, x ∈ A → x.1 ≠ i) :
    ResidualInvariant p q a A i := by
  rcases hinv with ⟨X, hXpos, hEq⟩
  refine ⟨p * X, ?_, ?_⟩
  · exact Nat.mul_pos hp_pos hXpos
  · have hEqCol : firstEQ i A = [] := firstEQ_eq_nil_of_no_first hno
    have hsplit := firstGE_eq_firstEQ_add_firstGT_sum p q i A
    have hsucc := sumTerms_firstGE_succ_eq_firstGT p q i A
    calc
      p ^ i * (p * X) + SumTerms p q (firstGE i A)
          = p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A) := by
              rw [hsplit, hEqCol, hsucc]
              simp [SumTerms]
              rw [Nat.pow_succ]
              ac_rfl
      _ = p ^ a := hEq

theorem qpow_dvd_sumTerms_firstLT_of_selected
    {p q i j : Nat} {A : List Point}
    (hA : IsAntichain A)
    (hx : (i, j) ∈ A) :
    q ^ j ∣ SumTerms p q (firstLT i A) := by
  apply qpow_dvd_sumTerms_of_all_second_ge
  intro y hy
  have hyA : y ∈ A := (List.mem_filter.mp hy).1
  have hylt : y.1 < i := mem_firstLT hy
  have hsecond : j < y.2 := by
    have hstrict := antichain_second_strictAnti_of_first_lt hA hyA hx hylt
    simpa using hstrict
  exact Nat.le_of_lt hsecond

theorem qpow_dvd_qpow_mul_of_le
    {q j M u : Nat}
    (hle : j ≤ M) :
    q ^ j ∣ q ^ M * u := by
  have hpow : q ^ j ∣ q ^ M := Nat.pow_dvd_pow q hle
  exact Nat.dvd_trans hpow (Nat.dvd_mul_right _ _)

theorem residualInvariant_step_selected
    {p q a M i j : Nat} {A : List Point}
    (hp : 1 < p)
    (_hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hA : IsAntichain A)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v)
    (hinv : ResidualInvariant p q a A (i + 1))
    (hx : (i, j) ∈ A) :
    ResidualInvariant p q a A i := by
  rcases hinv with ⟨X, hXpos, hEq⟩
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hjM : j < M := hrow (i, j) hx
  have hjleM : j ≤ M := Nat.le_of_lt hjM
  have hEqCol : firstEQ i A = [(i, j)] :=
    firstEQ_eq_singleton_of_antichain hA hx rfl
  have hsplitGE := firstGE_eq_firstEQ_add_firstGT_sum p q i A
  have hsucc := sumTerms_firstGE_succ_eq_firstGT p q i A
  have hSuffix :
      SumTerms p q (firstGE i A) =
        Term p q (i, j) + SumTerms p q (firstGE (i + 1) A) := by
    calc
      SumTerms p q (firstGE i A)
          = SumTerms p q (firstEQ i A) + SumTerms p q (firstGT i A) := hsplitGE
      _ = Term p q (i, j) + SumTerms p q (firstGE (i + 1) A) := by
          rw [hEqCol, ← hsucc]
          simp [SumTerms]
  have hAll :
      SumTerms p q A =
        SumTerms p q (firstGE (i + 1) A) +
          Term p q (i, j) + SumTerms p q (firstLT i A) := by
    have hsplitAll := sumTerms_firstGE_add_firstLT p q i A
    calc
      SumTerms p q A
          = SumTerms p q (firstGE i A) + SumTerms p q (firstLT i A) := hsplitAll
      _ = (Term p q (i, j) + SumTerms p q (firstGE (i + 1) A)) +
            SumTerms p q (firstLT i A) := by rw [hSuffix]
      _ = SumTerms p q (firstGE (i + 1) A) +
            Term p q (i, j) + SumTerms p q (firstLT i A) := by ac_rfl
  have hqj_dvd_term : q ^ j ∣ Term p q (i, j) :=
    qpow_dvd_term_of_second_ge (p := p) (q := q) (k := j) (x := (i, j))
      (Nat.le_refl j)
  have hqj_dvd_lower : q ^ j ∣ SumTerms p q (firstLT i A) :=
    qpow_dvd_sumTerms_firstLT_of_selected hA hx
  have hqj_dvd_X : q ^ j ∣ X := by
    rcases hcong with ⟨u, v, heq⟩
    have hqj_dvd_qMu : q ^ j ∣ q ^ M * u :=
      qpow_dvd_qpow_mul_of_le hjleM
    have hqj_dvd_qMv : q ^ j ∣ q ^ M * v :=
      qpow_dvd_qpow_mul_of_le hjleM
    have hcancel :
        Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u =
          p ^ (i + 1) * X + q ^ M * v := by
      have hbig :
          SumTerms p q (firstGE (i + 1) A) +
              (Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u) =
            SumTerms p q (firstGE (i + 1) A) +
              (p ^ (i + 1) * X + q ^ M * v) := by
        calc
          SumTerms p q (firstGE (i + 1) A) +
              (Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u)
              = SumTerms p q A + q ^ M * u := by
                  rw [hAll]
                  ac_rfl
          _ = p ^ a + q ^ M * v := heq
          _ = (p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A)) +
                q ^ M * v := by rw [hEq]
          _ = SumTerms p q (firstGE (i + 1) A) +
                (p ^ (i + 1) * X + q ^ M * v) := by ac_rfl
      exact Nat.add_left_cancel hbig
    have hleft :
        q ^ j ∣ Term p q (i, j) + SumTerms p q (firstLT i A) + q ^ M * u :=
      Nat.dvd_add (Nat.dvd_add hqj_dvd_term hqj_dvd_lower) hqj_dvd_qMu
    have hright :
        q ^ j ∣ p ^ (i + 1) * X + q ^ M * v := by
      rwa [hcancel] at hleft
    have hpX : q ^ j ∣ p ^ (i + 1) * X :=
      (Nat.dvd_add_left hqj_dvd_qMv).mp hright
    have hcop : Nat.Coprime (q ^ j) (p ^ (i + 1)) :=
      (hpq.symm.pow_left j).pow_right (i + 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hpX
  have hqj_le_X : q ^ j ≤ X := Nat.le_of_dvd hXpos hqj_dvd_X
  have hX_lt_pX : X < p * X :=
    (Nat.lt_mul_iff_one_lt_left hXpos).2 hp
  have hqj_lt_pX : q ^ j < p * X :=
    Nat.lt_of_le_of_lt hqj_le_X hX_lt_pX
  have hqj_le_pX : q ^ j ≤ p * X := Nat.le_of_lt hqj_lt_pX
  refine ⟨p * X - q ^ j, Nat.sub_pos_of_lt hqj_lt_pX, ?_⟩
  have hmul_cancel :
      p ^ i * (p * X - q ^ j) + p ^ i * q ^ j = p ^ i * (p * X) := by
    rw [Nat.mul_sub_left_distrib]
    exact Nat.sub_add_cancel (Nat.mul_le_mul_left (p ^ i) hqj_le_pX)
  calc
    p ^ i * (p * X - q ^ j) + SumTerms p q (firstGE i A)
        = p ^ i * (p * X - q ^ j) +
            (Term p q (i, j) + SumTerms p q (firstGE (i + 1) A)) := by
            rw [hSuffix]
    _ = p ^ i * (p * X - q ^ j) +
          (p ^ i * q ^ j + SumTerms p q (firstGE (i + 1) A)) := by
            simp [Term]
    _ = (p ^ i * (p * X - q ^ j) + p ^ i * q ^ j) +
          SumTerms p q (firstGE (i + 1) A) := by ac_rfl
    _ = p ^ i * (p * X) + SumTerms p q (firstGE (i + 1) A) := by
            rw [hmul_cancel]
    _ = p ^ (i + 1) * X + SumTerms p q (firstGE (i + 1) A) := by
            rw [Nat.pow_succ]
            ac_rfl
    _ = p ^ a := hEq

theorem residualInvariant_zero_of_zero_before
    {p q a M t : Nat} {A : List Point}
    (hp : 1 < p)
    (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (t, 0) ∈ A)
    (ht : t < a)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    ResidualInvariant p q a A 0 := by
  have hp_pos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hdesc :
      ∀ n : Nat, n ≤ a → ResidualInvariant p q a A (a - n) := by
    intro n hn
    induction n with
    | zero =>
        simpa using residualInvariant_top (p := p) (q := q)
          hA hcol hzero ht
    | succ n ih =>
        have hnle : n ≤ a := by omega
        have hprev : ResidualInvariant p q a A (a - n) := ih hnle
        have hidx : a - (n + 1) + 1 = a - n := by omega
        have hprev' :
            ResidualInvariant p q a A ((a - (n + 1)) + 1) := by
          simpa [hidx] using hprev
        by_cases hex : ∃ x, x ∈ A ∧ x.1 = a - (n + 1)
        · rcases hex with ⟨x, hxA, hxfirst⟩
          cases x with
          | mk xi j =>
              dsimp at hxfirst
              rw [hxfirst] at hxA
              exact residualInvariant_step_selected
                (p := p) (q := q) (a := a) (M := M)
                (i := a - (n + 1)) (j := j) hp hq hpq hA hrow hcong hprev' hxA
        · apply residualInvariant_step_empty (p := p) (q := q)
            (a := a) (i := a - (n + 1)) (A := A) hp_pos hprev'
          intro x hxA hxfirst
          exact hex ⟨x, hxA, hxfirst⟩
  simpa using hdesc a (Nat.le_refl a)

theorem false_of_zero_before_of_lowrow_congruence
    {p q a M t : Nat} {A : List Point}
    (hp : 1 < p)
    (hq : 1 < q)
    (hpq : Nat.Coprime p q)
    (hpow : p ^ a < q ^ M)
    (hA : IsAntichain A)
    (hcol : ∀ x, x ∈ A → x.1 ≤ a)
    (hrow : ∀ x, x ∈ A → x.2 < M)
    (hzero : (t, 0) ∈ A)
    (ht : t < a)
    (hcong : ∃ u v : Nat,
      SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) :
    False := by
  rcases residualInvariant_zero_of_zero_before
      hp hq hpq hA hcol hrow hzero ht hcong with
    ⟨X, hXpos, hEq0⟩
  have hfirstGE0 := sumTerms_firstGE_zero p q A
  have hXS : X + SumTerms p q A = p ^ a := by
    simpa [hfirstGE0] using hEq0
  have hX_le_pa : X ≤ p ^ a := by
    rw [← hXS]
    exact Nat.le_add_right X (SumTerms p q A)
  have hX_lt_qM : X < q ^ M := Nat.lt_of_le_of_lt hX_le_pa hpow
  have hqM_dvd_X : q ^ M ∣ X := by
    rcases hcong with ⟨u, v, heq⟩
    have hcancel : q ^ M * u = X + q ^ M * v := by
      have hbig :
          SumTerms p q A + q ^ M * u =
            SumTerms p q A + (X + q ^ M * v) := by
        calc
          SumTerms p q A + q ^ M * u
              = p ^ a + q ^ M * v := heq
          _ = (X + SumTerms p q A) + q ^ M * v := by rw [hXS]
          _ = SumTerms p q A + (X + q ^ M * v) := by ac_rfl
      exact Nat.add_left_cancel hbig
    have hdiv : q ^ M ∣ X + q ^ M * v := by
      rw [← hcancel]
      exact Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_left (Nat.dvd_mul_right _ _)).mp hdiv
  exact (Nat.not_dvd_of_pos_of_lt hXpos hX_lt_qM) hqM_dvd_X

theorem lowRowResidualProvider_core
    {p q : Nat} :
    LowRowResidualProvider p q := by
  intro a M A t hp hq hpq _hM hpow hA hcol hrow hzero ht hcong
  exact false_of_zero_before_of_lowrow_congruence
    hp hq hpq hpow hA hcol hrow hzero ht hcong

end Erdos1110
