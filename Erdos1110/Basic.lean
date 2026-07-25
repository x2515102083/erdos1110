/-!
# Basic definitions and antichain lemmas
-/

namespace Erdos1110

abbrev Point := Nat × Nat

def Term (p q : Nat) (x : Point) : Nat :=
  p ^ x.1 * q ^ x.2

def CoordLe (x y : Point) : Prop :=
  x.1 ≤ y.1 ∧ x.2 ≤ y.2

def IsAntichain (A : List Point) : Prop :=
  A.Nodup ∧ ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≠ y → ¬ CoordLe x y

def SumTerms (p q : Nat) (A : List Point) : Nat :=
  (A.map (Term p q)).sum

def Representable (p q n : Nat) : Prop :=
  ∃ A : List Point, IsAntichain A ∧ SumTerms p q A = n

def Nonrepresentable (p q n : Nat) : Prop :=
  ¬ Representable p q n

def PairwiseCoprimeOn (P : Nat → Prop) : Prop :=
  ∀ F : List Nat, ∃ n : Nat, 0 < n ∧ P n ∧ ∀ m, m ∈ F → Nat.Coprime n m

def PairwiseCoprimeNonrepSeq (p q : Nat) (f : Nat → Nat) : Prop :=
  (∀ n, 1 < f n ∧ Nonrepresentable p q (f n) ∧ Nat.Coprime (f n) (p * q)) ∧
  (∀ ⦃m n⦄, m ≠ n → Nat.Coprime (f m) (f n))

def Erdos1110Conclusion (p q : Nat) : Prop :=
  ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq p q f

theorem mem_term_le_sum
    {p q : Nat} {x : Point} :
    ∀ {A : List Point}, x ∈ A → Term p q x ≤ SumTerms p q A
  | [], hx => nomatch hx
  | y :: ys, hx => by
      rw [List.mem_cons] at hx
      cases hx with
      | inl hxy =>
          subst x
          simp [SumTerms]
      | inr hxys =>
          have ih : Term p q x ≤ SumTerms p q ys := mem_term_le_sum hxys
          dsimp [SumTerms] at ih ⊢
          simp
          exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem antichain_not_coordLe
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ¬ CoordLe x y :=
  hA.2 hx hy hne

theorem antichain_incomparable
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) :
    ¬ CoordLe x y ∧ ¬ CoordLe y x :=
  ⟨hA.2 hx hy hne, hA.2 hy hx (fun hyx => hne hyx.symm)⟩

theorem antichain_same_first_eq
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hfirst : x.1 = y.1) :
    x = y := by
  by_cases hxy : x = y
  · exact hxy
  have hle_or : x.2 ≤ y.2 ∨ y.2 ≤ x.2 := Nat.le_total x.2 y.2
  cases hle_or with
  | inl hxy2 =>
      have hcoord : CoordLe x y := by
        constructor
        · rw [hfirst]
          exact Nat.le_refl y.1
        · exact hxy2
      exact False.elim ((hA.2 hx hy hxy) hcoord)
  | inr hyx2 =>
      have hcoord : CoordLe y x := by
        constructor
        · rw [hfirst]
          exact Nat.le_refl y.1
        · exact hyx2
      exact False.elim ((hA.2 hy hx (fun hyx => hxy hyx.symm)) hcoord)

theorem antichain_same_second_eq
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hsecond : x.2 = y.2) :
    x = y := by
  by_cases hxy : x = y
  · exact hxy
  have hle_or : x.1 ≤ y.1 ∨ y.1 ≤ x.1 := Nat.le_total x.1 y.1
  cases hle_or with
  | inl hxy1 =>
      have hcoord : CoordLe x y := by
        constructor
        · exact hxy1
        · rw [hsecond]
          exact Nat.le_refl y.2
      exact False.elim ((hA.2 hx hy hxy) hcoord)
  | inr hyx1 =>
      have hcoord : CoordLe y x := by
        constructor
        · exact hyx1
        · rw [hsecond]
          exact Nat.le_refl y.2
      exact False.elim ((hA.2 hy hx (fun hyx => hxy hyx.symm)) hcoord)

theorem antichain_second_strictAnti_of_first_lt
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hfirst : x.1 < y.1) :
    y.2 < x.2 := by
  have hxy_ne : x ≠ y := by
    intro hxy
    rw [hxy] at hfirst
    exact (Nat.lt_irrefl y.1) hfirst
  exact Nat.lt_of_not_le fun hxy2 =>
    hA.2 hx hy hxy_ne ⟨Nat.le_of_lt hfirst, hxy2⟩

theorem antichain_first_strictAnti_of_second_lt
    {A : List Point} (hA : IsAntichain A)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A)
    (hsecond : x.2 < y.2) :
    y.1 < x.1 := by
  have hxy_ne : x ≠ y := by
    intro hxy
    rw [hxy] at hsecond
    exact (Nat.lt_irrefl y.2) hsecond
  exact Nat.lt_of_not_le fun hxy1 =>
    hA.2 hx hy hxy_ne ⟨hxy1, Nat.le_of_lt hsecond⟩

theorem coordLe_term_dvd
    {p q : Nat} {x y : Point}
    (hxy : CoordLe x y) :
    Term p q x ∣ Term p q y := by
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p hxy.1) (Nat.pow_dvd_pow q hxy.2)

theorem pow_mul_pow_dvd_first_le
    {r s i j i' j' : Nat}
    (hr : 1 < r) (hrs : Nat.Coprime r s)
    (hdiv : r ^ i * s ^ j ∣ r ^ i' * s ^ j') :
    i ≤ i' := by
  by_cases hle : i ≤ i'
  · exact hle
  have hi'i : i' < i := Nat.lt_of_not_ge hle
  let d := i - i'
  have hdpos : 0 < d := Nat.sub_pos_of_lt hi'i
  have hr_pos : 0 < r := Nat.lt_trans Nat.zero_lt_one hr
  have hi'_le_i : i' ≤ i := Nat.le_of_lt hi'i
  have hsplit : r ^ i = r ^ i' * r ^ d := by
    have hadd : i' + d = i := Nat.add_sub_of_le hi'_le_i
    rw [← hadd, Nat.pow_add]
  have hri_dvd_target : r ^ i ∣ r ^ i' * s ^ j' :=
    Nat.dvd_trans (Nat.dvd_mul_right _ _) hdiv
  have hcancel : r ^ d ∣ s ^ j' := by
    have hri'_pos : 0 < r ^ i' := (Nat.pow_pos hr_pos : 0 < r ^ i')
    exact (Nat.mul_dvd_mul_iff_left hri'_pos).mp (by
      simpa [hsplit] using hri_dvd_target)
  have hcop : Nat.Coprime (r ^ d) (s ^ j') :=
    (hrs.pow_left d).pow_right j'
  have hgcd_left : Nat.gcd (r ^ d) (s ^ j') = r ^ d :=
    Nat.gcd_eq_left hcancel
  have hgcd_one : Nat.gcd (r ^ d) (s ^ j') = 1 :=
    Nat.Coprime.gcd_eq_one hcop
  have hrd_eq_one : r ^ d = 1 := hgcd_left.symm.trans hgcd_one
  have hone_lt : 1 < r ^ d := Nat.one_lt_pow (Nat.ne_of_gt hdpos) hr
  rw [hrd_eq_one] at hone_lt
  exact False.elim ((Nat.lt_irrefl 1) hone_lt)

theorem term_dvd_coordLe
    {p q : Nat} {x y : Point}
    (hp : 1 < p) (hq : 1 < q) (hpq : Nat.Coprime p q)
    (hdiv : Term p q x ∣ Term p q y) :
    CoordLe x y := by
  constructor
  · exact pow_mul_pow_dvd_first_le hp hpq (by simpa [Term] using hdiv)
  · have hdiv' : q ^ x.2 * p ^ x.1 ∣ q ^ y.2 * p ^ y.1 := by
      simpa [Term, Nat.mul_comm] using hdiv
    exact pow_mul_pow_dvd_first_le hq hpq.symm hdiv'

theorem term_dvd_iff_coordLe
    {p q : Nat} {x y : Point}
    (hp : 1 < p) (hq : 1 < q) (hpq : Nat.Coprime p q) :
    Term p q x ∣ Term p q y ↔ CoordLe x y :=
  ⟨term_dvd_coordLe hp hq hpq, coordLe_term_dvd⟩

theorem antichain_filter
    {A : List Point} (hA : IsAntichain A) (P : Point → Bool) :
    IsAntichain (A.filter P) := by
  constructor
  · exact List.pairwise_filter.mpr
      (hA.1.imp (fun hxy _ _ => hxy))
  · intro x hx y hy hne hcoord
    have hxA : x ∈ A := (List.mem_filter.mp hx).1
    have hyA : y ∈ A := (List.mem_filter.mp hy).1
    exact hA.2 hxA hyA hne hcoord

theorem filter_eq_nil_of_forall_not (P : Point → Bool) :
    ∀ A : List Point, (∀ x, x ∈ A → ¬ P x = true) → A.filter P = []
  | [], _ => rfl
  | z :: zs, hnot => by
      have hz : ¬ P z = true := hnot z List.mem_cons_self
      have hzs : zs.filter P = [] := filter_eq_nil_of_forall_not P zs (by
        intro y hy
        exact hnot y (List.mem_cons_of_mem z hy))
      rw [List.filter_cons_of_neg hz, hzs]

theorem filter_eq_singleton_of_unique (P : Point → Bool) :
    ∀ {A : List Point} {w : Point},
      A.Nodup → w ∈ A → P w = true →
      (∀ y, y ∈ A → P y = true → y = w) →
      A.filter P = [w]
  | [], _, _, hw, _, _ => by
      exact False.elim (List.not_mem_nil hw)
  | z :: zs, w, hnodup, hw, hPw, huniq => by
      have hz_not_tail : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzs_nodup : zs.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hzP : P z = true
      · have hzw : z = w := huniq z List.mem_cons_self hzP
        subst w
        have hfilter_tail : zs.filter P = [] := by
          apply filter_eq_nil_of_forall_not
          intro y hy hyP
          have hyz : y = z := huniq y (List.mem_cons_of_mem z hy) hyP
          subst y
          exact hz_not_tail hy
        rw [List.filter_cons_of_pos hzP, hfilter_tail]
      · have hw_tail : w ∈ zs := by
          cases List.mem_cons.mp hw with
          | inl hwz =>
              subst w
              exact False.elim (hzP hPw)
          | inr hwt => exact hwt
        have huniq_tail : ∀ y, y ∈ zs → P y = true → y = w := by
          intro y hy hyP
          exact huniq y (List.mem_cons_of_mem z hy) hyP
        rw [List.filter_cons_of_neg hzP]
        exact filter_eq_singleton_of_unique P hzs_nodup hw_tail hPw huniq_tail

theorem list_eq_nil_of_forall_not_mem :
    ∀ A : List Point, (∀ x, x ∈ A → False) → A = []
  | [], _ => rfl
  | z :: _, h => by
      exact False.elim (h z List.mem_cons_self)

theorem list_eq_singleton_of_mem_unique
    {A : List Point} {w : Point}
    (hnodup : A.Nodup)
    (hw : w ∈ A)
    (huniq : ∀ y, y ∈ A → y = w) :
    A = [w] := by
  cases A with
  | nil =>
      exact False.elim (List.not_mem_nil hw)
  | cons z zs =>
      have hz_not : ¬ z ∈ zs := (List.nodup_cons.mp hnodup).1
      have hzw : z = w := huniq z List.mem_cons_self
      subst z
      have hzs_nil : zs = [] := by
        apply list_eq_nil_of_forall_not_mem
        intro y hy
        have hyw : y = w := huniq y (List.mem_cons_of_mem w hy)
        subst y
        exact hz_not hy
      rw [hzs_nil]

end Erdos1110
