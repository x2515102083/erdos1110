import Erdos1110.LowRows

/-!
# Provider interfaces
-/

namespace Erdos1110

structure ValidBases (p q : Nat) : Prop where
  one_lt_p : 1 < p
  one_lt_q : 1 < q
  coprime : Nat.Coprime p q

theorem validBases_mul_gt_one
    {p q : Nat} (hb : ValidBases p q) :
    1 < p * q := by
  have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hb.one_lt_q
  have hp_le_pm : p ≤ p * q := Nat.le_mul_of_pos_right p hqpos
  exact Nat.lt_of_lt_of_le hb.one_lt_p hp_le_pm

theorem positive_of_coprime_mul_validBases
    {p q D : Nat}
    (hb : ValidBases p q)
    (hD : Nat.Coprime D (p * q)) :
    0 < D := by
  by_cases hzero : D = 0
  · subst D
    rw [Nat.Coprime, Nat.gcd_zero_left] at hD
    have hpq_gt : 1 < p * q := validBases_mul_gt_one hb
    rw [hD] at hpq_gt
    exact False.elim ((Nat.lt_irrefl 1) hpq_gt)
  · exact Nat.pos_of_ne_zero hzero

def SupportCoprimeWithin (u v : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D v → Nat.Coprime u D

structure GoodSeed (p q c : Nat) : Prop where
  c_pos : 0 < c
  c_lt : c < p - 1
  nonrep : Nonrepresentable p q c
  coprime_pq : Nat.Coprime c (p * q)
  support_succ : SupportCoprimeWithin (c + 1) (p * q)

def FreshExtension (p q D N : Nat) : Prop :=
  1 < N ∧ Nonrepresentable p q N ∧ Nat.Coprime N (p * q) ∧ Nat.Coprime N D

def FreshExtensionProvider (p q _c : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) → ∃ N : Nat, FreshExtension p q D N

def CongruentExtension (p q c D N : Nat) : Prop :=
  1 < N ∧
  Nonrepresentable p q N ∧
  Nat.Coprime N (p * q) ∧
  ∃ k : Nat, N = (c + 1) + D * k

def CongruentExtensionProvider (p q c : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) → ∃ N : Nat, CongruentExtension p q c D N

def CoprimeBasePeriodProvider (b : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime b D →
    ∃ L : Nat, 0 < L ∧ ∃ r : Nat, b ^ L = 1 + D * r

def BasicPeriodProvider (p q : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) →
    ∃ L : Nat,
      0 < L ∧
      (∃ r : Nat, p ^ L = 1 + D * r) ∧
      (∃ r : Nat, q ^ L = 1 + D * r)

def PeriodProvider (p q : Nat) : Prop :=
  ∀ D : Nat, Nat.Coprime D (p * q) →
    ∃ L : Nat,
      0 < L ∧
      (∀ a : Nat, L ∣ a → ∃ r : Nat, p ^ a = 1 + D * r) ∧
      (∀ M : Nat, L ∣ M → ∃ r : Nat, q ^ M = 1 + D * r)

def PowerWindowProvider (p q c : Nat) : Prop :=
  ∀ L : Nat, 0 < L →
    ∃ a M : Nat,
      0 < a ∧ 0 < M ∧
      L ∣ a ∧ L ∣ M ∧
      p ^ a < q ^ M ∧
      c * q ^ M < (p - 1) * p ^ a

def LowRowSyncProvider (p q : Nat) : Prop :=
  ∀ a M : Nat, ∀ A : List Point,
    1 < p →
    1 < q →
    Nat.Coprime p q →
    0 < M →
    p ^ a < q ^ M →
    IsAntichain A →
    (∀ x, x ∈ A → x.1 ≤ a) →
    (∀ x, x ∈ A → x.2 < M) →
    (∃ u v : Nat, SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) →
      A = [(a, 0)]

def LowRowResidualProvider (p q : Nat) : Prop :=
  ∀ a M : Nat, ∀ A : List Point, ∀ t : Nat,
    1 < p →
    1 < q →
    Nat.Coprime p q →
    0 < M →
    p ^ a < q ^ M →
    IsAntichain A →
    (∀ x, x ∈ A → x.1 ≤ a) →
    (∀ x, x ∈ A → x.2 < M) →
    (t, 0) ∈ A →
    t < a →
    (∃ u v : Nat, SumTerms p q A + q ^ M * u = p ^ a + q ^ M * v) →
      False

end Erdos1110
