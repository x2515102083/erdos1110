import Erdos1110.Exceptional

/-!
# Yu-Chen range bridge
-/

namespace Erdos1110

def MissingPair (p q : Nat) : Prop :=
  (p = 5 ∧ q = 2) ∨ (p = 9 ∧ q = 2) ∨ (p = 5 ∧ q = 3)

def YuChenRange (p q : Nat) : Prop :=
  q > 3 ∨ (q = 3 ∧ p ≠ 5) ∨ (q = 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 9)

private theorem nat_cases_ge2_le3 {q : Nat} (hq : q ≥ 2) (hqle : q ≤ 3) :
    q = 2 ∨ q = 3 := by
  cases q with
  | zero => exact False.elim ((by decide : ¬ 0 ≥ 2) hq)
  | succ q1 =>
      cases q1 with
      | zero => exact False.elim ((by decide : ¬ 1 ≥ 2) hq)
      | succ q2 =>
          cases q2 with
          | zero => exact Or.inl rfl
          | succ q3 =>
              cases q3 with
              | zero => exact Or.inr rfl
              | succ q4 =>
                  have h1 : Nat.succ (Nat.succ (Nat.succ q4)) ≤ 2 :=
                    Nat.le_of_succ_le_succ hqle
                  have h2 : Nat.succ (Nat.succ q4) ≤ 1 :=
                    Nat.le_of_succ_le_succ h1
                  have h3 : Nat.succ q4 ≤ 0 :=
                    Nat.le_of_succ_le_succ h2
                  exact False.elim (Nat.not_succ_le_zero q4 h3)

theorem range_split
    {p q : Nat}
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    YuChenRange p q ∨ MissingPair p q := by
  by_cases hq3lt : q > 3
  · exact Or.inl (Or.inl hq3lt)
  · have hqle3 : q ≤ 3 := Nat.le_of_not_gt hq3lt
    cases nat_cases_ge2_le3 hq hqle3 with
    | inl hq2 =>
        subst q
        by_cases hp3 : p = 3
        · exact False.elim (hnot32 ⟨hp3, rfl⟩)
        · by_cases hp5 : p = 5
          · exact Or.inr (Or.inl ⟨hp5, rfl⟩)
          · by_cases hp9 : p = 9
            · exact Or.inr (Or.inr (Or.inl ⟨hp9, rfl⟩))
            · exact Or.inl (Or.inr (Or.inr ⟨rfl, hp3, hp5, hp9⟩))
    | inr hq3 =>
        subst q
        by_cases hp5 : p = 5
        · exact Or.inr (Or.inr (Or.inr ⟨hp5, rfl⟩))
        · exact Or.inl (Or.inr (Or.inl ⟨rfl, hp5⟩))

theorem erdos1110_unconditional_bridge
    (yuChen : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → YuChenRange p q →
        Erdos1110Conclusion p q)
    (exceptional : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → MissingPair p q →
        Erdos1110Conclusion p q)
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    Erdos1110Conclusion p q := by
  cases range_split hpq hq hnot32 with
  | inl hYC => exact yuChen hpq_coprime hpq hq hYC
  | inr hMissing => exact exceptional hpq_coprime hpq hq hMissing

end Erdos1110
