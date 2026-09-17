import Erdos1110.Sequence
import Mathlib.Tactic

/-!
# The base pair (4, 3)

A divisibility antichain contains at most one term with second exponent zero.
Such a term is 1 modulo 3; all other terms vanish modulo 3. Thus every integer
congruent to 2 modulo 3 is nonrepresentable. The witnesses 12D - 1 avoid all
prime divisors of both 12 and the previous-product modulus D.
-/

namespace Erdos1110

private theorem term_four_three_mod (x : Point) :
    Term 4 3 x % 3 = if x.2 = 0 then 1 else 0 := by
  rcases x with ⟨a, b⟩
  cases b with
  | zero => simp [Term, Nat.pow_mod]
  | succ b => simp [Term, pow_succ, Nat.mul_mod]

private theorem sum_four_three_mod_zero (A : List Point)
    (h : ∀ x ∈ A, x.2 ≠ 0) : SumTerms 4 3 A % 3 = 0 := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    change (Term 4 3 x + SumTerms 4 3 xs) % 3 = 0
    rw [Nat.add_mod, term_four_three_mod, if_neg hx, ht]

 theorem representable_four_three_mod {n : Nat} (hn : Representable 4 3 n) :
    n % 3 = 0 ∨ n % 3 = 1 := by
  obtain ⟨A, hA, rfl⟩ := hn
  induction A with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    have htail : IsAntichain xs := by
      refine ⟨(List.nodup_cons.mp hA.1).2, ?_⟩
      intro y hy z hz hne
      exact hA.2 (by simp [hy]) (by simp [hz]) hne
    by_cases hx : x.2 = 0
    · have ht : SumTerms 4 3 xs % 3 = 0 := by
        apply sum_four_three_mod_zero
        intro y hy hzero
        have heq : x = y := antichain_same_second_eq hA
          (by simp) (by simp [hy]) (hx.trans hzero.symm)
        exact (List.nodup_cons.mp hA.1).1 (heq.symm ▸ hy)
      right
      change (Term 4 3 x + SumTerms 4 3 xs) % 3 = 1
      rw [Nat.add_mod, term_four_three_mod, if_pos hx, ht]
    · have ht := ih htail
      change (Term 4 3 x + SumTerms 4 3 xs) % 3 = 0 ∨
        (Term 4 3 x + SumTerms 4 3 xs) % 3 = 1
      simpa [Nat.add_mod, term_four_three_mod, hx] using ht

theorem nonrepresentable_four_three_of_mod {n : Nat} (hn : n % 3 = 2) :
    Nonrepresentable 4 3 n := by
  intro h
  have := representable_four_three_mod h
  omega

theorem freshExtension_four_three : FreshExtensionProvider 4 3 0 := by
  intro D hD
  have hDpos : 0 < D := positive_of_coprime_mul_validBases
    ⟨by decide, by decide, by decide⟩ hD
  have hprod : 1 ≤ 12 * D := by omega
  have hsum : 12 * D - 1 + 1 = 12 * D := Nat.sub_add_cancel hprod
  have hcop : Nat.Coprime (12 * D - 1) (12 * D) := by
    have hc : Nat.Coprime (12 * D - 1) (12 * D - 1 + 1) := by
      simp [Nat.Coprime]
    simpa only [hsum] using hc
  refine ⟨12 * D - 1, ?_, ?_, ?_, ?_⟩
  · omega
  · apply nonrepresentable_four_three_of_mod
    omega
  · exact hcop.of_dvd_right (by omega : 4 * 3 ∣ 12 * D)
  · exact hcop.of_dvd_right (dvd_mul_left D 12)

theorem exceptional4_3_unconditional : Erdos1110Conclusion 4 3 :=
  infinite_pairwise_nonrep_of_freshExtensionProvider freshExtension_four_three

end Erdos1110
