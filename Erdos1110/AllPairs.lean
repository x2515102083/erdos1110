import Erdos1110.Density
import Erdos1110.GenericWindow
import Erdos1110.ResidueCase
import Erdos1110.Statement

/-!
# Pairwise-coprime nonrepresentable integers for all admissible bases

The counting argument covers the large-base range of Yu and Chen,
*On a conjecture of Erdős and Lewin*, J. Number Theory 238 (2022), 763–778,
DOI: 10.1016/j.jnt.2021.09.018. The remaining small pairs use the residue
argument for (4,3), a seed for (7,2), and Apiros3's existing formalization
of (5,2), (9,2), and (5,3).

This proves the pairwise-coprime existence clause of Erdős #1110. It does
not assert a value of the density for the exceptional small base pairs.
-/

namespace Erdos1110

theorem yuChenRange_unconditional {p q : ℕ}
    (hcop : Nat.Coprime p q) (hpq : p > q) (hq : q ≥ 2)
    (hr : YuChenRange p q) : Erdos1110Conclusion p q := by
  have hb : ValidBases p q := ⟨by omega, by omega, hcop⟩
  by_cases hd : (4 ≤ q) ∨ (q = 3 ∧ 7 ≤ p) ∨ (q = 2 ∧ 11 ≤ p)
  · exact infinite_pairwise_nonrep_of_freshExtensionProvider
      (densityRange_freshExtension hb hpq hd)
  · have hc3 : ¬ (p = 6 ∧ q = 3) := by
      rintro ⟨rfl, rfl⟩
      norm_num at hcop
    have hc2 : q = 2 → p % 2 = 1 := by
      intro hq2
      subst q
      exact Nat.odd_iff.mp hcop.odd_of_right
    have hcases : (p = 4 ∧ q = 3) ∨ (p = 7 ∧ q = 2) := by
      rcases hr with hr | ⟨rfl, hr⟩ | ⟨rfl, h3, h5, h9⟩
      · omega
      · omega
      · have := hc2 rfl
        omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact exceptional4_3_unconditional
    · exact exceptional7_2_unconditional

theorem erdos1110_pairwise_unconditional {p q : ℕ}
    (hcop : Nat.Coprime p q) (hpq : p > q) (hq : q ≥ 2)
    (hne : ¬ (p = 3 ∧ q = 2)) : Erdos1110Conclusion p q :=
  erdos1110_from_yuChen (fun {_ _} => yuChenRange_unconditional) hcop hpq hq hne

theorem erdos1110_pairwise {p q : ℕ}
    (hcop : Nat.Coprime p q) (hpq : p > q) (hq : q ≥ 2)
    (hne : ¬ (p = 3 ∧ q = 2)) :
    ∃ A : Set ℕ, A.Infinite ∧ A.Pairwise Nat.Coprime ∧
      ∀ n ∈ A, ¬ PrimitiveRepresentable p q n :=
  primitiveConclusion_of_conclusion ⟨by omega, by omega, hcop⟩
    (erdos1110_pairwise_unconditional hcop hpq hq hne)

end Erdos1110
