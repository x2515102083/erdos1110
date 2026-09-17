import Erdos1110.PowerWindow

namespace Erdos1110

/-- The generic logarithmic window and seed amplification already proved upstream
in `PowerWindow` and `Sequence` give the conclusion for any good seed. -/
theorem erdos1110Conclusion_of_goodSeed
    {p q c : Nat} (hb : ValidBases p q) (hs : GoodSeed p q c) :
    Erdos1110Conclusion p q :=
  goodSeedAmplification_of_window hb hs
    (powerWindowProvider_of_validBases_goodSeed hb hs)

theorem validBases_7_2 : ValidBases 7 2 where
  one_lt_p := by decide
  one_lt_q := by decide
  coprime := by decide

theorem c3_nonrepresentable_7_2 : Nonrepresentable 7 2 3 := by
  apply c_lt_p_and_not_q_power_nonrepresentable
    (by decide) (by decide) (by decide) (by decide)
  intro j h
  cases j with
  | zero => norm_num at h
  | succ j =>
    cases j with
    | zero => norm_num at h
    | succ j =>
      have hle : 4 ≤ 2 ^ (j + 1 + 1) := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
          (by omega : 2 ≤ j + 1 + 1)
        exact hpow
      omega

theorem support_4_within_14 : SupportCoprimeWithin 4 14 := by
  intro D hD
  have hD14 : Nat.Coprime D (7 * 2) := by simpa using hD
  have hD2 : Nat.Coprime D 2 := (Nat.coprime_mul_iff_right.mp hD14).2
  simpa using hD2.symm.pow_left 2

theorem seed_7_2 : GoodSeed 7 2 3 where
  c_pos := by decide
  c_lt := by decide
  nonrep := c3_nonrepresentable_7_2
  coprime_pq := by decide
  support_succ := by simpa using support_4_within_14

theorem powerWindow_7_2 : PowerWindowProvider 7 2 3 :=
  powerWindowProvider_of_validBases_goodSeed validBases_7_2 seed_7_2

theorem exceptional7_2_unconditional : Erdos1110Conclusion 7 2 :=
  erdos1110Conclusion_of_goodSeed validBases_7_2 seed_7_2

end Erdos1110
