import Erdos1110.Counting
import Erdos1110.Sequence
import Mathlib

namespace Erdos1110

noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

private theorem weighted_choose (A B : ℕ) :
    Nat.choose (A + B) A * 3 ^ B ≤ 4 ^ (A + B) := by
  have h := Finset.single_le_sum (f := fun i : ℕ =>
    1 ^ i * 3 ^ (A + B - i) * Nat.choose (A + B) i)
    (fun i _ => Nat.zero_le _) (show A ∈ Finset.range (A + B + 1) by simp)
  have he := add_pow (1 : ℕ) 3 (A + B)
  simp only [Nat.cast_id] at he
  rw [← he] at h
  simpa [Nat.add_sub_cancel_left, Nat.mul_comm] using h

private theorem geometric_gap {u v w M : ℕ}
    (hv : 0 < v) (hvw : v ≤ w) (hwu : w < u * v) :
    ∃ t : ℕ, 3 * M * w ^ t < u ^ t * v ^ t := by
  have hw : 0 < w := lt_of_lt_of_le hv hvw
  have hr : (1 : ℚ) < (u * v : ℕ) / (w : ℚ) := by
    rw [one_lt_div (by exact_mod_cast hw)]
    exact_mod_cast hwu
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (3 * M : ℚ) hr
  refine ⟨t, ?_⟩
  rw [div_pow, lt_div_iff₀ (by positivity)] at ht
  have ht' : (3 * M * w ^ t : ℕ) < (u * v) ^ t := by exact_mod_cast ht
  simpa [mul_pow] using ht'

private theorem fresh_of_geometric_count {p q u v w : ℕ}
    (hb : ValidBases p q) (hv : 0 < v) (hvw : v ≤ w) (hwu : w < u * v)
    (hc : ∀ t : ℕ,
      ((Finset.range (u ^ t)).filter (fun m => Representable p q m)).card * v ^ t ≤ w ^ t) :
    FreshExtensionProvider p q 0 := by
  classical
  intro D hD
  let M := p * q * D
  have hM : 0 < M := Nat.mul_pos
    (Nat.mul_pos (by have := hb.one_lt_p; omega) (by have := hb.one_lt_q; omega))
    (positive_of_coprime_mul_validBases hb hD)
  obtain ⟨t, ht⟩ := geometric_gap hv hvw hwu (M := M)
  let S := (Finset.range (u ^ t)).filter (fun m => Representable p q m)
  have hc' : S.card * v ^ t ≤ w ^ t := hc t
  have hvw' : v ^ t ≤ w ^ t := Nat.pow_le_pow_left hvw t
  have hgap : M * (S.card + 2) < u ^ t := by
    have hbound : M * (S.card + 2) * v ^ t ≤ 3 * M * w ^ t := by
      have hcm := Nat.mul_le_mul_left M hc'
      have hvm := Nat.mul_le_mul_left (2 * M) hvw'
      nlinarith
    have hlt := lt_of_le_of_lt hbound ht
    exact (Nat.mul_lt_mul_right (Nat.pow_pos hv)).mp hlt
  have hex : ∃ k ∈ Finset.range (S.card + 1),
      ¬ Representable p q (1 + M * (k + 1)) := by
    by_contra! hall
    have hsub : (Finset.range (S.card + 1)).image (fun k => 1 + M * (k + 1)) ⊆ S := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, hall k hk⟩
      have hk' := Finset.mem_range.mp hk
      have : 1 + M * (k + 1) ≤ M * (S.card + 2) := by nlinarith
      exact lt_of_le_of_lt this hgap
    have hi : Function.Injective (fun k : ℕ => 1 + M * (k + 1)) := by
      intro a b hab
      nlinarith
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hi, Finset.card_range] at hcard
    omega
  obtain ⟨k, hk, hn⟩ := hex
  refine ⟨1 + M * (k + 1), ?_, hn, ?_, ?_⟩
  · nlinarith
  · have hcop : Nat.Coprime (1 + M * (k + 1)) M := by
      simp [Nat.Coprime]
    exact hcop.of_dvd_right (by dsimp [M]; exact Nat.dvd_mul_right _ _)
  · have hcop : Nat.Coprime (1 + M * (k + 1)) M := by
      simp [Nat.Coprime]
    exact hcop.of_dvd_right (by dsimp [M]; exact Nat.dvd_mul_left _ _)

private theorem density_unweighted {p q u a b : ℕ}
    (hb : ValidBases p q) (hu : u ≤ p ^ a) (huq : u ≤ q ^ b)
    (hgap : 2 ^ (a + b) < u) : FreshExtensionProvider p q 0 := by
  apply fresh_of_geometric_count hb (v := 1) (w := 2 ^ (a + b)) (by omega)
    (Nat.one_le_pow _ _ (by omega)) (by simpa using hgap)
  intro t
  have hp : u ^ t ≤ p ^ (a * t) := by
    simpa [pow_mul] using Nat.pow_le_pow_left hu t
  have hq : u ^ t ≤ q ^ (b * t) := by
    simpa [pow_mul] using Nat.pow_le_pow_left huq t
  have hc := representable_count_le hb.one_lt_p hb.one_lt_q hp hq
  have hbin := Nat.choose_le_two_pow (a * t + b * t) (a * t)
  have hpow : 2 ^ (a * t + b * t) = (2 ^ (a + b)) ^ t := by
    rw [← pow_mul, Nat.add_mul]
  simpa [hpow] using le_trans hc hbin

theorem densityRange_freshExtension {p q : ℕ} (hb : ValidBases p q)
    (hpq : q < p)
    (hr : (4 ≤ q) ∨ (q = 3 ∧ 7 ≤ p) ∨ (q = 2 ∧ 11 ≤ p)) :
    FreshExtensionProvider p q 0 := by
  rcases hr with hq | ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · apply density_unweighted hb (u := 2 ^ 20) (a := 9) (b := 10)
    · exact le_trans (by norm_num) (Nat.pow_le_pow_left (by omega : 5 ≤ p) 9)
    · exact le_trans (by norm_num) (Nat.pow_le_pow_left hq 10)
    · norm_num
  · apply density_unweighted hb (u := 2 ^ 200) (a := 72) (b := 127)
    · exact le_trans (by norm_num) (Nat.pow_le_pow_left hp 72)
    · norm_num
    · norm_num
  · apply fresh_of_geometric_count hb (u := 2 ^ 100) (v := 3 ^ 100)
      (w := 4 ^ 129) (by positivity) (by norm_num) (by norm_num)
    intro t
    have hbase : 2 ^ 100 ≤ p ^ 29 :=
      le_trans (by norm_num) (Nat.pow_le_pow_left hp 29)
    have hpp : (2 ^ 100) ^ t ≤ p ^ (29 * t) := by
      simpa [pow_mul] using Nat.pow_le_pow_left hbase t
    have hqq : (2 ^ 100) ^ t ≤ 2 ^ (100 * t) := by rw [pow_mul]
    have hc := representable_count_le hb.one_lt_p hb.one_lt_q hpp hqq
    have hw := weighted_choose (29 * t) (100 * t)
    have hm := Nat.mul_le_mul_right (3 ^ (100 * t)) hc
    have he : 29 * t + 100 * t = 129 * t := by omega
    simpa [he, pow_mul] using le_trans hm hw

end
end Erdos1110
