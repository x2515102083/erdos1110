import Erdos1110.Core
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Erdos1110

open Set
open scoped Topology

noncomputable section

private theorem coprime_pow_eq_pow_absurd
    {p q a b : Nat}
    (hp : 1 < p)
    (hc : Nat.Coprime p q)
    (hb : 0 < b)
    (h : p ^ b = q ^ a) :
    False := by
  have hcop : Nat.Coprime (p ^ b) (q ^ a) :=
    (hc.pow_left b).pow_right a
  have hself : Nat.Coprime (p ^ b) (p ^ b) := by
    simpa [h] using hcop
  have hgcd : Nat.gcd (p ^ b) (p ^ b) = 1 :=
    Nat.Coprime.gcd_eq_one hself
  rw [Nat.gcd_self] at hgcd
  have hpgt : 1 < p ^ b :=
    Nat.one_lt_pow (Nat.ne_of_gt hb) hp
  omega

theorem irrational_log_nat_div_log_nat
    {p q : Nat}
    (hp : 1 < p)
    (hq : 1 < q)
    (hc : Nat.Coprime p q) :
    Irrational (Real.log (p : Real) / Real.log (q : Real)) := by
  intro hrat
  rcases hrat with ⟨r, hr⟩
  have hpR : (1 : Real) < p := by exact_mod_cast hp
  have hqR : (1 : Real) < q := by exact_mod_cast hq
  have hlogp_pos : 0 < Real.log (p : Real) := Real.log_pos hpR
  have hlogq_pos : 0 < Real.log (q : Real) := Real.log_pos hqR
  have hratio_pos : 0 < Real.log (p : Real) / Real.log (q : Real) :=
    div_pos hlogp_pos hlogq_pos
  have hr_pos : 0 < r := by
    exact (Rat.cast_pos (K := Real)).mp (by simpa [hr] using hratio_pos)
  have hnum_pos : 0 < r.num := by
    exact (Rat.num_pos (a := r)).mpr hr_pos
  have hden_pos : 0 < r.den := r.den_pos
  have hden_ne : ((r.den : Nat) : Real) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hlogq_ne : Real.log (q : Real) ≠ 0 := hlogq_pos.ne'
  have hratio :
      (r.num : Real) / (r.den : Real) =
        Real.log (p : Real) / Real.log (q : Real) := by
    simpa [Rat.cast_def] using hr
  have hmul :
      (r.den : Real) * Real.log (p : Real) =
        (r.num : Real) * Real.log (q : Real) := by
    field_simp [hden_ne, hlogq_ne] at hratio
    linarith
  let a : Nat := r.num.natAbs
  have hnum_nonneg : 0 ≤ r.num := le_of_lt hnum_pos
  have hnum_cast_int : ((a : Nat) : Int) = r.num := by
    dsimp [a]
    exact Int.natAbs_of_nonneg hnum_nonneg
  have hnum_cast_real : (a : Real) = (r.num : Real) := by
    exact_mod_cast hnum_cast_int
  have hlogeq :
      Real.log ((p : Real) ^ r.den) = Real.log ((q : Real) ^ a) := by
    rw [Real.log_pow (p : Real) r.den, Real.log_pow (q : Real) a]
    rw [hnum_cast_real]
    exact hmul
  have hp_pow_pos : 0 < (p : Real) ^ r.den := pow_pos (lt_trans zero_lt_one hpR) _
  have hq_pow_pos : 0 < (q : Real) ^ a := pow_pos (lt_trans zero_lt_one hqR) _
  have hpow_real : (p : Real) ^ r.den = (q : Real) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hp_pow_pos) (Set.mem_Ioi.mpr hq_pow_pos) hlogeq
  have hpow_nat : p ^ r.den = q ^ a := by
    apply Nat.cast_injective (R := Real)
    simpa only [Nat.cast_pow] using hpow_real
  exact coprime_pow_eq_pow_absurd hp hc hden_pos hpow_nat

private theorem circle_arc_open
    {δ : Real} (hδlt : δ < 1) :
    IsOpen (((↑) : Real → AddCircle (1 : Real)) '' Set.Ioo (1 - δ) 1) := by
  let e : OpenPartialHomeomorph Real (AddCircle (1 : Real)) :=
    AddCircle.openPartialHomeomorphCoe (p := (1 : Real)) (a := 0)
  have hsub : Set.Ioo (1 - δ) 1 ⊆ e.source := by
    intro x hx
    change x ∈ Set.Ioo (0 : Real) (0 + 1)
    constructor
    · linarith [hx.1, hδlt]
    · simpa using hx.2
  have hopen : IsOpen (e '' Set.Ioo (1 - δ) 1) :=
    e.isOpen_image_of_subset_source isOpen_Ioo hsub
  simpa [e, AddCircle.openPartialHomeomorphCoe] using hopen

theorem exists_pos_nat_one_sided_sub_mul_lt
    {α ε : Real}
    (hirr : Irrational α)
    (hαpos : 0 < α)
    (hε : 0 < ε) :
    ∃ n m : Nat,
      0 < n ∧ 0 < m ∧
      0 < (m : Real) - (n : Real) * α ∧
      (m : Real) - (n : Real) * α < ε := by
  let δ : Real := min ε (1 / 2)
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδleε : δ ≤ ε := min_le_left _ _
  have hδlt1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let U : Set (AddCircle (1 : Real)) :=
    ((↑) : Real → AddCircle (1 : Real)) '' Set.Ioo (1 - δ) 1
  have hUopen : IsOpen U := circle_arc_open hδlt1
  have hUne : U.Nonempty := by
    refine ⟨((1 - δ / 2 : Real) : AddCircle (1 : Real)), ?_⟩
    refine ⟨1 - δ / 2, ?_, rfl⟩
    constructor <;> linarith
  have hdZ : DenseRange (fun z : Int => z • (α : AddCircle (1 : Real))) := by
    simpa using
      (AddCircle.denseRange_zsmul_coe_iff (a := α) (p := (1 : Real))).mpr
        (by simpa using hirr)
  have hdN : DenseRange (fun n : Nat => n • (α : AddCircle (1 : Real))) :=
    (_root_.denseRange_zsmul_iff_nsmul.mp hdZ)
  rcases hdN.exists_mem_open hUopen hUne with ⟨n, hnU⟩
  rcases hnU with ⟨x, hxI, hxEq⟩
  have hxIco : x ∈ Set.Ico (0 : Real) (0 + 1) := by
    constructor
    · have hx0 : 0 < x := by
        have hleft : 1 - δ < x := hxI.1
        linarith
      exact le_of_lt hx0
    · simpa using hxI.2
  have hzero_not : (x : AddCircle (1 : Real)) ≠ 0 := by
    intro hxzero
    have hxeq0 : x = 0 := by
      have h0mem : (0 : Real) ∈ Set.Ico (0 : Real) (0 + 1) := by
        constructor <;> norm_num
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxIco h0mem).mp (by simpa using hxzero)
    have hx0 : 0 < x := by
      have hleft : 1 - δ < x := hxI.1
      linarith
    linarith
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have : (x : AddCircle (1 : Real)) = 0 := by
      simpa [hn0] using hxEq
    exact hzero_not this
  have hxEq' : (x : AddCircle (1 : Real)) =
      (((n : Real) * α : Real) : AddCircle (1 : Real)) := by
    calc
      (x : AddCircle (1 : Real)) = n • (α : AddCircle (1 : Real)) := hxEq
      _ = (((n • α : Real)) : AddCircle (1 : Real)) := by
        exact (AddCircle.coe_nsmul (p := (1 : Real)) (n := n) (x := α)).symm
      _ = (((n : Real) * α : Real) : AddCircle (1 : Real)) := by
        simp [nsmul_eq_mul]
  have hzero :
      (((x - (n : Real) * α : Real)) : AddCircle (1 : Real)) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr hxEq'
  rcases (AddCircle.coe_eq_zero_iff (p := (1 : Real)) (x := x - (n : Real) * α)).mp hzero
    with ⟨z, hz⟩
  have hzreal : (z : Real) = x - (n : Real) * α := by
    simpa [zsmul_eq_mul] using hz
  have hnα_nonneg : 0 ≤ (n : Real) * α :=
    mul_nonneg (Nat.cast_nonneg n) (le_of_lt hαpos)
  have hzlt1R : (z : Real) < 1 := by
    rw [hzreal]
    linarith [hxI.2, hnα_nonneg]
  have hzlt1 : z < (1 : Int) := by exact_mod_cast hzlt1R
  have hzle0 : z ≤ 0 := by omega
  have hmInt_nonneg : 0 ≤ (1 : Int) - z := by omega
  let m : Nat := ((1 : Int) - z).toNat
  have hmcast : (m : Real) = (((1 : Int) - z : Int) : Real) := by
    dsimp [m]
    exact_mod_cast (Int.toNat_of_nonneg hmInt_nonneg)
  have hdiff : (m : Real) - (n : Real) * α = 1 - x := by
    calc
      (m : Real) - (n : Real) * α =
          (((1 : Int) - z : Int) : Real) - (n : Real) * α := by
            rw [hmcast]
      _ = (1 - (z : Real)) - (n : Real) * α := by norm_num
      _ = 1 - x := by
            rw [hzreal]
            ring
  have hdiff_pos : 0 < (m : Real) - (n : Real) * α := by
    rw [hdiff]
    linarith [hxI.2]
  have hm_pos : 0 < m := by
    have hnα_pos : 0 < (n : Real) * α :=
      mul_pos (Nat.cast_pos.mpr hn_pos) hαpos
    have hmR : 0 < (m : Real) := by linarith
    exact Nat.cast_pos.mp hmR
  refine ⟨n, m, hn_pos, hm_pos, hdiff_pos, ?_⟩
  rw [hdiff]
  have : 1 - x < δ := by linarith [hxI.1]
  exact lt_of_lt_of_le this hδleε

private theorem real_pow_lt_of_log_lt
    {p q a M : Nat}
    (hp : 1 < p)
    (hq : 1 < q)
    (hlog : (a : Real) * Real.log (p : Real) < (M : Real) * Real.log (q : Real)) :
    p ^ a < q ^ M := by
  have hpRpos : 0 < (p : Real) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hp)
  have hqRpos : 0 < (q : Real) := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hq)
  have hpowa_pos : 0 < (p : Real) ^ a := pow_pos hpRpos _
  have hqM_pos : 0 < (q : Real) ^ M := pow_pos hqRpos _
  have hreal : (p : Real) ^ a < (q : Real) ^ M := by
    rw [← Real.log_lt_log_iff hpowa_pos hqM_pos]
    rw [Real.log_pow, Real.log_pow]
    exact hlog
  exact_mod_cast hreal

theorem powerWindowProvider_of_validBases_goodSeed
    {p q c : Nat}
    (hb : ValidBases p q)
    (hs : GoodSeed p q c) :
    PowerWindowProvider p q c := by
  intro L hL
  let rho : Real := ((p - 1 : Nat) : Real) / (c : Real)
  have hcRpos : 0 < (c : Real) := by exact_mod_cast hs.c_pos
  have hρgt1 : 1 < rho := by
    have hc_ltR : (c : Real) < ((p - 1 : Nat) : Real) := by exact_mod_cast hs.c_lt
    rw [one_lt_div hcRpos]
    simpa [rho] using hc_ltR
  have hlogρ_pos : 0 < Real.log rho := Real.log_pos hρgt1
  have hpR : (1 : Real) < p := by exact_mod_cast hb.one_lt_p
  have hqR : (1 : Real) < q := by exact_mod_cast hb.one_lt_q
  have hlogp_pos : 0 < Real.log (p : Real) := Real.log_pos hpR
  have hlogq_pos : 0 < Real.log (q : Real) := Real.log_pos hqR
  let α : Real := Real.log (p : Real) / Real.log (q : Real)
  have hαpos : 0 < α := div_pos hlogp_pos hlogq_pos
  have hαirr : Irrational α :=
    irrational_log_nat_div_log_nat hb.one_lt_p hb.one_lt_q hb.coprime
  let eps : Real := Real.log rho / ((L : Real) * Real.log (q : Real))
  have hLposR : 0 < (L : Real) := Nat.cast_pos.mpr hL
  have heps_pos : 0 < eps :=
    div_pos hlogρ_pos (mul_pos hLposR hlogq_pos)
  rcases exists_pos_nat_one_sided_sub_mul_lt hαirr hαpos heps_pos with
    ⟨n, m, hn_pos, hm_pos, hdiff_pos, hdiff_lt⟩
  let a : Nat := L * n
  let M : Nat := L * m
  refine ⟨a, M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hL hn_pos
  · exact Nat.mul_pos hL hm_pos
  · exact ⟨n, rfl⟩
  · exact ⟨m, rfl⟩
  · have hleft0 :
        (n : Real) * (Real.log (p : Real) / Real.log (q : Real)) < (m : Real) :=
      sub_pos.mp (by simpa [α] using hdiff_pos)
    have hleft1 : (n : Real) * Real.log (p : Real) <
        (m : Real) * Real.log (q : Real) := by
      have h := mul_lt_mul_of_pos_right hleft0 hlogq_pos
      have hcancel :
          (Real.log (p : Real) / Real.log (q : Real)) * Real.log (q : Real) =
            Real.log (p : Real) :=
        div_mul_cancel₀ _ hlogq_pos.ne'
      calc
        (n : Real) * Real.log (p : Real) =
            (n : Real) * ((Real.log (p : Real) / Real.log (q : Real)) *
              Real.log (q : Real)) := by rw [hcancel]
        _ = ((n : Real) * (Real.log (p : Real) / Real.log (q : Real))) *
              Real.log (q : Real) := by ring
        _ < (m : Real) * Real.log (q : Real) := h
    have hleftlog : (a : Real) * Real.log (p : Real) <
        (M : Real) * Real.log (q : Real) := by
      have h := mul_lt_mul_of_pos_left hleft1 hLposR
      dsimp [a, M]
      simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h
    exact real_pow_lt_of_log_lt hb.one_lt_p hb.one_lt_q hleftlog
  · have hden_pos : 0 < (L : Real) * Real.log (q : Real) :=
      mul_pos hLposR hlogq_pos
    have hupper0 :
        ((m : Real) - (n : Real) * (Real.log (p : Real) / Real.log (q : Real))) *
            ((L : Real) * Real.log (q : Real)) < Real.log rho := by
      have h := mul_lt_mul_of_pos_right (by simpa [α, eps] using hdiff_lt) hden_pos
      have hcancel :
          Real.log rho / ((L : Real) * Real.log (q : Real)) *
            ((L : Real) * Real.log (q : Real)) = Real.log rho :=
        div_mul_cancel₀ _ hden_pos.ne'
      simpa [eps, hcancel] using h
    have hupper :
        (M : Real) * Real.log (q : Real) -
            (a : Real) * Real.log (p : Real) < Real.log rho := by
      have hcancel :
          (Real.log (p : Real) / Real.log (q : Real)) * Real.log (q : Real) =
            Real.log (p : Real) :=
        div_mul_cancel₀ _ hlogq_pos.ne'
      have hexpr :
          ((m : Real) - (n : Real) *
              (Real.log (p : Real) / Real.log (q : Real))) *
              ((L : Real) * Real.log (q : Real)) =
            (M : Real) * Real.log (q : Real) -
              (a : Real) * Real.log (p : Real) := by
        dsimp [a, M]
        rw [Nat.cast_mul, Nat.cast_mul]
        field_simp [hlogq_pos.ne']
      calc
        (M : Real) * Real.log (q : Real) -
            (a : Real) * Real.log (p : Real) =
              ((m : Real) - (n : Real) *
                (Real.log (p : Real) / Real.log (q : Real))) *
                ((L : Real) * Real.log (q : Real)) := hexpr.symm
        _ < Real.log rho := hupper0
    have hpRpos : 0 < (p : Real) := lt_trans zero_lt_one hpR
    have hqRpos : 0 < (q : Real) := lt_trans zero_lt_one hqR
    have hpowa_pos : 0 < (p : Real) ^ a := pow_pos hpRpos _
    have hqM_pos : 0 < (q : Real) ^ M := pow_pos hqRpos _
    have hlog_ratio :
        Real.log (((q : Real) ^ M) / ((p : Real) ^ a)) < Real.log rho := by
      rw [Real.log_div hqM_pos.ne' hpowa_pos.ne', Real.log_pow, Real.log_pow]
      exact hupper
    have hratio :
        ((q : Real) ^ M) / ((p : Real) ^ a) < rho :=
      (Real.log_lt_log_iff (div_pos hqM_pos hpowa_pos) (lt_trans zero_lt_one hρgt1)).mp
        hlog_ratio
    have hq_lt : (q : Real) ^ M < rho * (p : Real) ^ a := by
      have h := mul_lt_mul_of_pos_right hratio hpowa_pos
      field_simp [hpowa_pos.ne'] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have hright_real :
        (c : Real) * (q : Real) ^ M <
          ((p - 1 : Nat) : Real) * (p : Real) ^ a := by
      calc
        (c : Real) * (q : Real) ^ M
            < (c : Real) * (rho * (p : Real) ^ a) :=
              mul_lt_mul_of_pos_left hq_lt hcRpos
        _ = ((p - 1 : Nat) : Real) * (p : Real) ^ a := by
              dsimp [rho]
              field_simp [hcRpos.ne']
    have hright_cast :
        ((c * q ^ M : Nat) : Real) <
          (((p - 1) * p ^ a : Nat) : Real) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using hright_real
    exact_mod_cast hright_cast

theorem powerWindow_5_2 : PowerWindowProvider 5 2 3 :=
  powerWindowProvider_of_validBases_goodSeed validBases_5_2 seed_5_2

theorem powerWindow_9_2 : PowerWindowProvider 9 2 5 :=
  powerWindowProvider_of_validBases_goodSeed validBases_9_2 seed_9_2

theorem powerWindow_5_3 : PowerWindowProvider 5 3 2 :=
  powerWindowProvider_of_validBases_goodSeed validBases_5_3 seed_5_3

theorem exceptional_5_2_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f :=
  exceptional_5_2_from_window powerWindow_5_2

theorem exceptional_9_2_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f :=
  exceptional_9_2_from_window powerWindow_9_2

theorem exceptional_5_3_unconditional :
    ∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f :=
  exceptional_5_3_from_window powerWindow_5_3

theorem exceptional_cases_unconditional :
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 9 2 f) ∧
    (∃ f : Nat → Nat, PairwiseCoprimeNonrepSeq 5 3 f) :=
  exceptional_cases_from_window powerWindow_5_2 powerWindow_9_2 powerWindow_5_3

theorem missingPair_unconditional
    {p q : Nat} (hMissing : MissingPair p q) :
    Erdos1110Conclusion p q := by
  rcases hMissing with h52 | hRest
  · rcases h52 with ⟨rfl, rfl⟩
    exact exceptional_5_2_unconditional
  · rcases hRest with h92 | h53
    · rcases h92 with ⟨rfl, rfl⟩
      exact exceptional_9_2_unconditional
    · rcases h53 with ⟨rfl, rfl⟩
      exact exceptional_5_3_unconditional

theorem erdos1110_from_yuChen
    (yuChen : ∀ ⦃p q : Nat⦄,
      Nat.Coprime p q → p > q → q ≥ 2 → YuChenRange p q →
        Erdos1110Conclusion p q)
    {p q : Nat}
    (hpq_coprime : Nat.Coprime p q)
    (hpq : p > q)
    (hq : q ≥ 2)
    (hnot32 : ¬ (p = 3 ∧ q = 2)) :
    Erdos1110Conclusion p q :=
  erdos1110_unconditional_bridge yuChen
    (fun {p q} _ _ _ hMissing =>
      missingPair_unconditional (p := p) (q := q) hMissing)
    hpq_coprime hpq hq hnot32

end

end Erdos1110
