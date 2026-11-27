import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_602_aux

def dd (m : ℕ) : ℕ := ∏ j ∈ Finset.range m, (2*j+1)

theorem dd_succ (m : ℕ) : dd (m+1) = dd m * (2*m+1) := by
  simp [dd, Finset.prod_range_succ]

theorem dd_pos (m : ℕ) : 0 < dd m := Finset.prod_pos (fun j _ => by omega)

theorem dd_fact (m : ℕ) : dd m * 2^m * m.factorial = (2*m).factorial := by
  induction m with
  | zero => simp [dd]
  | succ m ih =>
    have e : 2*(m+1) = (2*m+1)+1 := by ring
    rw [e, Nat.factorial_succ (2*m+1), Nat.factorial_succ (2*m), ← ih, dd_succ,
      Nat.factorial_succ m, pow_succ]
    ring

theorem comb_le (m i : ℕ) (hi : i ≤ m) :
    (2*m).choose (2*i) * dd i ≤ dd m * m.choose i := by
  obtain ⟨a, rfl⟩ : ∃ a, m = i + a := ⟨m - i, by omega⟩
  have h1 : (2*(i+a)).choose (2*i) * (2*i).factorial * (2*a).factorial
      = (2*(i+a)).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show 2*i ≤ 2*(i+a) by omega)
    have e : 2*(i+a) - 2*i = 2*a := by omega
    rw [e] at h
    exact h
  have h2 : (i+a).choose i * i.factorial * a.factorial = (i+a).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show i ≤ i+a by omega)
    have e : i + a - i = a := by omega
    rw [e] at h
    exact h
  have d1 := dd_fact i
  have d2 := dd_fact (i+a)
  have d3 := dd_fact a
  have key : ((2*(i+a)).choose (2*i) * dd i) * (2*a).factorial * (2^i * i.factorial)
      = (dd (i+a) * (i+a).choose i) * (2^a * a.factorial) * (2^i * i.factorial) := by
    calc ((2*(i+a)).choose (2*i) * dd i) * (2*a).factorial * (2^i * i.factorial)
        = (2*(i+a)).choose (2*i) * (dd i * 2^i * i.factorial) * (2*a).factorial := by ring
      _ = (2*(i+a)).factorial := by rw [d1, h1]
      _ = dd (i+a) * 2^(i+a) * ((i+a).choose i * i.factorial * a.factorial) := by
          rw [h2, d2]
      _ = (dd (i+a) * (i+a).choose i) * (2^a * a.factorial) * (2^i * i.factorial) := by
          rw [pow_add]
          ring
  have hpos : 0 < 2^i * i.factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos i)
  have key2 := Nat.eq_of_mul_eq_mul_right hpos key
  have h3 : 2^a * a.factorial ≤ (2*a).factorial := by
    rw [← d3]
    calc 2^a * a.factorial = 1 * (2^a * a.factorial) := by ring
      _ ≤ dd a * (2^a * a.factorial) := Nat.mul_le_mul_right _ (dd_pos a)
      _ = dd a * 2^a * a.factorial := by ring
  have h4 : ((2*(i+a)).choose (2*i) * dd i) * (2*a).factorial
      ≤ (dd (i+a) * (i+a).choose i) * (2*a).factorial := by
    rw [key2]
    exact Nat.mul_le_mul_left _ h3
  exact Nat.le_of_mul_le_mul_right h4 (Nat.factorial_pos _)

theorem even_split (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (2*m+1), f j * (1 + (-1:ℝ)^j)
      = 2 * ∑ i ∈ Finset.range (m+1), f (2*i) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    have e : 2*(m+1)+1 = (2*m+1)+1+1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun i => f (2*i)) (m+1)]
    have h1 : (-1:ℝ)^(2*m+1) = -1 := by
      rw [pow_succ, pow_mul]
      simp
    have h2 : (-1:ℝ)^(2*m+1+1) = 1 := by
      rw [pow_succ, h1]
      simp
    rw [h1, h2]
    have e2 : 2*(m+1) = 2*m+1+1 := by ring
    rw [e2]
    ring

theorem even_binom (t a : ℝ) (m : ℕ) :
    (t + a)^(2*m) + (t - a)^(2*m)
      = 2 * ∑ i ∈ Finset.range (m+1), ((2*m).choose (2*i) : ℝ) * t^(2*i) * a^(2*m - 2*i) := by
  rw [← even_split (fun j => ((2*m).choose j : ℝ) * t^j * a^(2*m - j)) m,
    sub_eq_add_neg, add_pow, add_pow, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ 2*m := by
    have := Finset.mem_range.1 hj
    omega
  have h2 : (-1:ℝ)^j * (-1:ℝ)^j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have h3 : (-1:ℝ)^(2*m-j) * (-1:ℝ)^j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj', pow_mul]
    simp
  have h4 : (-1:ℝ)^(2*m-j) = (-1:ℝ)^j := by
    calc (-1:ℝ)^(2*m-j) = (-1:ℝ)^(2*m-j) * ((-1:ℝ)^j * (-1:ℝ)^j) := by rw [h2, mul_one]
      _ = ((-1:ℝ)^(2*m-j) * (-1:ℝ)^j) * (-1:ℝ)^j := by ring
      _ = (-1:ℝ)^j := by rw [h3, one_mul]
  have hneg : (-a)^(2*m - j) = (-1:ℝ)^j * a^(2*m-j) := by
    rw [neg_pow, h4]
  rw [hneg]
  ring

def eps : Bool → ℝ
  | true => -1
  | false => 1

theorem eps_sq (e : Bool) : eps e ^ 2 = 1 := by
  cases e <;> simp [eps]

theorem step {ι : Type} [Fintype ι] (t : ι → ℝ) (a s2 K : ℝ) (hs : 0 ≤ s2) (hK : 0 ≤ K)
    (m : ℕ) (hIH : ∀ i, ∑ y, (t y)^(2*i) ≤ K * (dd i : ℝ) * s2^i) :
    ∑ y, ((t y + a)^(2*m) + (t y - a)^(2*m)) ≤ 2 * K * (dd m : ℝ) * (s2 + a^2)^m := by
  have hstep : ∑ y, ((t y + a)^(2*m) + (t y - a)^(2*m))
      = 2 * ∑ i ∈ Finset.range (m+1),
          ((2*m).choose (2*i) : ℝ) * a^(2*m-2*i) * ∑ y, (t y)^(2*i) := by
    simp_rw [even_binom]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hstep, add_pow, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m := by
    have := Finset.mem_range.1 hi
    omega
  have hpow : a^(2*m-2*i) = (a^2)^(m-i) := by
    rw [← pow_mul]
    congr 1
    omega
  have hcomb : ((2*m).choose (2*i) : ℝ) * (dd i : ℝ) ≤ (dd m : ℝ) * (m.choose i : ℝ) := by
    exact_mod_cast comb_le m i hi'
  rw [hpow]
  have hA : 0 ≤ (a^2)^(m-i) := pow_nonneg (sq_nonneg a) _
  have hC : (0:ℝ) ≤ ((2*m).choose (2*i) : ℝ) := Nat.cast_nonneg _
  calc 2 * (((2*m).choose (2*i) : ℝ) * (a^2)^(m-i) * ∑ y, (t y)^(2*i))
      ≤ 2 * (((2*m).choose (2*i) : ℝ) * (a^2)^(m-i) * (K * (dd i : ℝ) * s2^i)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (hIH i) (mul_nonneg hC hA)
    _ = 2 * K * (a^2)^(m-i) * s2^i * (((2*m).choose (2*i) : ℝ) * (dd i : ℝ)) := by ring
    _ ≤ 2 * K * (a^2)^(m-i) * s2^i * ((dd m : ℝ) * (m.choose i : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hcomb
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hA) (pow_nonneg hs i)
    _ = 2 * K * (dd m : ℝ) * (s2^i * (a^2)^(m-i) * (m.choose i : ℝ)) := by ring

theorem khin : ∀ (k : ℕ) (v : Fin k → ℝ) (m : ℕ),
    ∑ y : Fin k → Bool, (∑ j, v j * eps (y j))^(2*m)
      ≤ 2^k * (dd m : ℝ) * (∑ j, (v j)^2)^m := by
  intro k
  induction k with
  | zero =>
    intro v m
    rcases m with _ | m
    · simp [dd]
    · simp
  | succ k ih =>
    intro v m
    have hre : ∑ y : Fin (k+1) → Bool, (∑ j, v j * eps (y j))^(2*m)
        = ∑ y' : Fin k → Bool,
            ((∑ j, v (Fin.succ j) * eps (y' j) + v 0)^(2*m)
              + (∑ j, v (Fin.succ j) * eps (y' j) - v 0)^(2*m)) := by
      rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Bool)).sum_comp, Fintype.sum_prod_type,
        Fintype.sum_bool, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y' _
      simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, eps]
      ring
    have hs : 0 ≤ ∑ j : Fin k, (v (Fin.succ j))^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hst := step (fun y' : Fin k → Bool => ∑ j, v (Fin.succ j) * eps (y' j)) (v 0)
      (∑ j : Fin k, (v (Fin.succ j))^2) (2^k) hs (by positivity) m
      (fun i => ih (fun j => v (Fin.succ j)) i)
    rw [hre]
    refine le_trans hst (le_of_eq ?_)
    rw [Fin.sum_univ_succ, pow_succ]
    ring

theorem bits_bij (k : ℕ) :
    Function.Bijective (fun (x : Fin (2^k)) (j : Fin k) => x.val.testBit j.val) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro x y hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun hxy ⟨i, hi⟩
  · have hx : x.val < 2^i :=
      lt_of_lt_of_le x.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hy : y.val < 2^i :=
      lt_of_lt_of_le y.2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

theorem final (k m : ℕ) (hm : 0 < m) (S : Finset (Fin (2^k))) (b : Fin (2^k) → Bool)
    (v : Fin k → ℝ)
    (hv : ∀ j, v j = ∑ x ∈ S, eps (b x) * eps (x.val.testBit j.val)) :
    (∑ j, (v j)^2)^m ≤ (2:ℝ)^k * (S.card : ℝ)^(2*m-1) * (dd m : ℝ) := by
  have hL0 : 0 ≤ ∑ j, (v j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rcases S.eq_empty_or_nonempty with hS | hS
  · have hv0 : ∀ j, v j = 0 := by
      intro j
      rw [hv j, hS]
      simp
    have h0 : ∑ j, (v j)^2 = 0 := by simp [hv0]
    rw [h0, zero_pow (by omega)]
    positivity
  · have hc : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hLsum : ∑ j, (v j)^2
        = ∑ x ∈ S, eps (b x) * ∑ j, v j * eps (x.val.testBit j.val) := by
      have h1 : ∀ j, (v j)^2 = ∑ x ∈ S, eps (b x) * (v j * eps (x.val.testBit j.val)) := by
        intro j
        have e : (v j)^2 = (∑ x ∈ S, eps (b x) * eps (x.val.testBit j.val)) * v j := by
          rw [sq, ← hv j]
        rw [e, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    have hmean := Real.pow_arith_mean_le_arith_mean_pow_of_even S
      (fun _ => 1 / (S.card : ℝ))
      (fun x => eps (b x) * ∑ j, v j * eps (x.val.testBit j.val))
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
      (even_two_mul m)
    have hz : ∀ x, (eps (b x) * ∑ j, v j * eps (x.val.testBit j.val))^(2*m)
        = (∑ j, v j * eps (x.val.testBit j.val))^(2*m) := by
      intro x
      rw [mul_pow, pow_mul, eps_sq, one_pow, one_mul]
    simp only [hz] at hmean
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← hLsum] at hmean
    have hext : ∑ x ∈ S, (∑ j, v j * eps (x.val.testBit j.val))^(2*m)
        ≤ ∑ x : Fin (2^k), (∑ j, v j * eps (x.val.testBit j.val))^(2*m) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro x
      rw [pow_mul]
      positivity
    have hkh : ∑ x : Fin (2^k), (∑ j, v j * eps (x.val.testBit j.val))^(2*m)
        ≤ 2^k * (dd m : ℝ) * (∑ j, (v j)^2)^m := by
      have hb := (bits_bij k).sum_comp (fun y : Fin k → Bool => (∑ j, v j * eps (y j))^(2*m))
      exact le_trans (le_of_eq hb) (khin k v m)
    have hmain : (∑ j, (v j)^2)^(2*m)
        ≤ (S.card : ℝ)^(2*m-1) * (2^k * (dd m : ℝ) * (∑ j, (v j)^2)^m) := by
      have h5 : (1 / (S.card : ℝ) * ∑ j, (v j)^2)^(2*m) * (S.card : ℝ)^(2*m)
          = (∑ j, (v j)^2)^(2*m) := by
        rw [← mul_pow]
        congr 1
        field_simp
      have h6 : (S.card : ℝ)^(2*m) = (S.card : ℝ)^(2*m-1) * (S.card : ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      calc (∑ j, (v j)^2)^(2*m)
          = (1 / (S.card : ℝ) * ∑ j, (v j)^2)^(2*m) * (S.card : ℝ)^(2*m) := h5.symm
        _ ≤ (1 / (S.card : ℝ) * ∑ x ∈ S, (∑ j, v j * eps (x.val.testBit j.val))^(2*m))
              * (S.card : ℝ)^(2*m) := mul_le_mul_of_nonneg_right hmean (by positivity)
        _ = (S.card : ℝ)^(2*m-1) * ∑ x ∈ S, (∑ j, v j * eps (x.val.testBit j.val))^(2*m) := by
            rw [h6]
            field_simp
        _ ≤ (S.card : ℝ)^(2*m-1) * (2^k * (dd m : ℝ) * (∑ j, (v j)^2)^m) :=
            mul_le_mul_of_nonneg_left (le_trans hext hkh) (by positivity)
    rcases eq_or_lt_of_le hL0 with h0 | hpos
    · rw [← h0, zero_pow (by omega)]
      positivity
    · have hLm : 0 < (∑ j, (v j)^2)^m := pow_pos hpos m
      have h7 : (∑ j, (v j)^2)^(2*m) = (∑ j, (v j)^2)^m * (∑ j, (v j)^2)^m := by
        rw [← pow_add]
        congr 1
        omega
      rw [h7] at hmain
      have h8 : (∑ j, (v j)^2)^m * (∑ j, (v j)^2)^m
          ≤ ((2:ℝ)^k * (S.card : ℝ)^(2*m-1) * (dd m : ℝ)) * (∑ j, (v j)^2)^m := by
        calc (∑ j, (v j)^2)^m * (∑ j, (v j)^2)^m
            ≤ (S.card : ℝ)^(2*m-1) * (2^k * (dd m : ℝ) * (∑ j, (v j)^2)^m) := hmain
          _ = ((2:ℝ)^k * (S.card : ℝ)^(2*m-1) * (dd m : ℝ)) * (∑ j, (v j)^2)^m := by ring
      exact le_of_mul_le_mul_right h8 hLm

theorem main : ∀ (k m : ℕ), 0 < m →
  let N := 2^k
  ∀ (S : Finset (Fin N)) (b : Fin N → Bool),
    let v := fun (j : Fin k) =>
      ∑ x ∈ S, if xor (b x) (x.val.testBit j.val) then (-1 : ℝ) else 1
    let energy := ∑ j : Fin k, (v j)^2
    energy^m ≤ (N : ℝ) * (S.card : ℝ)^(2*m-1) * (∏ j ∈ Finset.range m, (2*(j:ℝ)+1)) := by
  intro k m hm N S b v energy
  have hv : ∀ j : Fin k, v j = ∑ x ∈ S, eps (b x) * eps (x.val.testBit j.val) := by
    intro j
    apply Finset.sum_congr rfl
    intro x _
    cases b x <;> cases (x.val.testBit j.val) <;> simp [eps]
  have hfin := final k m hm S b v hv
  have hN : ((N : ℕ) : ℝ) = (2:ℝ)^k := by
    simp [N]
  have hprod : (∏ j ∈ Finset.range m, (2*(j:ℝ)+1)) = (dd m : ℝ) := by
    simp [dd]
  rw [hN, hprod]
  exact hfin

end PEqualNP.Outside.L_lib_602_aux

theorem PEqualNP.Outside.L_lib_602 : (∀ (k m : ℕ), 0 < m →
  let N := 2^k
  ∀ (S : Finset (Fin N)) (b : Fin N → Bool),
    let v := fun (j : Fin k) =>
      ∑ x ∈ S, if xor (b x) (x.val.testBit j.val) then (-1 : ℝ) else 1
    let energy := ∑ j : Fin k, (v j)^2
    energy^m ≤ (N : ℝ) * (S.card : ℝ)^(2*m-1) * (∏ j ∈ Finset.range m, (2*(j:ℝ)+1))) := by
  exact PEqualNP.Outside.L_lib_602_aux.main
