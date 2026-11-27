import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_661_aux

theorem toNat_testBit' (c : Bool) (j : Nat) : c.toNat.testBit j = (decide (j = 0) && c) := by
  cases c
  · simp
  · cases j with
    | zero => simp
    | succ j =>
      simp only [Bool.toNat_true, Nat.add_one_ne_zero, decide_false, Bool.false_and]
      exact Nat.testBit_lt_two_pow (by
        have : 2 ≤ 2 ^ (j + 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)

theorem fold_bit (f : Nat → Bool) : ∀ N i : Nat,
    ((List.range N).foldl (fun acc b => acc ||| ((f b).toNat <<< b)) 0).testBit i =
      (decide (i < N) && f i) := by
  intro N
  induction N with
  | zero => intro i; simp
  | succ N ih =>
    intro i
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih,
      Nat.testBit_shiftLeft, toNat_testBit']
    by_cases h1 : i < N
    · have : ¬ (i - N = 0 ∧ i ≥ N) := by omega
      simp [h1, show i < N + 1 by omega]
    · by_cases h2 : i = N
      · subst h2
        simp
      · simp [h1, h2, show ¬ i < N + 1 by omega]
        omega

theorem rot_bit (k s x i : Nat) (hk : 0 < k) (hx : x < 2 ^ k) (hi : i < k) :
    ((((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k)).testBit i =
      x.testBit ((i + k - s % k) % k) := by
  have hs : s % k < k := Nat.mod_lt _ hk
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : i ≥ s % k
  · have e : (i + k - s % k) % k = i - s % k := by
      rw [show i + k - s % k = (i - s % k) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have hf : x.testBit (k - s % k + i) = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [h, hf]
  · have e : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]
    simp [h]

theorem main : ∀ (k lanes gap : Nat) (hk : 0 < k), gap ≤ k →
  let word := Fin (2 ^ k)
  let atSite := fun j : Nat => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s x : Nat) =>
    ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k
  let step := fun (raw : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (raw.testBit b)
        (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0
  ∀ (state addend : Fin lanes → word) (planes additions : Fin k → Nat),
    (∀ i w, (planes i).testBit w.val = (state w).val.testBit i.val) →
    (∀ i w, (additions i).testBit w.val = (addend w).val.testBit i.val) →
    let mix := fun j : Nat =>
      planes (atSite j) ^^^ planes (atSite (j + k - gap % k)) ^^^
        planes (atSite (j + gap))
    let full := 2 ^ lanes - 1
    ∀ (i : Fin k) (w : Fin lanes),
      (mix i.val ^^^ ((full ^^^ mix (i.val + 1)) &&& mix (i.val + 2)) ^^^
        additions i).testBit w.val =
      (step ((state w).val ^^^ rot gap (state w).val ^^^ rot (k - gap) (state w).val) ^^^
        (addend w).val).testBit i.val := by
  intro k lanes gap hk hgap word atSite rot step state addend planes additions hpl had mix full i w
  set s := (state w).val with hsdef
  have hsk : s < 2 ^ k := (state w).isLt
  have hstep : ∀ raw j, j < k → (step raw).testBit j =
      xor (raw.testBit j) (!(raw.testBit ((j + 1) % k)) && raw.testBit ((j + 2) % k)) := by
    intro raw j hj
    have := fold_bit (fun b => xor (raw.testBit b)
      (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))) k j
    simp only [hj, decide_true, Bool.true_and] at this
    exact this
  let e : Nat → Bool := fun j =>
    xor (xor (s.testBit (j % k)) (s.testBit ((j + k - gap % k) % k))) (s.testBit ((j + gap) % k))
  have hmix : ∀ j, (mix j).testBit w.val = e j := by
    intro j
    show (planes (atSite j) ^^^ planes (atSite (j + k - gap % k)) ^^^
        planes (atSite (j + gap))).testBit w.val = _
    rw [Nat.testBit_xor, Nat.testBit_xor, hpl, hpl, hpl]
  have hy : ∀ j, (s ^^^ rot gap s ^^^ rot (k - gap) s).testBit (j % k) = e j := by
    intro j
    have hb : j % k < k := Nat.mod_lt _ hk
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hr1 : (rot gap s).testBit (j % k) = s.testBit ((j % k + k - gap % k) % k) :=
      rot_bit k gap s (j % k) hk hsk hb
    have hr2 : (rot (k - gap) s).testBit (j % k) =
        s.testBit ((j % k + k - (k - gap) % k) % k) :=
      rot_bit k (k - gap) s (j % k) hk hsk hb
    rw [hr1, hr2]
    have hg : gap % k < k := Nat.mod_lt _ hk
    have E1 : (j % k + k - gap % k) % k = (j + k - gap % k) % k := by
      rw [show j % k + k - gap % k = j % k + (k - gap % k) by omega,
        show j + k - gap % k = j + (k - gap % k) by omega, Nat.mod_add_mod]
    have E2 : (j % k + k - (k - gap) % k) % k = (j + gap) % k := by
      by_cases h0 : gap = 0
      · subst h0
        rw [Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod, Nat.add_zero]
      · rw [Nat.mod_eq_of_lt (show k - gap < k by omega),
          show j % k + k - (k - gap) = j % k + gap by omega, Nat.mod_add_mod]
    rw [E1, E2]
  have hfull : full.testBit w.val = true := by
    show (2 ^ lanes - 1).testBit w.val = true
    rw [Nat.testBit_two_pow_sub_one]
    simp [w.isLt]
  clear_value mix full step rot
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, hfull, had,
    Nat.testBit_xor, hstep _ _ i.isLt, hmix, hmix, hmix]
  have hi : i.val % k = i.val := Nat.mod_eq_of_lt i.isLt
  have h0 := hy i.val
  rw [hi] at h0
  rw [h0, hy (i.val + 1), hy (i.val + 2)]
  simp

end PEqualNP.Outside.L_lib_661_aux

theorem PEqualNP.Outside.L_lib_661 : (∀ (k lanes gap : Nat) (hk : 0 < k), gap ≤ k →
  let word := Fin (2 ^ k)
  let atSite := fun j : Nat => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s x : Nat) =>
    ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k
  let step := fun (raw : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (raw.testBit b)
        (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0
  ∀ (state addend : Fin lanes → word) (planes additions : Fin k → Nat),
    (∀ i w, (planes i).testBit w.val = (state w).val.testBit i.val) →
    (∀ i w, (additions i).testBit w.val = (addend w).val.testBit i.val) →
    let mix := fun j : Nat =>
      planes (atSite j) ^^^ planes (atSite (j + k - gap % k)) ^^^
        planes (atSite (j + gap))
    let full := 2 ^ lanes - 1
    ∀ (i : Fin k) (w : Fin lanes),
      (mix i.val ^^^ ((full ^^^ mix (i.val + 1)) &&& mix (i.val + 2)) ^^^
        additions i).testBit w.val =
      (step ((state w).val ^^^ rot gap (state w).val ^^^ rot (k - gap) (state w).val) ^^^
        (addend w).val).testBit i.val) := by
  exact PEqualNP.Outside.L_lib_661_aux.main
