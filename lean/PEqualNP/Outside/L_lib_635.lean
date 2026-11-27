import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_635_aux

theorem gram {N : ℕ} (sH : Fin N → Fin N → ℤ)
    (hH : ∀ a b, (∑ y : Fin N, sH a y * sH b y) = if a = b then (N : ℤ) else 0)
    (a b : Fin N → ℤ) :
    ∑ y, (∑ x, a x * sH x y) * (∑ x, b x * sH x y) = (N : ℤ) * ∑ x, a x * b x := by
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ x, ∑ y, ∑ x', a x * sH x y * (b x' * sH x' y) =
      ∑ x', a x * b x' * (∑ y, sH x y * sH x' y) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  simp_rw [this, hH]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem matpart {m : ℕ} (hm : 0 < m) (h2 : ℕ) (hh : 0 < h2) (D : Fin m → Fin m → ℤ)
    (hD : ∀ a b, D a b * D a b = 1) (n : Fin m → ℕ)
    (hG : ∀ p p', (∑ c, (n c : ℤ) * D p c * D p' c) = if p = p' then ((m * h2 : ℕ) : ℤ) else 0) :
    (∀ c, n c = h2) ∧ ∀ a b, (∑ v, D a v * D b v) = if a = b then (m : ℤ) else 0 := by
  classical
  let Dq : Matrix (Fin m) (Fin m) ℚ := fun p c => (D p c : ℚ)
  let Nd : Matrix (Fin m) (Fin m) ℚ := Matrix.diagonal (fun c => (n c : ℚ))
  have hDq : ∀ a b, Dq a b * Dq a b = 1 := by
    intro a b
    show (D a b : ℚ) * (D a b : ℚ) = 1
    exact_mod_cast hD a b
  have hMN : ((m * h2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hmat : Dq * Nd * Dq.transpose = ((m * h2 : ℕ) : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ) := by
    ext p p'
    rw [Matrix.mul_apply]
    simp only [Nd, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    have := hG p p'
    by_cases hp : p = p'
    · rw [if_pos hp] at this ⊢
      have h' : ((∑ c, (n c : ℤ) * D p c * D p' c : ℤ) : ℚ) = ((m * h2 : ℕ) : ℚ) := by
        rw [this]
        norm_cast
      rw [← h']
      push_cast
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
    · rw [if_neg hp] at this ⊢
      have h' : ((∑ c, (n c : ℤ) * D p c * D p' c : ℤ) : ℚ) = 0 := by
        rw [this]
        norm_cast
      rw [← h']
      push_cast
      refine Finset.sum_congr rfl (fun c _ => ?_)
      ring
  have e1 : Dq * ((((m * h2 : ℕ) : ℚ))⁻¹ • (Nd * Dq.transpose)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hmat, smul_smul, inv_mul_cancel₀ hMN, one_smul]
  have e2 := mul_eq_one_comm.mp e1
  have hent : ∀ c1 c2, (((m * h2 : ℕ) : ℚ))⁻¹ * ((n c1 : ℚ) * ∑ p, Dq p c1 * Dq p c2) =
      if c1 = c2 then 1 else 0 := by
    intro c1 c2
    have := congrFun (congrFun e2 c1) c2
    rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this, smul_eq_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [Nd, Matrix.diagonal_mul, Matrix.transpose_apply]
    ring
  have hsq : ∀ c, ∑ p, Dq p c * Dq p c = (m : ℚ) := by
    intro c
    simp_rw [hDq]
    simp
  have hn : ∀ c, n c = h2 := by
    intro c
    have := hent c c
    rw [if_pos rfl, hsq] at this
    have hm' : (m : ℚ) ≠ 0 := by positivity
    have : (n c : ℚ) * m = (m * h2 : ℕ) := by
      field_simp at this
      linarith
    push_cast at this
    have : (n c : ℚ) = h2 := by
      apply mul_right_cancel₀ hm'
      linarith
    exact_mod_cast this
  refine ⟨hn, ?_⟩
  have hcol : Dq.transpose * Dq = (m : ℚ) • (1 : Matrix (Fin m) (Fin m) ℚ) := by
    ext c1 c2
    have := hent c1 c2
    rw [hn c1] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    have hm' : (m : ℚ) ≠ 0 := by positivity
    have hh' : (h2 : ℚ) ≠ 0 := by positivity
    push_cast at this
    rw [smul_eq_mul]
    by_cases hc : c1 = c2
    · rw [if_pos hc] at this ⊢
      field_simp at this
      linarith
    · rw [if_neg hc] at this ⊢
      have : (∑ p, Dq p c1 * Dq p c2) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exfalso
          simp at h
          omega
        · rcases mul_eq_zero.mp h with h | h
          · exfalso
            exact hh' h
          · exact h
      rw [this]
      ring
  have hm' : (m : ℚ) ≠ 0 := by positivity
  have e3 : ((m : ℚ)⁻¹ • Dq.transpose) * Dq = 1 := by
    rw [Matrix.smul_mul, hcol, smul_smul, inv_mul_cancel₀ hm', one_smul]
  have e4 := mul_eq_one_comm.mp e3
  intro a b
  have := congrFun (congrFun e4 a) b
  rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Matrix.transpose_apply, smul_eq_mul] at this
  have key : ((∑ v, D a v * D b v : ℤ) : ℚ) = ((if a = b then (m : ℤ) else 0 : ℤ) : ℚ) := by
    push_cast
    by_cases hab : a = b
    · rw [if_pos hab] at this ⊢
      field_simp at this
      simpa [Dq] using this
    · rw [if_neg hab] at this ⊢
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (inv_ne_zero hm')
      · simpa [Dq] using h
  exact_mod_cast key

theorem main : ∀ m h : ℕ, 0 < m → 0 < h →
  let N := m*h^2
  let sign := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ (H : Fin N → Fin N → Bool),
  (∀ a b, (∑ y : Fin N, sign (H a y) * sign (H b y)) =
    if a = b then (N : ℤ) else 0) →
  ∀ (row col : Fin N → Fin m) (Q R : Fin N → Bool) (D : Fin m → Fin m → Bool),
    let corr := ∑ x : Fin N, ∑ y : Fin N,
      sign (H x y) * sign (Q x) * sign (R y) * sign (D (row x) (col y))
    let S := fun (p : Fin m) (v : Fin N) =>
      ∑ x : Fin N, if row x = p then sign (Q x) * sign (H x v) else 0
    ((∑ p : Fin m, ∑ y : Fin N,
      (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2) +
      2*(h : ℤ)*corr = 2*(N : ℤ)^2) ∧
    ((h : ℤ)*corr = (N : ℤ)^2 →
      (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
            ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
      ∀ a b, (∑ v : Fin m, sign (D a v)*sign (D b v)) =
        if a = b then (m : ℤ) else 0) := by
  intro m h hm hh N sign H hH row col Q R D corr S
  have hs : ∀ v : Bool, sign v * sign v = 1 := by
    intro v
    cases v <;> simp [sign]
  have hN : (N : ℤ) = (m : ℤ) * (h : ℤ)^2 := by
    show ((m * h^2 : ℕ) : ℤ) = _
    push_cast
    ring
  let a : Fin m → Fin N → ℤ := fun p x => if row x = p then sign (Q x) else 0
  have hSa : ∀ p y, S p y = ∑ x, a p x * sign (H x y) := by
    intro p y
    show (∑ x : Fin N, if row x = p then sign (Q x) * sign (H x y) else 0) = _
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [a]
    split_ifs <;> ring
  let cnt : Fin m → ℕ := fun p => ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card
  have haa : ∀ p p', ∑ x, a p x * a p' x = if p = p' then (cnt p : ℤ) else 0 := by
    intro p p'
    have : ∀ x, a p x * a p' x = if p = p' then (if row x = p then 1 else 0) else 0 := by
      intro x
      simp only [a]
      by_cases h3 : p = p'
      · subst h3
        by_cases h1 : row x = p
        · simp only [h1, if_true]
          exact hs (Q x)
        · simp only [h1, if_false, mul_zero, if_true]
      · by_cases h1 : row x = p
        · have h2 : ¬ row x = p' := fun hh' => h3 (h1.symm.trans hh')
          simp only [h1, h3, if_true, if_false, mul_zero]
        · simp only [h1, h3, if_false, zero_mul]
    simp_rw [this]
    by_cases hp : p = p'
    · simp only [if_pos hp]
      rw [Finset.sum_boole]
    · simp [if_neg hp]
  have hSS : ∀ p p', ∑ y, S p y * S p' y = (N : ℤ) * (if p = p' then (cnt p : ℤ) else 0) := by
    intro p p'
    simp_rw [hSa]
    rw [gram (fun x y => sign (H x y)) hH, haa]
  have hcnt : ∑ p, (cnt p : ℤ) = (N : ℤ) := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset (Fin m))) (f := row) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.symm
  have hcorr : ∑ p, ∑ y, S p y * (sign (R y) * sign (D p (col y))) = corr := by
    simp_rw [hSa, Finset.sum_mul]
    have : ∀ p y x, a p x * sign (H x y) * (sign (R y) * sign (D p (col y))) =
        if row x = p then sign (H x y) * sign (Q x) * sign (R y) * sign (D (row x) (col y)) else 0 := by
      intro p y x
      simp only [a]
      split_ifs with hx
      · rw [hx]
        ring
      · ring
    simp_rw [this]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
  have hid : (∑ p : Fin m, ∑ y : Fin N,
      (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2) + 2*(h : ℤ)*corr = 2*(N : ℤ)^2 := by
    have : ∀ p y, (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2 =
        S p y * S p y - 2 * (h : ℤ) * (S p y * (sign (R y) * sign (D p (col y)))) + (h : ℤ)^2 := by
      intro p y
      have e1 := hs (R y)
      have e2 := hs (D p (col y))
      linear_combination (h : ℤ)^2 * sign (D p (col y)) * sign (D p (col y)) * e1 + (h : ℤ)^2 * e2
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcorr]
    simp_rw [hSS]
    simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hcnt]
    have : ((N : ℕ) : ℤ) = (N : ℤ) := rfl
    rw [hN]
    push_cast
    ring
  refine ⟨hid, ?_⟩
  intro heq
  have hsum0 : (∑ p : Fin m, ∑ y : Fin N,
      (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2) = 0 := by
    have : 2 * (h : ℤ) * corr = 2 * (N : ℤ)^2 := by rw [mul_assoc, heq]
    linarith
  have hzero : ∀ p y, S p y = (h : ℤ) * sign (R y) * sign (D p (col y)) := by
    intro p y
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg
      (fun y _ => sq_nonneg (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))))).mp hsum0 p
      (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
      sq_nonneg (S p y - (h : ℤ) * sign (R y) * sign (D p (col y))))).mp h1 y (Finset.mem_univ _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  have hNpos : (0 : ℤ) < N := by
    rw [hN]
    have : (0 : ℤ) < m := by exact_mod_cast hm
    have : (0 : ℤ) < h := by exact_mod_cast hh
    positivity
  have hrow : ∀ p, cnt p = h^2 := by
    intro p
    have h1 := hSS p p
    rw [if_pos rfl] at h1
    have h2 : ∑ y, S p y * S p y = (N : ℤ) * (h : ℤ)^2 := by
      simp_rw [hzero]
      have : ∀ y, (h : ℤ) * sign (R y) * sign (D p (col y)) * ((h : ℤ) * sign (R y) * sign (D p (col y)))
          = (h : ℤ)^2 := by
        intro y
        have e1 := hs (R y)
        have e2 := hs (D p (col y))
        linear_combination (h : ℤ)^2 * sign (D p (col y)) * sign (D p (col y)) * e1 + (h : ℤ)^2 * e2
      simp_rw [this]
      simp
    rw [h2] at h1
    have : (cnt p : ℤ) = (h : ℤ)^2 := by
      have := mul_left_cancel₀ (ne_of_gt hNpos) h1
      linarith
    exact_mod_cast this
  let ncol : Fin m → ℕ := fun c => ((Finset.univ : Finset (Fin N)).filter (fun y => col y = c)).card
  have hG : ∀ p p', (∑ c, (ncol c : ℤ) * sign (D p c) * sign (D p' c)) =
      if p = p' then ((m * h^2 : ℕ) : ℤ) else 0 := by
    intro p p'
    have h1 := hSS p p'
    simp_rw [hzero] at h1
    have h3 : ∀ y, (h : ℤ) * sign (R y) * sign (D p (col y)) * ((h : ℤ) * sign (R y) * sign (D p' (col y)))
        = (h : ℤ)^2 * (sign (D p (col y)) * sign (D p' (col y))) := by
      intro y
      have e1 := hs (R y)
      linear_combination (h : ℤ)^2 * sign (D p (col y)) * sign (D p' (col y)) * e1
    simp_rw [h3, ← Finset.mul_sum] at h1
    have hfib : ∑ y, sign (D p (col y)) * sign (D p' (col y)) =
        ∑ c, (ncol c : ℤ) * sign (D p c) * sign (D p' c) := by
      rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (Fin N))) (g := col)]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.sum_congr rfl (g := fun _ => sign (D p c) * sign (D p' c))]
      · simp only [Finset.sum_const, nsmul_eq_mul, ncol]
        ring
      · intro y hy
        rw [(Finset.mem_filter.mp hy).2]
    rw [← hfib]
    have hh2 : (0 : ℤ) < (h : ℤ)^2 := by
      have : (0 : ℤ) < h := by exact_mod_cast hh
      positivity
    by_cases hp : p = p'
    · rw [if_pos hp] at h1 ⊢
      rw [hrow p] at h1
      have h1' : (h : ℤ)^2 * (∑ y, sign (D p (col y)) * sign (D p' (col y))) =
          (h : ℤ)^2 * ((m : ℤ) * (h : ℤ)^2) := by
        rw [h1, hN]
        push_cast
        ring
      push_cast
      exact mul_left_cancel₀ (ne_of_gt hh2) h1'
    · rw [if_neg hp] at h1 ⊢
      rw [mul_zero] at h1
      rcases mul_eq_zero.mp h1 with h4 | h4
      · exact absurd h4 (ne_of_gt hh2)
      · exact h4
  have hmp := matpart hm (h^2) (by positivity) (fun a b => sign (D a b)) (fun a b => hs (D a b)) ncol hG
  refine ⟨fun p => ⟨hrow p, hmp.1 p⟩, ?_⟩
  intro a b
  exact hmp.2 a b

end PEqualNP.Outside.L_lib_635_aux

theorem PEqualNP.Outside.L_lib_635 : (∀ m h : ℕ, 0 < m → 0 < h →
  let N := m*h^2
  let sign := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ (H : Fin N → Fin N → Bool),
  (∀ a b, (∑ y : Fin N, sign (H a y) * sign (H b y)) =
    if a = b then (N : ℤ) else 0) →
  ∀ (row col : Fin N → Fin m) (Q R : Fin N → Bool) (D : Fin m → Fin m → Bool),
    let corr := ∑ x : Fin N, ∑ y : Fin N,
      sign (H x y) * sign (Q x) * sign (R y) * sign (D (row x) (col y))
    let S := fun (p : Fin m) (v : Fin N) =>
      ∑ x : Fin N, if row x = p then sign (Q x) * sign (H x v) else 0
    ((∑ p : Fin m, ∑ y : Fin N,
      (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2) +
      2*(h : ℤ)*corr = 2*(N : ℤ)^2) ∧
    ((h : ℤ)*corr = (N : ℤ)^2 →
      (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
            ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
      ∀ a b, (∑ v : Fin m, sign (D a v)*sign (D b v)) =
        if a = b then (m : ℤ) else 0)) := by
  exact PEqualNP.Outside.L_lib_635_aux.main
