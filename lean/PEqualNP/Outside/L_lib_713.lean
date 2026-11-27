import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_713_aux

def sg (b : Bool) : ℤ := if b then -1 else 1

theorem ind_id : ∀ A B Hx P Q : Bool,
    ((if (Bool.xor A Hx = P ∧ Bool.xor B Hx = Q) then 1 else 0 : ℤ)) * 4
      = (1 + sg P * sg A * sg Hx) * (1 + sg Q * sg B * sg Hx) := by
  decide

theorem sg_sq : ∀ b : Bool, sg b * sg b = 1 := by
  decide

theorem sg_ne : ∀ a b : Bool,
    sg a * sg b = 1 - 2 * (if a ≠ b then 1 else 0) := by
  decide

theorem orth {n m : ℕ} (F : Fin n → Fin m → Bool)
    (hF : ∀ u v : Fin n, u ≠ v →
      2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m)
    (u v : Fin n) : ∑ x, sg (F u x) * sg (F v x) = if u = v then (m : ℤ) else 0 := by
  by_cases h : u = v
  · subst h
    simp [sg_sq]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
    have h1 : ∀ x, sg (F u x) * sg (F v x) = 1 - 2 * (if F u x ≠ F v x then 1 else 0) :=
      fun x => sg_ne _ _
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    have h2 : (2 * (((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card : ℤ))
        = m := by
      exact_mod_cast hF u v h
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith

theorem gram {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (f : ι → Fin m → ℤ)
    (hf : ∀ c c' : ι, ∑ x, f c x * f c' x = if c = c' then (m : ℤ) else 0) (τ : ι → ℤ) :
    ∑ x, (∑ c, τ c * f c x) ^ 2 = m * ∑ c, τ c ^ 2 := by
  have h1 : ∀ x, (∑ c, τ c * f c x) ^ 2 = ∑ c, ∑ c', (τ c * τ c') * (f c x * f c' x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ c, ∑ x, ∑ c', (τ c * τ c') * (f c x * f c' x) = m * τ c ^ 2 := by
    intro c
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hf]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp_rw [h2]
  rw [Finset.mul_sum]

theorem core {n m l : ℕ} (F : Fin n → Fin m → Bool)
    (hF : ∀ u v : Fin n, u ≠ v →
      2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m)
    (name : Fin l × Bool ↪ Fin n) (H : Fin m → Bool) (p q : Fin l → Bool) (e : ℕ)
    (he : e = ∑ i : Fin l, ((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card) :
    (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 ∧ m*l ≤ 2*m + 8*e := by
  have hper : ∀ i : Fin l, 4 * (((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card : ℤ)
        = m + ∑ x : Fin m, (sg (p i) * sg (F (name (i,false)) x)
            + sg (q i) * sg (F (name (i,true)) x)) * sg (H x) := by
    intro i
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    have hne : name (i,false) ≠ name (i,true) := by
      intro h
      have h2 := name.injective h
      simp at h2
    have ho := orth F hF (name (i,false)) (name (i,true))
    rw [ite_eq_right_of_eq_false _ _ (eq_false hne)] at ho
    have hterm : ∀ x : Fin m, 4 * (if (Bool.xor (F (name (i,false)) x) (H x) = p i ∧
        Bool.xor (F (name (i,true)) x) (H x) = q i) then (1:ℤ) else 0)
          = 1 + (sg (p i) * sg (F (name (i,false)) x)
              + sg (q i) * sg (F (name (i,true)) x)) * sg (H x)
            + sg (p i) * sg (q i) * (sg (F (name (i,false)) x) * sg (F (name (i,true)) x)) := by
      intro x
      have h1 := ind_id (F (name (i,false)) x) (F (name (i,true)) x) (H x) (p i) (q i)
      have h2 := sg_sq (H x)
      linear_combination h1 + (sg (p i) * sg (q i) * sg (F (name (i,false)) x)
        * sg (F (name (i,true)) x)) * h2
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ho]
    simp
  have h4e : 4 * (e : ℤ) - (m:ℤ) * l
      = ∑ x : Fin m, (∑ c : Fin l × Bool,
          (if c.2 then sg (q c.1) else sg (p c.1)) * sg (F (name c) x)) * sg (H x) := by
    rw [he, Nat.cast_sum, Finset.mul_sum]
    simp_rw [hper]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : Fin m, ∑ i : Fin l, (sg (p i) * sg (F (name (i,false)) x)
          + sg (q i) * sg (F (name (i,true)) x)) * sg (H x)
        = (∑ c : Fin l × Bool,
            (if c.2 then sg (q c.1) else sg (p c.1)) * sg (F (name c) x)) * sg (H x) := by
      intro x
      rw [← Finset.sum_mul, Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      simp
      ring
    simp_rw [hx]
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun x => ∑ c : Fin l × Bool,
      (if c.2 then sg (q c.1) else sg (p c.1)) * sg (F (name c) x))
    (fun x => sg (H x))
  have hG := gram (fun (c : Fin l × Bool) x => sg (F (name c) x))
    (fun c c' => by
      rw [orth F hF (name c) (name c')]
      simp)
    (fun c : Fin l × Bool => if c.2 then sg (q c.1) else sg (p c.1))
  have hτ : ∑ c : Fin l × Bool, (if c.2 then sg (q c.1) else sg (p c.1)) ^ 2 = 2 * (l : ℤ) := by
    have h1 : ∀ c : Fin l × Bool, (if c.2 then sg (q c.1) else sg (p c.1)) ^ 2 = 1 := by
      intro c
      split_ifs <;> (rw [sq]; exact sg_sq _)
    simp [h1]
    ring
  have hh : ∑ x : Fin m, sg (H x) ^ 2 = (m : ℤ) := by
    have h1 : ∀ x : Fin m, sg (H x) ^ 2 = 1 := fun x => by rw [sq]; exact sg_sq _
    simp [h1]
  have hfirst : (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 := by
    rw [h4e]
    refine le_trans hCS (le_of_eq ?_)
    rw [hG, hτ, hh]
    ring
  refine ⟨hfirst, ?_⟩
  have hsecond : (m:ℤ) * l ≤ 2 * m + 8 * e := by
    by_contra hcon
    have hlt : 2 * (m:ℤ) + 8 * e < m * l := lt_of_not_ge hcon
    have hA : (0:ℤ) ≤ m * (l + 2) := by positivity
    have h1 : (m:ℤ) * (l + 2) < 2 * (m * l - 4 * e) := by linarith
    have h2 := mul_self_lt_mul_self hA h1
    nlinarith [h2, hfirst, mul_nonneg (sq_nonneg (m:ℤ)) (sq_nonneg ((l:ℤ)-2))]
  exact_mod_cast hsecond

theorem main : ∀ (n m l : ℕ) (F : Fin n → Fin m → Bool),
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m) →
  ∀ (name : Fin l × Bool ↪ Fin n) (H : Fin m → Bool) (p q : Fin l → Bool),
    let e := ∑ i : Fin l, ((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card
    (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 ∧
      m*l ≤ 2*m + 8*e := by
  intro n m l F hF name H p q e
  exact core F hF name H p q e rfl

end PEqualNP.Outside.L_lib_713_aux

theorem PEqualNP.Outside.L_lib_713 : (∀ (n m l : ℕ) (F : Fin n → Fin m → Bool),
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m) →
  ∀ (name : Fin l × Bool ↪ Fin n) (H : Fin m → Bool) (p q : Fin l → Bool),
    let e := ∑ i : Fin l, ((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card
    (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 ∧
      m*l ≤ 2*m + 8*e) := by
  exact PEqualNP.Outside.L_lib_713_aux.main
