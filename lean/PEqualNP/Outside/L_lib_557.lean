import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_557_aux

open Matrix

noncomputable def colv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => M i j)

theorem gram_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * H i j) ^ 2 = n * ∑ i, v i ^ 2 := by
  have h1 : ∀ j, (∑ i, v i * H i j) ^ 2 = ∑ i, ∑ k, (v i * v k) * (H i j * H k j) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ j, ∑ k, (v i * v k) * (H i j * H k j) = n * v i ^ 2 := by
    intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hH]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp_rw [h2]
  rw [Finset.mul_sum]

theorem expand {n r : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin r) ℝ V) (h a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ V) :
    inner ℝ h a = ∑ t, inner ℝ (b t : EuclideanSpace ℝ (Fin n)) a
      * inner ℝ (b t : EuclideanSpace ℝ (Fin n)) h := by
  have e1 := b.sum_repr' ⟨a, ha⟩
  have e2 : a = ∑ t, inner ℝ (b t : EuclideanSpace ℝ (Fin n)) a
      • (b t : EuclideanSpace ℝ (Fin n)) := by
    have e3 := congrArg Subtype.val e1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e3
    exact e3.symm
  conv_lhs => rw [e2]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [inner_smul_right, real_inner_comm h]

theorem pars {n r : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin r) ℝ V) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ V) :
    ∑ t, (inner ℝ (b t : EuclideanSpace ℝ (Fin n)) a) ^ 2 = ‖a‖ ^ 2 := by
  have h1 := b.sum_sq_norm_inner_right ⟨a, ha⟩
  have e : ‖(⟨a, ha⟩ : V)‖ = ‖a‖ := rfl
  rw [e] at h1
  rw [← h1]
  apply Finset.sum_congr rfl
  intro t _
  have e2 : inner ℝ (b t) (⟨a, ha⟩ : V) = inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) a := rfl
  rw [e2, Real.norm_eq_abs, sq_abs]

theorem core {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, H i j * A i j)^2 ≤ (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.range A.mulVecLin).map (e : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hV : Module.finrank ℝ V = A.rank := LinearEquiv.finrank_map_eq e _
  let b := stdOrthonormalBasis ℝ V
  have hmem : ∀ j, colv A j ∈ V := by
    intro j
    refine Submodule.mem_map.2 ⟨A *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩, ?_⟩
    rw [mulVec_single_one]
    rfl
  have hin : ∀ j, inner ℝ (colv H j) (colv A j) = ∑ i, H i j * A i j := by
    intro j
    simp [colv, PiLp.inner_apply, mul_comm]
  have hno : ∀ j, ‖colv A j‖ ^ 2 = ∑ i, (A i j) ^ 2 := by
    intro j
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [colv]
  have hbi : ∀ t j, inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (colv H j)
      = ∑ i, ((b t : EuclideanSpace ℝ (Fin n)) i) * H i j := by
    intro t j
    simp [colv, PiLp.inner_apply, mul_comm]
  have hbt : ∀ t, ∑ j, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (colv H j)) ^ 2 = n := by
    intro t
    simp only [hbi]
    rw [gram_sum H hH]
    have h1 : ‖(b t : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      have hn1 : ‖(b t : EuclideanSpace ℝ (Fin n))‖ = 1 := b.norm_eq_one t
      rw [hn1]
      norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at h1
    rw [h1, mul_one]
  have hS : (∑ i, ∑ j, H i j * A i j)
      = ∑ p : Fin n × Fin (Module.finrank ℝ V),
          inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv A p.1)
            * inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv H p.1) := by
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [← hin, expand V b _ _ (hmem j)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin n × Fin (Module.finrank ℝ V)))
    (fun p => inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv A p.1))
    (fun p => inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv H p.1))
  have hA2 : ∑ p : Fin n × Fin (Module.finrank ℝ V),
      (inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv A p.1)) ^ 2
        = ∑ i, ∑ j, (A i j) ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm (f := fun i j => (A i j)^2)]
    apply Finset.sum_congr rfl
    intro j _
    rw [pars V b _ (hmem j), hno]
  have hH2 : ∑ p : Fin n × Fin (Module.finrank ℝ V),
      (inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv H p.1)) ^ 2
        = (A.rank : ℝ) * n := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [hbt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hV]
  rw [hS]
  calc (∑ p : Fin n × Fin (Module.finrank ℝ V),
          inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv A p.1)
            * inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv H p.1)) ^ 2
      ≤ (∑ p : Fin n × Fin (Module.finrank ℝ V),
          (inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv A p.1)) ^ 2)
        * (∑ p : Fin n × Fin (Module.finrank ℝ V),
          (inner ℝ ((b p.2 : EuclideanSpace ℝ (Fin n))) (colv H p.1)) ^ 2) := hCS
    _ = (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
      rw [hA2, hH2]
      ring

theorem lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (r : ℕ) (hr : r ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.rank ≤ r) :
    (n : ℝ) * ((n - r : ℕ) : ℝ) ≤ ∑ i, ∑ j, (H i j - A i j)^2 := by
  have hc := core H hH A
  have hQ0 : 0 ≤ ∑ i, ∑ j, (A i j)^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hone : ∀ i j, (H i j)^2 = 1 := by
    intro i j
    rcases hpm i j with h | h <;> rw [h] <;> norm_num
  have hH2 : ∑ i : Fin n, ∑ j : Fin n, (H i j)^2 = (n:ℝ) * n := by
    simp [hone]
  have hexp : ∑ i, ∑ j, (H i j - A i j)^2
      = (n:ℝ) * n - 2 * (∑ i, ∑ j, H i j * A i j) + ∑ i, ∑ j, (A i j)^2 := by
    rw [← hH2, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrank : (A.rank : ℝ) ≤ r := by exact_mod_cast hA
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hc2 : (∑ i, ∑ j, H i j * A i j)^2 ≤ (n:ℝ) * r * (∑ i, ∑ j, (A i j)^2) :=
    le_trans hc (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank hn0) hQ0)
  have h4 : (2 * (∑ i, ∑ j, H i j * A i j))^2 ≤ ((∑ i, ∑ j, (A i j)^2) + n * r)^2 := by
    nlinarith [sq_nonneg ((∑ i, ∑ j, (A i j)^2) - n * r)]
  have h5 := abs_le_of_sq_le_sq' h4 (add_nonneg hQ0 (mul_nonneg hn0 hr0))
  rw [hexp, Nat.cast_sub hr]
  nlinarith [h5.2]

theorem upper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1) (r : ℕ) (hr : r ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.rank ≤ r ∧
      ∑ i, ∑ j, (H i j - A i j)^2 = (n : ℝ) * ((n - r : ℕ) : ℝ) := by
  refine ⟨Matrix.diagonal (fun i : Fin n => if i.val < r then (1:ℝ) else 0) * H, ?_, ?_⟩
  · refine le_trans (Matrix.rank_mul_le_left _ _) ?_
    rw [Matrix.rank_diagonal]
    calc _ ≤ Fintype.card (Fin r) := by
          apply Fintype.card_le_of_injective (fun x => (⟨x.1.val, by
            by_contra hlt
            exact x.2 (by simp [hlt])⟩ : Fin r))
          intro x y hxy
          apply Subtype.ext
          apply Fin.ext
          exact Fin.mk.inj hxy
      _ = r := Fintype.card_fin r
  · have hone : ∀ i j, (H i j)^2 = 1 := by
      intro i j
      rcases hpm i j with h | h <;> rw [h] <;> norm_num
    have h1 : ∀ i j, (H i j
        - (Matrix.diagonal (fun i : Fin n => if i.val < r then (1:ℝ) else 0) * H) i j)^2
          = if i.val < r then 0 else 1 := by
      intro i j
      rw [Matrix.diagonal_mul]
      split_ifs
      · simp
      · simp [hone]
    simp_rw [h1]
    have h3 : ∑ i : Fin n, (if i.val < r then (0:ℝ) else 1) = ((n - r : ℕ) : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then (0:ℝ) else 1) n]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
        mul_one]
      congr 1
      have h4 : (Finset.range n).filter (fun i => ¬ i < r) = Finset.Ico r n := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [h4, Nat.card_Ico]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, h3]

theorem main : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ r : ℕ, r ≤ n →
    let err := fun (A : Matrix (Fin n) (Fin n) ℝ) => ∑ i, ∑ j, (H i j - A i j)^2
    let best : ℝ := n * (n-r : ℕ)
    (∀ A, A.rank ≤ r → best ≤ err A) ∧ (∃ A, A.rank ≤ r ∧ err A = best) := by
  intro n H hn hpm hH r hr err best
  exact ⟨fun A hA => lower H hpm hH r hr A hA, upper H hpm r hr⟩

end PEqualNP.Outside.L_lib_557_aux

theorem PEqualNP.Outside.L_lib_557 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ r : ℕ, r ≤ n →
    let err := fun (A : Matrix (Fin n) (Fin n) ℝ) => ∑ i, ∑ j, (H i j - A i j)^2
    let best : ℝ := n * (n-r : ℕ)
    (∀ A, A.rank ≤ r → best ≤ err A) ∧ (∃ A, A.rank ≤ r ∧ err A = best)) := by
  exact PEqualNP.Outside.L_lib_557_aux.main
