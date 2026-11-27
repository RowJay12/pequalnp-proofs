import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_556_aux

theorem inner_toLp {n : ℕ} (f g : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 g) = ∑ i, f i * g i := by
  simp [PiLp.inner_apply, mul_comm]

theorem main : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, ∑ j, H i j * A i j)^2 ≤
      (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  intro n H hn hpm horth A
  classical
  let col : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  let hc : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => H i j)
  let R : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ (Set.range col)
  have hk : Module.finrank ℝ R ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
    have hmap : R.map e.toLinearMap = Submodule.span ℝ (Set.range A.col) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
    rw [← hmap, LinearEquiv.finrank_map_eq]
  have hmem : ∀ j, col j ∈ R := fun j => Submodule.subset_span ⟨j, rfl⟩
  let b := stdOrthonormalBasis ℝ R
  have hexp : ∀ j, inner ℝ (hc j) (col j) =
      ∑ l, inner ℝ (hc j) (b l : EuclideanSpace ℝ (Fin n)) *
        inner ℝ (b l : EuclideanSpace ℝ (Fin n)) (col j) := by
    intro j
    have h := b.sum_repr' ⟨col j, hmem j⟩
    have h2 := congrArg (fun y : R => inner ℝ (hc j) (y : EuclideanSpace ℝ (Fin n))) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_comm]
    rfl
  have hpars : ∀ j, ∑ l, (inner ℝ (b l : EuclideanSpace ℝ (Fin n)) (col j))^2 =
      ∑ i, (A i j)^2 := by
    intro j
    have h := b.sum_inner_mul_inner ⟨col j, hmem j⟩ ⟨col j, hmem j⟩
    have h3 : inner ℝ (col j) (col j) = ∑ i, (A i j)^2 := by
      rw [inner_toLp]
      simp [sq]
    rw [← h3]
    have h4 : inner ℝ (⟨col j, hmem j⟩ : R) ⟨col j, hmem j⟩ = inner ℝ (col j) (col j) := rfl
    rw [← h4, ← h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [sq]
    change _ = inner ℝ (col j) (b l : EuclideanSpace ℝ (Fin n)) *
      inner ℝ (b l : EuclideanSpace ℝ (Fin n)) (col j)
    rw [real_inner_comm (col j) (b l : EuclideanSpace ℝ (Fin n))]
  have hHrow : ∀ e : Fin n → ℝ, ∑ j, (∑ i, H i j * e i)^2 = (n : ℝ) * ∑ i, (e i)^2 := by
    intro e
    have : ∀ j, (∑ i, H i j * e i)^2 = ∑ i, ∑ i', e i * e i' * (H i j * H i' j) := by
      intro j
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun i' _ => ?_))
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, horth]
    simp [sq]
    ring
  have hnorm : ∀ l, ∑ j, (inner ℝ (hc j) (b l : EuclideanSpace ℝ (Fin n)))^2 = (n : ℝ) := by
    intro l
    set v : EuclideanSpace ℝ (Fin n) := (b l : EuclideanSpace ℝ (Fin n)) with hv
    have hv1 : inner ℝ v v = 1 := by
      rw [hv]
      have : inner ℝ (b l) (b l) = (1 : ℝ) := by
        rw [real_inner_self_eq_norm_sq, b.orthonormal.1 l]
        norm_num
      exact this
    have hvv : inner ℝ v v = ∑ i, (v.ofLp i)^2 := by
      have := inner_toLp v.ofLp v.ofLp
      simpa [sq] using this
    have hcj : ∀ j, inner ℝ (hc j) v = ∑ i, H i j * v.ofLp i := by
      intro j
      have := inner_toLp (fun i => H i j) v.ofLp
      simpa using this
    simp_rw [hcj]
    rw [hHrow, ← hvv, hv1, mul_one]
  have h1 : ∑ i, ∑ j, H i j * A i j = ∑ j, inner ℝ (hc j) (col j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_toLp]
  rw [h1]
  simp_rw [hexp]
  rw [← Finset.sum_product']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ)
    (fun p : Fin n × Fin (Module.finrank ℝ R) => inner ℝ (hc p.1) (b p.2 : EuclideanSpace ℝ (Fin n)))
    (fun p : Fin n × Fin (Module.finrank ℝ R) => inner ℝ (b p.2 : EuclideanSpace ℝ (Fin n)) (col p.1))
  refine hcs.trans ?_
  rw [Finset.sum_product, Finset.sum_product]
  simp_rw [hpars]
  rw [Finset.sum_comm]
  simp_rw [hnorm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]
  have hA : 0 ≤ ∑ i, ∑ j, (A i j)^2 := by positivity
  have hkr : (Module.finrank ℝ R : ℝ) ≤ (A.rank : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkr (mul_nonneg hn0 hA)]

end PEqualNP.Outside.L_lib_556_aux

theorem PEqualNP.Outside.L_lib_556 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, ∑ j, H i j * A i j)^2 ≤
      (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2)) := by
  exact PEqualNP.Outside.L_lib_556_aux.main
