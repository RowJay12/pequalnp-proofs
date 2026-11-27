import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_481

namespace PEqualNP.Outside.L_lib_604_aux

theorem farkas (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2)
    (R : Finset (Fin m))
    (h : ¬ ∃ x : Fin n → ZMod 2, ∀ e ∈ R, (∑ j, row e j * x j) = rhs e) :
    ∃ D : Finset (Fin m), D ⊆ R ∧ (∀ j : Fin n, D.sum (fun e => row e j) = 0) ∧
      D.sum rhs = 1 := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin m) (Fin n) (ZMod 2),
      ∀ e j, A e j = if e ∈ R then row e j else 0 :=
    ⟨fun e j => if e ∈ R then row e j else 0, fun _ _ => rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Fin m → ZMod 2, ∀ e, b' e = if e ∈ R then rhs e else 0 :=
    ⟨fun e => if e ∈ R then rhs e else 0, fun _ => rfl⟩
  have hb : b' ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨x, fun e he => ?_⟩
    have h1 := congrFun hx e
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hA, hb', he] using h1
  obtain ⟨f, hfb, hf⟩ := Submodule.exists_le_ker_of_notMem hb
  obtain ⟨y, hy⟩ : ∃ y : Fin m → ZMod 2, ∀ e, y e = f (fun j => if e = j then 1 else 0) :=
    ⟨_, fun _ => rfl⟩
  have hz : ∀ c d : ZMod 2, (if c = 1 then d else 0) = d * c := by decide
  have hD : ∀ gg : Fin m → ZMod 2, (R.filter (fun e => y e = 1)).sum gg =
      f (fun e => if e ∈ R then gg e else 0) := by
    intro gg
    rw [LinearMap.pi_apply_eq_sum_univ f, Finset.sum_filter]
    simp only [hz, ← hy, smul_eq_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  refine ⟨R.filter (fun e => y e = 1), Finset.filter_subset _ _, ?_, ?_⟩
  · intro j
    rw [hD]
    have hmem : (fun e => if e ∈ R then row e j else 0) ∈ LinearMap.range A.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      funext e
      simp [Matrix.mulVec, dotProduct, hA, Pi.single_apply]
    have h2 := hf hmem
    simpa using h2
  · rw [hD]
    have h3 : f (fun e => if e ∈ R then rhs e else 0) ≠ 0 := by
      have hbe : b' = fun e => if e ∈ R then rhs e else 0 := funext hb'
      rw [← hbe]
      exact hfb
    exact (show ∀ c : ZMod 2, c ≠ 0 → c = 1 by decide) _ h3

theorem symmDiff_sum (m : ℕ) (gg : Fin m → ZMod 2) (D D' : Finset (Fin m)) :
    (symmDiff D D').sum gg = D.sum gg + D'.sum gg := by
  have hi : ∀ S : Finset (Fin m), S.sum gg = ∑ i, if i ∈ S then gg i else 0 := by
    intro S
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hi (symmDiff D D'), hi D, hi D', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : gg i + gg i = 0 := CharTwo.add_self_eq_zero (gg i)
  by_cases h : i ∈ D <;> by_cases h' : i ∈ D' <;> simp [Finset.mem_symmDiff, h, h', h2]

theorem core (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2)
    (W : Finset (Finset (Fin m)))
    (hmem : ∀ D : Finset (Fin m), D ∈ W ↔
      ((∀ j : Fin n, D.sum (fun e => row e j) = 0) ∧ D.sum rhs = 1))
    (hne : W.Nonempty) (hmiss : ∀ e : Fin m, ∃ D ∈ W, e ∉ D) :
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  have hhalf : ∀ e ∈ W.biUnion id,
      2*(W.filter (fun subset => e ∈ subset)).card = W.card := by
    intro e he
    obtain ⟨D0, hD0, heD0⟩ := Finset.mem_biUnion.mp he
    obtain ⟨D1, hD1, heD1⟩ := hmiss e
    have heD0' : e ∈ D0 := heD0
    obtain ⟨K, hK⟩ : ∃ K, K = symmDiff D0 D1 := ⟨_, rfl⟩
    have heK : e ∈ K := by
      rw [hK, Finset.mem_symmDiff]
      left
      exact ⟨heD0', heD1⟩
    have h0 := (hmem D0).mp hD0
    have h1 := (hmem D1).mp hD1
    have hKW : ∀ D, D ∈ W → symmDiff D K ∈ W := by
      intro D hD
      have h2 := (hmem D).mp hD
      rw [hmem]
      constructor
      · intro j
        rw [hK, symmDiff_sum, symmDiff_sum, h2.1 j, h0.1 j, h1.1 j]
        simp
      · rw [hK, symmDiff_sum, symmDiff_sum, h2.2, h0.2, h1.2]
        decide
    have hcard : (W.filter (fun s => e ∈ s)).card = (W.filter (fun s => ¬ e ∈ s)).card := by
      apply Finset.card_bij' (fun D _ => symmDiff D K) (fun D _ => symmDiff D K)
      · intro D hD
        rw [Finset.mem_filter] at hD ⊢
        exact ⟨hKW D hD.1, by simp [Finset.mem_symmDiff, hD.2, heK]⟩
      · intro D hD
        rw [Finset.mem_filter] at hD ⊢
        exact ⟨hKW D hD.1, by simp [Finset.mem_symmDiff, hD.2, heK]⟩
      · intro D hD
        simp
      · intro D hD
        simp
    have hsplit : (W.filter (fun s => e ∈ s)).card + (W.filter (fun s => ¬ e ∈ s)).card
        = W.card := Finset.card_filter_add_card_filter_not _
    omega
  refine ⟨hhalf, ?_⟩
  intro w
  have hsum : 2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w := by
    have h1 : ∀ s ∈ W, s.sum w = (W.biUnion id).sum (fun e => if e ∈ s then w e else 0) := by
      intro s hs
      rw [Finset.sum_ite_mem]
      congr 1
      exact (Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem id hs)).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have h3 : ∑ s ∈ W, (if e ∈ s then w e else 0) = (W.filter (fun s => e ∈ s)).card * w e := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    rw [h3, ← mul_assoc, hhalf e he]
  refine ⟨hsum, ?_⟩
  have h4 : ∑ D ∈ W, 2 * D.sum w = ∑ D ∈ W, (W.biUnion id).sum w := by
    rw [← Finset.mul_sum, hsum, Finset.sum_const, smul_eq_mul]
  exact Finset.exists_le_of_sum_le hne (le_of_eq h4)

theorem main : ∀ (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2),
  let ok := fun (rows : Finset (Fin m)) => ∃ x : Fin n → ZMod 2,
    ∀ e ∈ rows, (∑ j, row e j * x j) = rhs e
  let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
    (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
  ¬ ok Finset.univ → (∀ e : Fin m, ¬ ok (Finset.univ.erase e)) →
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  intro n m row rhs ok W hno herase
  have hmemW : ∀ D : Finset (Fin m), D ∈ W ↔
      ((∀ j : Fin n, D.sum (fun e => row e j) = 0) ∧ D.sum rhs = 1) := by
    intro D
    show D ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hne : W.Nonempty := by
    obtain ⟨D, -, h1, h2⟩ := farkas n m row rhs Finset.univ hno
    exact ⟨D, (hmemW D).mpr ⟨h1, h2⟩⟩
  have hmiss : ∀ e : Fin m, ∃ D ∈ W, e ∉ D := by
    intro e
    obtain ⟨D, hsub, h1, h2⟩ := farkas n m row rhs (Finset.univ.erase e) (herase e)
    exact ⟨D, (hmemW D).mpr ⟨h1, h2⟩, fun he => (Finset.mem_erase.mp (hsub he)).1 rfl⟩
  exact ⟨hne, core n m row rhs W hmemW hne hmiss⟩

end PEqualNP.Outside.L_lib_604_aux

theorem PEqualNP.Outside.L_lib_604 : (∀ (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2),
  let ok := fun (rows : Finset (Fin m)) => ∃ x : Fin n → ZMod 2,
    ∀ e ∈ rows, (∑ j, row e j * x j) = rhs e
  let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
    (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
  ¬ ok Finset.univ → (∀ e : Fin m, ¬ ok (Finset.univ.erase e)) →
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w) := by
  exact PEqualNP.Outside.L_lib_604_aux.main
