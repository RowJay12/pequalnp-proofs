import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_691_aux

theorem main : ∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
  (∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2) →
  ((∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) ↔
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j))) := by
  intro q T hq hT
  constructor
  · rintro ⟨x, hx⟩
    choose f hf using hx
    have hfib : ∀ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card ≤ 2 := by
      intro j
      refine le_trans (Finset.card_le_card ?_) (hT j (x j))
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨hr.1, ?_⟩
      rw [← hr.2]
      exact hf r
    have hsum : ∑ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card = q + 3 := by
      rw [← Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
        (fun r _ => Finset.mem_univ (f r))]
      simp
    obtain ⟨B, hBdef⟩ : ∃ B : Finset (Fin q), B = Finset.univ.filter (fun j =>
        (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card = 2) := ⟨_, rfl⟩
    have h3 : 3 ≤ B.card := by
      have h1 : ∑ j : Fin q, (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card
          ≤ ∑ j : Fin q, (1 + if (Finset.univ.filter (fun r : Fin (q + 3) => f r = j)).card = 2
            then 1 else 0) := by
        apply Finset.sum_le_sum
        intro j _
        have h2 := hfib j
        split_ifs with h4 <;> omega
      rw [hsum, Finset.sum_add_distrib, ← Finset.card_filter, ← hBdef] at h1
      have h5 : ∑ _j : Fin q, 1 = q := by simp
      rw [h5] at h1
      omega
    obtain ⟨c, hcinj, hcB⟩ : ∃ c : Fin 3 → Fin q, Function.Injective c ∧ ∀ k, c k ∈ B :=
      ⟨fun k => B.orderEmbOfCardLe h3 k, (B.orderEmbOfCardLe h3).injective,
        fun k => Finset.orderEmbOfCardLe_mem B h3 k⟩
    refine ⟨c, fun k => Finset.univ.filter (fun r => f r = c k), hcinj, ?_, ?_⟩
    · intro k
      refine ⟨?_, x (c k), ?_⟩
      · have h6 := hcB k
        rw [hBdef, Finset.mem_filter] at h6
        exact h6.2
      · intro r hr
        rw [Finset.mem_filter] at hr
        rw [← hr.2]
        exact hf r
    · intro i j hij
      rw [Finset.disjoint_left]
      intro r hri hrj
      rw [Finset.mem_filter] at hri hrj
      exact hij (hcinj (hri.2.symm.trans hrj.2))
  · rintro ⟨c, P, hc, hP, hdis⟩
    choose a ha using fun k => (hP k).2
    obtain ⟨R, hRdef⟩ : ∃ R : Finset (Fin (q + 3)), R = Finset.univ.biUnion P := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ C : Finset (Fin q), C = Finset.univ.image c := ⟨_, rfl⟩
    have hR : R.card = 6 := by
      rw [hRdef, Finset.card_biUnion (fun i _ j _ hij => hdis i j hij),
        Finset.sum_congr rfl (fun k _ => (hP k).1)]
      simp
    have hC : C.card = 3 := by
      rw [hCdef, Finset.card_image_of_injective _ hc]
      simp
    have hcard : Rᶜ.card = Cᶜ.card := by
      rw [Finset.card_compl, Finset.card_compl, hR, hC, Fintype.card_fin, Fintype.card_fin]
      omega
    have hcard' : Fintype.card {r // r ∈ Rᶜ} = Fintype.card {j // j ∈ Cᶜ} := by
      rw [Fintype.card_coe, Fintype.card_coe]
      exact hcard
    obtain ⟨e⟩ : Nonempty ({r // r ∈ Rᶜ} ≃ {j // j ∈ Cᶜ}) := ⟨Fintype.equivOfCardEq hcard'⟩
    refine ⟨fun j => if h : ∃ k, c k = j then a h.choose else
        if h' : j ∈ Cᶜ then T (e.symm ⟨j, h'⟩).val j else j, fun r => ?_⟩
    by_cases hr : r ∈ R
    · rw [hRdef] at hr
      obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp hr
      refine ⟨c k, ?_⟩
      have hex : ∃ k', c k' = c k := ⟨k, rfl⟩
      simp only [dif_pos hex]
      have hch : hex.choose = k := hc hex.choose_spec
      rw [hch]
      exact ha k r hk
    · have hr' : r ∈ Rᶜ := Finset.mem_compl.mpr hr
      have hj := (e ⟨r, hr'⟩).2
      refine ⟨(e ⟨r, hr'⟩).val, ?_⟩
      have hne : ¬ ∃ k, c k = (e ⟨r, hr'⟩).val := by
        rintro ⟨k, hk⟩
        have hkC : c k ∈ C := by
          rw [hCdef]
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        rw [hk] at hkC
        exact Finset.mem_compl.mp hj hkC
      simp only [dif_neg hne, dif_pos hj]
      have hsym : e.symm ⟨(e ⟨r, hr'⟩).val, hj⟩ = ⟨r, hr'⟩ := by simp
      rw [hsym]

end PEqualNP.Outside.L_lib_691_aux

theorem PEqualNP.Outside.L_lib_691 : (∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
  (∀ (j a : Fin q), (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card ≤ 2) →
  ((∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j) ↔
    ∃ (c : Fin 3 → Fin q) (P : Fin 3 → Finset (Fin (q + 3))),
      Function.Injective c ∧
      (∀ k : Fin 3, (P k).card = 2 ∧ ∃ a : Fin q, ∀ r ∈ P k, T r (c k) = a) ∧
      (∀ i j : Fin 3, i ≠ j → Disjoint (P i) (P j)))) := by
  exact PEqualNP.Outside.L_lib_691_aux.main
