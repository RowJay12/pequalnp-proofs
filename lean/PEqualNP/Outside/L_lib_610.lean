import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_610_aux

theorem par_count {β : Type*} [DecidableEq β] (S : Finset β) (g : β → ℕ) :
    (S.filter (fun a => (g a % 2 == 1) = true)).card % 2 = (∑ a ∈ S, g a) % 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.filter_insert, Finset.sum_insert ha]
    by_cases hg : (g a % 2 == 1) = true
    · rw [if_pos hg, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
      have : g a % 2 = 1 := by simpa using hg
      omega
    · rw [if_neg hg]
      have : g a % 2 = 0 := by
        simp only [beq_iff_eq] at hg
        omega
      omega

theorem even_count {α : Type*} [DecidableEq α] (U f : Finset α) (u : α) (huU : u ∈ U)
    (huf : u ∉ f) (w : α → Bool) :
    2 ∣ (U.powerset.filter (fun A => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card := by
  set T := U.powerset.filter (fun A => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true) with hT
  have hinv : ∀ A B : Finset α, (∀ v, v ≠ u → (v ∈ A ↔ v ∈ B)) → A ∈ T → B ⊆ U → B ∈ T := by
    intro A B hAB hA hBU
    rw [hT, Finset.mem_filter, Finset.mem_powerset] at hA ⊢
    refine ⟨hBU, fun v hv => ?_⟩
    have hvu : v ≠ u := fun h => huf (h ▸ hv)
    have := hA.2 v hv
    by_cases hvU : v ∈ U
    · rw [if_pos hvU] at this ⊢
      simpa [← hAB v hvu] using this
    · rw [if_neg hvU] at this ⊢
      exact this
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun A => u ∈ A)
  have heq : (T.filter (fun A => u ∈ A)).card = (T.filter (fun A => ¬ u ∈ A)).card := by
    apply Finset.card_nbij' (fun A => A.erase u) (fun A => insert u A)
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA ⊢
      refine ⟨hinv A _ ?_ hA.1 ?_, Finset.notMem_erase u A⟩
      · intro v hv
        rw [Finset.mem_erase]
        tauto
      · exact (Finset.erase_subset u A).trans
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hA.1).1)
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA ⊢
      refine ⟨hinv A _ ?_ hA.1 ?_, Finset.mem_insert_self u A⟩
      · intro v hv
        rw [Finset.mem_insert]
        tauto
      · exact Finset.insert_subset huU (Finset.mem_powerset.mp (Finset.mem_filter.mp hA.1).1)
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA
      exact Finset.insert_erase hA.2
    · intro A hA
      rw [Finset.mem_coe, Finset.mem_filter] at hA
      exact Finset.erase_insert hA.2
  rw [← hsplit, heq]
  exact ⟨_, (two_mul _).symm⟩

theorem p1 {α : Type*} [DecidableEq α] (terms : Finset (Finset α)) (U : Finset α)
    (hU : U ∈ terms) (hmax : ∀ f ∈ terms, U ⊆ f → f = U) (w : α → Bool) :
    (U.powerset.filter (fun A => ((terms.filter (fun f => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card % 2 == 1) = true)).card % 2 = 1 := by
  rw [par_count]
  have h1 : ∑ A ∈ U.powerset, (terms.filter (fun f => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card =
      ∑ f ∈ terms, (U.powerset.filter (fun A => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [h1, ← Finset.add_sum_erase _ _ hU]
  have hUU : (U.powerset.filter (fun A => ∀ v ∈ U,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨U, ?_⟩
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hAU, hA⟩
      refine Finset.Subset.antisymm hAU (fun v hv => ?_)
      have := hA v hv
      rw [if_pos hv] at this
      simpa using this
    · rintro rfl
      refine ⟨Finset.Subset.refl _, fun v hv => ?_⟩
      rw [if_pos hv]
      simpa using hv
  have heven : ∀ f ∈ terms.erase U, 2 ∣ (U.powerset.filter (fun A => ∀ v ∈ f,
      (if v ∈ U then decide (v ∈ A) else w v) = true)).card := by
    intro f hf
    obtain ⟨hfU, hft⟩ := Finset.mem_erase.mp hf
    have hns : ¬ U ⊆ f := fun h => hfU (hmax f hft h)
    obtain ⟨u, huU, huf⟩ := Finset.not_subset.mp hns
    exact even_count U f u huU huf w
  obtain ⟨k, hk⟩ := Finset.dvd_sum heven
  rw [hUU, hk]
  omega

theorem main : ∀ (m r : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let eval := fun (T : Finset (Finset V)) (w : W) =>
    (((T.filter (fun f => ∀ v ∈ f, w v = true)).card % 2) == 1)
  ∀ (terms : Finset (Finset V)) (U : Finset V), U ∈ terms →
    (∀ f ∈ terms, U ⊆ f → f = U) →
    let old := (Finset.univ : Finset W).filter (fun x => eval terms x = true)
    (∀ w : W, (U.powerset.filter (fun A =>
      eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true)).card % 2 = 1) ∧
    ∀ (K : Nat) (bad : Fin K → Fin m → Symbol),
      let gone := U.image Prod.fst
      let miss := fun (J : Finset (Fin m)) (word : W) =>
        ∀ a, ∃ i, i ∉ J ∧ (fun v => word (i,v)) = bad a i
      ((Finset.univ : Finset W).filter (miss gone)).card ≤
        2^U.card * (old.filter (miss ∅)).card := by
  intro m r V W Symbol eval terms U hU hmax old
  have hp1 : ∀ w : W, (U.powerset.filter (fun A =>
      eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true)).card % 2 = 1 :=
by
    intro w
    have := p1 terms U hU hmax w
    simp only [eval]
    convert this using 8 with A hA
    ext f
    simp only [Finset.mem_filter]
  refine ⟨hp1, ?_⟩
  intro K bad gone miss
  have hex : ∀ w : W, ∃ A, A ∈ U.powerset ∧
      eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true := by
    intro w
    have h := hp1 w
    have hne : (U.powerset.filter (fun A =>
        eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨A, hA⟩ := hne
    exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2⟩
  let φ : W → W := fun w => fun v => if v ∈ U then decide (v ∈ Classical.choose (hex w)) else w v
  have hφoff : ∀ w : W, ∀ v, v ∉ U → φ w v = w v := by
    intro w v hv
    show (if v ∈ U then _ else w v) = w v
    rw [if_neg hv]
  refine Finset.card_le_mul_card_image_of_maps_to (f := φ) ?_ _ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Classical.choose_spec (hex w)).2⟩
    · intro a
      obtain ⟨i, hi, hb⟩ := hw.2 a
      refine ⟨i, Finset.notMem_empty i, ?_⟩
      rw [← hb]
      funext j
      apply hφoff
      intro hU'
      exact hi (Finset.mem_image.mpr ⟨(i, j), hU', rfl⟩)
  · intro x _
    have hcard : Fintype.card (↥U → Bool) = 2 ^ U.card := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    rw [← hcard, ← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun w : W => fun v : ↥U => w v.val)
    · intro w _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_coe, Finset.mem_filter] at hw1 hw2
      funext v
      by_cases hv : v ∈ U
      · exact congrFun heq ⟨v, hv⟩
      · rw [← hφoff w1 v hv, ← hφoff w2 v hv, hw1.2, hw2.2]

end PEqualNP.Outside.L_lib_610_aux

theorem PEqualNP.Outside.L_lib_610 : (∀ (m r : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let eval := fun (T : Finset (Finset V)) (w : W) =>
    (((T.filter (fun f => ∀ v ∈ f, w v = true)).card % 2) == 1)
  ∀ (terms : Finset (Finset V)) (U : Finset V), U ∈ terms →
    (∀ f ∈ terms, U ⊆ f → f = U) →
    let old := (Finset.univ : Finset W).filter (fun x => eval terms x = true)
    (∀ w : W, (U.powerset.filter (fun A =>
      eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true)).card % 2 = 1) ∧
    ∀ (K : Nat) (bad : Fin K → Fin m → Symbol),
      let gone := U.image Prod.fst
      let miss := fun (J : Finset (Fin m)) (word : W) =>
        ∀ a, ∃ i, i ∉ J ∧ (fun v => word (i,v)) = bad a i
      ((Finset.univ : Finset W).filter (miss gone)).card ≤
        2^U.card * (old.filter (miss ∅)).card) := by
  exact PEqualNP.Outside.L_lib_610_aux.main
