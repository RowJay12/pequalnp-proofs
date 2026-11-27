import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_605_aux

theorem inj_of_covers (m r : ℕ) (label : Fin m → Fin (m+1) → (Fin r → Bool))
    (h : ∀ x : Fin m → (Fin r → Bool), ∃ a, ∀ i, x i ≠ label i a) :
    ∀ i, Function.Injective (label i) := by
  intro i a a' haa
  by_contra hne
  have hcard : Fintype.card (Fin m) = Fintype.card {c : Fin (m+1) // c ≠ a'} := by
    simp [Fintype.card_subtype_compl]
  obtain ⟨e0⟩ := Fintype.card_eq.mp hcard
  obtain ⟨e, hei⟩ : ∃ e : Fin m ≃ {c : Fin (m+1) // c ≠ a'}, (e i).val = a :=
    ⟨(Equiv.swap i (e0.symm ⟨a, hne⟩)).trans e0, by simp⟩
  obtain ⟨c, hc⟩ := h (fun j => label j (e j).val)
  by_cases hca : c = a'
  · apply hc i
    show label i (e i).val = label i c
    rw [hei, hca, haa]
  · apply hc (e.symm ⟨c, hca⟩)
    simp

theorem covers_of_inj (m r : ℕ) (label : Fin m → Fin (m+1) → (Fin r → Bool))
    (hinj : ∀ i, Function.Injective (label i)) (x : Fin m → (Fin r → Bool)) :
    ∃ a, ∀ i, x i ≠ label i a := by
  by_contra hcon
  push_neg at hcon
  choose f hf using hcon
  have hfi : Function.Injective f := by
    intro a a' h
    apply hinj (f a)
    rw [← hf a, h]
    exact hf a'
  have := Fintype.card_le_of_injective f hfi
  simp at this

theorem part3 (m r : ℕ) (label : Fin m → Fin (m+1) → (Fin r → Bool))
    (hinj : ∀ i, Function.Injective (label i)) (b : Fin (m+1)) :
    ∃ order : Fin m → Fin (m+1), Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : Fin (m+1)),
        (∀ i, label i (if flags i then b else order i) ≠ label i v) ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j) := by
  refine ⟨b.succAbove, Fin.succAbove_right_injective, fun i => Fin.succAbove_ne b i, ?_⟩
  intro flags v
  have key : (∀ i, label i (if flags i then b else b.succAbove i) ≠ label i v) ↔
      ∀ i, (if flags i then b else b.succAbove i) ≠ v := by
    refine forall_congr' fun i => ?_
    exact (hinj i).ne_iff
  rw [key]
  constructor
  · intro h
    by_cases hv : v = b
    · left
      refine ⟨hv, fun j => ?_⟩
      by_contra hj
      have hj' : flags j = true := by simpa using hj
      have h2 := h j
      simp [hj', hv] at h2
    · right
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hv
      refine ⟨j, ?_, hj.symm⟩
      by_contra hfj
      have h2 := h j
      simp [hfj, hj] at h2
  · rintro (⟨hv, hall⟩ | ⟨j, hj, hv⟩) i
    · simp [hall i, hv, Fin.succAbove_ne]
    · subst hv
      by_cases hi : flags i = true
      · simp only [hi, if_true]
        exact (Fin.succAbove_ne b j).symm
      · have hij : i ≠ j := by
          rintro rfl
          exact hi hj
        simp only [hi]
        exact fun h => hij (Fin.succAbove_right_injective h)

theorem main : ∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) := by
  intro m r A W label ok covers
  exact ⟨⟨fun h => inj_of_covers m r label h, fun h x => covers_of_inj m r label h x⟩,
    fun h b => part3 m r label (inj_of_covers m r label h) b⟩

end PEqualNP.Outside.L_lib_605_aux

theorem PEqualNP.Outside.L_lib_605 : (∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j))) := by
  exact PEqualNP.Outside.L_lib_605_aux.main
