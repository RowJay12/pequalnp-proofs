import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_606_aux

theorem ind_card (k : ℕ) : (if (k % 2 == 1) = true then (1 : ZMod 2) else 0) = (k : ZMod 2) := by
  have h2 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod k 2).symm
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [h2, h]; simp
  · rw [h2, h]; simp

theorem even_sum {V ι : Type} [DecidableEq V] [DecidableEq ι] (pos : V → ι)
    (x : Finset ι → V → Bool)
    (hloc : ∀ (T T' : Finset ι) (v : V), (pos v ∈ T ↔ pos v ∈ T') → x T v = x T' v)
    (mon : Finset V) (S : Finset ι) (hS : mon.card < S.card)
    (inst : ∀ T : Finset ι, Decidable (∀ v ∈ mon, x T v = true)) :
    ∑ T ∈ S.powerset, (@ite (ZMod 2) (∀ v ∈ mon, x T v = true) (inst T) 1 0) = 0 := by
  have hex : ∃ p ∈ S, p ∉ mon.image pos := by
    by_contra hcon
    have hsub : S ⊆ mon.image pos := by
      intro p hp
      by_contra hpn
      exact hcon ⟨p, hp, hpn⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
    omega
  obtain ⟨p, hpS, hp⟩ := hex
  have hpv : ∀ v ∈ mon, pos v ≠ p := by
    intro v hv h
    exact hp (Finset.mem_image.mpr ⟨v, hv, h⟩)
  have hsame : ∀ T : Finset ι, (∀ v ∈ mon, x (if p ∈ T then T.erase p else insert p T) v = true) ↔
      (∀ v ∈ mon, x T v = true) := by
    intro T
    refine forall₂_congr fun v hv => ?_
    have hm : (pos v ∈ (if p ∈ T then T.erase p else insert p T) ↔ pos v ∈ T) := by
      have h3 := hpv v hv
      by_cases hpT : p ∈ T
      · simp [hpT, Finset.mem_erase, h3]
      · simp [hpT, Finset.mem_insert, h3]
    rw [hloc _ T v hm]
  refine Finset.sum_involution (fun T _ => if p ∈ T then T.erase p else insert p T) ?_ ?_ ?_ ?_
  · intro T hT
    by_cases hc : ∀ v ∈ mon, x T v = true
    · rw [if_pos hc, if_pos ((hsame T).mpr hc)]
      decide
    · rw [if_neg hc, if_neg (fun h => hc ((hsame T).mp h))]
      simp
  · intro T hT _
    by_cases hpT : p ∈ T
    · simp only [hpT, if_true]
      intro h
      have h4 : p ∈ T.erase p := by
        rw [h]
        exact hpT
      simp at h4
    · simp only [hpT, if_false]
      intro h
      have h4 : p ∈ insert p T := Finset.mem_insert_self p T
      rw [h] at h4
      exact hpT h4
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    by_cases hpT : p ∈ T
    · simp only [hpT, if_true]
      exact (Finset.erase_subset p T).trans hT
    · simp only [hpT, if_false]
      exact Finset.insert_subset hpS hT
  · intro T hT
    by_cases hpT : p ∈ T
    · simp [hpT, Finset.insert_erase hpT]
    · simp [hpT, Finset.erase_insert hpT]

theorem sum_one (ι : Type) [DecidableEq ι] (S : Finset ι) (hS : 0 < S.card) (c : Bool)
    (F : Finset ι → Bool) (hF : ∀ T ∈ S.powerset, F T = (if T = ∅ then c else !c)) :
    ∑ T ∈ S.powerset, (if F T = true then (1 : ZMod 2) else 0) = 1 := by
  have h0 : ∑ T ∈ S.powerset, (if T = ∅ then (1 : ZMod 2) else 0) = 1 := by simp
  cases c
  · have h1 : ∀ T ∈ S.powerset, (if F T = true then (1 : ZMod 2) else 0)
        = 1 + (if T = ∅ then 1 else 0) := by
      intro T hT
      rw [hF T hT]
      by_cases hTe : T = ∅
      · simp only [hTe, if_true]
        decide
      · simp [hTe]
    have h2 : ∑ T ∈ S.powerset, (1 : ZMod 2) = 0 := by
      rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one, Nat.cast_pow]
      have h3 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
      rw [h3, zero_pow (by omega)]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2, h0, zero_add]
  · have h1 : ∀ T ∈ S.powerset, (if F T = true then (1 : ZMod 2) else 0)
        = (if T = ∅ then 1 else 0) := by
      intro T hT
      rw [hF T hT]
      by_cases hTe : T = ∅ <;> simp [hTe]
    rw [Finset.sum_congr rfl h1, h0]

theorem core (g m r : ℕ) (label : Fin g → Fin m → Fin (m+1) → Fin r → Bool)
    (pick : (Fin g × Fin m × Fin r → Bool) → (Fin g → Fin (m+1)))
    (hpick : ∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j))
    (test : (Fin g → Fin (m+1)) → Bool) (base : Fin g → Fin (m+1)) (coord : Fin g)
    (b : ℕ) (terms : Finset (Finset (Fin g × Fin m × Fin r)))
    (hterms : ∀ mon ∈ terms, mon.card ≤ b)
    (hrep : ∀ input, test (pick input) =
      (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1))
    (bb : Fin (m+1)) :
    ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) ≠ test (Function.update base coord bb))).card ≤ b := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Bool, c = test (Function.update base coord bb) := ⟨_, rfl⟩
  rw [← hc]
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter
      (fun i => test (Function.update base coord (bb.succAbove i)) ≠ c) := ⟨_, rfl⟩
  have hinj : Function.Injective bb.succAbove := Fin.succAbove_right_injective
  have hScard : S.card = (Finset.univ.filter (fun z : Fin (m+1) =>
      test (Function.update base coord z) ≠ c)).card := by
    rw [← Finset.card_image_of_injective S hinj]
    congr 1
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hSdef]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hz
      have hzb : z ≠ bb := by
        rintro rfl
        exact hz hc.symm
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hzb
      exact ⟨i, hz, rfl⟩
  have hbS : b < S.card := by rw [hScard]; exact hlt
  obtain ⟨x, hx⟩ : ∃ x : Finset (Fin m) → (Fin g × Fin m × Fin r → Bool), ∀ T j i v,
      x T (j,i,v) = if j = coord then label coord i (if i ∈ T then bb else bb.succAbove i) v
        else label j i ((base j).succAbove i) v :=
    ⟨fun T q => if q.1 = coord then label coord q.2.1 (if q.2.1 ∈ T then bb else bb.succAbove q.2.1) q.2.2
        else label q.1 q.2.1 ((base q.1).succAbove q.2.1) q.2.2, fun T j i v => rfl⟩
  have hother : ∀ T j, j ≠ coord → pick (x T) j = base j := by
    intro T j hj
    by_contra hne
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
    apply hpick (x T) j i
    funext v
    rw [hx, if_neg hj, hi]
  have hempty : pick (x ∅) coord = bb := by
    by_contra hne
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
    apply hpick (x ∅) coord i
    funext v
    rw [hx, if_pos rfl, if_neg (Finset.notMem_empty i), hi]
  have hnonempty : ∀ T : Finset (Fin m), T.Nonempty → ∃ i ∈ T, pick (x T) coord = bb.succAbove i := by
    intro T hT
    obtain ⟨i0, hi0⟩ := hT
    have hne : pick (x T) coord ≠ bb := by
      intro h
      apply hpick (x T) coord i0
      funext v
      rw [hx, if_pos rfl, if_pos hi0, h]
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
    refine ⟨i, ?_, hi.symm⟩
    by_contra hiT
    apply hpick (x T) coord i
    funext v
    rw [hx, if_pos rfl, if_neg hiT, hi]
  have hupd : ∀ T, pick (x T) = Function.update base coord (pick (x T) coord) := by
    intro T
    funext j
    by_cases hj : j = coord
    · subst hj
      simp
    · rw [Function.update_of_ne hj]
      exact hother T j hj
  have hbool : ∀ u w : Bool, u ≠ w → u = !w := by decide
  have hF : ∀ T ∈ S.powerset, test (pick (x T)) = (if T = ∅ then c else !c) := by
    intro T hT
    by_cases hTe : T = ∅
    · subst hTe
      rw [if_pos rfl, hupd ∅, hempty]
      exact hc.symm
    · rw [if_neg hTe]
      obtain ⟨i, hiT, hi⟩ := hnonempty T (Finset.nonempty_iff_ne_empty.mpr hTe)
      have hiS : i ∈ S := (Finset.mem_powerset.mp hT) hiT
      rw [hSdef] at hiS
      have h1 : test (Function.update base coord (bb.succAbove i)) ≠ c := (Finset.mem_filter.mp hiS).2
      rw [hupd T, hi]
      exact hbool _ _ h1
  have hsum1 := sum_one (Fin m) S (by omega) c (fun T => test (pick (x T))) hF
  have hloc : ∀ (T T' : Finset (Fin m)) (q : Fin g × Fin m × Fin r),
      (q.2.1 ∈ T ↔ q.2.1 ∈ T') → x T q = x T' q := by
    rintro T T' ⟨j, i, v⟩ h
    have h' : i ∈ T ↔ i ∈ T' := h
    rw [hx, hx]
    simp only [h']
  have hterm : ∀ T, (if test (pick (x T)) = true then (1 : ZMod 2) else 0)
      = ∑ mon ∈ terms, (if (∀ v ∈ mon, x T v = true) then (1 : ZMod 2) else 0) := by
    intro T
    rw [hrep (x T), ind_card, Finset.natCast_card_filter]
  have hsum0 : ∑ T ∈ S.powerset, (if test (pick (x T)) = true then (1 : ZMod 2) else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun T _ => hterm T), Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro mon hmon
    exact even_sum (fun q : Fin g × Fin m × Fin r => q.2.1) x hloc mon S
      (lt_of_le_of_lt (hterms mon hmon) hbS) _
  rw [hsum0] at hsum1
  exact zero_ne_one hsum1

theorem main_aux (g m r : ℕ) (label : Fin g → Fin m → Fin (m+1) → Fin r → Bool)
    (pick : (Fin g × Fin m × Fin r → Bool) → (Fin g → Fin (m+1)))
    (hpick : ∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j))
    (test : (Fin g → Fin (m+1)) → Bool) (base : Fin g → Fin (m+1)) (coord : Fin g)
    (hpos : 0 < ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card)
    (hlt : ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card < m+1)
    (b : ℕ)
    (hdeg : ∃ terms : Finset (Finset (Fin g × Fin m × Fin r)), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, test (pick input) =
        (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)) :
    max ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card
      (m+1-((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card) ≤ b := by
  obtain ⟨terms, hterms, hrep⟩ := hdeg
  have hcore := core g m r label pick hpick test base coord b terms hterms hrep
  have hsplit : ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card
      + ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      ¬ test (Function.update base coord z) = true)).card = m + 1 := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  obtain ⟨z1, hz1⟩ : ∃ z1 : Fin (m+1), test (Function.update base coord z1) = true := by
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z, (Finset.mem_filter.mp hz).2⟩
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin (m+1), ¬ test (Function.update base coord z0) = true := by
    have hpos2 : 0 < ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      ¬ test (Function.update base coord z) = true)).card := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos2
    exact ⟨z, (Finset.mem_filter.mp hz).2⟩
  have hz0' : test (Function.update base coord z0) = false := by simpa using hz0
  have h2 : ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      ¬ test (Function.update base coord z) = true)).card ≤ b := by
    have h := hcore z1
    rw [hz1] at h
    exact h
  have h1 : ((Finset.univ : Finset (Fin (m+1))).filter (fun z =>
      test (Function.update base coord z) = true)).card ≤ b := by
    have h := hcore z0
    rw [hz0'] at h
    have e1 : ∀ z : Fin (m+1), (test (Function.update base coord z) ≠ false) ↔
        (test (Function.update base coord z) = true) := fun z => by simp
    simp only [e1] at h
    exact h
  exact max_le h1 (by omega)

theorem main : ∀ (g m r : Nat),
  let A := Fin (m+1)
  let V := Fin g × Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → A
  ∀ (label : Fin g → Fin m → A → Fin r → Bool) (pick : W → Y),
    (∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j)) →
    ∀ (test : Y → Bool) (base : Y) (coord : Fin g),
      let ones := ((Finset.univ : Finset A).filter (fun z =>
        test (Function.update base coord z) = true)).card
      0 < ones → ones < m+1 →
      ∀ b : Nat, deg b (fun word => test (pick word)) → max ones (m+1-ones) ≤ b := by
  intro g m r A V W deg Y label pick hpick test base coord ones hpos hlt b hdeg
  exact main_aux g m r label pick hpick test base coord hpos hlt b hdeg

end PEqualNP.Outside.L_lib_606_aux

theorem PEqualNP.Outside.L_lib_606 : (∀ (g m r : Nat),
  let A := Fin (m+1)
  let V := Fin g × Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → A
  ∀ (label : Fin g → Fin m → A → Fin r → Bool) (pick : W → Y),
    (∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j)) →
    ∀ (test : Y → Bool) (base : Y) (coord : Fin g),
      let ones := ((Finset.univ : Finset A).filter (fun z =>
        test (Function.update base coord z) = true)).card
      0 < ones → ones < m+1 →
      ∀ b : Nat, deg b (fun word => test (pick word)) → max ones (m+1-ones) ≤ b) := by
  exact PEqualNP.Outside.L_lib_606_aux.main
