import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_647_aux

abbrev W (t : ℕ) := (Fin t → ZMod 2) × (Fin t → ZMod 2)

def sh {t : ℕ} (a : Fin t) (u v : ZMod 2) : W t := (Pi.single a u, Pi.single a v)

lemma dd {t : ℕ} (d : W t) : d + d = 0 :=
  Prod.ext (funext fun _ => CharTwo.add_self_eq_zero _) (funext fun _ => CharTwo.add_self_eq_zero _)

lemma card_W (t : ℕ) : (Finset.univ : Finset (W t)).card = 4 ^ t := by
  have h : Fintype.card (W t) = 2 ^ t * 2 ^ t := by
    simp [W, Fintype.card_prod, ZMod.card]
  rw [Finset.card_univ, h, ← mul_pow]
  norm_num

lemma z2eq (x y : ZMod 2) (h : x ≠ 0 ↔ y ≠ 0) : x = y := by
  revert x y; decide

lemma shift_card {t : ℕ} (a : Fin t) (T : Finset (W t))
    (hT : ∀ z u v, z ∈ T → z + sh a u v ∈ T) :
    T.card = 4 * (T.filter (fun z => z.1 a = 0 ∧ z.2 a = 0)).card := by
  classical
  have h1 := Finset.card_eq_sum_card_fiberwise (s := T)
    (t := (Finset.univ : Finset (ZMod 2 × ZMod 2)))
    (f := fun z => (z.1 a, z.2 a)) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [h1]
  have h2 : ∀ w ∈ (Finset.univ : Finset (ZMod 2 × ZMod 2)),
      (T.filter (fun z => (z.1 a, z.2 a) = w)).card
        = (T.filter (fun z => z.1 a = 0 ∧ z.2 a = 0)).card := by
    intro w _
    refine Finset.card_bij' (fun z _ => z + sh a w.1 w.2) (fun z _ => z + sh a w.1 w.2) ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hT _ _ _ hz.1, ?_⟩
      have h := hz.2
      subst h
      simp [sh, CharTwo.add_self_eq_zero]
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨hT _ _ _ hz.1, ?_⟩
      simp [sh, hz.2.1, hz.2.2]
    · intro z _
      rw [add_assoc, dd, add_zero]
    · intro z _
      rw [add_assoc, dd, add_zero]
  rw [Finset.sum_congr rfl h2]
  have h4 : (Finset.univ : Finset (ZMod 2 × ZMod 2)).card = 4 := by decide
  rw [Finset.sum_const, h4, smul_eq_mul]

def L {t : ℕ} (c : Fin t → W t → ZMod 2) (S : Finset (Fin t)) : Finset (W t) :=
  Finset.univ.filter (fun z => ∀ j ∈ S, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))

lemma mem_L {t : ℕ} (c : Fin t → W t → ZMod 2) (S : Finset (Fin t)) (z : W t) :
    z ∈ L c S ↔ ∀ j ∈ S, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0) := by
  simp [L]

lemma arith (p q x y t0 w g : ℕ) (hp : 0 < p) (hx : y + 4 * t0 = x) (hw : w = y + t0)
    (hg : 2 * g = q) (hy : y ≤ g) (ihle : 2 * p * x ≤ (p + 1) * q) :
    2 * (p * 4) * w ≤ (p * 4 + 1) * q ∧
    (2 * (p * 4) * w = (p * 4 + 1) * q ↔ (2 * p * x = (p + 1) * q ∧ y = g)) := by
  subst hx hw hg
  have h1 : p * y ≤ p * g := Nat.mul_le_mul_left p hy
  refine ⟨by nlinarith, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h2 : p * g ≤ p * y := by nlinarith
    have h3 : g ≤ y := Nat.le_of_mul_le_mul_left h2 hp
    exact ⟨by nlinarith, le_antisymm hy h3⟩
  · obtain ⟨h2, h3⟩ := h
    subst h3
    nlinarith

lemma KL {t : ℕ} (c : Fin t → W t → ZMod 2) (S : Finset (Fin t)) :
    (∀ j ∈ S, ∀ a, a ≤ j → ∀ z u v, c j (z + sh a u v) = c j z) →
    (∀ j ∈ S, 2 * (Finset.univ.filter (fun z : W t => c j z ≠ 0)).card = 4 ^ t) →
    (∀ j ∈ S, ∀ a z, c j z ≠ 0 → ∃ u v : ZMod 2, (u ≠ 0 ∨ v ≠ 0) ∧ c j (z + sh a u v) ≠ 0) →
    2 * 4 ^ S.card * (L c S).card ≤ (4 ^ S.card + 1) * 4 ^ t ∧
    (2 * 4 ^ S.card * (L c S).card = (4 ^ S.card + 1) * 4 ^ t ↔
      ∀ j ∈ S, ∀ k ∈ S, ∀ z, c j z = c k z) := by
  classical
  refine Finset.induction_on_min S ?_ ?_
  · intro _ _ _
    have hL : L c ∅ = Finset.univ := by simp [L]
    rw [hL, card_W]
    simp
  · intro a S' ha ih h1 h2 h3
    have ha' : a ∉ S' := fun h => lt_irrefl a (ha a h)
    obtain ⟨ihle, iheq⟩ := ih (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h2 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h3 j (Finset.mem_insert_of_mem hj))
    have haS : a ∈ insert a S' := Finset.mem_insert_self _ _
    have hY : ((L c S').filter (fun z => c a z ≠ 0)) ⊆
        Finset.univ.filter (fun z : W t => c a z ≠ 0) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨Finset.mem_univ _, hz.2⟩
    have hYc := Finset.card_le_card hY
    have hxy := Finset.card_filter_add_card_filter_not (s := L c S') (fun z => c a z ≠ 0)
    have hTinv : ∀ z u v, z ∈ (L c S').filter (fun z => ¬ c a z ≠ 0) →
        z + sh a u v ∈ (L c S').filter (fun z => ¬ c a z ≠ 0) := by
      intro z u v hz
      rw [Finset.mem_filter, mem_L] at hz ⊢
      refine ⟨fun j hj => ?_, ?_⟩
      · have hja : a < j := ha j hj
        have e1 : (z + sh a u v).1 j = z.1 j := by simp [sh, hja.ne']
        have e2 : (z + sh a u v).2 j = z.2 j := by simp [sh, hja.ne']
        rw [h1 j (Finset.mem_insert_of_mem hj) a hja.le, e1, e2]
        exact hz.1 j hj
      · rw [h1 a haS a le_rfl]
        exact hz.2
    have hT4 := shift_card a _ hTinv
    have hw : (L c (insert a S')).card = ((L c S').filter (fun z => c a z ≠ 0)).card
        + (((L c S').filter (fun z => ¬ c a z ≠ 0)).filter
            (fun z => z.1 a = 0 ∧ z.2 a = 0)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext z
        simp only [mem_L, Finset.mem_union, Finset.mem_filter, Finset.forall_mem_insert]
        tauto
      · rw [Finset.disjoint_left]
        intro z hz1 hz2
        rw [Finset.mem_filter] at hz1
        rw [Finset.mem_filter, Finset.mem_filter] at hz2
        exact hz2.1.2 hz1.2
    have h2a := h2 a haS
    have hp : 0 < 4 ^ S'.card := by positivity
    obtain ⟨A1, A2⟩ := arith (4 ^ S'.card) (4 ^ t) (L c S').card
      ((L c S').filter (fun z => c a z ≠ 0)).card
      (((L c S').filter (fun z => ¬ c a z ≠ 0)).filter (fun z => z.1 a = 0 ∧ z.2 a = 0)).card
      (L c (insert a S')).card
      (Finset.univ.filter (fun z : W t => c a z ≠ 0)).card
      hp (by omega) hw h2a hYc ihle
    rw [Finset.card_insert_of_notMem ha', pow_succ]
    refine ⟨A1, A2.trans ⟨?_, ?_⟩⟩
    · rintro ⟨e1, e2⟩
      have hS' := iheq.1 e1
      have hYeq := Finset.eq_of_subset_of_card_le hY (le_of_eq e2.symm)
      have hin : ∀ z, c a z ≠ 0 → z ∈ L c S' := by
        intro z hz
        have hz' : z ∈ Finset.univ.filter (fun z : W t => c a z ≠ 0) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
        rw [← hYeq] at hz'
        exact (Finset.mem_filter.1 hz').1
      have hak : ∀ k ∈ S', ∀ z, c a z = c k z := by
        intro k hk
        have hkS : k ∈ insert a S' := Finset.mem_insert_of_mem hk
        have himp : ∀ z, c a z ≠ 0 → c k z ≠ 0 := by
          intro z hz
          by_cases hzk : z.1 k = 0 ∧ z.2 k = 0
          · obtain ⟨u, v, huv, hz'⟩ := h3 a haS k z hz
            have hm := (mem_L c S' _).1 (hin _ hz') k hk
            rw [h1 k hkS k le_rfl] at hm
            rcases hm with hm | hm
            · exact hm
            · exfalso
              have e1 : (z + sh k u v).1 k = u := by simp [sh, hzk.1]
              have e2 : (z + sh k u v).2 k = v := by simp [sh, hzk.2]
              rw [e1, e2] at hm
              rcases huv with h | h
              · exact h hm.1
              · exact h hm.2
          · rcases (mem_L c S' _).1 (hin _ hz) k hk with hm | hm
            · exact hm
            · exact absurd hm hzk
        have hsub : Finset.univ.filter (fun z : W t => c a z ≠ 0) ⊆
            Finset.univ.filter (fun z : W t => c k z ≠ 0) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨Finset.mem_univ _, himp z hz.2⟩
        have h2k := h2 k hkS
        have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
        intro z
        apply z2eq
        have hz := Finset.ext_iff.1 hEq z
        rw [Finset.mem_filter, Finset.mem_filter] at hz
        constructor
        · intro h
          exact (hz.1 ⟨Finset.mem_univ _, h⟩).2
        · intro h
          exact (hz.2 ⟨Finset.mem_univ _, h⟩).2
      intro j hj k hk z
      rcases Finset.mem_insert.1 hj with hj' | hj'
      · rcases Finset.mem_insert.1 hk with hk' | hk'
        · rw [hj', hk']
        · rw [hj']
          exact hak k hk' z
      · rcases Finset.mem_insert.1 hk with hk' | hk'
        · rw [hk']
          exact (hak j hj' z).symm
        · exact hS' j hj' k hk' z
    · intro hall
      refine ⟨iheq.2 (fun j hj k hk => hall j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk)), ?_⟩
      congr 1
      apply Finset.Subset.antisymm hY
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨(mem_L c S' z).2 (fun j hj => Or.inl ?_), hz.2⟩
      rw [hall j (Finset.mem_insert_of_mem hj) a haS z]
      exact hz.2

lemma lin_shift {t : ℕ} (A B : Fin t → Fin t → ZMod 2) (g : ZMod 2) (j a : Fin t) (z : W t)
    (u v : ZMod 2) :
    g + ∑ i ∈ Finset.Ioi j, ((z + sh a u v).1 i * A i j + (z + sh a u v).2 i * B i j)
    = (g + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j))
      + (if j < a then u * A a j + v * B a j else 0) := by
  have e1 : ∑ i ∈ Finset.Ioi j, ((z + sh a u v).1 i * A i j + (z + sh a u v).2 i * B i j)
      = ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
        + ∑ i ∈ Finset.Ioi j, ((Pi.single a u : Fin t → ZMod 2) i * A i j
            + (Pi.single a v : Fin t → ZMod 2) i * B i j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [sh, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  have e2 : ∑ i ∈ Finset.Ioi j, ((Pi.single a u : Fin t → ZMod 2) i * A i j
            + (Pi.single a v : Fin t → ZMod 2) i * B i j)
      = if j < a then u * A a j + v * B a j else 0 := by
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_Ioi]
    split_ifs <;> simp
  rw [e1, e2, add_assoc]

theorem main : ∀ t : ℕ,
  let V := Fin t → ZMod 2
  ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
    let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
      ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
    let c := fun (j : Fin t) (z : V × V) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
    let live := (Finset.univ : Finset (V × V)).filter (fun z =>
      ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
    let lhs := 2 * 4^sources.card * live.card
    let rhs := (4^sources.card + 1) * 4^t
    lhs ≤ rhs ∧
      (lhs = rhs ↔
        (∀ j, j ∉ sources → γ j = 1) ∧
        ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z) := by
  intro t V A B γ sources c live lhs rhs
  classical
  have hcs : ∀ (j a : Fin t) (z : W t) (u v : ZMod 2),
      c j (z + sh a u v) = c j z + (if j < a then u * A a j + v * B a j else 0) :=
    fun j a z u v => lin_shift A B (γ j) j a z u v
  have hsrc : ∀ j, j ∈ sources ↔ ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0) := by
    intro j
    show j ∈ Finset.filter _ _ ↔ _
    rw [Finset.mem_filter]
    simp
  have z2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h1 : ∀ j ∈ sources, ∀ a, a ≤ j → ∀ z u v, c j (z + sh a u v) = c j z := by
    intro j _ a haj z u v
    rw [hcs, if_neg (not_lt.mpr haj), add_zero]
  have h3 : ∀ j ∈ sources, ∀ a z, c j z ≠ 0 →
      ∃ u v : ZMod 2, (u ≠ 0 ∨ v ≠ 0) ∧ c j (z + sh a u v) ≠ 0 := by
    intro j _ a z hz
    by_cases hja : j < a
    · rcases z2 (A a j) with hA | hA
      · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
        rw [hcs, if_pos hja, hA]
        simpa using hz
      · rcases z2 (B a j) with hB | hB
        · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
          rw [hcs, if_pos hja, hB]
          simpa using hz
        · refine ⟨1, 1, Or.inl one_ne_zero, ?_⟩
          rw [hcs, if_pos hja, hA, hB]
          have h11 : (1 : ZMod 2) * 1 + 1 * 1 = 0 := by decide
          rw [h11, add_zero]
          exact hz
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      rw [hcs, if_neg hja, add_zero]
      exact hz
  have h2 : ∀ j ∈ sources, 2 * (Finset.univ.filter (fun z : W t => c j z ≠ 0)).card = 4 ^ t := by
    intro j hj
    obtain ⟨i, hji, hAB⟩ := (hsrc j).1 hj
    obtain ⟨u, v, huv⟩ : ∃ u v : ZMod 2, u * A i j + v * B i j = 1 := by
      rcases z2 (A i j) with hA | hA
      · rcases z2 (B i j) with hB | hB
        · exact absurd hAB (by simp [hA, hB])
        · exact ⟨0, 1, by simp [hB]⟩
      · exact ⟨1, 0, by simp [hA]⟩
    have hflip : ∀ z : W t, c j (z + sh i u v) = c j z + 1 := by
      intro z
      rw [hcs, if_pos hji, huv]
    have hcard : (Finset.univ.filter (fun z : W t => c j z ≠ 0)).card
        = (Finset.univ.filter (fun z : W t => ¬ c j z ≠ 0)).card := by
      refine Finset.card_bij' (fun z _ => z + sh i u v) (fun z _ => z + sh i u v) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [hflip]
        rcases z2 (c j z) with h | h
        · exact absurd h hz
        · rw [h]
          decide
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [hflip]
        rw [not_not] at hz
        rw [hz]
        decide
      · intro z _
        rw [add_assoc, dd, add_zero]
      · intro z _
        rw [add_assoc, dd, add_zero]
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (W t)))
      (fun z => c j z ≠ 0)
    rw [card_W] at htot
    omega
  obtain ⟨hle, heq⟩ := KL c sources h1 h2 h3
  have hsub : live ⊆ L c sources := by
    intro z hz
    rw [mem_L]
    have hz' := (Finset.mem_filter.1 hz).2
    exact fun j _ => hz' j
  have hcl : live.card ≤ (L c sources).card := Finset.card_le_card hsub
  have hnon : ∀ j, j ∉ sources → ∀ z : W t, c j z = γ j := by
    intro j hj z
    have hz : ∀ i ∈ Finset.Ioi j, z.1 i * A i j + z.2 i * B i j = 0 := by
      intro i hi
      have hji := Finset.mem_Ioi.1 hi
      have hA : A i j = 0 := by
        by_contra h
        exact hj ((hsrc j).2 ⟨i, hji, Or.inl h⟩)
      have hB : B i j = 0 := by
        by_contra h
        exact hj ((hsrc j).2 ⟨i, hji, Or.inr h⟩)
      rw [hA, hB]
      simp
    show γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j) = γ j
    rw [Finset.sum_eq_zero hz, add_zero]
  show 2 * 4 ^ sources.card * live.card ≤ (4 ^ sources.card + 1) * 4 ^ t ∧
    (2 * 4 ^ sources.card * live.card = (4 ^ sources.card + 1) * 4 ^ t ↔ _)
  refine ⟨le_trans (Nat.mul_le_mul_left _ hcl) hle, ⟨?_, ?_⟩⟩
  · intro h
    have hcard : live.card = (L c sources).card := by
      have hpos : 0 < 2 * 4 ^ sources.card := by positivity
      have h' : 2 * 4 ^ sources.card * (L c sources).card ≤ 2 * 4 ^ sources.card * live.card := by
        rw [h]
        exact hle
      exact le_antisymm hcl (Nat.le_of_mul_le_mul_left h' hpos)
    have hLeq : live = L c sources := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    refine ⟨?_, heq.1 (by rw [← hcard]; exact h)⟩
    intro j hj
    by_contra hg
    have hg0 : γ j = 0 := by
      rcases z2 (γ j) with h | h
      · exact h
      · exact absurd h hg
    have hzL : sh j 1 0 ∈ L c sources := by
      rw [mem_L]
      intro k hk
      right
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      simp [sh, hkj]
    rw [← hLeq] at hzL
    have hbad := (Finset.mem_filter.1 hzL).2 j
    rw [hnon j hj, hg0] at hbad
    simp [sh] at hbad
  · rintro ⟨hγ, hc⟩
    have hLeq : live = L c sources := by
      apply Finset.Subset.antisymm hsub
      intro z hz
      rw [mem_L] at hz
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ?_⟩
      by_cases hj : j ∈ sources
      · exact hz j hj
      · left
        rw [hnon j hj, hγ j hj]
        exact one_ne_zero
    rw [hLeq]
    exact heq.2 hc

end PEqualNP.Outside.L_lib_647_aux

theorem PEqualNP.Outside.L_lib_647 : (∀ t : ℕ,
  let V := Fin t → ZMod 2
  ∀ (A B : Fin t → Fin t → ZMod 2) (γ : V),
    let sources := (Finset.univ : Finset (Fin t)).filter (fun j =>
      ∃ i, j < i ∧ (A i j ≠ 0 ∨ B i j ≠ 0))
    let c := fun (j : Fin t) (z : V × V) =>
      γ j + ∑ i ∈ Finset.Ioi j, (z.1 i * A i j + z.2 i * B i j)
    let live := (Finset.univ : Finset (V × V)).filter (fun z =>
      ∀ j, c j z ≠ 0 ∨ (z.1 j = 0 ∧ z.2 j = 0))
    let lhs := 2 * 4^sources.card * live.card
    let rhs := (4^sources.card + 1) * 4^t
    lhs ≤ rhs ∧
      (lhs = rhs ↔
        (∀ j, j ∉ sources → γ j = 1) ∧
        ∀ j ∈ sources, ∀ k ∈ sources, ∀ z, c j z = c k z)) := by
  exact PEqualNP.Outside.L_lib_647_aux.main
