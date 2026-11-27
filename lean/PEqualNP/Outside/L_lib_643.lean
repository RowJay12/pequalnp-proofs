import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_643_aux

theorem chooseA {α : Type} [DecidableEq α] (h : ℕ) (hh : 2 ≤ h) (p : Finset (Finset α))
    (hp : ∀ s ∈ p, 2 ≤ s.card ∧ s.card - 1 < h) (hg : p.sum (fun s => s.card - 1) = h) :
    ∃ A ⊆ p, 0 < A.sum (fun s => s.card - 1) ∧ A.sum (fun s => s.card - 1) < h ∧
      (2 * h < 3 * A.sum (fun s => s.card - 1) → A.card = 1) ∧
      (2 * h < 3 * (h - A.sum (fun s => s.card - 1)) → (p \ A).card = 1) := by
  by_cases hbig : ∃ s ∈ p, h ≤ 3 * (s.card - 1)
  · obtain ⟨s, hs, hs3⟩ := hbig
    obtain ⟨h2, hlt⟩ := hp s hs
    refine ⟨{s}, Finset.singleton_subset_iff.mpr hs, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.sum_singleton]
      omega
    · simp only [Finset.sum_singleton]
      exact hlt
    · intro _
      exact Finset.card_singleton s
    · simp only [Finset.sum_singleton]
      intro hc
      omega
  · push_neg at hbig
    have key : ∀ q : Finset (Finset α), q ⊆ p → h ≤ 3 * q.sum (fun s => s.card - 1) →
        ∃ A ⊆ q, h ≤ 3 * A.sum (fun s => s.card - 1) ∧
          3 * A.sum (fun s => s.card - 1) ≤ 2 * h := by
      intro q
      induction q using Finset.induction_on with
      | empty =>
        intro _ h0
        rw [Finset.sum_empty] at h0
        omega
      | insert s q' hs ih =>
        intro hsub hq
        rw [Finset.sum_insert hs] at hq
        by_cases hq' : h ≤ 3 * q'.sum (fun s => s.card - 1)
        · obtain ⟨A, hA, h1, h2⟩ := ih ((Finset.subset_insert _ _).trans hsub) hq'
          exact ⟨A, hA.trans (Finset.subset_insert _ _), h1, h2⟩
        · refine ⟨insert s q', subset_rfl, ?_, ?_⟩
          · rw [Finset.sum_insert hs]
            exact hq
          · rw [Finset.sum_insert hs]
            have h3 := hbig s (hsub (Finset.mem_insert_self _ _))
            omega
    obtain ⟨A, hA, h1, h2⟩ := key p subset_rfl (by rw [hg]; omega)
    refine ⟨A, hA, by omega, by omega, fun hc => by omega, fun hc => by omega⟩

theorem goodCount {v : ℕ} (h : ℕ) (p A : Finset (Finset (Fin v))) (hA : A ⊆ p)
    (hp : ∀ s ∈ p, 2 ≤ s.card ∧ s.card - 1 < h)
    (hd : ∀ s ∈ p, ∀ u ∈ p, s ≠ u → Disjoint s u)
    (hg : p.sum (fun s => s.card - 1) = h) :
    2 ^ v ≤ ((Finset.univ : Finset (Finset (Fin v))).filter (fun red =>
      A.biUnion id ⊆ red ∧ Disjoint ((p \ A).biUnion id) red)).card * 4 ^ h := by
  have hUW : Disjoint (A.biUnion id) ((p \ A).biUnion id) := by
    rw [Finset.disjoint_biUnion_left]
    intro s hs
    rw [Finset.disjoint_biUnion_right]
    intro u hu
    exact hd s (hA hs) u (Finset.mem_sdiff.mp hu).1
      (fun e => (Finset.mem_sdiff.mp hu).2 (e ▸ hs))
  have hsub : A.biUnion id ⊆ ((p \ A).biUnion id)ᶜ :=
    Finset.subset_compl_iff_disjoint_right.mpr hUW
  have hset : ((Finset.univ : Finset (Finset (Fin v))).filter (fun red =>
      A.biUnion id ⊆ red ∧ Disjoint ((p \ A).biUnion id) red))
      = Finset.Icc (A.biUnion id) ((p \ A).biUnion id)ᶜ := by
    ext red
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Finset.subset_compl_iff_disjoint_left.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Finset.subset_compl_iff_disjoint_left.mp h2⟩
  have hU : (A.biUnion id).card ≤ A.sum (fun s => s.card) := Finset.card_biUnion_le
  have hW : ((p \ A).biUnion id).card ≤ (p \ A).sum (fun s => s.card) := Finset.card_biUnion_le
  have hsum : (p \ A).sum (fun s => s.card) + A.sum (fun s => s.card) = p.sum (fun s => s.card) :=
    Finset.sum_sdiff hA
  have hpc : p.sum (fun s => s.card) = p.sum (fun s => s.card - 1) + p.card := by
    have e : p.sum (fun s => s.card) = p.sum (fun s => (s.card - 1) + 1) :=
      Finset.sum_congr rfl (fun s hs => by have := (hp s hs).1; omega)
    rw [e, Finset.sum_add_distrib]
    simp
  have hcard : p.card ≤ p.sum (fun s => s.card - 1) := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun s hs => by have := (hp s hs).1; omega)
  rw [hset, Finset.card_Icc_finset hsub, Finset.card_compl, Fintype.card_fin]
  have h4 : (4 : ℕ) ^ h = 2 ^ (2 * h) := by
    rw [pow_mul]
    norm_num
  rw [h4, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem filterEq {v : ℕ} (p A : Finset (Finset (Fin v))) (hA : A ⊆ p)
    (hp : ∀ s ∈ p, 2 ≤ s.card) (red : Finset (Fin v))
    (h1 : A.biUnion id ⊆ red) (h2 : Disjoint ((p \ A).biUnion id) red) :
    p.filter (fun s => s ⊆ red) = A ∧ p.filter (fun u => Disjoint u red) = p \ A := by
  have hne : ∀ s ∈ p, s.Nonempty := fun s hs =>
    Finset.card_pos.mp (by have := hp s hs; omega)
  constructor
  · ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hsr⟩
      by_contra hsA
      have hsW : s ⊆ (p \ A).biUnion id :=
        Finset.subset_biUnion_of_mem id (Finset.mem_sdiff.mpr ⟨hs, hsA⟩)
      obtain ⟨x, hx⟩ := hne s hs
      exact Finset.disjoint_left.mp h2 (hsW hx) (hsr hx)
    · intro hs
      have hsU : s ⊆ A.biUnion id := Finset.subset_biUnion_of_mem id hs
      exact ⟨hA hs, hsU.trans h1⟩
  · ext s
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hs, hsr⟩
      refine ⟨hs, fun hsA => ?_⟩
      have hsU : s ⊆ A.biUnion id := Finset.subset_biUnion_of_mem id hsA
      obtain ⟨x, hx⟩ := hne s hs
      exact Finset.disjoint_left.mp hsr hx (h1 (hsU hx))
    · rintro ⟨hs, hsA⟩
      have hsW : s ⊆ (p \ A).biUnion id :=
        Finset.subset_biUnion_of_mem id (Finset.mem_sdiff.mpr ⟨hs, hsA⟩)
      exact ⟨hs, Finset.disjoint_of_subset_left hsW h2⟩

theorem core (v n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h) (fam : Fin n → Finset (Finset (Fin v)))
    (hfam : ∀ i, (∀ s ∈ fam i, 2 ≤ s.card ∧ s.card - 1 < h) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧
      (fam i).sum (fun s => s.card - 1) = h) :
    ∃ (red : Finset (Fin v)) (redGain : ℕ) (I : Finset (Fin n)),
      0 < redGain ∧ redGain < h ∧ n ≤ I.card * h * 4 ^ h ∧
      ∀ i ∈ I,
        fam i = (fam i).filter (fun s => s ⊆ red) ∪ (fam i).filter (fun u => Disjoint u red) ∧
        ((fam i).filter (fun s => s ⊆ red)).sum (fun s => s.card - 1) = redGain ∧
        ((fam i).filter (fun u => Disjoint u red)).sum (fun s => s.card - 1) = h - redGain ∧
        (2 * h < 3 * redGain → ((fam i).filter (fun s => s ⊆ red)).card = 1) ∧
        (2 * h < 3 * (h - redGain) → ((fam i).filter (fun u => Disjoint u red)).card = 1) := by
  have hA := fun i => chooseA h hh (fam i) (hfam i).1 (hfam i).2.2
  choose A hAsub hApos hAlt hAc1 hAc2 using hA
  have hgood : ∀ i, 2 ^ v ≤ ((Finset.univ : Finset (Finset (Fin v))).filter (fun red =>
      (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card * 4 ^ h :=
    fun i => goodCount h (fam i) (A i) (hAsub i) (hfam i).1 (hfam i).2.1 (hfam i).2.2
  have hex : ∃ red : Finset (Fin v), n ≤ ((Finset.univ : Finset (Fin n)).filter (fun i =>
      (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card * 4 ^ h := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ red : Finset (Fin v), ((Finset.univ : Finset (Fin n)).filter (fun i =>
        (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card * 4 ^ h
        < ∑ _red : Finset (Fin v), n :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun red _ => hcon red)
    have h2 : ∑ _red : Finset (Fin v), n = 2 ^ v * n := by simp
    have h3 : ∑ red : Finset (Fin v), ((Finset.univ : Finset (Fin n)).filter (fun i =>
        (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card
        = ∑ i : Fin n, ((Finset.univ : Finset (Finset (Fin v))).filter (fun red =>
          (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have h4 : n * 2 ^ v ≤ (∑ i : Fin n, ((Finset.univ : Finset (Finset (Fin v))).filter (fun red =>
        (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red)).card) * 4 ^ h := by
      rw [Finset.sum_mul]
      calc n * 2 ^ v = ∑ _i : Fin n, 2 ^ v := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hgood i)
    rw [← Finset.sum_mul, h3, h2] at h1
    have h5 := lt_of_le_of_lt h4 h1
    rw [Nat.mul_comm] at h5
    exact lt_irrefl _ h5
  obtain ⟨red, hred⟩ := hex
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin n), J = (Finset.univ : Finset (Fin n)).filter (fun i =>
      (A i).biUnion id ⊆ red ∧ Disjoint ((fam i \ A i).biUnion id) red) := ⟨_, rfl⟩
  rw [← hJ] at hred
  have hJne : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty, Nat.zero_mul] at hred
    omega
  obtain ⟨g, hg⟩ : ∃ g : Fin n → ℕ, ∀ i, g i = (A i).sum (fun s => s.card - 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image J
    (fun i => (J.filter (fun j => g j = g i)).card) hJne
  refine ⟨red, g i0, J.filter (fun j => g j = g i0), ?_, ?_, ?_, ?_⟩
  · rw [hg]
    exact hApos i0
  · rw [hg]
    exact hAlt i0
  · have hJc : J.card ≤ h * (J.filter (fun j => g j = g i0)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.range h)
        (fun i _ => by rw [hg]; exact Finset.mem_range.mpr (hAlt i))]
      calc ∑ k ∈ Finset.range h, (J.filter (fun i => g i = k)).card
          ≤ ∑ _k ∈ Finset.range h, (J.filter (fun j => g j = g i0)).card := by
            apply Finset.sum_le_sum
            intro k _
            by_cases hk : (J.filter (fun i => g i = k)).Nonempty
            · obtain ⟨i1, hi1⟩ := hk
              obtain ⟨hi1J, hi1k⟩ := Finset.mem_filter.mp hi1
              have h6 : (J.filter (fun j => g j = g i1)).card
                  ≤ (J.filter (fun j => g j = g i0)).card := hmax i1 hi1J
              rw [hi1k] at h6
              exact h6
            · rw [Finset.not_nonempty_iff_eq_empty.mp hk, Finset.card_empty]
              exact Nat.zero_le _
        _ = h * (J.filter (fun j => g j = g i0)).card := by simp
    calc n ≤ J.card * 4 ^ h := hred
      _ ≤ (h * (J.filter (fun j => g j = g i0)).card) * 4 ^ h := Nat.mul_le_mul_right _ hJc
      _ = (J.filter (fun j => g j = g i0)).card * h * 4 ^ h := by ring
  · intro i hi
    obtain ⟨hiJ, hig⟩ := Finset.mem_filter.mp hi
    rw [hJ] at hiJ
    obtain ⟨hr1, hr2⟩ := (Finset.mem_filter.mp hiJ).2
    obtain ⟨e1, e2⟩ := filterEq (fam i) (A i) (hAsub i) (fun s hs => ((hfam i).1 s hs).1)
      red hr1 hr2
    rw [e1, e2]
    have hsum : (fam i \ A i).sum (fun s => s.card - 1) + (A i).sum (fun s => s.card - 1) = h := by
      rw [Finset.sum_sdiff (hAsub i)]
      exact (hfam i).2.2
    rw [hg i] at hig
    have hc1 := hAc1 i
    have hc2 := hAc2 i
    refine ⟨(Finset.union_sdiff_of_subset (hAsub i)).symm, hig, by omega, ?_, ?_⟩
    · intro hc
      exact hc1 (by omega)
    · intro hc
      exact hc2 (by omega)

theorem main : ∀ (v n h : Nat), 0 < n → 2 ≤ h →
  let V := Fin v
  let P := Finset (Finset V)
  let gain := fun (p : P) => p.sum (fun s => s.card-1)
  ∀ fam : Fin n → P,
    (∀ i, (∀ s ∈ fam i, 2 ≤ s.card ∧ s.card-1 < h) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧ gain (fam i) = h) →
    ∃ (red : Finset V) (redGain : Nat) (I : Finset (Fin n)),
      0 < redGain ∧ redGain < h ∧ n ≤ I.card * h * 4^h ∧
      ∀ i ∈ I,
        let left := (fam i).filter (fun s => s ⊆ red)
        let right := (fam i).filter (fun u => Disjoint u red)
        fam i = left ∪ right ∧ gain left = redGain ∧ gain right = h-redGain ∧
        (2*h < 3*redGain → left.card = 1) ∧
        (2*h < 3*(h-redGain) → right.card = 1) := by
  intro v n h hn hh V P gain fam hfam
  exact core v n h hn hh fam hfam

end PEqualNP.Outside.L_lib_643_aux

theorem PEqualNP.Outside.L_lib_643 : (∀ (v n h : Nat), 0 < n → 2 ≤ h →
  let V := Fin v
  let P := Finset (Finset V)
  let gain := fun (p : P) => p.sum (fun s => s.card-1)
  ∀ fam : Fin n → P,
    (∀ i, (∀ s ∈ fam i, 2 ≤ s.card ∧ s.card-1 < h) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧ gain (fam i) = h) →
    ∃ (red : Finset V) (redGain : Nat) (I : Finset (Fin n)),
      0 < redGain ∧ redGain < h ∧ n ≤ I.card * h * 4^h ∧
      ∀ i ∈ I,
        let left := (fam i).filter (fun s => s ⊆ red)
        let right := (fam i).filter (fun u => Disjoint u red)
        fam i = left ∪ right ∧ gain left = redGain ∧ gain right = h-redGain ∧
        (2*h < 3*redGain → left.card = 1) ∧
        (2*h < 3*(h-redGain) → right.card = 1)) := by
  exact PEqualNP.Outside.L_lib_643_aux.main
