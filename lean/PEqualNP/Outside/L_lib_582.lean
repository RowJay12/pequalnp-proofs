import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_582_aux

theorem ind_card (k : ℕ) : (if (k % 2 == 1) = true then (1 : ZMod 2) else 0) = (k : ZMod 2) := by
  have h2 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod k 2).symm
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [h2, h]; simp
  · rw [h2, h]; simp

theorem bool_of_ind (b1 b2 : Bool)
    (h : (if b1 = true then (1 : ZMod 2) else 0) = (if b2 = true then (1 : ZMod 2) else 0)) :
    b1 = b2 := by
  revert h
  cases b1 <;> cases b2 <;> decide

theorem ind_dec (k : ℕ) :
    (if decide (k % 2 = 1) = true then (1 : ZMod 2) else 0) = (k : ZMod 2) := by
  have h2 : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod k 2).symm
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [h2, h]; simp
  · rw [h2, h]; simp

theorem mobius_deg (m r : ℕ) (f : (Fin m × Fin r → Bool) → Bool) (b : ℕ)
    (hf : ∀ S : Finset (Fin m × Fin r), b < S.card →
      ∑ T ∈ S.powerset, (if f (fun q => decide (q ∈ T)) = true then (1 : ZMod 2) else 0) = 0) :
    ∃ terms : Finset (Finset (Fin m × Fin r)), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ input,
      f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Finset (Fin m × Fin r) → ZMod 2, ∀ S, μ S =
      ∑ T ∈ S.powerset, (if f (fun q => decide (q ∈ T)) = true then (1 : ZMod 2) else 0) :=
    ⟨_, fun _ => rfl⟩
  refine ⟨Finset.univ.filter (fun S => μ S = 1), ?_, ?_⟩
  · intro mon hmon
    rw [Finset.mem_filter] at hmon
    by_contra hlt
    rw [not_le] at hlt
    have h0 := hf mon hlt
    rw [← hμ, hmon.2] at h0
    exact one_ne_zero h0
  · intro input
    obtain ⟨X, hX⟩ : ∃ X : Finset (Fin m × Fin r),
        X = Finset.univ.filter (fun q => input q = true) := ⟨_, rfl⟩
    have hin : input = fun q => decide (q ∈ X) := by
      funext q
      rw [hX]
      simp
    have hfilt : ∀ S : Finset (Fin m × Fin r),
        (S ∈ (Finset.univ.filter (fun S => μ S = 1)).filter
          (fun mon => ∀ j ∈ mon, input j = true)) ↔
        S ∈ X.powerset.filter (fun S => μ S = 1) := by
      intro S
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset, hX]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩
        exact ⟨fun q hq => Finset.mem_filter.mpr ⟨Finset.mem_univ q, h2 q hq⟩, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨Finset.mem_univ S, h2⟩, fun q hq => (Finset.mem_filter.mp (h1 hq)).2⟩
    apply bool_of_ind
    rw [ind_card, Finset.ext hfilt, Finset.natCast_card_filter]
    have hz : ∀ c : ZMod 2, (if c = 1 then (1 : ZMod 2) else 0) = c := by decide
    simp only [hz, hμ]
    have hcomm : ∀ (S T : Finset (Fin m × Fin r)),
        S ∈ X.powerset ∧ T ∈ S.powerset ↔
        S ∈ X.powerset.filter (fun S => T ⊆ S) ∧ T ∈ X.powerset := by
      intro S T
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2⟩, h2.trans h1⟩
      · rintro ⟨⟨h1, h2⟩, -⟩
        exact ⟨h1, h2⟩
    rw [Finset.sum_comm' hcomm, Finset.sum_eq_single X]
    · have hsing : X.powerset.filter (fun S => X ⊆ S) = {X} := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          exact Finset.Subset.antisymm h1 h2
        · rintro rfl
          exact ⟨subset_rfl, subset_rfl⟩
      rw [hsing, Finset.sum_singleton, hin]
    · intro T hT hne
      rw [Finset.sum_const, ← Finset.Icc_eq_filter_powerset,
        Finset.card_Icc_finset (Finset.mem_powerset.mp hT)]
      have hlt : T.card < X.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hT, hne⟩)
      obtain ⟨c, hc⟩ : ∃ c, X.card - T.card = c + 1 := ⟨X.card - T.card - 1, by omega⟩
      have h2 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
      rw [hc, nsmul_eq_mul, Nat.cast_pow, h2, zero_pow (Nat.succ_ne_zero c), zero_mul]
    · intro hX'
      exact absurd (Finset.mem_powerset.mpr (subset_refl X)) hX'

theorem dep_even {V : Type} [DecidableEq V] (P : (V → Bool) → Prop) [DecidablePred P]
    (D S : Finset V) (hDS : D.card < S.card)
    (hdep : ∀ x x' : V → Bool, (∀ q ∈ D, x q = x' q) → (P x ↔ P x')) :
    ∑ T ∈ S.powerset, (if P (fun q => decide (q ∈ T)) then (1 : ZMod 2) else 0) = 0 := by
  have hex : ∃ p ∈ S, p ∉ D := by
    by_contra hcon
    have hsub : S ⊆ D := by
      intro p hp
      by_contra hpn
      exact hcon ⟨p, hp, hpn⟩
    have h1 := Finset.card_le_card hsub
    omega
  obtain ⟨p, hpS, hp⟩ := hex
  have hsame : ∀ T : Finset V,
      P (fun q => decide (q ∈ (if p ∈ T then T.erase p else insert p T))) ↔
      P (fun q => decide (q ∈ T)) := by
    intro T
    apply hdep
    intro q hq
    have hqp : q ≠ p := fun h => hp (by rw [← h]; exact hq)
    by_cases hpT : p ∈ T
    · simp [hpT, Finset.mem_erase, hqp]
    · simp [hpT, Finset.mem_insert, hqp]
  refine Finset.sum_involution (fun T _ => if p ∈ T then T.erase p else insert p T) ?_ ?_ ?_ ?_
  · intro T hT
    by_cases hc : P (fun q => decide (q ∈ T))
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

theorem lucas_pow (e : ℕ) : ∀ N : ℕ, 2^e ≤ N → N < 2^(e+1) → Nat.choose N (2^e) % 2 = 1 := by
  induction e with
  | zero =>
    intro N h1 h2
    have hN : N = 1 := by
      norm_num at h1 h2
      omega
    subst hN
    norm_num
  | succ e ih =>
    intro N h1 h2
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := 2^(e+1)) (p := 2)
    have h3 : 2^(e+1) % 2 = 0 := by
      rw [pow_succ]
      simp
    have h4 : 2^(e+1) / 2 = 2^e := by
      rw [pow_succ]
      simp
    rw [h3, h4, Nat.choose_zero_right, one_mul] at hmod
    have h5 := ih (N / 2) (by rw [pow_succ] at h1; omega) (by rw [pow_succ] at h2; omega)
    unfold Nat.ModEq at hmod
    rw [hmod, h5]

theorem trace_lt (step : ℕ → ℕ → Bool) (n : ℕ) :
    (List.range n).foldl (fun trace tick => trace + ((step tick trace).toNat <<< tick)) 0 < 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h1 := Bool.toNat_le (step n ((List.range n).foldl
      (fun trace tick => trace + ((step tick trace).toNat <<< tick)) 0))
    have h2 := Nat.mul_le_mul_right (2^n) h1
    rw [Nat.shiftLeft_eq, pow_succ]
    omega

theorem run_fix (d : ℕ) (step : ℕ → ℕ → Bool)
    (hloc : ∀ p h h', (∀ q, q < p → h.testBit q = h'.testBit q) → step p h = step p h') :
    ∀ p, p < d →
      ((List.range d).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0).testBit p
      = step p ((List.range d).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0) := by
  obtain ⟨tr, htr⟩ : ∃ tr : ℕ → ℕ, ∀ k, tr k =
      (List.range k).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0 := ⟨_, fun _ => rfl⟩
  have hs : ∀ k, tr (k+1) = 2^k * (step k (tr k)).toNat + tr k := by
    intro k
    rw [htr (k+1), List.range_succ, List.foldl_append, ← htr k]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.shiftLeft_eq, mul_comm, add_comm]
  have hlt : ∀ k, tr k < 2^k := by
    intro k
    rw [htr k]
    exact trace_lt step k
  have hlow : ∀ k p, p < k → (tr (k+1)).testBit p = (tr k).testBit p := by
    intro k p hp
    rw [hs, Nat.testBit_two_pow_mul_add _ (hlt k), if_pos hp]
  have htop : ∀ k, (tr (k+1)).testBit k = step k (tr k) := by
    intro k
    rw [hs, Nat.testBit_two_pow_mul_add _ (hlt k), if_neg (lt_irrefl k), Nat.sub_self,
      Nat.testBit_bool_toNat]
    simp
  have hstab : ∀ n k p, p < k → (tr (k + n)).testBit p = (tr k).testBit p := by
    intro n
    induction n with
    | zero =>
      intro k p _
      rfl
    | succ n ih =>
      intro k p hp
      rw [← add_assoc, hlow (k+n) p (by omega), ih k p hp]
  intro p hp
  rw [← htr d]
  have hd : d = (p + 1) + (d - (p+1)) := by omega
  have h1 := hstab (d - (p+1)) (p+1) p (by omega)
  rw [← hd] at h1
  have hd2 : d = p + (d - p) := by omega
  have h2 : ∀ q, q < p → (tr p).testBit q = (tr d).testBit q := by
    intro q hq
    have h3 := hstab (d - p) p q hq
    rw [← hd2] at h3
    exact h3.symm
  rw [h1, htop p]
  exact hloc p _ _ h2

def cnt1 (m r u h : ℕ) (x : Fin m × Fin r → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => ∀ (s : Fin r),
    ((s.val < u → x (i,s) = h.testBit s.val) ∧ (s.val = u → x (i,s) = false)))).card

theorem ask_deg (m r u h : ℕ) :
    ∃ terms : Finset (Finset (Fin m × Fin r)),
      (∀ mon ∈ terms, mon.card ≤ (u + 1) * 2^(r-1-u)) ∧ ∀ input,
      decide (Nat.choose (cnt1 m r u h input) (2^(r-1-u)) % 2 = 1) =
        (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1) := by
  apply mobius_deg m r
    (fun input => decide (Nat.choose (cnt1 m r u h input) (2^(r-1-u)) % 2 = 1))
  intro S hS
  have key : ∀ x : Fin m × Fin r → Bool,
      (if decide (Nat.choose (cnt1 m r u h x) (2^(r-1-u)) % 2 = 1) = true
        then (1 : ZMod 2) else 0)
      = ∑ B ∈ Finset.powersetCard (2^(r-1-u)) (Finset.univ : Finset (Fin m)),
          (if (∀ i ∈ B, ∀ (s : Fin r),
            ((s.val < u → x (i,s) = h.testBit s.val) ∧ (s.val = u → x (i,s) = false)))
            then (1 : ZMod 2) else 0) := by
    intro x
    rw [ind_dec, cnt1, ← Finset.card_powersetCard, ← Finset.natCast_card_filter]
    congr 2
    ext B
    rw [Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Finset.subset_univ B, h2⟩, fun i hi => (Finset.mem_filter.mp (h1 hi)).2⟩
    · rintro ⟨⟨-, h2⟩, h1⟩
      exact ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1 i hi⟩, h2⟩
  simp only [key]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro B hB
  have hBcard : B.card = 2^(r-1-u) := (Finset.mem_powersetCard.mp hB).2
  refine dep_even (fun x : Fin m × Fin r → Bool =>
      ∀ i ∈ B, ∀ (s : Fin r),
            ((s.val < u → x (i,s) = h.testBit s.val) ∧ (s.val = u → x (i,s) = false)))
    (Finset.univ.filter (fun q : Fin m × Fin r => q.1 ∈ B ∧ q.2.val ≤ u)) S ?_ ?_
  · refine lt_of_le_of_lt ?_ hS
    have hinj : Set.InjOn (fun q : Fin m × Fin r => (q.1, q.2.val))
        (↑(Finset.univ.filter (fun q : Fin m × Fin r => q.1 ∈ B ∧ q.2.val ≤ u)) :
          Set (Fin m × Fin r)) := by
      rintro ⟨q1, q2⟩ hq ⟨r1, r2⟩ hr heq
      simp only [Prod.mk.injEq] at heq
      have e2 : q2 = r2 := Fin.ext heq.2
      rw [heq.1, e2]
    rw [← Finset.card_image_of_injOn hinj]
    have hsub : (Finset.univ.filter (fun q : Fin m × Fin r => q.1 ∈ B ∧ q.2.val ≤ u)).image
          (fun q : Fin m × Fin r => (q.1, q.2.val))
        ⊆ B ×ˢ Finset.range (u + 1) := by
      rw [Finset.image_subset_iff]
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      rw [Finset.mem_product, Finset.mem_range]
      exact ⟨hq'.1, by omega⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_range, hBcard, mul_comm] at hle
    exact hle
  · intro x x' hxx
    have hq : ∀ (i : Fin m), i ∈ B → ∀ (s : Fin r), s.val ≤ u → x (i,s) = x' (i,s) := by
      intro i hi s hs
      exact hxx (i,s) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hs⟩)
    constructor
    · intro hP i hi s
      have h1 := hP i hi s
      exact ⟨fun hs => by rw [← hq i hi s (le_of_lt hs)]; exact h1.1 hs,
             fun hs => by rw [← hq i hi s (le_of_eq hs)]; exact h1.2 hs⟩
    · intro hP i hi s
      have h1 := hP i hi s
      exact ⟨fun hs => by rw [hq i hi s (le_of_lt hs)]; exact h1.1 hs,
             fun hs => by rw [hq i hi s (le_of_eq hs)]; exact h1.2 hs⟩

theorem cnt1_congr (m r u : ℕ) (h h' : ℕ) (x : Fin m × Fin r → Bool)
    (hbits : ∀ q, q < u → h.testBit q = h'.testBit q) :
    cnt1 m r u h x = cnt1 m r u h' x := by
  rw [cnt1, cnt1]
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hM s
    refine ⟨fun hs => ?_, (hM s).2⟩
    rw [← hbits _ hs]
    exact (hM s).1 hs
  · intro hM s
    refine ⟨fun hs => ?_, (hM s).2⟩
    rw [hbits _ hs]
    exact (hM s).1 hs

theorem proto (m r : ℕ) (hm : m < 2^r) (x : Fin m × Fin r → Bool) (l : ℕ) (hl : l ≤ r) (H : ℕ)
    (hfix : ∀ p, p < l → H.testBit p =
      decide (Nat.choose (cnt1 m r p H x) (2^(r-1-p)) % 2 = 1)) :
    (Finset.univ.filter (fun i : Fin m =>
      ∀ j : Fin r, j.val < l → x (i,j) = H.testBit j.val)).card < 2^(r-l) := by
  have hcnt : ∀ t, t ≤ l → (Finset.univ.filter (fun i : Fin m =>
      ∀ s : Fin r, s.val < t → x (i,s) = H.testBit s.val)).card < 2^(r-t) := by
    intro t
    induction t with
    | zero =>
      intro _
      have h1 := Finset.card_le_univ (Finset.univ.filter (fun i : Fin m =>
        ∀ s : Fin r, s.val < 0 → x (i,s) = H.testBit s.val))
      rw [Fintype.card_fin] at h1
      rw [Nat.sub_zero]
      omega
    | succ t ih =>
      intro ht
      have ht' : t < r := by omega
      have ih' := ih (by omega)
      have hbit := hfix t (by omega)
      obtain ⟨Pf, hPf⟩ : ∃ Pf : Finset (Fin m), Pf = Finset.univ.filter
        (fun i : Fin m => ∀ s : Fin r, s.val < t → x (i,s) = H.testBit s.val) := ⟨_, rfl⟩
      rw [← hPf] at ih'
      have hsplit : (Pf.filter (fun i => x (i,⟨t,ht'⟩) = false)).card +
          (Pf.filter (fun i => ¬ x (i,⟨t,ht'⟩) = false)).card = Pf.card :=
        Finset.card_filter_add_card_filter_not _
      have hN0 : cnt1 m r t H x = (Pf.filter (fun i => x (i,⟨t,ht'⟩) = false)).card := by
        rw [cnt1, hPf, Finset.filter_filter]
        congr 1
        apply Finset.filter_congr
        intro i _
        constructor
        · intro hM
          exact ⟨fun s hs => (hM s).1 hs, (hM ⟨t, ht'⟩).2 rfl⟩
        · rintro ⟨h1, h2⟩ s
          refine ⟨fun hs => h1 s hs, fun hs => ?_⟩
          have hs' : s = ⟨t, ht'⟩ := Fin.ext hs
          rw [hs']
          exact h2
      have hnext : (Finset.univ.filter (fun i : Fin m =>
          ∀ s : Fin r, s.val < t + 1 → x (i,s) = H.testBit s.val))
          = Pf.filter (fun i => x (i,⟨t,ht'⟩) = H.testBit t) := by
        rw [hPf, Finset.filter_filter]
        apply Finset.filter_congr
        intro i _
        constructor
        · intro hM
          exact ⟨fun s hs => hM s (by omega), hM ⟨t, ht'⟩ (by simp)⟩
        · rintro ⟨h1, h2⟩ s hs
          by_cases hst : s.val < t
          · exact h1 s hst
          · have hs' : s = ⟨t, ht'⟩ := Fin.ext (show s.val = t by omega)
            rw [hs']
            exact h2
      rw [hnext]
      have hK : 2^(r-t) = 2 * 2^(r-(t+1)) := by
        have h1 : r - t = (r - (t+1)) + 1 := by omega
        rw [h1, pow_succ, mul_comm]
      have hexp : r - 1 - t = r - (t+1) := by omega
      rw [hexp, hN0] at hbit
      by_cases hb : H.testBit t = true
      · rw [hb] at hbit
        have hodd : Nat.choose (Pf.filter (fun i => x (i,⟨t,ht'⟩) = false)).card
            (2^(r-(t+1))) % 2 = 1 := by simpa using hbit.symm
        have hge : 2^(r-(t+1)) ≤ (Pf.filter (fun i => x (i,⟨t,ht'⟩) = false)).card := by
          by_contra hlt
          rw [not_le] at hlt
          rw [Nat.choose_eq_zero_of_lt hlt] at hodd
          simp at hodd
        have hsub : Pf.filter (fun i => x (i,⟨t,ht'⟩) = H.testBit t) ⊆
            Pf.filter (fun i => ¬ x (i,⟨t,ht'⟩) = false) := by
          intro i hi
          rw [Finset.mem_filter] at hi ⊢
          refine ⟨hi.1, ?_⟩
          rw [hi.2, hb]
          simp
        have hle := Finset.card_le_card hsub
        omega
      · have hb' : H.testBit t = false := by simpa using hb
        rw [hb'] at hbit ⊢
        have hnodd : ¬ Nat.choose (Pf.filter (fun i => x (i,⟨t,ht'⟩) = false)).card
            (2^(r-(t+1))) % 2 = 1 := by
          intro h
          rw [h] at hbit
          simp at hbit
        by_contra hge
        rw [not_lt] at hge
        apply hnodd
        apply lucas_pow _ _ hge
        rw [pow_succ]
        omega
  exact hcnt l le_rfl

theorem main_aux (m r : ℕ) (hm : m < 2^r) :
    ∃ ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool,
      (∀ (u : Fin r) (path : ℕ), ∃ terms : Finset (Finset (Fin m × Fin r)),
        (∀ mon ∈ terms, mon.card ≤ (u.val+1)*2^(r-1-u.val)) ∧
        ∀ word, ask u.val path word =
          (((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2) == 1)) ∧
      ∀ (input : Fin m × Fin r → Bool) (l : ℕ), l ≤ r →
        ((Finset.univ : Finset (Fin m)).filter (fun i =>
          ∀ j : Fin r, j.val < l → input (i,j) =
            ((List.range l).foldl (fun past pos =>
              past + ((ask pos past input).toNat <<< pos)) 0).testBit j.val)).card
          < 2^(r-l) := by
  refine ⟨fun u h x => decide (Nat.choose (cnt1 m r u h x) (2^(r-1-u)) % 2 = 1), ?_, ?_⟩
  · intro u path
    exact ask_deg m r u.val path
  · intro x l hl
    have hfix := run_fix l
      (fun p h => decide (Nat.choose (cnt1 m r p h x) (2^(r-1-p)) % 2 = 1))
      (fun p h h' hb => by
        show decide (Nat.choose (cnt1 m r p h x) (2^(r-1-p)) % 2 = 1) =
          decide (Nat.choose (cnt1 m r p h' x) (2^(r-1-p)) % 2 = 1)
        rw [cnt1_congr m r p h h' x hb])
    exact proto m r hm x l hl _ hfix

theorem main : ∀ (m r : Nat), m < 2^r →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range steps).foldl (fun past pos => past + ((ask pos past x).toNat <<< pos)) 0
  ∃ ask : Nat → Nat → W → Bool,
    (∀ (u : Fin r) (path : Nat), deg ((u.val+1)*2^(r-1-u.val)) (ask u.val path)) ∧
    ∀ (input : W) (l : Nat), l ≤ r →
      let trace := run l ask input
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∀ j : Fin r, j.val < l → input (i,j) = trace.testBit j.val)).card < 2^(r-l) := by
  intro m r hm V W par deg run
  exact main_aux m r hm

end PEqualNP.Outside.L_lib_582_aux

theorem PEqualNP.Outside.L_lib_582 : (∀ (m r : Nat), m < 2^r →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range steps).foldl (fun past pos => past + ((ask pos past x).toNat <<< pos)) 0
  ∃ ask : Nat → Nat → W → Bool,
    (∀ (u : Fin r) (path : Nat), deg ((u.val+1)*2^(r-1-u.val)) (ask u.val path)) ∧
    ∀ (input : W) (l : Nat), l ≤ r →
      let trace := run l ask input
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        ∀ j : Fin r, j.val < l → input (i,j) = trace.testBit j.val)).card < 2^(r-l)) := by
  exact PEqualNP.Outside.L_lib_582_aux.main
