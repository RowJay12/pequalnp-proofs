import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_611_aux

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

theorem symmDiff_sum' {ι : Type} [Fintype ι] [DecidableEq ι] (gg : ι → ZMod 2)
    (D D' : Finset ι) : (symmDiff D D').sum gg = D.sum gg + D'.sum gg := by
  have hi : ∀ S : Finset ι, S.sum gg = ∑ i, if i ∈ S then gg i else 0 := by
    intro S
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hi (symmDiff D D'), hi D, hi D', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : gg i + gg i = 0 := CharTwo.add_self_eq_zero (gg i)
  by_cases h : i ∈ D <;> by_cases h' : i ∈ D' <;> simp [Finset.mem_symmDiff, h, h', h2]

theorem toggle_sum {V : Type} [DecidableEq V] (U : Finset V) (p : V) (hpU : p ∈ U)
    (P : Finset V → Prop) (inst : DecidablePred P)
    (hP : ∀ A : Finset V, P (if p ∈ A then A.erase p else insert p A) ↔ P A) :
    ∑ A ∈ U.powerset, (@ite (ZMod 2) (P A) (inst A) 1 0) = 0 := by
  refine Finset.sum_involution (fun T _ => if p ∈ T then T.erase p else insert p T) ?_ ?_ ?_ ?_
  · intro T hT
    by_cases hc : P T
    · rw [if_pos hc, if_pos ((hP T).mpr hc)]
      decide
    · rw [if_neg hc, if_neg (fun h => hc ((hP T).mp h))]
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
      exact Finset.insert_subset hpU hT
  · intro T hT
    by_cases hpT : p ∈ T
    · simp [hpT, Finset.insert_erase hpT]
    · simp [hpT, Finset.erase_insert hpT]

theorem tr_succ (step : ℕ → ℕ → Bool) (k : ℕ) :
    (List.range (k+1)).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0
    = 2^k * (step k ((List.range k).foldl
        (fun h pos => h + ((step pos h).toNat <<< pos)) 0)).toNat
      + (List.range k).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0 := by
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [Nat.shiftLeft_eq, mul_comm, add_comm]

theorem trunc_aux (tr : ℕ → ℕ) (bit : ℕ → ℕ)
    (hs : ∀ k, tr (k+1) = 2^k * bit k + tr k) (hlt : ∀ k, tr k < 2^k) :
    ∀ n k, tr (k + n) % 2^k = tr k := by
  intro n
  induction n with
  | zero =>
    intro k
    exact Nat.mod_eq_of_lt (hlt k)
  | succ n ih =>
    intro k
    rw [← add_assoc, hs, pow_add, mul_assoc, Nat.mul_add_mod, ih]

theorem cell_iff (step step' : ℕ → ℕ → Bool) (j : ℕ) :
    ((List.range j).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0
      = (List.range j).foldl (fun h pos => h + ((step' pos h).toNat <<< pos)) 0)
    ↔ ∀ t, t < j →
        step t ((List.range t).foldl (fun h pos => h + ((step' pos h).toNat <<< pos)) 0)
        = step' t ((List.range t).foldl
            (fun h pos => h + ((step' pos h).toNat <<< pos)) 0) := by
  obtain ⟨tr, htr⟩ : ∃ tr : ℕ → ℕ, ∀ k, tr k =
      (List.range k).foldl (fun h pos => h + ((step pos h).toNat <<< pos)) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨tr', htr'⟩ : ∃ tr' : ℕ → ℕ, ∀ k, tr' k =
      (List.range k).foldl (fun h pos => h + ((step' pos h).toNat <<< pos)) 0 :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ k, tr (k+1) = 2^k * (step k (tr k)).toNat + tr k := by
    intro k
    rw [htr (k+1), htr k]
    exact tr_succ step k
  have hs' : ∀ k, tr' (k+1) = 2^k * (step' k (tr' k)).toNat + tr' k := by
    intro k
    rw [htr' (k+1), htr' k]
    exact tr_succ step' k
  have hlt : ∀ k, tr k < 2^k := fun k => by
    rw [htr k]
    exact trace_lt step k
  have hlt' : ∀ k, tr' k < 2^k := fun k => by
    rw [htr' k]
    exact trace_lt step' k
  simp only [← htr, ← htr']
  constructor
  · intro h t ht
    have hk : ∀ k, k ≤ j → tr k = tr' k := by
      intro k hk
      have e1 := trunc_aux tr (fun k => (step k (tr k)).toNat) hs hlt (j - k) k
      have e2 := trunc_aux tr' (fun k => (step' k (tr' k)).toNat) hs' hlt' (j - k) k
      have hj : k + (j - k) = j := by omega
      rw [hj] at e1 e2
      rw [← e1, ← e2, h]
    have h1 := hk (t+1) (by omega)
    have h0 := hk t (by omega)
    rw [hs, hs', h0] at h1
    have h2 : 2^t * (step t (tr' t)).toNat = 2^t * (step' t (tr' t)).toNat := by omega
    have h3 := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    revert h3
    cases step t (tr' t) <;> cases step' t (tr' t) <;> simp
  · intro h
    have hk : ∀ k, k ≤ j → tr k = tr' k := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [htr 0, htr' 0]
        rfl
      | succ k ih =>
        intro hk
        have e := ih (by omega)
        rw [hs, hs', e, h k (by omega)]
    exact hk j le_rfl

theorem cell_deg (m r j : ℕ) (q : Fin j → (Fin m × Fin r → Bool) → Bool) (β : Fin j → Bool)
    (B : Fin j → ℕ)
    (hq : ∀ t, ∃ terms : Finset (Finset (Fin m × Fin r)), (∀ mon ∈ terms, mon.card ≤ B t) ∧
      ∀ word, q t word =
        (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)) :
    ∃ terms : Finset (Finset (Fin m × Fin r)), (∀ mon ∈ terms, mon.card ≤ ∑ t, B t) ∧
      ∀ word, decide (∀ t, q t word = β t) =
        (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1) := by
  classical
  choose T hT1 hT2 using hq
  obtain ⟨T', hT'⟩ : ∃ T' : Fin j → Finset (Finset (Fin m × Fin r)),
      ∀ t, T' t = if β t = true then T t else symmDiff (T t) {∅} := ⟨_, fun _ => rfl⟩
  have hT'card : ∀ t, ∀ mon ∈ T' t, mon.card ≤ B t := by
    intro t mon hmon
    rw [hT'] at hmon
    by_cases hb : β t = true
    · rw [if_pos hb] at hmon
      exact hT1 t mon hmon
    · rw [if_neg hb, Finset.mem_symmDiff] at hmon
      rcases hmon with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hT1 t mon h1
      · rw [Finset.mem_singleton] at h1
        rw [h1]
        simp
  have hbool : ∀ c : Bool, (if c = false then (1 : ZMod 2) else 0) =
      (if c = true then (1 : ZMod 2) else 0) + 1 := by decide
  have hfac : ∀ t (x : Fin m × Fin r → Bool), (if q t x = β t then (1 : ZMod 2) else 0) =
      ∑ mon ∈ T' t, (if (∀ v ∈ mon, x v = true) then (1 : ZMod 2) else 0) := by
    intro t x
    have h1 : (if q t x = true then (1 : ZMod 2) else 0) =
        ∑ mon ∈ T t, (if (∀ v ∈ mon, x v = true) then (1 : ZMod 2) else 0) := by
      rw [hT2 t x, ind_card, Finset.natCast_card_filter]
    rw [hT']
    by_cases hb : β t = true
    · rw [if_pos hb, ← h1, hb]
    · have hb' : β t = false := by simpa using hb
      have hone : (∑ mon ∈ ({∅} : Finset (Finset (Fin m × Fin r))),
          (if (∀ v ∈ mon, x v = true) then (1 : ZMod 2) else 0)) = 1 := by
        rw [Finset.sum_singleton, if_pos]
        intro v hv
        exact absurd hv (Finset.notMem_empty v)
      rw [if_neg hb, symmDiff_sum', ← h1, hb', hone]
      exact hbool (q t x)
  have hprod : ∀ x : Fin m × Fin r → Bool,
      (if decide (∀ t, q t x = β t) = true then (1 : ZMod 2) else 0) =
      ∑ φ ∈ Fintype.piFinset T',
        (if (∀ t, ∀ v ∈ φ t, x v = true) then (1 : ZMod 2) else 0) := by
    intro x
    have h1 : (if decide (∀ t, q t x = β t) = true then (1 : ZMod 2) else 0) =
        ∏ t : Fin j, (if q t x = β t then (1 : ZMod 2) else 0) := by
      rw [Fintype.prod_boole]
      simp
    rw [h1]
    simp only [hfac]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro φ _
    rw [Fintype.prod_boole]
    by_cases hc : ∀ t, ∀ v ∈ φ t, x v = true
    · simp only [if_pos hc]
    · simp only [if_neg hc]
  apply mobius_deg m r (fun word => decide (∀ t, q t word = β t))
  intro S hS
  simp only [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro φ hφ
  refine dep_even (fun x : Fin m × Fin r → Bool => ∀ t, ∀ v ∈ φ t, x v = true)
    (Finset.univ.biUnion φ) S ?_ ?_
  · refine lt_of_le_of_lt ?_ hS
    refine Finset.card_biUnion_le.trans ?_
    apply Finset.sum_le_sum
    intro t _
    exact hT'card t (φ t) ((Fintype.mem_piFinset.mp hφ) t)
  · intro x x' hxx
    constructor
    · intro hP t v hv
      rw [← hxx v (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, hv⟩)]
      exact hP t v hv
    · intro hP t v hv
      rw [hxx v (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, hv⟩)]
      exact hP t v hv

theorem exists_fill (m r : ℕ) (f : (Fin m × Fin r → Bool) → Bool)
    (terms : Finset (Finset (Fin m × Fin r)))
    (hrep : ∀ word, f word =
      (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1))
    (U : Finset (Fin m × Fin r)) (hU : U ∈ terms) (hmax : ∀ mon ∈ terms, U ⊆ mon → mon = U)
    (w : Fin m × Fin r → Bool) :
    ∃ A ∈ U.powerset, f (fun v => if v ∈ U then decide (v ∈ A) else w v) = true := by
  classical
  by_contra hcon
  have hall : ∀ A ∈ U.powerset,
      (if f (fun v => if v ∈ U then decide (v ∈ A) else w v) = true
        then (1 : ZMod 2) else 0) = 0 := by
    intro A hA
    rw [if_neg]
    intro h
    exact hcon ⟨A, hA, h⟩
  have hsum0 : ∑ A ∈ U.powerset,
      (if f (fun v => if v ∈ U then decide (v ∈ A) else w v) = true
        then (1 : ZMod 2) else 0) = 0 := Finset.sum_eq_zero hall
  have hterm : ∀ A : Finset (Fin m × Fin r),
      (if f (fun v => if v ∈ U then decide (v ∈ A) else w v) = true
        then (1 : ZMod 2) else 0) =
      ∑ mon ∈ terms, (if (∀ v ∈ mon, (if v ∈ U then decide (v ∈ A) else w v) = true)
        then (1 : ZMod 2) else 0) := by
    intro A
    rw [hrep, ind_card, Finset.natCast_card_filter]
  rw [Finset.sum_congr rfl (fun A _ => hterm A), Finset.sum_comm] at hsum0
  have hinner : ∀ mon ∈ terms, ∑ A ∈ U.powerset,
      (if (∀ v ∈ mon, (if v ∈ U then decide (v ∈ A) else w v) = true)
        then (1 : ZMod 2) else 0) = if mon = U then 1 else 0 := by
    intro mon hmon
    by_cases hmU : mon = U
    · rw [if_pos hmU, hmU, Finset.sum_eq_single U]
      · rw [if_pos]
        intro v hv
        simp [hv]
      · intro A hA hne
        rw [if_neg]
        intro h
        apply hne
        apply Finset.Subset.antisymm (Finset.mem_powerset.mp hA)
        intro v hv
        have h1 := h v hv
        simpa [hv] using h1
      · intro h
        exact absurd (Finset.mem_powerset.mpr (subset_refl U)) h
    · rw [if_neg hmU]
      have hnsub : ¬ U ⊆ mon := fun h => hmU (hmax mon hmon h)
      obtain ⟨p, hpU, hpm⟩ := Finset.not_subset.mp hnsub
      refine toggle_sum U p hpU
        (fun A => ∀ v ∈ mon, (if v ∈ U then decide (v ∈ A) else w v) = true) _ ?_
      intro A
      refine forall₂_congr fun v hv => ?_
      have hvp : v ≠ p := fun h => hpm (by rw [← h]; exact hv)
      by_cases hpA : p ∈ A
      · simp [hpA, Finset.mem_erase, hvp]
      · simp [hpA, Finset.mem_insert, hvp]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq', if_pos hU] at hsum0
  exact one_ne_zero hsum0

def runF (m r : ℕ) (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool) (len : ℕ)
    (x : Fin m × Fin r → Bool) : ℕ :=
  (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0

theorem main_aux (m r d : ℕ) (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool)
    (anchor : Fin m × Fin r → Bool) (j : ℕ) (B : Fin j → ℕ)
    (hdeg : ∀ t : Fin j, ∃ terms : Finset (Finset (Fin m × Fin r)),
      (∀ mon ∈ terms, mon.card ≤ B t) ∧ ∀ word,
      ask t.val (runF m r ask t.val anchor) word
        = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)) :
    ∃ U : Finset (Fin m × Fin r), U.card ≤ ∑ t : Fin j, B t ∧
      ∀ (L : ℕ) (bad : ℕ → Fin L → Fin m → (Fin r → Bool)),
        ((Finset.univ : Finset (Fin m × Fin r → Bool)).filter (fun w =>
          ∀ h ∈ ((Finset.univ : Finset (Fin m × Fin r → Bool)).filter
              (fun sample => runF m r ask j sample = runF m r ask j anchor)).image
                (runF m r ask d),
            ∀ a, ∃ i, i ∉ U.image Prod.fst ∧ (fun v => w (i,v)) = bad h a i)).card
        ≤ 2^U.card * (((Finset.univ : Finset (Fin m × Fin r → Bool)).filter
            (fun sample => runF m r ask j sample = runF m r ask j anchor)).filter
              (fun input => ∀ a, ∃ i,
                (fun v => input (i,v)) = bad (runF m r ask d input) a i)).card := by
  classical
  obtain ⟨terms, hterms, hrep⟩ := cell_deg m r j
    (fun t => ask t.val (runF m r ask t.val anchor))
    (fun t => ask t.val (runF m r ask t.val anchor) anchor) B hdeg
  have hcell : ∀ x : Fin m × Fin r → Bool,
      (runF m r ask j x = runF m r ask j anchor) ↔
      ∀ t : Fin j, ask t.val (runF m r ask t.val anchor) x =
        ask t.val (runF m r ask t.val anchor) anchor := by
    intro x
    have h := cell_iff (fun pos h => ask pos h x) (fun pos h => ask pos h anchor) j
    constructor
    · intro e t
      exact (h.mp e) t.val t.isLt
    · intro e
      exact h.mpr (fun t ht => e ⟨t, ht⟩)
  have hne : terms.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h1 := hrep anchor
    rw [hemp] at h1
    simp at h1
  obtain ⟨U, hU, hUmax⟩ := Finset.exists_max_image terms Finset.card hne
  refine ⟨U, hterms U hU, ?_⟩
  intro L bad
  have hmax : ∀ mon ∈ terms, U ⊆ mon → mon = U := by
    intro mon hmon hsub
    exact (Finset.eq_of_subset_of_card_le hsub (hUmax mon hmon)).symm
  have hfill : ∀ w : Fin m × Fin r → Bool, ∃ A ∈ U.powerset,
      decide (∀ t : Fin j, ask t.val (runF m r ask t.val anchor)
        (fun v => if v ∈ U then decide (v ∈ A) else w v) =
        ask t.val (runF m r ask t.val anchor) anchor) = true :=
    fun w => exists_fill m r _ terms hrep U hU hmax w
  choose Afn hA1 hA2 using hfill
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin m × Fin r → Bool) → (Fin m × Fin r → Bool),
      ∀ w v, Φ w v = if v ∈ U then decide (v ∈ Afn w) else w v := ⟨_, fun _ _ => rfl⟩
  have hΦcell : ∀ w, runF m r ask j (Φ w) = runF m r ask j anchor := by
    intro w
    have e : Φ w = fun v => if v ∈ U then decide (v ∈ Afn w) else w v := funext (hΦ w)
    rw [e]
    exact (hcell _).mpr (of_decide_eq_true (hA2 w))
  refine (Finset.card_le_mul_card_image (f := Φ) _ (2^U.card) ?_).trans ?_
  · intro e _
    refine (Finset.card_le_card (t := U.powerset.image
      (fun A => fun v => if v ∈ U then decide (v ∈ A) else e v)) ?_).trans
      (Finset.card_image_le.trans (le_of_eq (Finset.card_powerset U)))
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_image]
    refine ⟨U.filter (fun v => w v = true), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    funext v
    by_cases hv : v ∈ U
    · simp [hv]
    · rw [if_neg hv, ← hw.2, hΦ, if_neg hv]
  · apply Nat.mul_le_mul_left
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨w, hw, rfl⟩ := he
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, hΦcell w⟩, fun a => ?_⟩
    obtain ⟨i, hi, hbi⟩ := hw.2 (runF m r ask d (Φ w))
      (Finset.mem_image.mpr ⟨Φ w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hΦcell w⟩, rfl⟩) a
    refine ⟨i, ?_⟩
    rw [← hbi]
    funext v
    have hv : (i, v) ∉ U := fun h => hi (Finset.mem_image.mpr ⟨(i,v), h, rfl⟩)
    rw [hΦ, if_neg hv]

theorem main : ∀ (m r d : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ word,
      f word = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)
  let run := fun (ask : Nat → Nat → W → Bool) (len : Nat) (x : W) =>
    (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0
  ∀ (ask : Nat → Nat → W → Bool) (anchor : W) (j : Nat), j ≤ d →
    let pathCode := run ask j anchor
    let cell := (Finset.univ : Finset W).filter (fun sample => run ask j sample = pathCode)
    let leaves := cell.image (run ask d)
    ∀ B : Fin j → Nat, (∀ t, deg (B t) (ask t.val (run ask t.val anchor))) →
      ∃ U : Finset V, U.card ≤ ∑ t : Fin j, B t ∧
        ∀ (L : Nat) (bad : Nat → Fin L → Fin m → Symbol),
          let gone := U.image Prod.fst
          let outside := (Finset.univ : Finset W).filter (fun w =>
            ∀ h ∈ leaves, ∀ a, ∃ i, i ∉ gone ∧ (fun v => w (i,v)) = bad h a i)
          let errors := cell.filter (fun input => ∀ a, ∃ i,
            (fun v => input (i,v)) = bad (run ask d input) a i)
          outside.card ≤ 2^U.card * errors.card := by
  intro m r d V W Symbol deg run ask anchor j hj pathCode cell leaves B hdeg
  exact main_aux m r d ask anchor j B hdeg

end PEqualNP.Outside.L_lib_611_aux

theorem PEqualNP.Outside.L_lib_611 : (∀ (m r d : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧ ∀ word,
      f word = (((terms.filter (fun mon => ∀ v ∈ mon, word v = true)).card % 2) == 1)
  let run := fun (ask : Nat → Nat → W → Bool) (len : Nat) (x : W) =>
    (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0
  ∀ (ask : Nat → Nat → W → Bool) (anchor : W) (j : Nat), j ≤ d →
    let pathCode := run ask j anchor
    let cell := (Finset.univ : Finset W).filter (fun sample => run ask j sample = pathCode)
    let leaves := cell.image (run ask d)
    ∀ B : Fin j → Nat, (∀ t, deg (B t) (ask t.val (run ask t.val anchor))) →
      ∃ U : Finset V, U.card ≤ ∑ t : Fin j, B t ∧
        ∀ (L : Nat) (bad : Nat → Fin L → Fin m → Symbol),
          let gone := U.image Prod.fst
          let outside := (Finset.univ : Finset W).filter (fun w =>
            ∀ h ∈ leaves, ∀ a, ∃ i, i ∉ gone ∧ (fun v => w (i,v)) = bad h a i)
          let errors := cell.filter (fun input => ∀ a, ∃ i,
            (fun v => input (i,v)) = bad (run ask d input) a i)
          outside.card ≤ 2^U.card * errors.card) := by
  exact PEqualNP.Outside.L_lib_611_aux.main
