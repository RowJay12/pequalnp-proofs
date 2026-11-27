import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_609_aux

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

def runF (m r : ℕ) (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool) (len : ℕ)
    (x : Fin m × Fin r → Bool) : ℕ :=
  (List.range len).foldl (fun h step => h + ((ask step h x).toNat <<< step)) 0

theorem bxor_ind (x y : Bool) : (if (xor x y) = true then (1 : ZMod 2) else 0) =
    (if x = true then (1 : ZMod 2) else 0) + (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem ind_add_zero (x y : Bool)
    (h : (if x = true then (1 : ZMod 2) else 0) + (if y = true then 1 else 0) = 0) : x = y := by
  revert h
  cases x <;> cases y <;> decide

theorem ins_eq {ι : Type} [DecidableEq ι] (p : ι) (T : Finset ι) (hp : p ∉ T) :
    insert p T = symmDiff T {p} := by
  ext z
  rw [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      exact ⟨h, by rw [h]; exact hp⟩
    · left
      exact ⟨h, fun e => hp (by rw [← e]; exact h)⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · right
      exact h
    · left
      exact h

theorem rm {ι : Type} [DecidableEq ι] : ∀ (S : Finset ι) (D : ℕ) (G : Finset ι → Bool),
    (∀ (Y S' : Finset ι), D < S'.card →
      ∑ T ∈ S'.powerset, (if G (symmDiff Y T) = true then (1 : ZMod 2) else 0) = 0) →
    ∀ Y : Finset ι, (∃ T ∈ S.powerset, G (symmDiff Y T) = true) →
      2^(S.card - D) ≤ (S.powerset.filter (fun T => G (symmDiff Y T) = true)).card := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro D G hSD Y hex
    obtain ⟨T, hT, hG⟩ := hex
    rw [Finset.powerset_empty, Finset.mem_singleton] at hT
    subst hT
    rw [Finset.powerset_empty, Finset.filter_singleton, if_pos hG]
    simp
  | insert p S' hp ih =>
    intro D G hSD Y hex
    have hcount : ((insert p S').powerset.filter (fun T => G (symmDiff Y T) = true)).card
        = (S'.powerset.filter (fun T => G (symmDiff Y T) = true)).card
          + (S'.powerset.filter (fun T => G (symmDiff (symmDiff Y {p}) T) = true)).card := by
      rw [Finset.card_filter, Finset.sum_powerset_insert hp, Finset.card_filter,
        Finset.card_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro T hT
      have hpT : p ∉ T := fun h => hp (Finset.mem_powerset.mp hT h)
      rw [ins_eq p T hpT, symmDiff_assoc, symmDiff_comm T {p}]
    have hsplit : (∃ T ∈ S'.powerset, G (symmDiff Y T) = true) ∨
        (∃ T ∈ S'.powerset, G (symmDiff (symmDiff Y {p}) T) = true) := by
      obtain ⟨T0, hT0, hG⟩ := hex
      by_cases hpT : p ∈ T0
      · right
        refine ⟨T0.erase p, ?_, ?_⟩
        · rw [Finset.mem_powerset] at hT0 ⊢
          intro z hz
          have h1 := hT0 (Finset.mem_of_mem_erase hz)
          rw [Finset.mem_insert] at h1
          rcases h1 with h1 | h1
          · exact absurd h1 (Finset.ne_of_mem_erase hz)
          · exact h1
        · rw [symmDiff_assoc, symmDiff_comm {p} (T0.erase p),
            ← ins_eq p _ (Finset.notMem_erase p T0), Finset.insert_erase hpT]
          exact hG
      · left
        refine ⟨T0, ?_, hG⟩
        rw [Finset.mem_powerset] at hT0 ⊢
        intro z hz
        have h1 := hT0 hz
        rw [Finset.mem_insert] at h1
        rcases h1 with h1 | h1
        · rw [h1] at hz
          exact absurd hz hpT
        · exact h1
    have one_side : ∀ Z : Finset ι, 0 < D → (∃ T ∈ S'.powerset, G (symmDiff Z T) = true) →
        (∀ T ∈ S'.powerset, G (symmDiff (symmDiff Z {p}) T) = false) →
        2^(S'.card + 1 - D) ≤ (S'.powerset.filter (fun T => G (symmDiff Z T) = true)).card := by
      intro Z hDpos hex0 hnone
      have hSDH : ∀ (Y' S'' : Finset ι), D - 1 < S''.card →
          ∑ T ∈ S''.powerset, (if (xor (G (symmDiff Y' T)) (G (symmDiff (symmDiff Y' T) {p})))
            = true then (1 : ZMod 2) else 0) = 0 := by
        intro Y' S'' hS''
        simp only [bxor_ind]
        rw [Finset.sum_add_distrib]
        by_cases hpS : p ∈ S''
        · have hre : ∑ T ∈ S''.powerset,
              (if G (symmDiff (symmDiff Y' T) {p}) = true then (1 : ZMod 2) else 0)
              = ∑ T ∈ S''.powerset, (if G (symmDiff Y' T) = true then (1 : ZMod 2) else 0) := by
            have hmaps : ∀ T ∈ S''.powerset, symmDiff T {p} ∈ S''.powerset := by
              intro T hT
              rw [Finset.mem_powerset] at hT ⊢
              intro z hz
              rw [Finset.mem_symmDiff, Finset.mem_singleton] at hz
              rcases hz with ⟨h1, -⟩ | ⟨h1, -⟩
              · exact hT h1
              · rw [h1]
                exact hpS
            apply Finset.sum_bij' (fun T _ => symmDiff T {p}) (fun T _ => symmDiff T {p})
              hmaps hmaps
            · intro T hT
              simp
            · intro T hT
              simp
            · intro T hT
              rw [symmDiff_assoc]
          rw [hre]
          exact CharTwo.add_self_eq_zero _
        · have h1 := hSD Y' (insert p S'') (by
            rw [Finset.card_insert_of_notMem hpS]
            omega)
          rw [Finset.sum_powerset_insert hpS] at h1
          refine Eq.trans ?_ h1
          congr 1
          apply Finset.sum_congr rfl
          intro T hT
          have hpT : p ∉ T := fun h => hpS (Finset.mem_powerset.mp hT h)
          rw [ins_eq p T hpT, symmDiff_assoc]
      obtain ⟨T0, hT0, hG0⟩ := hex0
      have hH : ∀ T ∈ S'.powerset,
          (xor (G (symmDiff Z T)) (G (symmDiff (symmDiff Z T) {p}))) = G (symmDiff Z T) := by
        intro T hT
        have e : symmDiff (symmDiff Z T) {p} = symmDiff (symmDiff Z {p}) T := by
          rw [symmDiff_assoc, symmDiff_assoc, symmDiff_comm T {p}]
        rw [e, hnone T hT]
        simp
      have i0 : 2^(S'.card - (D - 1)) ≤ (S'.powerset.filter (fun T =>
          (xor (G (symmDiff Z T)) (G (symmDiff (symmDiff Z T) {p}))) = true)).card :=
        ih (D - 1) (fun T => xor (G T) (G (symmDiff T {p}))) hSDH Z
          ⟨T0, hT0, by rw [hH T0 hT0]; exact hG0⟩
      have efil : S'.powerset.filter (fun T =>
          (xor (G (symmDiff Z T)) (G (symmDiff (symmDiff Z T) {p}))) = true)
          = S'.powerset.filter (fun T => G (symmDiff Z T) = true) := by
        apply Finset.filter_congr
        intro T hT
        rw [hH T hT]
      rw [efil] at i0
      have e1 : S'.card - (D - 1) = S'.card + 1 - D := by omega
      rw [e1] at i0
      exact i0
    rw [hcount, Finset.card_insert_of_notMem hp]
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · subst hD0
      have htog : ∀ Y' : Finset ι, G (symmDiff Y' {p}) = G Y' := by
        intro Y'
        have h1 := hSD Y' (insert p ∅) (by simp)
        rw [Finset.sum_powerset_insert (Finset.notMem_empty p), Finset.powerset_empty,
          Finset.sum_singleton, Finset.sum_singleton] at h1
        have e0 : symmDiff Y' (∅ : Finset ι) = Y' := by
          ext z
          simp [Finset.mem_symmDiff]
        have e1 : insert p (∅ : Finset ι) = {p} := by
          ext z
          simp
        rw [e0, e1] at h1
        exact (ind_add_zero _ _ h1).symm
      have eqs : ∀ T, symmDiff (symmDiff Y {p}) T = symmDiff (symmDiff Y T) {p} := by
        intro T
        rw [symmDiff_assoc, symmDiff_assoc, symmDiff_comm {p} T]
      have hboth : (∃ T ∈ S'.powerset, G (symmDiff Y T) = true) ∧
          (∃ T ∈ S'.powerset, G (symmDiff (symmDiff Y {p}) T) = true) := by
        rcases hsplit with ⟨T, hT, hG⟩ | ⟨T, hT, hG⟩
        · exact ⟨⟨T, hT, hG⟩, ⟨T, hT, by rw [eqs, htog]; exact hG⟩⟩
        · exact ⟨⟨T, hT, by rw [eqs, htog] at hG; exact hG⟩, ⟨T, hT, hG⟩⟩
      have i0 := ih 0 G hSD Y hboth.1
      have i1 := ih 0 G hSD (symmDiff Y {p}) hboth.2
      simp only [Nat.sub_zero] at i0 i1 ⊢
      rw [pow_succ]
      omega
    · by_cases hb0 : ∃ T ∈ S'.powerset, G (symmDiff Y T) = true
      · by_cases hb1 : ∃ T ∈ S'.powerset, G (symmDiff (symmDiff Y {p}) T) = true
        · have i0 := ih D G hSD Y hb0
          have i1 := ih D G hSD (symmDiff Y {p}) hb1
          have hpow : 2^(S'.card + 1 - D) ≤ 2 * 2^(S'.card - D) := by
            rcases Nat.lt_or_ge S'.card D with h | h
            · have e1 : S'.card + 1 - D = 0 := by omega
              rw [e1]
              have h5 := Nat.one_le_two_pow (n := S'.card - D)
              omega
            · have e1 : S'.card + 1 - D = (S'.card - D) + 1 := by omega
              rw [e1, pow_succ]
              omega
          omega
        · have h6 := one_side Y hDpos hb0 (by
            intro T hT
            by_contra hne
            exact hb1 ⟨T, hT, by simpa using hne⟩)
          omega
      · have hb1 : ∃ T ∈ S'.powerset, G (symmDiff (symmDiff Y {p}) T) = true := by
          rcases hsplit with h | h
          · exact absurd h hb0
          · exact h
        have h6 := one_side (symmDiff Y {p}) hDpos hb1 (by
          intro T hT
          rw [symmDiff_symmDiff_cancel_right]
          by_contra hne
          exact hb0 ⟨T, hT, by simpa using hne⟩)
        omega

theorem uniq (L z z' a a' : ℕ) (hL : 0 < L) (ha : a < L) (ha' : a' < L)
    (h : L * z + a = L * z' + a') : z = z' ∧ a = a' := by
  have e1 : (L * z + a) / L = z := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt ha, add_zero]
  have e2 : (L * z' + a') / L = z' := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt ha', add_zero]
  have hz : z = z' := by rw [← e1, ← e2, h]
  subst hz
  exact ⟨rfl, by omega⟩

theorem main_aux (m r L d : ℕ) (hL : 0 < L)
    (ask : ℕ → ℕ → (Fin m × Fin r → Bool) → Bool)
    (leaf : ℕ → Fin L → Fin m → Fin r → Bool) (base : Fin m × Fin r → Bool)
    (hsucc : ∃ a : Fin L, ∀ i, (fun v => base (i,v)) ≠ leaf (runF m r ask d base) a i)
    (B : Fin d → ℕ)
    (hdeg : ∀ u : Fin d, ∃ terms : Finset (Finset (Fin m × Fin r)),
      (∀ mon ∈ terms, mon.card ≤ B u) ∧ ∀ input,
      ask u.val (runF m r ask u.val base) input
        = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)) :
    ∃ (driver : Fin m × Fin r → Option (Fin (m / L)))
      (embed : (Fin (m / L) → Bool) → (Fin m × Fin r → Bool)),
      (∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags)) ∧
      Function.Injective embed ∧
      (∀ flags : Fin (m / L) → Bool, (∃ z, flags z = true) → ∀ a : Fin L, ∃ i,
        (fun v => embed flags (i,v)) = leaf (runF m r ask d base) a i) ∧
      2^(m / L - ∑ u : Fin d, B u) ≤ 1 +
        ((Finset.univ : Finset (Fin (m / L) → Bool)).filter (fun active =>
          (∃ z, active z = true) ∧
            runF m r ask d (embed active) = runF m r ask d base)).card := by
  classical
  obtain ⟨path, hpath⟩ : ∃ path : ℕ, path = runF m r ask d base := ⟨_, rfl⟩
  rw [← hpath] at hsucc ⊢
  obtain ⟨driver, hdrvdef⟩ : ∃ driver : Fin m × Fin r → Option (Fin (m / L)), ∀ site,
      driver site = if h : ∃ za : Fin (m / L) × Fin L,
          site.1.val = L * za.1.val + za.2.val ∧ base site ≠ leaf path za.2 site.1 site.2
        then some (Classical.choose h).1 else none := ⟨_, fun _ => rfl⟩
  have hdrv : ∀ (z : Fin (m / L)) (a : Fin L) (i : Fin m) (v : Fin r),
      i.val = L * z.val + a.val →
      driver (i, v) = if base (i,v) ≠ leaf path a i v then some z else none := by
    intro z a i v hi
    rw [hdrvdef]
    by_cases hne : base (i,v) ≠ leaf path a i v
    · have hex : ∃ za : Fin (m / L) × Fin L,
          (i, v).1.val = L * za.1.val + za.2.val ∧
            base (i, v) ≠ leaf path za.2 (i, v).1 (i, v).2 :=
        ⟨(z, a), hi, hne⟩
      rw [dif_pos hex, if_pos hne]
      have hch := (Classical.choose_spec hex).1
      have hu := uniq L (Classical.choose hex).1.val z.val (Classical.choose hex).2.val a.val hL
        (Classical.choose hex).2.isLt a.isLt (by rw [← hch]; exact hi)
      rw [Fin.ext hu.1]
    · rw [if_neg hne, dif_neg]
      rintro ⟨⟨z', a'⟩, h1, h2⟩
      have hu := uniq L z'.val z.val a'.val a.val hL a'.isLt a.isLt (by
        rw [← hi]
        exact h1.symm)
      have ha : a' = a := Fin.ext hu.2
      rw [ha] at h2
      exact hne h2
  have hidx : ∀ (z : Fin (m / L)) (a : Fin L), L * z.val + a.val < m := by
    intro z a
    have h1 : L * (z.val + 1) ≤ L * (m / L) := Nat.mul_le_mul_left L z.isLt
    have h2 : L * (m / L) ≤ m := Nat.mul_div_le m L
    have h3 : L * (z.val + 1) = L * z.val + L := by ring
    have h4 := a.isLt
    omega
  obtain ⟨embed, hembed⟩ : ∃ embed : (Fin (m / L) → Bool) → (Fin m × Fin r → Bool),
      ∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags) :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨driver, embed, hembed, ?_, ?_, ?_⟩
  · intro fl fl' heq
    funext z
    by_contra hne
    obtain ⟨a0, ha0⟩ := hsucc
    have hblk := ha0 ⟨L * z.val + a0.val, hidx z a0⟩
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hblk
    have hd := hdrv z a0 ⟨L * z.val + a0.val, hidx z a0⟩ v rfl
    rw [if_pos hv] at hd
    have h1 := congrFun heq (⟨L * z.val + a0.val, hidx z a0⟩, v)
    rw [hembed, hembed, hd] at h1
    apply hne
    revert h1
    show xor (base _) (fl z) = xor (base _) (fl' z) → fl z = fl' z
    cases base (⟨L * z.val + a0.val, hidx z a0⟩, v) <;> cases fl z <;> cases fl' z <;> decide
  · rintro flags ⟨z, hz⟩ a
    refine ⟨⟨L * z.val + a.val, hidx z a⟩, ?_⟩
    funext v
    have hd := hdrv z a ⟨L * z.val + a.val, hidx z a⟩ v rfl
    rw [hembed, hd]
    by_cases hne : base (⟨L * z.val + a.val, hidx z a⟩, v) ≠
        leaf path a ⟨L * z.val + a.val, hidx z a⟩ v
    · rw [if_pos hne]
      show xor (base _) (flags z) = _
      rw [hz]
      revert hne
      cases base (⟨L * z.val + a.val, hidx z a⟩, v) <;>
        cases leaf path a ⟨L * z.val + a.val, hidx z a⟩ v <;> decide
    · rw [if_neg hne]
      have he : base (⟨L * z.val + a.val, hidx z a⟩, v) =
          leaf path a ⟨L * z.val + a.val, hidx z a⟩ v := by
        by_contra h
        exact hne h
      show xor (base _) false = _
      rw [he]
      simp
  · obtain ⟨terms, hterms, hrep⟩ := cell_deg m r d
      (fun u => ask u.val (runF m r ask u.val base))
      (fun u => ask u.val (runF m r ask u.val base) base) B hdeg
    have hcell : ∀ x : Fin m × Fin r → Bool,
        (runF m r ask d x = path) ↔
        ∀ u : Fin d, ask u.val (runF m r ask u.val base) x =
          ask u.val (runF m r ask u.val base) base := by
      intro x
      rw [hpath]
      have h := cell_iff (fun pos h => ask pos h x) (fun pos h => ask pos h base) d
      constructor
      · intro e u
        exact (h.mp e) u.val u.isLt
      · intro e
        exact h.mpr (fun t ht => e ⟨t, ht⟩)
    have hzero : embed (fun _ => false) = base := by
      funext site
      rw [hembed]
      cases driver site <;> simp
    obtain ⟨G, hG⟩ : ∃ G : Finset (Fin (m / L)) → Bool, ∀ T, G T =
        decide (∀ u : Fin d, ask u.val (runF m r ask u.val base)
          (embed (fun z => decide (z ∈ T))) =
          ask u.val (runF m r ask u.val base) base) := ⟨_, fun _ => rfl⟩
    have hSD : ∀ (Y S' : Finset (Fin (m / L))), (∑ u : Fin d, B u) < S'.card →
        ∑ T ∈ S'.powerset, (if G (symmDiff Y T) = true then (1 : ZMod 2) else 0) = 0 := by
      intro Y S' hS'
      have hterm : ∀ T : Finset (Fin (m / L)),
          (if G (symmDiff Y T) = true then (1 : ZMod 2) else 0) =
          ∑ mon ∈ terms, (if (∀ site ∈ mon,
            embed (fun z => decide (z ∈ symmDiff Y T)) site = true)
              then (1 : ZMod 2) else 0) := by
        intro T
        rw [hG, hrep, ind_card, Finset.natCast_card_filter]
      rw [Finset.sum_congr rfl (fun T _ => hterm T), Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro mon hmon
      have hlt : (mon.image driver).card < (S'.image some).card := by
        rw [Finset.card_image_of_injective S' (Option.some_injective _)]
        exact lt_of_le_of_lt (Finset.card_image_le.trans (hterms mon hmon)) hS'
      obtain ⟨e, he1, he2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp he1
      refine toggle_sum S' p hpS (fun T => ∀ site ∈ mon,
        embed (fun z => decide (z ∈ symmDiff Y T)) site = true) _ ?_
      intro A
      refine forall₂_congr fun site hsite => ?_
      rw [hembed, hembed]
      have hds : driver site ≠ some p :=
        fun h => he2 (Finset.mem_image.mpr ⟨site, hsite, h⟩)
      cases hdsite : driver site with
      | none => simp
      | some z =>
        have hzp : z ≠ p := fun h => hds (by rw [hdsite, h])
        have hmemz : (z ∈ symmDiff Y (if p ∈ A then A.erase p else insert p A)) ↔
            (z ∈ symmDiff Y A) := by
          by_cases hpA : p ∈ A
          · simp [hpA, Finset.mem_symmDiff, Finset.mem_erase, hzp]
          · simp [hpA, Finset.mem_symmDiff, Finset.mem_insert, hzp]
        simp only [Option.elim, hmemz]
    have hbaseG : G (symmDiff ∅ ∅) = true := by
      rw [hG]
      have e : (fun z : Fin (m / L) => decide (z ∈ symmDiff (∅ : Finset (Fin (m / L))) ∅))
          = fun _ => false := by
        funext z
        simp
      rw [e, hzero]
      simp
    have hrm := rm (Finset.univ : Finset (Fin (m / L))) (∑ u : Fin d, B u) G hSD ∅
      ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), hbaseG⟩
    rw [Finset.card_univ, Fintype.card_fin] at hrm
    refine hrm.trans ?_
    have hinj : Set.InjOn (fun T : Finset (Fin (m / L)) => fun z => decide (z ∈ T))
        (↑((Finset.univ : Finset (Fin (m / L))).powerset.filter
          (fun T => G (symmDiff ∅ T) = true)) : Set (Finset (Fin (m / L)))) := by
      intro T1 _ T2 _ h
      ext z
      have h1 := congrFun h z
      simpa using h1
    rw [← Finset.card_image_of_injOn hinj]
    refine (Finset.card_le_card (t := insert (fun _ => false)
      ((Finset.univ : Finset (Fin (m / L) → Bool)).filter (fun active =>
        (∃ z, active z = true) ∧ runF m r ask d (embed active) = path))) ?_).trans ?_
    · rw [Finset.image_subset_iff]
      intro T hT
      have hGT := (Finset.mem_filter.mp hT).2
      have e0 : symmDiff (∅ : Finset (Fin (m / L))) T = T := by
        ext z
        simp [Finset.mem_symmDiff]
      rw [e0, hG] at hGT
      rw [Finset.mem_insert]
      by_cases hall : ∀ z : Fin (m / L), z ∉ T
      · left
        funext z
        simp [hall z]
      · right
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, (hcell _).mpr (of_decide_eq_true hGT)⟩
        by_contra hno
        apply hall
        intro z hz
        exact hno ⟨z, by simp [hz]⟩
    · exact (Finset.card_insert_le _ _).trans (by omega)

theorem main : ∀ (m r L d : Nat), 0 < L →
  let V := Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let t := m/L
  let F := Fin t → Bool
  let run := fun (ask : Nat → Nat → W → Bool) (n : Nat) (x : W) =>
    (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  ∀ (ask : Nat → Nat → W → Bool) (leaf : Nat → Fin L → Fin m → Fin r → Bool) (base : W),
    let path := run ask d base
    (∃ a : Fin L, ∀ i, (fun v => base (i,v)) ≠ leaf path a i) →
    ∀ B : Fin d → Nat, (∀ u, deg (B u) (ask u.val (run ask u.val base))) →
    ∃ (driver : V → Option (Fin t)) (embed : F → W),
      (∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags)) ∧
      Function.Injective embed ∧
      (∀ flags : F, (∃ z, flags z = true) → ∀ a : Fin L, ∃ i,
        (fun v => embed flags (i,v)) = leaf path a i) ∧
      2^(t - ∑ u : Fin d, B u) ≤ 1 +
        ((Finset.univ : Finset F).filter (fun active =>
          (∃ z, active z = true) ∧ run ask d (embed active) = path)).card := by
  intro m r L d hL V W deg t F run ask leaf base path hsucc B hdeg
  exact main_aux m r L d hL ask leaf base hsucc B hdeg

end PEqualNP.Outside.L_lib_609_aux

theorem PEqualNP.Outside.L_lib_609 : (∀ (m r L d : Nat), 0 < L →
  let V := Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let t := m/L
  let F := Fin t → Bool
  let run := fun (ask : Nat → Nat → W → Bool) (n : Nat) (x : W) =>
    (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  ∀ (ask : Nat → Nat → W → Bool) (leaf : Nat → Fin L → Fin m → Fin r → Bool) (base : W),
    let path := run ask d base
    (∃ a : Fin L, ∀ i, (fun v => base (i,v)) ≠ leaf path a i) →
    ∀ B : Fin d → Nat, (∀ u, deg (B u) (ask u.val (run ask u.val base))) →
    ∃ (driver : V → Option (Fin t)) (embed : F → W),
      (∀ flags site, embed flags site = xor (base site) ((driver site).elim false flags)) ∧
      Function.Injective embed ∧
      (∀ flags : F, (∃ z, flags z = true) → ∀ a : Fin L, ∃ i,
        (fun v => embed flags (i,v)) = leaf path a i) ∧
      2^(t - ∑ u : Fin d, B u) ≤ 1 +
        ((Finset.univ : Finset F).filter (fun active =>
          (∃ z, active z = true) ∧ run ask d (embed active) = path)).card) := by
  exact PEqualNP.Outside.L_lib_609_aux.main
