import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_651_aux

def Cf (n : ℕ) (F : Fin n → Fin n → Bool) (f : Fin n → ℕ) (S : Finset (Fin n)) : ℕ :=
  ∑ z1 ∈ S, (S.filter (fun z2 => f z2 < f z1 ∧ F z1 z2 ≠ F z2 z1)).card

def Ef (n : ℕ) (F : Fin n → Fin n → Bool) (S : Finset (Fin n)) : ℕ :=
  ∑ u ∈ S, (S.filter (fun u' => F u u' ≠ F u' u)).card

theorem Cf_congr (n : ℕ) (F : Fin n → Fin n → Bool) (f f' : Fin n → ℕ) (S : Finset (Fin n))
    (h : ∀ i ∈ S, f i = f' i) : Cf n F f S = Cf n F f' S := by
  unfold Cf
  apply Finset.sum_congr rfl
  intro z1 hz1
  congr 1
  apply Finset.filter_congr
  intro z2 hz2
  rw [h z1 hz1, h z2 hz2]

theorem Cf_insert (n : ℕ) (F : Fin n → Fin n → Bool) (f : Fin n → ℕ) (s' : Finset (Fin n))
    (v : Fin n) (hv : v ∉ s') (hlt : ∀ u ∈ s', f u < f v) :
    Cf n F f (insert v s') = Cf n F f s' + (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
  unfold Cf
  have e1 : ∑ z1 ∈ s', ((insert v s').filter
        (fun z2 => f z2 < f z1 ∧ F z1 z2 ≠ F z2 z1)).card
      = ∑ z1 ∈ s', (s'.filter (fun z2 => f z2 < f z1 ∧ F z1 z2 ≠ F z2 z1)).card := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.filter_insert, if_neg]
    intro h
    exact absurd h.1 (not_lt.mpr (le_of_lt (hlt u hu)))
  have e2 : ((insert v s').filter (fun z2 => f z2 < f v ∧ F v z2 ≠ F z2 v)).card
      = (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
    rw [Finset.filter_insert, if_neg (fun h => lt_irrefl _ h.1)]
    congr 1
    apply Finset.filter_congr
    intro u hu
    exact ⟨fun h => h.2, fun h => ⟨hlt u hu, h⟩⟩
  rw [Finset.sum_insert hv, e1, e2, add_comm]

theorem Ef_insert (n : ℕ) (F : Fin n → Fin n → Bool) (s' : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ s') :
    Ef n F (insert v s') = Ef n F s' + 2 * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
  unfold Ef
  have e2 : ((insert v s').filter (fun u' => F v u' ≠ F u' v)).card
      = (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
    rw [Finset.filter_insert, if_neg (fun h => h rfl)]
  have e1 : ∑ u ∈ s', ((insert v s').filter (fun u' => F u u' ≠ F u' u)).card
      = ∑ u ∈ s', ((s'.filter (fun u' => F u u' ≠ F u' u)).card +
          (if F u v ≠ F v u then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.filter_insert]
    by_cases h : F u v ≠ F v u
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem]
      intro hmem
      exact hv (Finset.mem_filter.mp hmem).1
    · rw [if_neg h, if_neg h, add_zero]
  have e3 : ∑ u ∈ s', (if F u v ≠ F v u then 1 else 0)
      = (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : F u v ≠ F v u
    · rw [if_pos h, if_pos (fun e => h e.symm)]
    · rw [if_neg h, if_neg (fun e => h (fun e' => e e'.symm))]
  rw [Finset.sum_insert hv, e1, e2, Finset.sum_add_distrib, e3]
  omega

theorem peel (n : ℕ) (F : Fin n → Fin n → Bool) :
    ∀ (k : ℕ) (s : Finset (Fin n)), s.card = k →
    ∃ f : Fin n → ℕ, (∀ i ∈ s, f i < k) ∧ (∀ i ∈ s, ∀ i' ∈ s, f i = f i' → i = i') ∧
      2 * Cf n F f s = Ef n F s ∧
      ∀ h, 1 < h → h ≤ k →
        h * Cf n F f (s.filter (fun i => f i < h - 1)) ≤
          (h - 2) * Cf n F f (s.filter (fun i => f i < h)) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [Finset.card_eq_zero] at hs
    subst hs
    refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact absurd hi (Finset.notMem_empty i)
    · intro i hi
      exact absurd hi (Finset.notMem_empty i)
    · simp [Cf, Ef]
    · intro h h1 h2
      omega
  | succ k ih =>
    intro s hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image s
      (fun u => (s.filter (fun u' => F u u' ≠ F u' u)).card) hne
    obtain ⟨s', hs'⟩ : ∃ s' : Finset (Fin n), s' = s.erase v := ⟨_, rfl⟩
    have hvs' : v ∉ s' := by
      rw [hs']
      exact Finset.notMem_erase v s
    have hins : insert v s' = s := by
      rw [hs']
      exact Finset.insert_erase hv
    have hcard' : s'.card = k := by
      rw [hs', Finset.card_erase_of_mem hv, hs]
      omega
    obtain ⟨f', hb', hinj', h2', hpeel'⟩ := ih s' hcard'
    obtain ⟨f, hf⟩ : ∃ f : Fin n → ℕ, ∀ i, f i = if i = v then k else f' i :=
      ⟨_, fun _ => rfl⟩
    have hfv : f v = k := by rw [hf, if_pos rfl]
    have hfs' : ∀ i ∈ s', f i = f' i := by
      intro i hi
      rw [hf, if_neg]
      rintro rfl
      exact hvs' hi
    have hmem : ∀ i, i ∈ s ↔ i = v ∨ i ∈ s' := by
      intro i
      rw [← hins, Finset.mem_insert]
    have hltv : ∀ u ∈ s', f u < f v := by
      intro u hu
      rw [hfs' u hu, hfv]
      exact hb' u hu
    have hC : Cf n F f s = Cf n F f' s' + (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
      rw [← hins, Cf_insert n F f s' v hvs' hltv, Cf_congr n F f f' s' hfs']
    have hE : Ef n F s = Ef n F s' + 2 * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
      rw [← hins, Ef_insert n F s' v hvs']
    have hdg : (s.filter (fun u' => F v u' ≠ F u' v)).card
        = (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
      rw [← hins, Finset.filter_insert, if_neg (fun h => h rfl)]
    have hEle : Ef n F s ≤ (k + 1) * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
      rw [← hdg, ← hs]
      unfold Ef
      have h3 := Finset.sum_le_card_nsmul s
        (fun u => (s.filter (fun u' => F u u' ≠ F u' u)).card) _ hvmax
      simpa using h3
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases (hmem i).mp hi with rfl | hi'
      · rw [hfv]
        omega
      · rw [hfs' i hi']
        have h4 := hb' i hi'
        omega
    · intro i hi i' hi' hff
      rcases (hmem i).mp hi with h1 | h1 <;> rcases (hmem i').mp hi' with h2 | h2
      · rw [h1, h2]
      · rw [h1, hfv, hfs' i' h2] at hff
        have h4 := hb' i' h2
        omega
      · rw [h2, hfv, hfs' i h1] at hff
        have h4 := hb' i h1
        omega
      · rw [hfs' i h1, hfs' i' h2] at hff
        exact hinj' i h1 i' h2 hff
    · rw [hC, hE]
      omega
    · intro h h1 hle
      by_cases hk : h ≤ k
      · have hset : ∀ c, c ≤ k →
            s.filter (fun i => f i < c) = s'.filter (fun i => f' i < c) := by
          intro c hc
          ext i
          rw [Finset.mem_filter, Finset.mem_filter, hmem]
          constructor
          · rintro ⟨hi | hi, hlt⟩
            · rw [hi, hfv] at hlt
              omega
            · exact ⟨hi, by rw [← hfs' i hi]; exact hlt⟩
          · rintro ⟨hi, hlt⟩
            exact ⟨Or.inr hi, by rw [hfs' i hi]; exact hlt⟩
        rw [hset (h-1) (by omega), hset h hk,
          Cf_congr n F f f' (s'.filter (fun i => f' i < h - 1))
            (fun i hi => hfs' i (Finset.mem_filter.mp hi).1),
          Cf_congr n F f f' (s'.filter (fun i => f' i < h))
            (fun i hi => hfs' i (Finset.mem_filter.mp hi).1)]
        exact hpeel' h h1 hk
      · have hh : h = k + 1 := by omega
        rw [hh]
        have hset1 : s.filter (fun i => f i < k + 1) = s := by
          apply Finset.filter_true_of_mem
          intro i hi
          rcases (hmem i).mp hi with hi' | hi'
          · rw [hi', hfv]
            omega
          · rw [hfs' i hi']
            have h4 := hb' i hi'
            omega
        have hset0 : s.filter (fun i => f i < k + 1 - 1) = s' := by
          ext i
          rw [Finset.mem_filter, hmem]
          constructor
          · rintro ⟨hi | hi, hlt⟩
            · rw [hi, hfv] at hlt
              omega
            · exact hi
          · intro hi
            refine ⟨Or.inr hi, ?_⟩
            rw [hfs' i hi]
            have h4 := hb' i hi
            omega
        rw [hset1, hset0, Cf_congr n F f f' s' hfs', hC]
        have hk1 : 1 ≤ k := by omega
        rw [hE] at hEle
        have e : (k + 1) * (s'.filter (fun u' => F v u' ≠ F u' v)).card
            = (k - 1) * (s'.filter (fun u' => F v u' ≠ F u' v)).card
              + 2 * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
          obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [hk']
          have e0 : k' + 1 - 1 = k' := by omega
          rw [e0]
          ring
        have c1 : 2 * Cf n F f' s' ≤ (k - 1) * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
          omega
        have e2 : (k + 1) * Cf n F f' s' = (k - 1) * Cf n F f' s' + 2 * Cf n F f' s' := by
          obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [hk']
          have e0 : k' + 1 - 1 = k' := by omega
          rw [e0]
          ring
        have e3 : (k + 1 - 2) * (Cf n F f' s' + (s'.filter (fun u' => F v u' ≠ F u' v)).card)
            = (k - 1) * Cf n F f' s'
              + (k - 1) * (s'.filter (fun u' => F v u' ≠ F u' v)).card := by
          have e0 : k + 1 - 2 = k - 1 := by omega
          rw [e0]
          ring
        omega

theorem pair_eq (n : ℕ) (z1 z2 x y : Fin n)
    (h : ({z1, z2} : Finset (Fin n)) = {x, y}) (hx : x = z1) : y = z2 := by
  subst hx
  have hy : y ∈ ({x, z2} : Finset (Fin n)) := by
    rw [h]
    simp
  have hz : z2 ∈ ({x, y} : Finset (Fin n)) := by
    rw [← h]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with hy | hy
  · rcases hz with hz | hz
    · rw [hy, hz]
    · exact hz.symm
  · exact hy

theorem evalD1 (n : ℕ) (F : Fin n → Fin n → Bool) (f : Fin n → ℕ) (z1 z2 : Fin n) :
    decide (∃ x y, ({z1, z2} : Finset (Fin n)) = {x, y} ∧
      (({z1} : Finset (Fin n)) = {x} ∨ (({z1} : Finset (Fin n)) = ∅ ∧ f x ≤ f y)) ∧
      F x y = true) = F z1 z2 := by
  by_cases hF : F z1 z2 = true
  · rw [hF]
    exact decide_eq_true ⟨z1, z2, rfl, Or.inl rfl, hF⟩
  · have hF' : F z1 z2 = false := by simpa using hF
    rw [hF']
    apply decide_eq_false
    rintro ⟨x, y, hP, hs | hs, hxy⟩
    · have hx : x = z1 := (Finset.singleton_inj.mp hs).symm
      have hy := pair_eq n z1 z2 x y hP hx
      rw [hx, hy] at hxy
      exact hF hxy
    · exact Finset.singleton_ne_empty z1 hs.1

theorem evalD0 (n : ℕ) (F : Fin n → Fin n → Bool) (f : Fin n → ℕ)
    (hinj : Function.Injective f) (z1 z2 : Fin n) (hle : f z1 ≤ f z2) :
    decide (∃ x y, ({z1, z2} : Finset (Fin n)) = {x, y} ∧
      ((∅ : Finset (Fin n)) = {x} ∨ ((∅ : Finset (Fin n)) = ∅ ∧ f x ≤ f y)) ∧
      F x y = true) = F z1 z2 := by
  by_cases hF : F z1 z2 = true
  · rw [hF]
    exact decide_eq_true ⟨z1, z2, rfl, Or.inr ⟨rfl, hle⟩, hF⟩
  · have hF' : F z1 z2 = false := by simpa using hF
    rw [hF']
    apply decide_eq_false
    rintro ⟨x, y, hP, hs | ⟨-, hxy'⟩, hxy⟩
    · exact Finset.singleton_ne_empty x hs.symm
    · have hx : x ∈ ({z1, z2} : Finset (Fin n)) := by
        rw [hP]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · have hy := pair_eq n z1 z2 x y hP hx
        rw [hx, hy] at hxy
        exact hF hxy
      · have hP' : ({z2, z1} : Finset (Fin n)) = {x, y} := by
          rw [Finset.pair_comm]
          exact hP
        have hy := pair_eq n z2 z1 x y hP' hx
        rw [hx, hy] at hxy'
        have heq : z1 = z2 := hinj (le_antisymm hle hxy')
        subst heq
        rw [hx, hy] at hxy
        exact hF hxy

theorem main : ∀ (n : ℕ) (F : Fin n → Fin n → Bool),
  ∃ order : Equiv.Perm (Fin n),
    let exposed := fun h : ℕ => Finset.univ.filter (fun i : Fin n => h ≤ (order i).val)
    let cost := fun (h : ℕ) (out : Finset (Fin n) → Finset (Fin n) → Bool) =>
      (Finset.univ.filter (fun z : Fin n × Fin n =>
        out ({z.1,z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2)).card
    ∃ D : Finset (Fin n) → Finset (Fin n) → Bool,
      (∀ h : ℕ, h ≤ n → ∀ other, cost h D ≤ cost h other) ∧
      (∀ h : ℕ, 1 < h → h ≤ n → h * cost (h-1) D ≤ (h-2) * cost h D) ∧
      (∀ h : ℕ, h ≤ n → n*(n-1)*cost h D ≤ h*(h-1)*cost n D) := by
  intro n F
  obtain ⟨f, hb, hinjOn, -, hpeel⟩ := peel n F n Finset.univ (by simp)
  have hinj : Function.Injective f :=
    fun i i' h => hinjOn i (Finset.mem_univ i) i' (Finset.mem_univ i') h
  have hg : Function.Injective (fun i : Fin n => (⟨f i, hb i (Finset.mem_univ i)⟩ : Fin n)) :=
    fun i i' h => hinj (congrArg Fin.val h)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hg), ?_⟩
  intro exposed cost
  have hexp : ∀ (h : ℕ) (z1 : Fin n),
      exposed h ∩ {z1} = if h ≤ f z1 then {z1} else ∅ := by
    intro h z1
    by_cases hc : h ≤ f z1
    · rw [if_pos hc]
      apply Finset.inter_singleton_of_mem
      show z1 ∈ Finset.univ.filter _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hc⟩
    · rw [if_neg hc]
      apply Finset.inter_singleton_of_notMem
      show z1 ∉ Finset.univ.filter _
      rw [Finset.mem_filter]
      exact fun h' => hc h'.2
  obtain ⟨D, hDdef⟩ : ∃ D : Finset (Fin n) → Finset (Fin n) → Bool, ∀ P s,
      D P s = decide (∃ x y, P = {x, y} ∧ (s = {x} ∨ (s = ∅ ∧ f x ≤ f y)) ∧ F x y = true) :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨D, ?_⟩
  have hD : ∀ (h : ℕ) (z : Fin n × Fin n),
      (D {z.1, z.2} (exposed h ∩ {z.1}) ≠ F z.1 z.2) ↔
      (f z.1 < h ∧ f z.2 < f z.1 ∧ F z.1 z.2 ≠ F z.2 z.1) := by
    rintro h ⟨z1, z2⟩
    dsimp only
    rw [hexp, hDdef]
    by_cases hc : h ≤ f z1
    · rw [if_pos hc, evalD1 n F f z1 z2]
      constructor
      · intro h'
        exact absurd rfl h'
      · rintro ⟨h', -⟩
        exact absurd h' (not_lt.mpr hc)
    · rw [if_neg hc]
      by_cases hle : f z1 ≤ f z2
      · rw [evalD0 n F f hinj z1 z2 hle]
        constructor
        · intro h'
          exact absurd rfl h'
        · rintro ⟨-, h', -⟩
          exact absurd h' (not_lt.mpr hle)
      · have hle' : f z2 ≤ f z1 := by omega
        have e := evalD0 n F f hinj z2 z1 hle'
        rw [Finset.pair_comm z2 z1] at e
        rw [e]
        constructor
        · intro h'
          exact ⟨by omega, by omega, fun e' => h' e'.symm⟩
        · rintro ⟨-, -, h'⟩
          exact fun e' => h' e'.symm
  have hcount : ∀ h, (Finset.univ.filter (fun z : Fin n × Fin n =>
      f z.1 < h ∧ f z.2 < f z.1 ∧ F z.1 z.2 ≠ F z.2 z.1)).card
      = Cf n F f (Finset.univ.filter (fun i => f i < h)) := by
    intro h
    unfold Cf
    have e1 : (Finset.univ.filter (fun z : Fin n × Fin n =>
        f z.1 < h ∧ f z.2 < f z.1 ∧ F z.1 z.2 ≠ F z.2 z.1))
        = ((Finset.univ.filter (fun i : Fin n => f i < h)) ×ˢ
            (Finset.univ.filter (fun i : Fin n => f i < h))).filter
          (fun z => f z.2 < f z.1 ∧ F z.1 z.2 ≠ F z.2 z.1) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, by omega⟩, h2, h3⟩
      · rintro ⟨⟨h1, -⟩, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [e1, Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro z1 _
    rw [Finset.card_filter]
  have hcostD : ∀ h, cost h D = Cf n F f (Finset.univ.filter (fun i => f i < h)) := by
    intro h
    rw [← hcount h]
    show (Finset.univ.filter (fun z : Fin n × Fin n =>
      D {z.1, z.2} (exposed h ∩ {z.1}) ≠ F z.1 z.2)).card = _
    congr 1
    apply Finset.filter_congr
    intro z _
    exact hD h z
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ h, c h = Cf n F f (Finset.univ.filter (fun i => f i < h)) :=
    ⟨_, fun _ => rfl⟩
  have hpeelc : ∀ h, 1 < h → h ≤ n → h * c (h - 1) ≤ (h - 2) * c h := by
    intro h h1 h2
    rw [hc, hc]
    exact hpeel h h1 h2
  have hc0 : c 0 = 0 := by
    rw [hc]
    simp [Cf]
  refine ⟨?_, ?_, ?_⟩
  · intro h hh other
    rw [hcostD h, ← hcount h]
    show _ ≤ (Finset.univ.filter (fun z : Fin n × Fin n =>
      other {z.1, z.2} (exposed h ∩ {z.1}) ≠ F z.1 z.2)).card
    have hinjφ : Set.InjOn (fun z : Fin n × Fin n =>
        if other {z.1, z.2} (exposed h ∩ {z.1}) ≠ F z.1 z.2 then z else z.swap)
        (↑(Finset.univ.filter (fun z : Fin n × Fin n =>
          f z.1 < h ∧ f z.2 < f z.1 ∧ F z.1 z.2 ≠ F z.2 z.1)) : Set (Fin n × Fin n)) := by
      rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb' hab
      have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb'' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb')).2
      dsimp only at hab ha' hb''
      by_cases h1 : other {a1, a2} (exposed h ∩ {a1}) ≠ F a1 a2 <;>
        by_cases h2 : other {b1, b2} (exposed h ∩ {b1}) ≠ F b1 b2
      · rw [if_pos h1, if_pos h2] at hab
        exact hab
      · rw [if_pos h1, if_neg h2] at hab
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hab
        rw [hab.1, hab.2] at ha'
        omega
      · rw [if_neg h1, if_pos h2] at hab
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hab
        rw [← hab.1, ← hab.2] at hb''
        omega
      · rw [if_neg h1, if_neg h2] at hab
        simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hab
        rw [hab.1, hab.2]
    rw [← Finset.card_image_of_injOn hinjφ]
    apply Finset.card_le_card
    rw [Finset.image_subset_iff]
    rintro ⟨a1, a2⟩ ha
    have ha' := (Finset.mem_filter.mp ha).2
    dsimp only at ha'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases h1 : other {a1, a2} (exposed h ∩ {a1}) ≠ F a1 a2
    · rw [if_pos h1]
      exact h1
    · rw [if_neg h1]
      have h1' : other {a1, a2} (exposed h ∩ {a1}) = F a1 a2 := by
        by_contra hne
        exact h1 hne
      rw [hexp, if_neg (by omega)] at h1'
      show other {a2, a1} (exposed h ∩ {a2}) ≠ F a2 a1
      rw [hexp, if_neg (by omega), Finset.pair_comm a2 a1, h1']
      exact ha'.2.2
  · intro h h1 hh
    rw [hcostD, hcostD, ← hc, ← hc]
    exact hpeelc h h1 hh
  · intro h hh
    rw [hcostD, hcostD, ← hc, ← hc]
    have key : ∀ k h, h + k = n → n * (n - 1) * c h ≤ h * (h - 1) * c n := by
      intro k
      induction k with
      | zero =>
        intro h hk
        have e : h = n := by omega
        rw [e]
      | succ k ih =>
        intro h hk
        have ih' := ih (h + 1) (by omega)
        rcases Nat.eq_zero_or_pos h with h0 | hpos
        · rw [h0, hc0]
          simp
        · obtain ⟨h', hh'⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
          rw [hh'] at ih' ⊢
          have hp := hpeelc (h' + 1 + 1) (by omega) (by omega)
          have e1 : h' + 1 + 1 - 1 = h' + 1 := by omega
          have e2 : h' + 1 + 1 - 2 = h' := by omega
          have e3 : h' + 1 - 1 = h' := by omega
          rw [e1, e2] at hp
          rw [e1] at ih'
          rw [e3]
          have a1 := Nat.mul_le_mul_left (n * (n - 1)) hp
          have a2 := Nat.mul_le_mul_left h' ih'
          refine Nat.le_of_mul_le_mul_left (?_ : (h' + 1 + 1) * (n * (n - 1) * c (h' + 1)) ≤
            (h' + 1 + 1) * ((h' + 1) * h' * c n)) (by omega)
          calc (h' + 1 + 1) * (n * (n - 1) * c (h' + 1))
              = n * (n - 1) * ((h' + 1 + 1) * c (h' + 1)) := by ring
            _ ≤ n * (n - 1) * (h' * c (h' + 1 + 1)) := a1
            _ = h' * (n * (n - 1) * c (h' + 1 + 1)) := by ring
            _ ≤ h' * ((h' + 1 + 1) * (h' + 1) * c n) := a2
            _ = (h' + 1 + 1) * ((h' + 1) * h' * c n) := by ring
    exact key (n - h) h (by omega)

end PEqualNP.Outside.L_lib_651_aux

theorem PEqualNP.Outside.L_lib_651 : (∀ (n : ℕ) (F : Fin n → Fin n → Bool),
  ∃ order : Equiv.Perm (Fin n),
    let exposed := fun h : ℕ => Finset.univ.filter (fun i : Fin n => h ≤ (order i).val)
    let cost := fun (h : ℕ) (out : Finset (Fin n) → Finset (Fin n) → Bool) =>
      (Finset.univ.filter (fun z : Fin n × Fin n =>
        out ({z.1,z.2} : Finset (Fin n)) (exposed h ∩ {z.1}) ≠ F z.1 z.2)).card
    ∃ D : Finset (Fin n) → Finset (Fin n) → Bool,
      (∀ h : ℕ, h ≤ n → ∀ other, cost h D ≤ cost h other) ∧
      (∀ h : ℕ, 1 < h → h ≤ n → h * cost (h-1) D ≤ (h-2) * cost h D) ∧
      (∀ h : ℕ, h ≤ n → n*(n-1)*cost h D ≤ h*(h-1)*cost n D)) := by
  exact PEqualNP.Outside.L_lib_651_aux.main
