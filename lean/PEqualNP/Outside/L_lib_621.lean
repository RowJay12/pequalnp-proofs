import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_621_aux

theorem parity_inv {α : Type} [DecidableEq α] (X : Finset α) (f : α → α)
    (hmap : ∀ a ∈ X, f a ∈ X) (hinv : ∀ a ∈ X, f (f a) = a) :
    X.card % 2 = (X.filter (fun a => f a = a)).card % 2 := by
  have hsplit : (X.filter (fun a => f a = a)).card + (X.filter (fun a => ¬ f a = a)).card
      = X.card := Finset.card_filter_add_card_filter_not _
  have hz : ((X.filter (fun a => ¬ f a = a)).card : ZMod 2) = 0 := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    apply Finset.sum_involution (fun a _ => f a)
    · intro a _
      decide
    · intro a ha _
      exact (Finset.mem_filter.1 ha).2
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨hmap a ha.1, ?_⟩
      intro h
      rw [hinv a ha.1] at h
      exact ha.2 h.symm
    · intro a ha
      exact hinv a (Finset.mem_filter.1 ha).1
  have hev : 2 ∣ (X.filter (fun a => ¬ f a = a)).card := (ZMod.natCast_eq_zero_iff _ 2).1 hz
  omega

def slots {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) :
    Finset (Fin r × Finset (Fin n)) :=
  (Finset.univ : Finset (Fin r × Finset (Fin n))).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)

def total {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (table : Finset (Fin r × Finset (Fin n))) : ℕ :=
  (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card

def cnt {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n))
    (M : Finset (Fin r × Finset (Fin n))) (g : ℕ → Bool) : ℕ :=
  (M.powerset.filter (fun T => g (total scope U T))).card

def lift1 {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U U' : Finset (Fin n))
    (A : Finset (Fin r × Finset (Fin n))) : Finset (Fin r × Finset (Fin n)) :=
  (slots scope U').filter (fun s => (s.1, s.2 ∩ U) ∈ A)

def flip {n r : ℕ} (scope : Fin r → Finset (Fin n)) (k : Fin n)
    (s : Fin r × Finset (Fin n)) : Fin r × Finset (Fin n) :=
  (s.1, symmDiff s.2 ({k} ∩ scope s.1))

def proj {n r : ℕ} (U : Finset (Fin n)) (s : Fin r × Finset (Fin n)) :
    Fin r × Finset (Fin n) := (s.1, s.2 ∩ U)

theorem flip_flip {n r : ℕ} (scope : Fin r → Finset (Fin n)) (k : Fin n)
    (s : Fin r × Finset (Fin n)) : flip scope k (flip scope k s) = s := by
  rcases s with ⟨i, S⟩
  simp only [flip]
  rw [symmDiff_symmDiff_cancel_right]

theorem sd_inter {n : ℕ} (U S B : Finset (Fin n)) (hB : ∀ a ∈ B, a ∉ U) :
    symmDiff S B ∩ U = S ∩ U := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_symmDiff]
  constructor
  · rintro ⟨h | h, hU⟩
    · exact ⟨h.1, hU⟩
    · exact absurd hU (hB a h.1)
  · rintro ⟨h, hU⟩
    exact ⟨Or.inl ⟨h, fun hb => hB a hb hU⟩, hU⟩

theorem proj_flip {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ U) (s : Fin r × Finset (Fin n)) : proj U (flip scope k s) = proj U s := by
  simp only [proj, flip]
  rw [sd_inter U s.2 ({k} ∩ scope s.1) (by
    intro a ha
    rw [Finset.mem_inter, Finset.mem_singleton] at ha
    rw [ha.1]
    exact hk)]

theorem mem_lift1 {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U U' : Finset (Fin n))
    (A : Finset (Fin r × Finset (Fin n))) (s : Fin r × Finset (Fin n)) :
    s ∈ lift1 scope U U' A ↔ s.2 ⊆ scope s.1 ∩ U' ∧ (s.1, s.2 ∩ U) ∈ A := by
  simp [lift1, slots]

theorem flip_mem {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ U) (A : Finset (Fin r × Finset (Fin n))) (s : Fin r × Finset (Fin n))
    (hs : s ∈ lift1 scope U (insert k U) A) : flip scope k s ∈ lift1 scope U (insert k U) A := by
  rw [mem_lift1] at hs ⊢
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [flip, Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_singleton] at ha
    rcases ha with ⟨h1, _⟩ | ⟨⟨h1, h2⟩, _⟩
    · exact hs.1 h1
    · rw [Finset.mem_inter]
      exact ⟨h2, by rw [h1]; exact Finset.mem_insert_self k U⟩
  · have h := proj_flip scope U k hk s
    simp only [proj] at h
    rw [h]
    exact hs.2

theorem inter_flip {n r : ℕ} (scope : Fin r → Finset (Fin n)) (k : Fin n)
    (x : Finset (Fin n)) (i : Fin r) :
    (i, symmDiff x {k} ∩ scope i) = flip scope k (i, x ∩ scope i) := by
  simp only [flip]
  congr 1
  ext a
  simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
  tauto

theorem sd_sub {n : ℕ} (U' x : Finset (Fin n)) (k : Fin n) (hk : k ∈ U') (hx : x ⊆ U') :
    symmDiff x {k} ⊆ U' := by
  intro a ha
  simp only [Finset.mem_symmDiff, Finset.mem_singleton] at ha
  rcases ha with ⟨h, _⟩ | ⟨h, _⟩
  · exact hx h
  · rw [h]
    exact hk

theorem total_flip {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U' : Finset (Fin n)) (k : Fin n)
    (hk : k ∈ U') (T : Finset (Fin r × Finset (Fin n))) :
    total scope U' (T.image (flip scope k)) = total scope U' T := by
  unfold total
  symm
  apply Finset.card_nbij' (fun x => symmDiff x {k}) (fun x => symmDiff x {k})
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hx ⊢
    refine ⟨sd_sub U' x k hk hx.1, fun i => ?_⟩
    rw [inter_flip]
    exact Finset.mem_image_of_mem _ (hx.2 i)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hy ⊢
    refine ⟨sd_sub U' y k hk hy.1, fun i => ?_⟩
    rw [inter_flip]
    obtain ⟨s, hs, hse⟩ := Finset.mem_image.1 (hy.2 i)
    rw [← hse, flip_flip]
    exact hs
  · intro x _
    exact symmDiff_symmDiff_cancel_right _ _
  · intro x _
    exact symmDiff_symmDiff_cancel_right _ _

theorem erase_inter {n : ℕ} (U x S : Finset (Fin n)) (k : Fin n) (hk : k ∉ U)
    (hx : x ⊆ insert k U) : x ∩ S ∩ U = x.erase k ∩ S := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨fun h => hk (h ▸ h3), h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h2, h3⟩, ?_⟩
    rcases Finset.mem_insert.1 (hx h2) with h | h
    · exact absurd h h1
    · exact h

theorem total_sat {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ U) (A T0 : Finset (Fin r × Finset (Fin n))) (hT0 : T0 ⊆ A) :
    total scope (insert k U)
        ((lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ T0))
      = 2 * total scope U T0 := by
  have hfilter : (insert k U).powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i)
        ∈ (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ T0))
      = (insert k U).powerset.filter
          (fun x => ∀ i : Fin r, (i, x.erase k ∩ scope i) ∈ T0) := by
    apply Finset.filter_congr
    intro x hx
    have hx' : x ⊆ insert k U := Finset.mem_powerset.1 hx
    constructor
    · intro h i
      have h1 := (Finset.mem_filter.1 (h i)).2
      simp only [proj] at h1
      rw [erase_inter U x (scope i) k hk hx'] at h1
      exact h1
    · intro h i
      have h1 := h i
      rw [← erase_inter U x (scope i) k hk hx'] at h1
      rw [Finset.mem_filter, mem_lift1]
      refine ⟨⟨?_, hT0 h1⟩, h1⟩
      intro a ha
      rw [Finset.mem_inter] at ha ⊢
      exact ⟨ha.2, hx' ha.1⟩
  unfold total
  rw [hfilter, Finset.card_filter, Finset.sum_powerset_insert hk, Finset.card_filter, two_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.erase_eq_of_notMem (fun h => hk (Finset.mem_powerset.1 ht h))]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.erase_insert (fun h => hk (Finset.mem_powerset.1 ht h))]

theorem mem_of_A {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (A : Finset (Fin r × Finset (Fin n))) (hA : A ⊆ slots scope U)
    (a : Fin r × Finset (Fin n)) (ha : a ∈ A) :
    a ∈ lift1 scope U (insert k U) A ∧ proj U a = a := by
  have h1 : a.2 ⊆ scope a.1 ∩ U := by
    have h := hA ha
    simpa [slots] using h
  have h2 : a.2 ∩ U = a.2 :=
    Finset.inter_eq_left.2 (h1.trans Finset.inter_subset_right)
  have h3 : proj U a = a := by
    simp only [proj]
    rw [h2]
  refine ⟨?_, h3⟩
  rw [mem_lift1]
  refine ⟨?_, ?_⟩
  · intro b hb
    have hb' := h1 hb
    rw [Finset.mem_inter] at hb' ⊢
    exact ⟨hb'.1, Finset.mem_insert_of_mem hb'.2⟩
  · rw [h2]
    exact ha

theorem same_proj {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (A : Finset (Fin r × Finset (Fin n))) (s s' : Fin r × Finset (Fin n))
    (hs : s ∈ lift1 scope U (insert k U) A) (hs' : s' ∈ lift1 scope U (insert k U) A)
    (hp : proj U s = proj U s') : s = s' ∨ s = flip scope k s' := by
  rcases s with ⟨i, S⟩
  rcases s' with ⟨i', S'⟩
  rw [mem_lift1] at hs hs'
  simp only [proj, Prod.mk.injEq] at hp
  obtain ⟨hi, hSU⟩ := hp
  subst hi
  have hS : S ⊆ scope i ∩ insert k U := hs.1
  have hS' : S' ⊆ scope i ∩ insert k U := hs'.1
  have hrest : ∀ a, a ≠ k → (a ∈ S ↔ a ∈ S') := by
    intro a hak
    constructor
    · intro h
      have hU : a ∈ U := by
        rcases Finset.mem_insert.1 (Finset.mem_inter.1 (hS h)).2 with h1 | h1
        · exact absurd h1 hak
        · exact h1
      have h2 : a ∈ S ∩ U := Finset.mem_inter.2 ⟨h, hU⟩
      rw [hSU] at h2
      exact (Finset.mem_inter.1 h2).1
    · intro h
      have hU : a ∈ U := by
        rcases Finset.mem_insert.1 (Finset.mem_inter.1 (hS' h)).2 with h1 | h1
        · exact absurd h1 hak
        · exact h1
      have h2 : a ∈ S' ∩ U := Finset.mem_inter.2 ⟨h, hU⟩
      rw [← hSU] at h2
      exact (Finset.mem_inter.1 h2).1
  by_cases hkk : (k ∈ S ↔ k ∈ S')
  · left
    congr 1
    ext a
    by_cases hak : a = k
    · rw [hak]
      exact hkk
    · exact hrest a hak
  · right
    simp only [flip]
    congr 1
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_inter, Finset.mem_singleton]
    by_cases hak : a = k
    · subst hak
      have hsc : a ∈ scope i := by
        by_cases h : a ∈ S
        · exact (Finset.mem_inter.1 (hS h)).1
        · have h' : a ∈ S' := by
            by_contra hn
            exact hkk ⟨fun h1 => absurd h1 h, fun h1 => absurd h1 hn⟩
          exact (Finset.mem_inter.1 (hS' h')).1
      constructor
      · intro h
        right
        exact ⟨⟨rfl, hsc⟩, fun h' => hkk ⟨fun _ => h', fun _ => h⟩⟩
      · rintro (⟨h1, h2⟩ | ⟨_, h2⟩)
        · exact absurd ⟨rfl, hsc⟩ h2
        · by_contra hn
          exact hkk ⟨fun h1 => absurd h1 hn, fun h1 => absurd h1 h2⟩
    · rw [hrest a hak]
      constructor
      · intro h
        left
        exact ⟨h, fun h' => hak h'.1⟩
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
        · exact h1
        · exact absurd h1.1 hak

theorem one_step {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ U) (A : Finset (Fin r × Finset (Fin n))) (hA : A ⊆ slots scope U)
    (g : ℕ → Bool) :
    cnt scope (insert k U) (lift1 scope U (insert k U) A) g % 2
      = cnt scope U A (fun c => g (2 * c)) % 2 := by
  have hkU : k ∈ insert k U := Finset.mem_insert_self k U
  have himg2 : ∀ T : Finset (Fin r × Finset (Fin n)),
      (T.image (flip scope k)).image (flip scope k) = T := by
    intro T
    rw [Finset.image_image]
    have h : (flip scope k) ∘ (flip scope k) = id := by
      funext s
      exact flip_flip scope k s
    rw [h, Finset.image_id]
  have hpar := parity_inv
    ((lift1 scope U (insert k U) A).powerset.filter
      (fun T => g (total scope (insert k U) T)))
    (fun T => T.image (flip scope k))
    (by
      intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      refine ⟨?_, ?_⟩
      · intro s hs
        obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.1 hs
        exact flip_mem scope U k hk A s0 (hT.1 hs0)
      · rw [total_flip scope (insert k U) k hkU T]
        exact hT.2)
    (fun T _ => himg2 T)
  unfold cnt
  rw [hpar]
  congr 1
  symm
  apply Finset.card_bij
    (fun T0 _ => (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ T0))
  · intro T0 hT0
    rw [Finset.mem_filter, Finset.mem_powerset] at hT0
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · rw [total_sat scope U k hk A T0 hT0.1]
      exact hT0.2
    · apply Finset.Subset.antisymm
      · intro s hs
        obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.1 hs
        rw [Finset.mem_filter] at hs0 ⊢
        refine ⟨flip_mem scope U k hk A s0 hs0.1, ?_⟩
        rw [proj_flip scope U k hk s0]
        exact hs0.2
      · intro s hs
        rw [Finset.mem_filter] at hs
        refine Finset.mem_image.2 ⟨flip scope k s, ?_, flip_flip scope k s⟩
        rw [Finset.mem_filter]
        refine ⟨flip_mem scope U k hk A s hs.1, ?_⟩
        rw [proj_flip scope U k hk s]
        exact hs.2
  · intro T0 hT0 T1 hT1 heq
    rw [Finset.mem_filter, Finset.mem_powerset] at hT0 hT1
    have key : ∀ (P Q : Finset (Fin r × Finset (Fin n))), P ⊆ A →
        (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ P)
          = (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ Q) → P ⊆ Q := by
      intro P Q hP hPQ a ha
      obtain ⟨h1, h2⟩ := mem_of_A scope U k A hA a (hP ha)
      have h3 : a ∈ (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ P) := by
        rw [Finset.mem_filter, h2]
        exact ⟨h1, ha⟩
      rw [hPQ, Finset.mem_filter, h2] at h3
      exact h3.2
    exact Finset.Subset.antisymm (key T0 T1 hT0.1 heq) (key T1 T0 hT1.1 heq.symm)
  · intro T hT
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hTsub, hTg⟩, hTfix⟩ := hT
    have hsat : (lift1 scope U (insert k U) A).filter (fun s => proj U s ∈ T.image (proj U))
        = T := by
      apply Finset.Subset.antisymm
      · intro s hs
        rw [Finset.mem_filter] at hs
        obtain ⟨s', hs', hpe⟩ := Finset.mem_image.1 hs.2
        rcases same_proj scope U k A s s' hs.1 (hTsub hs') hpe.symm with h | h
        · rw [h]
          exact hs'
        · rw [h, ← hTfix]
          exact Finset.mem_image_of_mem _ hs'
      · intro s hs
        rw [Finset.mem_filter]
        exact ⟨hTsub hs, Finset.mem_image_of_mem _ hs⟩
    have hsubA : T.image (proj U) ⊆ A := by
      intro a ha
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ha
      exact ((mem_lift1 scope U (insert k U) A s).1 (hTsub hs)).2
    refine ⟨T.image (proj U), ?_, hsat⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hsubA, ?_⟩
    have h2 := total_sat scope U k hk A (T.image (proj U)) hsubA
    rw [hsat] at h2
    show g (2 * total scope U (T.image (proj U))) = true
    rw [← h2]
    exact hTg

theorem lift_comp {n r : ℕ} (scope : Fin r → Finset (Fin n)) (U : Finset (Fin n)) (k : Fin n)
    (A : Finset (Fin r × Finset (Fin n))) :
    lift1 scope (insert k U) Finset.univ (lift1 scope U (insert k U) A)
      = lift1 scope U Finset.univ A := by
  ext s
  simp only [mem_lift1]
  have h1 : s.2 ∩ insert k U ∩ U = s.2 ∩ U := by
    rw [Finset.inter_assoc]
    congr 1
    exact Finset.inter_eq_right.2 (Finset.subset_insert k U)
  constructor
  · rintro ⟨hs, _, hA⟩
    rw [h1] at hA
    exact ⟨hs, hA⟩
  · rintro ⟨hs, hA⟩
    refine ⟨hs, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha ⊢
      exact ⟨(Finset.mem_inter.1 (hs ha.1)).1, ha.2⟩
    · rw [h1]
      exact hA

theorem gen {n r : ℕ} (scope : Fin r → Finset (Fin n)) :
    ∀ (d : ℕ) (U : Finset (Fin n)) (A : Finset (Fin r × Finset (Fin n))) (g : ℕ → Bool),
      n - U.card = d → A ⊆ slots scope U →
      cnt scope Finset.univ (lift1 scope U Finset.univ A) g % 2
        = cnt scope U A (fun c => g (2^(n - U.card) * c)) % 2 := by
  intro d
  induction d with
  | zero =>
    intro U A g hd hA
    have hcard : U.card = n := by
      have h := Finset.card_le_univ U
      rw [Fintype.card_fin] at h
      omega
    have hU : U = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    subst hU
    have hl : lift1 scope Finset.univ Finset.univ A = A := by
      ext s
      rw [mem_lift1]
      have e : (s.1, s.2 ∩ Finset.univ) = s := by rw [Finset.inter_univ]
      rw [e]
      constructor
      · intro h
        exact h.2
      · intro h
        refine ⟨?_, h⟩
        have h2 := hA h
        simpa [slots] using h2
    rw [hl, hcard, Nat.sub_self]
    simp
  | succ d ih =>
    intro U A g hd hA
    have hlt : U.card < n := by omega
    obtain ⟨k, hk⟩ : ∃ k, k ∉ U := by
      by_contra hcon
      have hall : ∀ k, k ∈ U := by
        intro k
        by_contra hk
        exact hcon ⟨k, hk⟩
      have hU : U = Finset.univ := Finset.eq_univ_iff_forall.2 hall
      rw [hU, Finset.card_univ, Fintype.card_fin] at hlt
      omega
    have hc : (insert k U).card = U.card + 1 := Finset.card_insert_of_notMem hk
    have h1 := ih (insert k U) (lift1 scope U (insert k U) A) g (by omega)
      (Finset.filter_subset _ _)
    rw [lift_comp] at h1
    rw [h1, one_step scope U k hk A hA]
    have hfun : (fun c => g (2 ^ (n - (insert k U).card) * (2 * c)))
        = (fun c => g (2 ^ (n - U.card) * c)) := by
      funext c
      have e : n - U.card = (n - (insert k U).card) + 1 := by omega
      rw [e, pow_succ, mul_assoc]
    rw [hfun]

theorem main : ∀ (n r : Nat) (scope : Fin r → Finset (Fin n)),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let all := (Finset.univ : Finset Site)
  let slots := fun U : Finset Site => (Finset.univ : Finset Slot).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)
  let total := fun (U : Finset Site) (table : Finset Slot) =>
    (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (U : Finset Site) (M : Finset Slot) (g : Nat → Bool) =>
    ((M.powerset.filter (fun T => g (total U T))).card).testBit 0
  ∀ (U : Finset Site) (A : Finset Slot), A ⊆ slots U →
    let lift := (slots all).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    ∀ g : Nat → Bool, coeff all lift g =
      coeff U A (fun c => g (2^(n-U.card)*c)) := by
  intro n r scope Site Slot all slots' total' coeff U A hA lift g
  have h := gen scope (n - U.card) U A g rfl hA
  show (cnt scope Finset.univ (lift1 scope U Finset.univ A) g).testBit 0
    = (cnt scope U A (fun c => g (2^(n - U.card) * c))).testBit 0
  rw [Nat.testBit_zero, Nat.testBit_zero, h]

end PEqualNP.Outside.L_lib_621_aux

theorem PEqualNP.Outside.L_lib_621 : (∀ (n r : Nat) (scope : Fin r → Finset (Fin n)),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let all := (Finset.univ : Finset Site)
  let slots := fun U : Finset Site => (Finset.univ : Finset Slot).filter
    (fun candidate => candidate.2 ⊆ scope candidate.1 ∩ U)
  let total := fun (U : Finset Site) (table : Finset Slot) =>
    (U.powerset.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (U : Finset Site) (M : Finset Slot) (g : Nat → Bool) =>
    ((M.powerset.filter (fun T => g (total U T))).card).testBit 0
  ∀ (U : Finset Site) (A : Finset Slot), A ⊆ slots U →
    let lift := (slots all).filter (fun s => (s.1, s.2 ∩ U) ∈ A)
    ∀ g : Nat → Bool, coeff all lift g =
      coeff U A (fun c => g (2^(n-U.card)*c))) := by
  exact PEqualNP.Outside.L_lib_621_aux.main
