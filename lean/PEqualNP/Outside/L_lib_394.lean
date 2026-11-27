import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_127

namespace PEqualNP.Outside.L_lib_394_aux

theorem two_col {X : Type} [Fintype X] [DecidableEq X] (a b : X → X)
    (ha : ∀ p, a (a p) = p) (ha' : ∀ p, a p ≠ p)
    (hb : ∀ p, b (b p) = p) (hb' : ∀ p, b p ≠ p) :
    ∃ c : X → Bool, ∀ p, c (a p) ≠ c p ∧ c (b p) ≠ c p := by
  classical
  obtain ⟨A, hA, hA'⟩ : ∃ A : Equiv.Perm X, (∀ p, A p = a p) ∧ (∀ p, A⁻¹ p = a p) :=
    ⟨⟨a, a, ha, ha⟩, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨σ, hσ, hσ'⟩ : ∃ σ : Equiv.Perm X, (∀ p, σ p = a (b p)) ∧ (∀ p, σ⁻¹ p = b (a p)) :=
    ⟨⟨fun p => a (b p), fun p => b (a p),
      fun p => by show b (a (a (b p))) = p; rw [ha, hb],
      fun p => by show a (b (b (a p))) = p; rw [hb, ha]⟩, fun _ => rfl, fun _ => rfl⟩
  have hconj1 : A * σ * A⁻¹ = σ⁻¹ := by
    ext p
    simp only [Equiv.Perm.mul_apply, hA, hA', hσ, hσ', ha]
  have hconj : ∀ (j : ℤ) (p : X), a ((σ ^ j) p) = ((σ ^ j)⁻¹) (a p) := by
    intro j p
    have h2 : A * σ ^ j * A⁻¹ = (σ ^ j)⁻¹ := by rw [← conj_zpow, hconj1, inv_zpow]
    have h3 := congrArg (fun f : Equiv.Perm X => f (a p)) h2
    simp only [Equiv.Perm.mul_apply, hA, hA', ha] at h3
    exact h3
  have hinv : ∀ (τ : Equiv.Perm X) (u : X), τ (τ⁻¹ u) = u := fun τ u => τ.apply_symm_apply u
  have hns : ∀ p, ¬ σ.SameCycle p (a p) := by
    rintro p ⟨i, hi⟩
    rcases Int.even_or_odd' i with ⟨j, rfl | rfl⟩
    · have h1 : (σ ^ (2 * j)) p = (σ ^ j) ((σ ^ j) p) := by
        rw [two_mul, zpow_add, Equiv.Perm.mul_apply]
      rw [h1] at hi
      have h2 := hconj j ((σ ^ j) p)
      rw [hi, ha] at h2
      have h3 := congrArg (σ ^ j) h2
      rw [hinv] at h3
      exact ha' _ h3.symm
    · have h1 : (σ ^ (2 * j + 1)) p = (σ ^ j) (σ ((σ ^ j) p)) := by
        have e : (2 * j + 1 : ℤ) = j + (1 + j) := by ring
        rw [e, zpow_add, zpow_add, zpow_one]
        rfl
      rw [h1] at hi
      have h2 := hconj j (σ ((σ ^ j) p))
      rw [hi, ha] at h2
      have h3 := congrArg (σ ^ j) h2
      rw [hinv] at h3
      rw [hσ, ha] at h3
      exact hb' _ h3.symm
  obtain ⟨e, he⟩ : ∃ e : X → ℕ, Function.Injective e :=
    ⟨fun p => (Fintype.equivFin X p : ℕ), fun p q h => (Fintype.equivFin X).injective (Fin.ext h)⟩
  obtain ⟨m, hm⟩ : ∃ m : X → ℕ, ∀ p, m p = sInf (e '' {q | σ.SameCycle p q}) := ⟨_, fun _ => rfl⟩
  have hm_mem : ∀ p, ∃ q, σ.SameCycle p q ∧ e q = m p := by
    intro p
    have hne : (e '' {q | σ.SameCycle p q}).Nonempty := ⟨e p, p, Equiv.Perm.SameCycle.refl σ p, rfl⟩
    have := Nat.sInf_mem hne
    rw [← hm p] at this
    exact this
  have hm1 : ∀ p, m (a (b p)) = m p := by
    intro p
    have hset : {q | σ.SameCycle (σ p) q} = {q | σ.SameCycle p q} := by
      ext q
      exact Equiv.Perm.sameCycle_apply_left
    rw [← hσ, hm, hm, hset]
  have hm2 : ∀ p, m (a p) ≠ m p := by
    intro p h
    obtain ⟨q, hq, hq'⟩ := hm_mem p
    obtain ⟨q', hq2, hq2'⟩ := hm_mem (a p)
    have hqq : q' = q := he (by rw [hq2', hq', h])
    subst hqq
    exact hns p (hq.trans hq2.symm)
  refine ⟨fun p => decide (m p < m (a p)), fun p => ⟨?_, ?_⟩⟩
  · have h := hm2 p
    show decide (m (a p) < m (a (a p))) ≠ decide (m p < m (a p))
    rw [ha]
    intro hc
    rw [decide_eq_decide] at hc
    omega
  · have h := hm2 p
    have h1 := hm1 p
    have h2 := hm1 (b p)
    rw [hb] at h2
    show decide (m (b p) < m (a (b p))) ≠ decide (m p < m (a p))
    intro hc
    rw [decide_eq_decide] at hc
    omega

def RF {X R : Type} (r : X → R) (n : ℕ) (x : ℕ → X → Bool) : Prop :=
  (∀ p q, r p = r q → (∀ i, i < n → x i p = x i q) → p = q) ∧
  (∀ p (v : ℕ → Bool), ∃ q, r q = r p ∧ ∀ i, i < n → x i q = v i)

def Sp {X R : Type} (r : X → R) (n : ℕ) (x : ℕ → X → Bool) (c0 : X → Bool) : Prop :=
  ∀ p q, r p = r q → (∀ i, i < n → x (i + 1) p = x (i + 1) q) → p ≠ q → c0 p ≠ c0 q

theorem partner {X R : Type} (r : X → R) (n : ℕ) (x : ℕ → X → Bool) (hx : RF r (n + 1) x) :
    ∃ a : X → X, (∀ p, a (a p) = p) ∧ (∀ p, a p ≠ p) ∧
      (∀ p q, r p = r q → (∀ i, i < n → x (i + 1) p = x (i + 1) q) → p ≠ q → q = a p) := by
  obtain ⟨hinj, hsur⟩ := hx
  choose a ha1 ha2 using fun p => hsur p (fun i => if i = 0 then !(x 0 p) else x i p)
  have h0 : ∀ p, x 0 (a p) = !(x 0 p) := fun p => by simpa using ha2 p 0 (Nat.succ_pos n)
  have hs : ∀ p i, i < n → x (i + 1) (a p) = x (i + 1) p := fun p i hi => by
    simpa using ha2 p (i + 1) (by omega)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro p
    apply hinj
    · rw [ha1, ha1]
    · intro i hi
      cases i with
      | zero => rw [h0, h0, Bool.not_not]
      | succ k => rw [hs _ k (by omega), hs _ k (by omega)]
  · intro p h
    have h1 := h0 p
    rw [h] at h1
    revert h1
    cases x 0 p <;> simp
  · intro p q hr hq hne
    have hne0 : x 0 p ≠ x 0 q := fun h0' => hne (hinj p q hr (fun i hi => by
      cases i with
      | zero => exact h0'
      | succ k => exact hq k (by omega)))
    apply hinj
    · rw [ha1]; exact hr.symm
    · intro i hi
      cases i with
      | zero =>
        rw [h0]
        revert hne0
        cases x 0 p <;> cases x 0 q <;> simp
      | succ k =>
        rw [hs p k (by omega)]
        exact (hq k (by omega)).symm

theorem split {X R : Type} [Fintype X] [DecidableEq X] (r : X → R) (n : ℕ) (x y : ℕ → X → Bool)
    (hx : RF r (n + 1) x) (hy : RF r (n + 1) y) :
    ∃ c0 : X → Bool, Sp r n x c0 ∧ Sp r n y c0 := by
  obtain ⟨a, a1, a2, a3⟩ := partner r n x hx
  obtain ⟨b, b1, b2, b3⟩ := partner r n y hy
  obtain ⟨c, hc⟩ := two_col a b a1 a2 b1 b2
  refine ⟨c, ?_, ?_⟩
  · intro p q hr hq hne h
    have hqa := a3 p q hr hq hne
    rw [hqa] at h
    exact (hc p).1 h.symm
  · intro p q hr hq hne h
    have hqb := b3 p q hr hq hne
    rw [hqb] at h
    exact (hc p).2 h.symm

theorem down {X R : Type} (r : X → R) (n : ℕ) (x : ℕ → X → Bool) (c0 : X → Bool)
    (hx : RF r (n + 1) x) (hs : Sp r n x c0) :
    RF (fun p => (r p, c0 p)) n (fun i => x (i + 1)) := by
  refine ⟨?_, ?_⟩
  · intro p q hr hq
    by_contra hne
    have h1 : r p = r q := congrArg Prod.fst hr
    have h2 : c0 p = c0 q := congrArg Prod.snd hr
    exact hs p q h1 hq hne h2
  · intro p v
    obtain ⟨q1, hq1, hv1⟩ := hx.2 p (fun i => if i = 0 then false else v (i - 1))
    obtain ⟨q2, hq2, hv2⟩ := hx.2 p (fun i => if i = 0 then true else v (i - 1))
    have e1 : ∀ i, i < n → x (i + 1) q1 = v i := fun i hi => by
      simpa using hv1 (i + 1) (by omega)
    have e2 : ∀ i, i < n → x (i + 1) q2 = v i := fun i hi => by
      simpa using hv2 (i + 1) (by omega)
    have z1 : x 0 q1 = false := by simpa using hv1 0 (by omega)
    have z2 : x 0 q2 = true := by simpa using hv2 0 (by omega)
    have hne : q1 ≠ q2 := by
      intro h
      rw [h, z2] at z1
      cases z1
    have hc := hs q1 q2 (hq1.trans hq2.symm) (fun i hi => (e1 i hi).trans (e2 i hi).symm) hne
    by_cases h : c0 q1 = c0 p
    · exact ⟨q1, Prod.ext hq1 h, e1⟩
    · refine ⟨q2, Prod.ext hq2 ?_, e2⟩
      show c0 q2 = c0 p
      revert hc h
      cases c0 q1 <;> cases c0 q2 <;> cases c0 p <;> simp

theorem flip {X R : Type} (r : X → R) (n : ℕ) (x : ℕ → X → Bool) (c0 : X → Bool)
    (hx : RF r (n + 1) x) (hs : Sp r n x c0) : ∀ p, ∃ p', r p' = r p ∧ c0 p' ≠ c0 p := by
  intro p
  obtain ⟨q, hq, hv⟩ := hx.2 p (fun i => if i = 0 then !(x 0 p) else x i p)
  have z : x 0 q = !(x 0 p) := by simpa using hv 0 (by omega)
  have e : ∀ i, i < n → x (i + 1) q = x (i + 1) p := fun i hi => by
    simpa using hv (i + 1) (by omega)
  have hne : q ≠ p := by
    intro h
    rw [h] at z
    revert z
    cases x 0 p <;> simp
  exact ⟨q, hq, hs q p hq e hne⟩

theorem up {X R : Type} (r : X → R) (n : ℕ) (c0 : X → Bool) (z w : ℕ → X → Bool)
    (hz : RF (fun p => (r p, c0 p)) n z)
    (hf : ∀ p, ∃ p', r p' = r p ∧ c0 p' ≠ c0 p)
    (hw0 : w 0 = c0) (hws : ∀ i, w (i + 1) = z i) : RF r (n + 1) w := by
  refine ⟨?_, ?_⟩
  · intro p q hr hq
    apply hz.1 p q
    · have h0 := hq 0 (by omega)
      rw [hw0] at h0
      exact Prod.ext hr h0
    · intro i hi
      have h1 := hq (i + 1) (by omega)
      rw [hws] at h1
      exact h1
  · intro p v
    have hp : ∃ p', r p' = r p ∧ c0 p' = v 0 := by
      by_cases h : c0 p = v 0
      · exact ⟨p, rfl, h⟩
      · obtain ⟨p', h1, h2⟩ := hf p
        refine ⟨p', h1, ?_⟩
        revert h h2
        cases c0 p <;> cases c0 p' <;> cases v 0 <;> simp
    obtain ⟨p', h1, h2⟩ := hp
    obtain ⟨q, hq, hv⟩ := hz.2 p' (fun i => v (i + 1))
    have h3 : r q = r p' := congrArg Prod.fst hq
    have h4 : c0 q = c0 p' := congrArg Prod.snd hq
    refine ⟨q, h3.trans h1, ?_⟩
    intro i hi
    cases i with
    | zero => rw [hw0]; exact h4.trans h2
    | succ k => rw [hws]; exact hv k (by omega)

theorem bgt {X : Type} [Fintype X] [DecidableEq X] :
    ∀ (n : ℕ) {R : Type} (r : X → R) (x y : ℕ → X → Bool),
    RF r n x → RF r n y → ∃ c : ℕ → X → Bool, ∀ k, k ≤ n →
      RF r n (fun i => if i < k then c i else x i) ∧
      RF r n (fun i => if i < k then c i else y i) := by
  intro n
  induction n with
  | zero =>
    intro R r x y hx hy
    refine ⟨x, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using And.intro hx hy
  | succ n ih =>
    intro R r x y hx hy
    obtain ⟨c0, sx, sy⟩ := split r n x y hx hy
    obtain ⟨c', hc'⟩ := ih (fun p => (r p, c0 p)) (fun i => x (i + 1)) (fun i => y (i + 1))
      (down r n x c0 hx sx) (down r n y c0 hy sy)
    refine ⟨fun i => if i = 0 then c0 else c' (i - 1), fun k hk => ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simpa using And.intro hx hy
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      obtain ⟨h1, h2⟩ := hc' k' (by omega)
      refine ⟨up r n c0 _ _ h1 (flip r n x c0 hx sx) ?_ ?_,
        up r n c0 _ _ h2 (flip r n y c0 hy sy) ?_ ?_⟩
      · simp
      · intro i; simp
      · simp
      · intro i; simp

theorem rev {X R : Type} (r : X → R) (n : ℕ) (y : ℕ → X → Bool) (hy : RF r n y) :
    RF r n (fun i => y (n - 1 - i)) := by
  refine ⟨?_, ?_⟩
  · intro p q hr hq
    apply hy.1 p q hr
    intro i hi
    have h1 : y (n - 1 - (n - 1 - i)) p = y (n - 1 - (n - 1 - i)) q := hq (n - 1 - i) (by omega)
    have e : n - 1 - (n - 1 - i) = i := by omega
    rw [e] at h1
    exact h1
  · intro p v
    obtain ⟨q, hq, hv⟩ := hy.2 p (fun i => v (n - 1 - i))
    refine ⟨q, hq, fun i hi => ?_⟩
    have h1 : y (n - 1 - i) q = v (n - 1 - (n - 1 - i)) := hv (n - 1 - i) (by omega)
    have e : n - 1 - (n - 1 - i) = i := by omega
    rw [e] at h1
    exact h1

theorem xc : ∀ a b a' b' : Bool, xor a b = xor a' b' → b = b' → a = a' := by decide

theorem xc' : ∀ a b a' b' : Bool, xor a b = xor a' b' → a = a' → b = b' := by decide

theorem core (d : ℕ) (perm : Equiv.Perm (Fin (d + 1) → Bool)) :
    ∃ G : ℕ → (Fin (d + 1) → Bool) → Bool,
      (∀ (x : Fin (d + 1) → Bool) (j : Fin (d + 1)), G j x = x j) ∧
      (∀ (x : Fin (d + 1) → Bool) (j : Fin (d + 1)), G (4 * (d + 1) + j) x = perm x j) ∧
      (∀ t, t ≤ 4 * (d + 1) → ∀ p q : Fin (d + 1) → Bool,
        (∀ j, j < d + 1 → G (t + j) p = G (t + j) q) → p = q) := by
  classical
  obtain ⟨r, -⟩ : ∃ r : (Fin (d + 1) → Bool) → Unit, True := ⟨fun _ => (), trivial⟩
  obtain ⟨x, hxd⟩ : ∃ x : ℕ → (Fin (d + 1) → Bool) → Bool,
      ∀ (i : ℕ) (h : i < d + 1) (p : Fin (d + 1) → Bool), x i p = p ⟨i, h⟩ :=
    ⟨fun i p => if h : i < d + 1 then p ⟨i, h⟩ else false, fun i h p => by simp [h]⟩
  obtain ⟨y, hyd⟩ : ∃ y : ℕ → (Fin (d + 1) → Bool) → Bool,
      ∀ (i : ℕ) (p : Fin (d + 1) → Bool), y i p = x i (perm p) := ⟨fun i p => x i (perm p), fun _ _ => rfl⟩
  have hx : RF r (d + 1) x := by
    refine ⟨?_, ?_⟩
    · intro p q _ h
      funext j
      have h1 := h j.val j.isLt
      rw [hxd j.val j.isLt, hxd j.val j.isLt] at h1
      exact h1
    · intro p v
      refine ⟨fun j => v j.val, rfl, ?_⟩
      intro i hi
      rw [hxd i hi]
  have hy : RF r (d + 1) y := by
    refine ⟨?_, ?_⟩
    · intro p q hr h
      apply perm.injective
      apply hx.1 (perm p) (perm q) rfl
      intro i hi
      have h1 := h i hi
      rw [hyd, hyd] at h1
      exact h1
    · intro p v
      obtain ⟨q, _, hq⟩ := hx.2 p v
      refine ⟨perm.symm q, rfl, ?_⟩
      intro i hi
      rw [hyd, Equiv.apply_symm_apply]
      exact hq i hi
  have hyr : RF r (d + 1) (fun i => y (d - i)) := by
    simpa using rev r (d + 1) y hy
  obtain ⟨c, hc⟩ := bgt (d + 1) r x (fun i => y (d - i)) hx hyr
  have hcx : ∀ k, k ≤ d + 1 → RF r (d + 1) (fun i => if i < k then c i else x i) :=
    fun k hk => (hc k hk).1
  have hcy : ∀ k, k ≤ d + 1 → RF r (d + 1) (fun i => if i < k then c i else y (d - i)) :=
    fun k hk => (hc k hk).2
  have cinj : ∀ p q : Fin (d + 1) → Bool, (∀ i, i < d + 1 → c i p = c i q) → p = q := by
    intro p q h
    apply (hcx (d + 1) le_rfl).1 p q rfl
    intro i hi
    show (if i < d + 1 then c i else x i) p = (if i < d + 1 then c i else x i) q
    rw [if_pos hi]
    exact h i hi
  obtain ⟨m, hmlo, hmhi⟩ : ∃ m : ℕ → (Fin (d + 1) → Bool) → Bool,
      (∀ (z : Fin (d + 1) → Bool) (i : ℕ), 2 * i < d → m i z = xor (c i z) (c (d - i) z)) ∧
      (∀ (z : Fin (d + 1) → Bool) (i : ℕ), ¬ 2 * i < d → m i z = c (d - i) z) :=
    ⟨fun i z => if 2 * i < d then xor (c i z) (c (d - i) z) else c (d - i) z,
      fun z i h => by simp only [if_pos h], fun z i h => by simp only [if_neg h]⟩
  obtain ⟨G, G0, G1, G2, G3, G4⟩ : ∃ G : ℕ → (Fin (d + 1) → Bool) → Bool,
      (∀ i, i < d + 1 → G i = x i) ∧
      (∀ i, i < d + 1 → G ((d + 1) + i) = c i) ∧
      (∀ i, i < d + 1 → G (2 * (d + 1) + i) = m i) ∧
      (∀ i, i < d + 1 → G (3 * (d + 1) + i) = c (d - i)) ∧
      (∀ i, G (4 * (d + 1) + i) = y i) := by
    refine ⟨fun t => if t < d + 1 then x t else if t < 2 * (d + 1) then c (t - (d + 1))
      else if t < 3 * (d + 1) then m (t - 2 * (d + 1))
      else if t < 4 * (d + 1) then c (d - (t - 3 * (d + 1))) else y (t - 4 * (d + 1)),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp only [if_pos hi]
    · intro i hi
      have h1 : ¬ ((d + 1) + i < d + 1) := by omega
      have h2 : (d + 1) + i < 2 * (d + 1) := by omega
      have h3 : (d + 1) + i - (d + 1) = i := by omega
      simp only [if_neg h1, if_pos h2, h3]
    · intro i hi
      have h1 : ¬ (2 * (d + 1) + i < d + 1) := by omega
      have h2 : ¬ (2 * (d + 1) + i < 2 * (d + 1)) := by omega
      have h3 : 2 * (d + 1) + i < 3 * (d + 1) := by omega
      have h4 : 2 * (d + 1) + i - 2 * (d + 1) = i := by omega
      simp only [if_neg h1, if_neg h2, if_pos h3, h4]
    · intro i hi
      have h1 : ¬ (3 * (d + 1) + i < d + 1) := by omega
      have h2 : ¬ (3 * (d + 1) + i < 2 * (d + 1)) := by omega
      have h3 : ¬ (3 * (d + 1) + i < 3 * (d + 1)) := by omega
      have h4 : 3 * (d + 1) + i < 4 * (d + 1) := by omega
      have h5 : 3 * (d + 1) + i - 3 * (d + 1) = i := by omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, h5]
    · intro i
      have h1 : ¬ (4 * (d + 1) + i < d + 1) := by omega
      have h2 : ¬ (4 * (d + 1) + i < 2 * (d + 1)) := by omega
      have h3 : ¬ (4 * (d + 1) + i < 3 * (d + 1)) := by omega
      have h4 : ¬ (4 * (d + 1) + i < 4 * (d + 1)) := by omega
      have h5 : 4 * (d + 1) + i - 4 * (d + 1) = i := by omega
      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, h5]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro p j
    rw [G0 j.val j.isLt, hxd j.val j.isLt]
  · intro p j
    rw [G4 j.val, hyd, hxd j.val j.isLt]
  · intro t ht p q h
    by_cases c0 : t ≤ d + 1
    · apply (hcx t c0).1 p q rfl
      intro i hi
      show (if i < t then c i else x i) p = (if i < t then c i else x i) q
      by_cases hit : i < t
      · rw [if_pos hit]
        have h1 := h (d + 1 + i - t) (by omega)
        rw [show t + (d + 1 + i - t) = (d + 1) + i by omega, G1 i hi] at h1
        exact h1
      · rw [if_neg hit]
        have h1 := h (i - t) (by omega)
        rw [show t + (i - t) = i by omega, G0 i hi] at h1
        exact h1
    · by_cases c1 : t ≤ 2 * (d + 1)
      · obtain ⟨k, rfl⟩ : ∃ k, t = (d + 1) + k := ⟨t - (d + 1), by omega⟩
        have H1 : ∀ i, k ≤ i → i < d + 1 → c i p = c i q := by
          intro i hki hi
          have h1 := h (i - k) (by omega)
          rw [show (d + 1) + k + (i - k) = (d + 1) + i by omega, G1 i hi] at h1
          exact h1
        have H2 : ∀ i, i < k → m i p = m i q := by
          intro i hik
          have h1 := h (d + 1 + i - k) (by omega)
          rw [show (d + 1) + k + (d + 1 + i - k) = 2 * (d + 1) + i by omega, G2 i (by omega)] at h1
          exact h1
        apply cinj
        intro i hi
        by_cases hik : k ≤ i
        · exact H1 i hik hi
        · by_cases h2i : 2 * i < d
          · by_cases hdk : d - i < k
            · have h3 := H2 (d - i) hdk
              rw [hmhi p (d - i) (by omega), hmhi q (d - i) (by omega),
                show d - (d - i) = i by omega] at h3
              exact h3
            · have h3 := H1 (d - i) (by omega) (by omega)
              have h4 := H2 i (by omega)
              rw [hmlo p i h2i, hmlo q i h2i] at h4
              exact xc _ _ _ _ h4 h3
          · by_cases h2j : 2 * (d - i) < d
            · have h3 := H2 (d - i) (by omega)
              rw [hmlo p (d - i) h2j, hmlo q (d - i) h2j, show d - (d - i) = i by omega] at h3
              have h4 := H2 i (by omega)
              rw [hmhi p i h2i, hmhi q i h2i] at h4
              exact xc' _ _ _ _ h3 h4
            · have h4 := H2 i (by omega)
              rw [hmhi p i h2i, hmhi q i h2i, show d - i = i by omega] at h4
              exact h4
      · by_cases c2 : t ≤ 3 * (d + 1)
        · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * (d + 1) + k := ⟨t - 2 * (d + 1), by omega⟩
          have H1 : ∀ i, k ≤ i → i < d + 1 → m i p = m i q := by
            intro i hki hi
            have h1 := h (i - k) (by omega)
            rw [show 2 * (d + 1) + k + (i - k) = 2 * (d + 1) + i by omega, G2 i hi] at h1
            exact h1
          have H2 : ∀ i, d + 1 - k ≤ i → i < d + 1 → c i p = c i q := by
            intro i hki hi
            have h1 := h (d + 1 + (d - i) - k) (by omega)
            rw [show 2 * (d + 1) + k + (d + 1 + (d - i) - k) = 3 * (d + 1) + (d - i) by omega,
              G3 (d - i) (by omega), show d - (d - i) = i by omega] at h1
            exact h1
          apply cinj
          intro i hi
          by_cases hik : d + 1 - k ≤ i
          · exact H2 i hik hi
          · have h3 := H1 (d - i) (by omega) (by omega)
            by_cases h2j : 2 * (d - i) < d
            · rw [hmlo p (d - i) h2j, hmlo q (d - i) h2j, show d - (d - i) = i by omega] at h3
              by_cases hki : k ≤ i
              · have h4 := H1 i hki hi
                rw [hmhi p i (by omega), hmhi q i (by omega)] at h4
                exact xc' _ _ _ _ h3 h4
              · have h4 := H2 (d - i) (by omega) (by omega)
                exact xc' _ _ _ _ h3 h4
            · rw [hmhi p (d - i) h2j, hmhi q (d - i) h2j, show d - (d - i) = i by omega] at h3
              exact h3
        · obtain ⟨k, rfl⟩ : ∃ k, t = 3 * (d + 1) + k := ⟨t - 3 * (d + 1), by omega⟩
          apply (hcy (d + 1 - k) (by omega)).1 p q rfl
          intro i hi
          show (if i < d + 1 - k then c i else y (d - i)) p
            = (if i < d + 1 - k then c i else y (d - i)) q
          by_cases hik : i < d + 1 - k
          · rw [if_pos hik]
            have h1 := h (d - i - k) (by omega)
            rw [show 3 * (d + 1) + k + (d - i - k) = 3 * (d + 1) + (d - i) by omega,
              G3 (d - i) (by omega), show d - (d - i) = i by omega] at h1
            exact h1
          · rw [if_neg hik]
            have h1 := h (d + 1 + (d - i) - k) (by omega)
            rw [show 3 * (d + 1) + k + (d + 1 + (d - i) - k) = 4 * (d + 1) + (d - i) by omega,
              G4 (d - i)] at h1
            exact h1

theorem decode (d : ℕ) (perm : (Fin (d + 1) → Bool) → (Fin (d + 1) → Bool))
    (G : ℕ → (Fin (d + 1) → Bool) → Bool)
    (hG0 : ∀ (x : Fin (d + 1) → Bool) (j : Fin (d + 1)), G j x = x j)
    (hG4 : ∀ (x : Fin (d + 1) → Bool) (j : Fin (d + 1)), G (4 * (d + 1) + j) x = perm x j)
    (hW : ∀ t, t ≤ 4 * (d + 1) → ∀ p q : Fin (d + 1) → Bool,
      (∀ j, j < d + 1 → G (t + j) p = G (t + j) q) → p = q) :
    ∃ control : Fin (4 * (d + 1)) → (Fin d → Bool) → Bool,
      ∀ x : Fin (d + 1) → Bool, (List.finRange (4 * (d + 1))).foldl
        (fun (s : Fin (d + 1) → Bool) row =>
          Fin.snoc (α := fun _ : Fin (d + 1) => Bool) (fun j => s j.succ)
            (xor (s 0) (control row (fun j => s j.succ)))) x = perm x := by
  classical
  obtain ⟨ctl, hctl⟩ : ∃ ctl : ℕ → (Fin d → Bool) → Bool,
      ∀ (t : ℕ) (z : Fin d → Bool)
        (h : ∃ x : Fin (d + 1) → Bool, (fun j : Fin d => G (t + 1 + (j : ℕ)) x) = z),
        ctl t z = xor (G t h.choose) (G (t + (d + 1)) h.choose) :=
    ⟨fun t z => if h : ∃ x : Fin (d + 1) → Bool, (fun j : Fin d => G (t + 1 + (j : ℕ)) x) = z then
      xor (G t h.choose) (G (t + (d + 1)) h.choose) else false, fun t z h => dif_pos h⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin (d + 1) → Bool) → ℕ → (Fin (d + 1) → Bool),
      ∀ s t, F s t = Fin.snoc (α := fun _ : Fin (d + 1) => Bool) (fun j => s j.succ)
        (xor (s 0) (ctl t (fun j => s j.succ))) := ⟨_, fun _ _ => rfl⟩
  have hstep : ∀ t, t < 4 * (d + 1) → ∀ (x s : Fin (d + 1) → Bool),
      (∀ j : Fin (d + 1), s j = G (t + (j : ℕ)) x) →
      ∀ j : Fin (d + 1), F s t j = G (t + 1 + (j : ℕ)) x := by
    intro t ht x s hs j
    have htail : (fun j : Fin d => s j.succ) = (fun j : Fin d => G (t + 1 + (j : ℕ)) x) := by
      funext i
      rw [hs i.succ]
      show G (t + ((i : ℕ) + 1)) x = G (t + 1 + (i : ℕ)) x
      rw [show t + ((i : ℕ) + 1) = t + 1 + (i : ℕ) by omega]
    have hs0 : s 0 = G t x := by
      rw [hs 0]
      simp
    have key : ∀ z : Fin d → Bool, z = (fun j : Fin d => G (t + 1 + (j : ℕ)) x) →
        xor (s 0) (ctl t z) = G (t + (d + 1)) x := by
      intro z hz
      subst hz
      have hex : ∃ x' : Fin (d + 1) → Bool,
          (fun j : Fin d => G (t + 1 + (j : ℕ)) x') = (fun j : Fin d => G (t + 1 + (j : ℕ)) x) :=
        ⟨x, rfl⟩
      rw [hctl t _ hex, hs0]
      have hch : (fun j : Fin d => G (t + 1 + (j : ℕ)) hex.choose)
          = (fun j : Fin d => G (t + 1 + (j : ℕ)) x) := hex.choose_spec
      generalize hex.choose = x' at hch ⊢
      by_cases hxx : x' = x
      · rw [hxx]
        cases G t x <;> cases G (t + (d + 1)) x <;> rfl
      · have h1 : G t x' ≠ G t x := by
          intro h
          apply hxx
          apply hW t (by omega)
          intro j hj
          rcases Nat.eq_zero_or_pos j with rfl | hpos
          · exact h
          · have h5 : G (t + 1 + (j - 1)) x' = G (t + 1 + (j - 1)) x :=
              congrFun hch ⟨j - 1, by omega⟩
            rw [show t + 1 + (j - 1) = t + j by omega] at h5
            exact h5
        have h2 : G (t + (d + 1)) x' ≠ G (t + (d + 1)) x := by
          intro h
          apply hxx
          apply hW (t + 1) (by omega)
          intro j hj
          rcases Nat.lt_or_ge j d with hjd | hjd
          · exact congrFun hch ⟨j, hjd⟩
          · rw [show t + 1 + j = t + (d + 1) by omega]
            exact h
        revert h1 h2
        cases G t x' <;> cases G (t + (d + 1)) x' <;> cases G t x <;>
          cases G (t + (d + 1)) x <;> simp
    rw [hF]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, key _ htail]
      show G (t + (d + 1)) x = G (t + 1 + d) x
      rw [show t + (d + 1) = t + 1 + d by omega]
    · rw [Fin.snoc_castSucc]
      exact congrFun htail i
  have hfold : ∀ n, n ≤ 4 * (d + 1) → ∀ x : Fin (d + 1) → Bool,
      (List.range n).foldl F x = (fun j : Fin (d + 1) => G (n + (j : ℕ)) x) := by
    intro n
    induction n with
    | zero =>
      intro _ x
      funext j
      simp [hG0]
    | succ n ih =>
      intro hn x
      rw [List.range_succ, List.foldl_append, ih (by omega) x]
      funext j
      exact hstep n (by omega) x _ (fun _ => rfl) j
  have hmap : ∀ (l : List (Fin (4 * (d + 1)))) (s : Fin (d + 1) → Bool),
      l.foldl (fun (s : Fin (d + 1) → Bool) row =>
          Fin.snoc (α := fun _ : Fin (d + 1) => Bool) (fun j => s j.succ)
            (xor (s 0) (ctl row.val (fun j => s j.succ)))) s
        = (l.map (fun a : Fin (4 * (d + 1)) => a.val)).foldl F s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons a l ih =>
      intro s
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hF]
      exact ih _
  have hrange : (List.finRange (4 * (d + 1))).map (fun a : Fin (4 * (d + 1)) => a.val)
      = List.range (4 * (d + 1)) := List.map_coe_finRange_eq_range
  refine ⟨fun row => ctl row.val, fun x => ?_⟩
  refine (hmap (List.finRange (4 * (d + 1))) x).trans ?_
  rw [hrange, hfold _ le_rfl x]
  funext j
  exact hG4 x j

theorem main : ∀ d : ℕ,
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  ∀ perm : Equiv.Perm State,
    ∃ control : Fin (4 * w) → Tail → Bool,
      ∀ x : State, (List.finRange (4 * w)).foldl (fun (s : State) row =>
        let z : Tail := fun j => s j.succ
        Fin.snoc (α := fun _ : Fin w => Bool) z (xor (s 0) (control row z))) x = perm x := by
  intro d w State Tail perm
  obtain ⟨G, h0, h4, hW⟩ := core d perm
  exact decode d perm G h0 h4 hW

end PEqualNP.Outside.L_lib_394_aux

theorem PEqualNP.Outside.L_lib_394 : (∀ d : ℕ,
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  ∀ perm : Equiv.Perm State,
    ∃ control : Fin (4 * w) → Tail → Bool,
      ∀ x : State, (List.finRange (4 * w)).foldl (fun (s : State) row =>
        let z : Tail := fun j => s j.succ
        Fin.snoc (α := fun _ : Fin w => Bool) z (xor (s 0) (control row z))) x = perm x) := by
  exact PEqualNP.Outside.L_lib_394_aux.main
