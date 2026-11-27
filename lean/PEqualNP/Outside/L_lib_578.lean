import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_578_aux

theorem sig_card (n : ℕ) (S : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun σ => ∀ v, v ∉ S → σ v = false)).card = 2 ^ S.card := by
  rw [← Finset.card_powerset]
  symm
  apply Finset.card_bij (fun T _ => fun v => decide (v ∈ T))
  · intro T hT
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
    have h1 : v ∉ T := fun h => hv (Finset.mem_powerset.mp hT h)
    simp [h1]
  · intro T1 _ T2 _ h
    ext v
    have h1 := congrFun h v
    simpa using h1
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    refine ⟨Finset.univ.filter (fun v => σ v = true), ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro v hv
      rw [Finset.mem_filter] at hv
      by_contra hvS
      have h1 := hv.2
      rw [hσ.2 v hvS] at h1
      exact absurd h1 (by decide)
    · funext v
      simp

theorem count_diag (n l r : ℕ) (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j)
    (σ τ : Fin n → Bool)
    (hσ : ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false)
    (hτ : ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → τ v = false) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i : Fin l, decide (∀ v : ↥(L i), x v.val = σ v.val) = true) ∧
      (∀ j : Fin r, decide (∀ v : ↥(R j), x v.val = τ v.val) = true))).card
      = if σ = τ then 1 else 0 := by
  by_cases hst : σ = τ
  · subst hst
    rw [if_pos rfl, Finset.card_eq_one]
    refine ⟨σ, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      funext v
      rcases hcov v with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact h1 i ⟨v, hi⟩
      · exact h2 j ⟨v, hj⟩
    · rintro rfl
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · rw [if_neg hst, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    simp only [decide_eq_true_eq]
    rintro ⟨h1, h2⟩
    apply hst
    funext v
    by_cases hv : (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j
    · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hv
      have e1 : x v = σ v := h1 i ⟨v, hi⟩
      have e2 : x v = τ v := h2 j ⟨v, hj⟩
      exact e1.symm.trans e2
    · rw [hσ v hv, hτ v hv]

theorem lower (K : Type) [Field K] (n l r : ℕ) (L : Fin l → Finset (Fin n))
    (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (d : ℕ)
    (A : ((i : Fin l) → ((↥(L i) → Bool) → Bool)) → Fin d → K)
    (B : ((j : Fin r) → ((↥(R j) → Bool) → Bool)) → Fin d → K)
    (hAB : ∀ (p : (i : Fin l) → ((↥(L i) → Bool) → Bool))
      (q : (j : Fin r) → ((↥(R j) → Bool) → Bool)),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧
        (∀ j, q j (fun v => x v.val) = true))).card : ℕ) : K)
        = ∑ j : Fin d, A p j * B q j) :
    2 ^ ((Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)).card ≤ d := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n),
      S = Finset.univ.filter (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) := ⟨_, rfl⟩
  rw [← hS, ← sig_card n S]
  obtain ⟨Sig, hSig⟩ : ∃ Sig : Finset (Fin n → Bool),
      Sig = Finset.univ.filter (fun σ => ∀ v, v ∉ S → σ v = false) := ⟨_, rfl⟩
  rw [← hSig]
  have hmemSig : ∀ σ ∈ Sig, ∀ v, ¬ ((∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false := by
    intro σ hσ v hv
    rw [hSig, Finset.mem_filter] at hσ
    apply hσ.2 v
    rw [hS, Finset.mem_filter]
    exact fun h => hv h.2
  let A' : Matrix ↥Sig (Fin d) K :=
    fun σ k => A (fun i z => decide (∀ v : ↥(L i), z v = σ.val v.val)) k
  let B' : Matrix (Fin d) ↥Sig K :=
    fun k τ => B (fun j z => decide (∀ v : ↥(R j), z v = τ.val v.val)) k
  have hprod : A' * B' = 1 := by
    ext σ τ
    rw [Matrix.mul_apply]
    have hc := count_diag n l r L R hcov σ.val τ.val (hmemSig σ.val σ.property)
      (hmemSig τ.val τ.property)
    have h1 := hAB (fun i z => decide (∀ v : ↥(L i), z v = σ.val v.val))
      (fun j z => decide (∀ v : ↥(R j), z v = τ.val v.val))
    refine h1.symm.trans ?_
    refine (congrArg (Nat.cast : ℕ → K) hc).trans ?_
    rw [Matrix.one_apply]
    by_cases h : σ = τ
    · subst h
      simp
    · have h' : σ.val ≠ τ.val := fun e => h (Subtype.ext e)
      simp [h, h']
  have hrank : (1 : Matrix ↥Sig ↥Sig K).rank ≤ d := by
    rw [← hprod]
    refine (Matrix.rank_mul_le_left A' B').trans ?_
    have h2 := Matrix.rank_le_card_width A'
    simpa using h2
  rw [Matrix.rank_one, Fintype.card_coe] at hrank
  exact hrank

theorem fiber_card (n : ℕ) (a b : Fin n → Bool) (hcov : ∀ v, a v = true ∨ b v = true)
    (P Q : (Fin n → Bool) → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ x y : Fin n → Bool, (∀ v, a v = true → x v = y v) → (P x ↔ P y))
    (hQ : ∀ x y : Fin n → Bool, (∀ v, b v = true → x v = y v) → (Q x ↔ Q y))
    (σ : Fin n → Bool) (hσ : ∀ v, σ v = true → a v = true ∧ b v = true) :
    ((Finset.univ.filter (fun x : Fin n → Bool => P x ∧ Q x)).filter
        (fun x => (fun v => a v && b v && x v) = σ)).card
    = (Finset.univ.filter (fun x1 : Fin n → Bool =>
          (∀ v, b v = true → x1 v = σ v) ∧ P x1)).card
      * (Finset.univ.filter (fun x2 : Fin n → Bool =>
          (∀ v, a v = true → x2 v = σ v) ∧ Q x2)).card := by
  have hσa : ∀ v, a v = false → σ v = false := by
    intro v hv
    by_contra hs
    have h1 := (hσ v (by simpa using hs)).1
    rw [hv] at h1
    exact absurd h1 (by decide)
  have hσb : ∀ v, b v = false → σ v = false := by
    intro v hv
    by_contra hs
    have h1 := (hσ v (by simpa using hs)).2
    rw [hv] at h1
    exact absurd h1 (by decide)
  have keyfacts : ∀ (t1 t2 : Fin n → Bool), (∀ v, b v = true → t1 v = σ v) →
      (∀ v, a v = true → t2 v = σ v) → ∀ v,
      (a v && (t1 v || t2 v)) = t1 v ∧ (b v && (t1 v || t2 v)) = t2 v ∧
      (a v && b v && (t1 v || t2 v)) = σ v := by
    intro t1 t2 h1 h2 v
    rcases hcov v with ha | hb
    · have e2 := h2 v ha
      cases hb : b v
      · have hs := hσb v hb
        rw [hs] at e2
        simp [ha, e2, hs]
      · have e1 := h1 v hb
        simp [ha, e1, e2]
    · have e1 := h1 v hb
      cases ha : a v
      · have hs := hσa v ha
        rw [hs] at e1
        simp [hb, e1, hs]
      · have e2 := h2 v ha
        simp [hb, e1, e2]
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun x _ => ((fun v => a v && x v), (fun v => b v && x v)))
    (fun t _ => fun v => t.1 v || t.2 v) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_filter] at hx
    obtain ⟨⟨-, hPx, hQx⟩, hsx⟩ := hx
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    dsimp only
    refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_univ _, ?_, ?_⟩⟩
    · intro v hv
      rw [← hsx]
      simp [hv]
    · exact (hP _ x (fun v hv => by simp [hv])).mpr hPx
    · intro v hv
      rw [← hsx]
      simp [hv]
    · exact (hQ _ x (fun v hv => by simp [hv])).mpr hQx
  · intro t ht
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at ht
    obtain ⟨⟨-, h1, hP1⟩, ⟨-, h2, hQ2⟩⟩ := ht
    have kf := keyfacts t.1 t.2 h1 h2
    rw [Finset.mem_filter, Finset.mem_filter]
    dsimp only
    refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · refine (hP _ t.1 (fun v hv => ?_)).mpr hP1
      have h3 := (kf v).1
      rw [hv] at h3
      simpa using h3
    · refine (hQ _ t.2 (fun v hv => ?_)).mpr hQ2
      have h3 := (kf v).2.1
      rw [hv] at h3
      simpa using h3
    · funext v
      exact (kf v).2.2
  · intro x hx
    funext v
    show (a v && x v || b v && x v) = x v
    rcases hcov v with h | h
    · rw [h]
      cases x v <;> cases b v <;> rfl
    · rw [h]
      cases x v <;> cases a v <;> rfl
  · intro t ht
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at ht
    obtain ⟨⟨-, h1, hP1⟩, ⟨-, h2, hQ2⟩⟩ := ht
    have kf := keyfacts t.1 t.2 h1 h2
    apply Prod.ext
    · funext v
      exact (kf v).1
    · funext v
      exact (kf v).2.1

theorem reindex (K : Type) [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (emb : ι ↪ Fin d) (F G : ι → K) :
    ∑ k : Fin d, (∑ σ : ι, if emb σ = k then F σ else 0) *
        (∑ τ : ι, if emb τ = k then G τ else 0)
      = ∑ σ : ι, F σ * G σ := by
  have hB : ∀ σ : ι, (∑ τ : ι, if emb τ = emb σ then G τ else 0) = G σ := by
    intro σ
    simp only [emb.injective.eq_iff]
    simp
  calc ∑ k : Fin d, (∑ σ : ι, if emb σ = k then F σ else 0) *
        (∑ τ : ι, if emb τ = k then G τ else 0)
      = ∑ k : Fin d, ∑ σ : ι,
          (if emb σ = k then F σ * (∑ τ : ι, if emb τ = k then G τ else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro σ _
        by_cases h : emb σ = k
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul]
    _ = ∑ σ : ι, ∑ k : Fin d,
          (if emb σ = k then F σ * (∑ τ : ι, if emb τ = k then G τ else 0) else 0) :=
        Finset.sum_comm
    _ = ∑ σ : ι, F σ * G σ := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hB]

theorem upper (K : Type) [Field K] (n l r : ℕ) (L : Fin l → Finset (Fin n))
    (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (d : ℕ)
    (hd : 2 ^ ((Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)).card ≤ d) :
    ∃ (A : ((i : Fin l) → ((↥(L i) → Bool) → Bool)) → Fin d → K)
      (B : ((j : Fin r) → ((↥(R j) → Bool) → Bool)) → Fin d → K),
      ∀ (p : (i : Fin l) → ((↥(L i) → Bool) → Bool))
        (q : (j : Fin r) → ((↥(R j) → Bool) → Bool)),
      ((((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧
        (∀ j, q j (fun v => x v.val) = true))).card : ℕ) : K)
        = ∑ j : Fin d, A p j * B q j := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin n → Bool, ∀ v, a v = true ↔ ∃ i, v ∈ L i :=
    ⟨fun v => decide (∃ i, v ∈ L i), fun v => by simp⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n → Bool, ∀ v, b v = true ↔ ∃ j, v ∈ R j :=
    ⟨fun v => decide (∃ j, v ∈ R j), fun v => by simp⟩
  have hcov' : ∀ v, a v = true ∨ b v = true :=
    fun v => (hcov v).imp (ha v).mpr (hb v).mpr
  obtain ⟨Sig, hSig⟩ : ∃ Sig : Finset (Fin n → Bool),
      Sig = Finset.univ.filter (fun σ : Fin n → Bool =>
        ∀ v, v ∉ (Finset.univ : Finset (Fin n)).filter
          (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j) → σ v = false) := ⟨_, rfl⟩
  have hSigcard : Fintype.card ↥Sig ≤ Fintype.card (Fin d) := by
    rw [Fintype.card_coe, Fintype.card_fin, hSig, sig_card]
    exact hd
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hSigcard
  have hSigmem : ∀ σ ∈ Sig, ∀ v, σ v = true → a v = true ∧ b v = true := by
    intro σ hσ v hv
    rw [hSig, Finset.mem_filter] at hσ
    by_contra hcon
    have h1 := hσ.2 v (by
      rw [Finset.mem_filter]
      rintro ⟨-, h2⟩
      exact hcon ⟨(ha v).mpr h2.1, (hb v).mpr h2.2⟩)
    rw [h1] at hv
    exact absurd hv (by decide)
  refine ⟨fun p k => ∑ σ : ↥Sig, if emb σ = k then
      (((Finset.univ.filter (fun x1 : Fin n → Bool => (∀ v, b v = true → x1 v = σ.val v) ∧
        ∀ i, p i (fun v => x1 v.val) = true)).card : ℕ) : K) else 0,
    fun q k => ∑ τ : ↥Sig, if emb τ = k then
      (((Finset.univ.filter (fun x2 : Fin n → Bool => (∀ v, a v = true → x2 v = τ.val v) ∧
        ∀ j, q j (fun v => x2 v.val) = true)).card : ℕ) : K) else 0, ?_⟩
  intro p q
  have hP : ∀ x y : Fin n → Bool, (∀ v, a v = true → x v = y v) →
      ((∀ i, p i (fun v => x v.val) = true) ↔ (∀ i, p i (fun v => y v.val) = true)) := by
    intro x y hxy
    have h1 : ∀ i, (fun v : ↥(L i) => x v.val) = (fun v : ↥(L i) => y v.val) :=
      fun i => funext (fun v => hxy v.val ((ha v.val).mpr ⟨i, v.property⟩))
    simp only [h1]
  have hQ : ∀ x y : Fin n → Bool, (∀ v, b v = true → x v = y v) →
      ((∀ j, q j (fun v => x v.val) = true) ↔ (∀ j, q j (fun v => y v.val) = true)) := by
    intro x y hxy
    have h1 : ∀ j, (fun v : ↥(R j) => x v.val) = (fun v : ↥(R j) => y v.val) :=
      fun j => funext (fun v => hxy v.val ((hb v.val).mpr ⟨j, v.property⟩))
    simp only [h1]
  rw [reindex K d emb]
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun (x : Fin n → Bool) => (fun v => a v && b v && x v))
    (s := Finset.univ.filter (fun x : Fin n → Bool =>
      (∀ i, p i (fun v => x v.val) = true) ∧ (∀ j, q j (fun v => x v.val) = true)))
    (t := Sig) (by
      intro x _
      rw [Finset.mem_coe, hSig, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
      rw [Finset.mem_filter] at hv
      have h3 : ¬ (a v = true ∧ b v = true) :=
        fun h => hv ⟨Finset.mem_univ _, (ha v).mp h.1, (hb v).mp h.2⟩
      show (a v && b v && x v) = false
      cases hav : a v <;> cases hbv : b v <;> simp_all)
  rw [hfib, Nat.cast_sum, ← Finset.sum_coe_sort Sig]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Nat.cast_mul]
  congr 1
  exact @fiber_card n a b hcov' (fun x => ∀ i, p i (fun v => x v.val) = true)
    (fun x => ∀ j, q j (fun v => x v.val) = true) _ _ hP hQ σ.val (hSigmem σ.val σ.property)

theorem main : ∀ (K : Type) [Field K] (n l r : ℕ)
  (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)),
  (∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) →
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
  let Left := (i : Fin l) → ((↥(L i) → Bool) → Bool)
  let Right := (j : Fin r) → ((↥(R j) → Bool) → Bool)
  let count := fun (p : Left) (q : Right) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧
      (∀ j, q j (fun v => x v.val) = true))).card
  ∀ d : ℕ,
    (∃ (A : Left → Fin d → K) (B : Right → Fin d → K),
      ∀ p q, (count p q : K) = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ S.card ≤ d := by
  intro K _ n l r L R hcov S Left Right count d
  constructor
  · rintro ⟨A, B, hAB⟩
    exact lower K n l r L R hcov d A B hAB
  · intro hd
    exact upper K n l r L R hcov d hd

end PEqualNP.Outside.L_lib_578_aux

theorem PEqualNP.Outside.L_lib_578 : (∀ (K : Type) [Field K] (n l r : ℕ)
  (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)),
  (∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) →
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
  let Left := (i : Fin l) → ((↥(L i) → Bool) → Bool)
  let Right := (j : Fin r) → ((↥(R j) → Bool) → Bool)
  let count := fun (p : Left) (q : Right) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧
      (∀ j, q j (fun v => x v.val) = true))).card
  ∀ d : ℕ,
    (∃ (A : Left → Fin d → K) (B : Right → Fin d → K),
      ∀ p q, (count p q : K) = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ S.card ≤ d) := by
  exact PEqualNP.Outside.L_lib_578_aux.main
