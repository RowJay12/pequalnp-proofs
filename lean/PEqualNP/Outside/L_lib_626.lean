import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_626_aux

def Adaptive (n names q : ℕ) (P N : Finset (Fin names × (Fin n → ZMod 2))) : Prop :=
  ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2)
      → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (answers : (Fin names × (Fin n → ZMod 2)) → Fin q → ZMod 2)
    (decode : Fin names → (Fin q → ZMod 2) → Bool),
    (∀ (z : Fin names × (Fin n → ZMod 2)) (j : Fin q), answers z j =
      ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
    (∃ p ∈ P, decode p.1 (answers p) = true) ∧
    ∀ z ∈ N, decode z.1 (answers z) = false

theorem z1 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide

theorem A1 {n names q : ℕ} (P N : Finset (Fin names × (Fin n → ZMod 2)))
    (h : Adaptive n names q P N) :
    ∃ p ∈ P, ∃ Q : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2),
      ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2 := by
  obtain ⟨ask, answers, decode, hrec, ⟨p, hp, hdec⟩, hN⟩ := h
  refine ⟨p, hp, LinearMap.pi (fun j : Fin q =>
    ask j p.1 (fun i => answers p ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩)), ?_⟩
  intro z hz hname heq
  have hQ : ∀ j : Fin q,
      ask j p.1 (fun i => answers p ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2
        = ask j p.1 (fun i => answers p ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) p.2 := by
    intro j
    have h1 := congrFun heq j
    simpa [LinearMap.pi_apply] using h1
  have key : ∀ (m : ℕ) (hm : m < q), answers z ⟨m, hm⟩ = answers p ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rw [hrec z ⟨m, hm⟩, hrec p ⟨m, hm⟩, hname]
      have e : (fun i : Fin m => answers z ⟨i.val, Nat.lt_trans i.isLt hm⟩)
          = (fun i : Fin m => answers p ⟨i.val, Nat.lt_trans i.isLt hm⟩) :=
        funext (fun i => ih i.val i.isLt _)
      calc ask ⟨m, hm⟩ p.1 (fun i : Fin m => answers z ⟨i.val, Nat.lt_trans i.isLt hm⟩) z.2
          = ask ⟨m, hm⟩ p.1 (fun i : Fin m => answers p ⟨i.val, Nat.lt_trans i.isLt hm⟩) z.2 := by
            rw [e]
        _ = ask ⟨m, hm⟩ p.1 (fun i : Fin m => answers p ⟨i.val, Nat.lt_trans i.isLt hm⟩) p.2 :=
            hQ ⟨m, hm⟩
  have hall : answers z = answers p := funext (fun j => key j.val j.isLt)
  have h2 := hN z hz
  rw [hall, hname] at h2
  rw [h2] at hdec
  exact Bool.false_ne_true hdec

theorem A2 {n names q : ℕ} (P N : Finset (Fin names × (Fin n → ZMod 2)))
    (p : Fin names × (Fin n → ZMod 2)) (hp : p ∈ P)
    (Q : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2))
    (hQ : ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2) : Adaptive n names q P N := by
  refine ⟨fun j _ _ => (LinearMap.proj j).comp Q, fun z j => Q z.2 j,
    fun name ans => decide (name = p.1 ∧ ans = Q p.2), ?_, ⟨p, hp, ?_⟩, ?_⟩
  · intro z j
    rfl
  · simp
  · intro z hz
    rw [decide_eq_false_iff_not]
    rintro ⟨h1, h2⟩
    exact hQ z hz h1 h2

def fn {n : ℕ} (a : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i, a i • LinearMap.proj i

theorem fn_apply {n : ℕ} (a d : Fin n → ZMod 2) : fn a d = ∑ i, a i * d i := by
  simp [fn, LinearMap.sum_apply]

theorem half {n : ℕ} (d : Fin n → ZMod 2) (hd : d ≠ 0) :
    2 * (Finset.univ.filter (fun a : Fin n → ZMod 2 => fn a d = 0)).card = 2^n := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hd
  have hi1 : d i0 = 1 := z1 _ hi0
  have hshift : ∀ a : Fin n → ZMod 2, fn (a + Pi.single i0 1) d = fn a d + 1 := by
    intro a
    rw [fn_apply, fn_apply]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, hi1]
  have hss : ∀ a : Fin n → ZMod 2, a + Pi.single i0 1 + Pi.single i0 1 = a := by
    intro a
    have h0 : (Pi.single i0 (1:ZMod 2) : Fin n → ZMod 2) + Pi.single i0 1 = 0 := by
      funext j
      exact CharTwo.add_self_eq_zero _
    rw [add_assoc, h0, add_zero]
  have hsplit : (Finset.univ.filter (fun a : Fin n → ZMod 2 => fn a d = 0)).card
      + (Finset.univ.filter (fun a : Fin n → ZMod 2 => ¬ fn a d = 0)).card
        = (Finset.univ : Finset (Fin n → ZMod 2)).card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2^n := by
    simp [ZMod.card]
  have heq : (Finset.univ.filter (fun a : Fin n → ZMod 2 => fn a d = 0)).card
      = (Finset.univ.filter (fun a : Fin n → ZMod 2 => ¬ fn a d = 0)).card := by
    apply Finset.card_nbij' (fun a => a + Pi.single i0 1) (fun a => a + Pi.single i0 1)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hshift, ha]
      decide
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hshift, z1 _ ha]
      decide
    · intro a _
      exact hss a
    · intro a _
      exact hss a
  rw [hcard] at hsplit
  rw [← hsplit, heq]
  ring

theorem avoid {n : ℕ} : ∀ (q : ℕ) (D : Finset (Fin n → ZMod 2)), (∀ d ∈ D, d ≠ 0) →
    D.card + 1 < 2^(q+1) →
    ∃ Q : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin q → ZMod 2), ∀ d ∈ D, Q d ≠ 0 := by
  intro q
  induction q with
  | zero =>
    intro D _ hc
    have h0 : D = ∅ := by
      rw [← Finset.card_eq_zero]
      have h2 : (2:ℕ)^(0+1) = 2 := by norm_num
      rw [h2] at hc
      omega
    subst h0
    exact ⟨0, by simp⟩
  | succ q ih =>
    intro D hD hc
    obtain ⟨a, ha⟩ : ∃ a : Fin n → ZMod 2,
        (D.filter (fun d => fn a d = 0)).card + 1 < 2^(q+1) := by
      by_contra hcon
      have hcon' : ∀ a : Fin n → ZMod 2,
          2^(q+1) ≤ (D.filter (fun d => fn a d = 0)).card + 1 := by
        intro a
        by_contra h
        exact hcon ⟨a, Nat.lt_of_not_le h⟩
      have hdc : 2 * ∑ a : Fin n → ZMod 2, (D.filter (fun d => fn a d = 0)).card
          = D.card * 2^n := by
        have h1 : ∀ a : Fin n → ZMod 2, (D.filter (fun d => fn a d = 0)).card
            = ∑ d ∈ D, if fn a d = 0 then 1 else 0 := fun a => Finset.card_filter _ _
        simp_rw [h1]
        rw [Finset.sum_comm, Finset.mul_sum]
        have h2 : D.card * 2^n = ∑ _d ∈ D, 2^n := by
          rw [Finset.sum_const, smul_eq_mul]
        rw [h2]
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.card_filter]
        exact half d (hD d hd)
      have h0 : (D.filter (fun d => fn (0 : Fin n → ZMod 2) d = 0)).card = D.card := by
        congr 1
        apply Finset.filter_true_of_mem
        intro d _
        simp [fn_apply]
      have hs := Finset.add_sum_erase Finset.univ
        (fun a : Fin n → ZMod 2 => (D.filter (fun d => fn a d = 0)).card + 1)
        (Finset.mem_univ 0)
      have hlow : (Finset.univ.erase (0 : Fin n → ZMod 2)).card * 2^(q+1)
          ≤ ∑ a ∈ Finset.univ.erase (0 : Fin n → ZMod 2),
              ((D.filter (fun d => fn a d = 0)).card + 1) := by
        rw [← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum (fun a _ => hcon' a)
      have hce : (Finset.univ.erase (0 : Fin n → ZMod 2)).card + 1 = 2^n := by
        rw [Finset.card_erase_add_one (Finset.mem_univ _)]
        simp [ZMod.card]
      have hsum1 : ∑ a : Fin n → ZMod 2, ((D.filter (fun d => fn a d = 0)).card + 1)
          = ∑ a : Fin n → ZMod 2, (D.filter (fun d => fn a d = 0)).card + 2^n := by
        rw [Finset.sum_add_distrib]
        simp [ZMod.card]
      have he := hcon' 0
      rw [h0] at he
      simp only [h0] at hs
      rw [hsum1] at hs
      have hc' : D.card + 1 < 2 * 2^(q+1) := by
        have e : 2^(q+1+1) = 2 * 2^(q+1) := by ring
        rw [e] at hc
        exact hc
      have hm2 : 2 ≤ 2^(q+1) := by
        have e : 2^(q+1) = 2 * 2^q := by ring
        have hp : 0 < 2^q := by positivity
        omega
      generalize (∑ a : Fin n → ZMod 2, (D.filter (fun d => fn a d = 0)).card) = T at hdc hs
      generalize (∑ a ∈ Finset.univ.erase (0 : Fin n → ZMod 2),
        ((D.filter (fun d => fn a d = 0)).card + 1)) = S' at hs hlow
      generalize (Finset.univ.erase (0 : Fin n → ZMod 2)).card = c at hlow hce
      generalize (2:ℕ)^(q+1) = m1 at hlow he hc' hm2
      rw [← hce] at hdc hs
      generalize D.card = Dc at hdc hs he hc'
      have hx : c * (Dc + 2) ≤ c * (2 * m1) := Nat.mul_le_mul_left c (by omega)
      have hDc0 : Dc = 0 := by nlinarith
      omega
    obtain ⟨Q', hQ'⟩ := ih (D.filter (fun d => fn a d = 0))
      (fun d hd => hD d (Finset.mem_filter.1 hd).1) ha
    refine ⟨LinearMap.pi (Fin.cons (α := fun _ => (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (fn a)
      (fun j => (LinearMap.proj j).comp Q')), ?_⟩
    intro d hd hzero
    by_cases h0 : fn a d = 0
    · apply hQ' d (Finset.mem_filter.2 ⟨hd, h0⟩)
      funext j
      have h1 := congrFun hzero (Fin.succ j)
      simpa [LinearMap.pi_apply] using h1
    · apply h0
      have h1 := congrFun hzero 0
      simpa [LinearMap.pi_apply] using h1

theorem part2 {n names q : ℕ} (P N : Finset (Fin names × (Fin n → ZMod 2)))
    (p : Fin names × (Fin n → ZMod 2)) (hp : p ∈ P) (hpN : p ∉ N)
    (hcard : (N.filter (fun z => z.1 = p.1)).card + 1 < 2^(q+1)) :
    Adaptive n names q P N := by
  have hD : ∀ d ∈ (N.filter (fun z => z.1 = p.1)).image (fun z => z.2 - p.2), d ≠ 0 := by
    intro d hd h0
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hd
    rw [Finset.mem_filter] at hz
    have hzp : z = p := Prod.ext hz.2 (sub_eq_zero.1 h0)
    exact hpN (hzp ▸ hz.1)
  have hDc : ((N.filter (fun z => z.1 = p.1)).image (fun z => z.2 - p.2)).card + 1 < 2^(q+1) :=
    lt_of_le_of_lt (Nat.add_le_add_right Finset.card_image_le 1) hcard
  obtain ⟨Q, hQ⟩ := avoid q _ hD hDc
  refine A2 P N p hp Q ?_
  intro z hz hname heq
  apply hQ (z.2 - p.2) (Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, hname⟩, rfl⟩)
  rw [map_sub, heq, sub_self]

theorem part3 {n names q : ℕ} (hnames : 0 < names) (hqn : q < n) :
    ∃ P N : Finset (Fin names × (Fin n → ZMod 2)), P.card = 1 ∧ Disjoint P N ∧
      N.card + 1 = 2^(q+1) ∧ ¬ Adaptive n names q P N := by
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin (q+1) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
      Function.Injective emb := by
    refine ⟨LinearMap.pi (fun i : Fin n => if h : i.val < q+1
      then LinearMap.proj (⟨i.val, h⟩ : Fin (q+1)) else 0), ?_⟩
    intro u u' huu
    funext k
    have h1 := congrFun huu ⟨k.val, by omega⟩
    have hk : k.val ≤ q := by omega
    simpa [LinearMap.pi_apply, hk] using h1
  refine ⟨{((⟨0, hnames⟩ : Fin names), 0)},
    (Finset.univ.erase (0 : Fin (q+1) → ZMod 2)).image
      (fun u => ((⟨0, hnames⟩ : Fin names), emb u)),
    Finset.card_singleton _, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_singleton_left]
    intro hmem
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.1 hmem
    have h1 : emb u = 0 := (Prod.mk.inj hue).2
    have h2 : u = 0 := hemb (by rw [h1, map_zero])
    exact (Finset.mem_erase.1 hu).1 h2
  · rw [Finset.card_image_of_injective _ (fun u u' h => hemb (Prod.mk.inj h).2),
      Finset.card_erase_add_one (Finset.mem_univ _)]
    simp [ZMod.card]
  · intro hA
    obtain ⟨p, hp, Q, hQ⟩ := A1 _ _ hA
    rw [Finset.mem_singleton] at hp
    subst hp
    have hinj : Function.Injective (Q.comp emb) := by
      refine (injective_iff_map_eq_zero (Q.comp emb)).2 ?_
      intro u hu
      by_contra hne
      have hz : ((⟨0, hnames⟩ : Fin names), emb u)
          ∈ (Finset.univ.erase (0 : Fin (q+1) → ZMod 2)).image
            (fun u => ((⟨0, hnames⟩ : Fin names), emb u)) :=
        Finset.mem_image.2 ⟨u, Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩, rfl⟩
      apply hQ _ hz rfl
      show Q (emb u) = Q 0
      rw [map_zero]
      exact hu
    have hfr := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hfr
    omega

theorem main : ∀ (n names q : ℕ),
  let V := Fin n → ZMod 2
  let Entry := Fin names × V
  let adaptive := fun (P N : Finset Entry) =>
    ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2))
      (answers : Entry → Fin q → ZMod 2) (decode : Fin names → (Fin q → ZMod 2) → Bool),
      (∀ (z : Entry) (j : Fin q), answers z j =
        ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
      (∃ p ∈ P, decode p.1 (answers p) = true) ∧
      ∀ z ∈ N, decode z.1 (answers z) = false
  (∀ P N : Finset Entry, adaptive P N ↔
    ∃ p ∈ P, ∃ Q : V →ₗ[ZMod 2] (Fin q → ZMod 2),
      ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2) ∧
  (∀ (P N : Finset Entry) (p : Entry), p ∈ P → p ∉ N →
    (N.filter (fun z => z.1 = p.1)).card + 1 < 2 ^ (q + 1) → adaptive P N) ∧
  (0 < names → q < n →
    ∃ P N : Finset Entry, P.card = 1 ∧ Disjoint P N ∧
      N.card + 1 = 2 ^ (q + 1) ∧ ¬adaptive P N) := by
  intro n names q V Entry adaptive
  refine ⟨fun P N => ⟨fun h => A1 P N h, ?_⟩,
    fun P N p hp hpN hcard => part2 P N p hp hpN hcard,
    fun hnames hqn => part3 hnames hqn⟩
  rintro ⟨p, hp, Q, hQ⟩
  exact A2 P N p hp Q hQ

end PEqualNP.Outside.L_lib_626_aux

theorem PEqualNP.Outside.L_lib_626 : (∀ (n names q : ℕ),
  let V := Fin n → ZMod 2
  let Entry := Fin names × V
  let adaptive := fun (P N : Finset Entry) =>
    ∃ (ask : (j : Fin q) → Fin names → (Fin j.val → ZMod 2) → (V →ₗ[ZMod 2] ZMod 2))
      (answers : Entry → Fin q → ZMod 2) (decode : Fin names → (Fin q → ZMod 2) → Bool),
      (∀ (z : Entry) (j : Fin q), answers z j =
        ask j z.1 (fun i => answers z ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩) z.2) ∧
      (∃ p ∈ P, decode p.1 (answers p) = true) ∧
      ∀ z ∈ N, decode z.1 (answers z) = false
  (∀ P N : Finset Entry, adaptive P N ↔
    ∃ p ∈ P, ∃ Q : V →ₗ[ZMod 2] (Fin q → ZMod 2),
      ∀ z ∈ N, z.1 = p.1 → Q z.2 ≠ Q p.2) ∧
  (∀ (P N : Finset Entry) (p : Entry), p ∈ P → p ∉ N →
    (N.filter (fun z => z.1 = p.1)).card + 1 < 2 ^ (q + 1) → adaptive P N) ∧
  (0 < names → q < n →
    ∃ P N : Finset Entry, P.card = 1 ∧ Disjoint P N ∧
      N.card + 1 = 2 ^ (q + 1) ∧ ¬adaptive P N)) := by
  exact PEqualNP.Outside.L_lib_626_aux.main
