import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_637_aux

def fold {n d : ℕ} (ask : Fin d → ℕ → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (x : Fin n → ZMod 2) (l : List (Fin d)) (h : ℕ) : ℕ :=
  l.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) h

theorem z2 : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide

theorem key6 : ∀ A B U W C E : ZMod 2,
    (A + U) * (B + W) + C + E = (1 + (A + B) + W + U) * A + C + (U * (A + B + W) + E) := by
  decide

theorem bit_inj (z z' : ZMod 2) (h h' : ℕ)
    (H : 2 * h + (if z = 0 then 0 else 1) = 2 * h' + (if z' = 0 then 0 else 1)) :
    h = h' ∧ z = z' := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl <;>
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z' with rfl | rfl <;>
  simp at H ⊢ <;> omega

theorem path {n d : ℕ} (ask : Fin d → ℕ → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)) :
    ∀ (l : List (Fin d)) (h : ℕ),
    ∃ qs : List ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2), qs.length ≤ l.length ∧
      ∀ w : Fin n → ZMod 2, (∀ q ∈ qs, q w = 0) → fold ask w l h = fold ask 0 l h := by
  intro l
  induction l with
  | nil =>
    intro h
    exact ⟨[], le_rfl, fun w _ => rfl⟩
  | cons j l ih =>
    intro h
    obtain ⟨qs, hlen, hqs⟩ := ih (2 * h + 0)
    refine ⟨ask j h :: qs, by simpa using hlen, ?_⟩
    intro w hw
    have h1 : ask j h w = 0 := hw _ (by simp)
    have h2 := hqs w (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have e1 : fold ask w (j :: l) h = fold ask w l (2 * h + 0) := by
      simp [fold, h1]
    have e2 : fold ask 0 (j :: l) h = fold ask 0 l (2 * h + 0) := by
      simp [fold]
    rw [e1, e2]
    exact h2

theorem dep {n : ℕ} (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a b c r : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (u v e β : ZMod 2)
    (hT : ∀ w ∈ W, (a w + u) * (b w + v) + c w + e = r w + β) :
    (∀ w ∈ W, a w = 0) ∨ (∀ w ∈ W, b w = 0) ∨ (∀ w ∈ W, a w + b w = 0) := by
  have key : ∀ w1 ∈ W, ∀ w2 ∈ W, a w1 * b w2 + a w2 * b w1 = 0 := by
    intro w1 hw1 w2 hw2
    have h12 := hT (w1 + w2) (W.add_mem hw1 hw2)
    have h1 := hT w1 hw1
    have h2 := hT w2 hw2
    have h0 := hT 0 W.zero_mem
    simp only [map_add, map_zero] at h12 h0
    linear_combination h12 - h1 - h2 + h0
  by_cases ha : ∀ w ∈ W, a w = 0
  · exact Or.inl ha
  · right
    obtain ⟨w1, hw1, ha1⟩ : ∃ w1 ∈ W, a w1 ≠ 0 := by
      by_contra hcon
      exact ha (fun w hw => by
        by_contra hne
        exact hcon ⟨w, hw, hne⟩)
    have ha1' : a w1 = 1 := z2 _ ha1
    by_cases hb : b w1 = 0
    · left
      intro w2 hw2
      have h3 := key w1 hw1 w2 hw2
      rw [ha1', hb, one_mul, mul_zero, add_zero] at h3
      exact h3
    · right
      have hb1 : b w1 = 1 := z2 _ hb
      intro w2 hw2
      have h3 := key w1 hw1 w2 hw2
      rw [ha1', hb1, one_mul, mul_one, add_comm] at h3
      exact h3

theorem fwd {n t d : ℕ} (a b c : Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (u v e : Fin t → ZMod 2) (ask : Fin d → ℕ → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (readout : ℕ → Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)) (bias : ℕ → Fin t → ZMod 2)
    (h : ∀ x i, (a i x + u i) * (b i x + v i) + c i x + e i
      = readout (fold ask x (List.finRange d) 0) i x + bias (fold ask x (List.finRange d) 0) i) :
    ∃ pick : Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick)) ≤ d := by
  obtain ⟨qs, hlen, hqs⟩ := path ask (List.finRange d) 0
  rw [List.length_finRange] at hlen
  have hW : ∀ w ∈ (⨅ k : Fin qs.length, LinearMap.ker (qs.get k) :
      Submodule (ZMod 2) (Fin n → ZMod 2)), ∀ q ∈ qs, q w = 0 := by
    intro w hw q hq
    obtain ⟨k, rfl⟩ := List.get_of_mem hq
    exact LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hw k)
  have hT : ∀ i, ∀ w ∈ (⨅ k : Fin qs.length, LinearMap.ker (qs.get k) :
      Submodule (ZMod 2) (Fin n → ZMod 2)),
      (a i w + u i) * (b i w + v i) + c i w + e i
        = readout (fold ask 0 (List.finRange d) 0) i w + bias (fold ask 0 (List.finRange d) 0) i := by
    intro i w hw
    have h3 := h w i
    rw [hqs w (hW w hw)] at h3
    exact h3
  have hex : ∀ i, ∃ p : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      (p = a i ∨ p = b i ∨ p = a i + b i) ∧
      p ∈ Submodule.span (ZMod 2) (Set.range (fun k : Fin qs.length => qs.get k)) := by
    intro i
    rcases dep _ (a i) (b i) (c i) _ (u i) (v i) (e i) _ (hT i) with h1 | h1 | h1
    · exact ⟨a i, Or.inl rfl,
        mem_span_of_iInf_ker_le_ker (fun w hw => LinearMap.mem_ker.2 (h1 w hw))⟩
    · exact ⟨b i, Or.inr (Or.inl rfl),
        mem_span_of_iInf_ker_le_ker (fun w hw => LinearMap.mem_ker.2 (h1 w hw))⟩
    · exact ⟨a i + b i, Or.inr (Or.inr rfl),
        mem_span_of_iInf_ker_le_ker (fun w hw => LinearMap.mem_ker.2 (by
          rw [LinearMap.add_apply]; exact h1 w hw))⟩
  choose pick hp1 hp2 using hex
  refine ⟨pick, hp1, ?_⟩
  have hle : Submodule.span (ZMod 2) (Set.range pick)
      ≤ Submodule.span (ZMod 2) (Set.range (fun k : Fin qs.length => qs.get k)) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hp2 i)
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick))
      ≤ Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2) (Set.range (fun k : Fin qs.length => qs.get k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin qs.length) := finrank_range_le_card _
    _ = qs.length := Fintype.card_fin _
    _ ≤ d := hlen

theorem inj {n d : ℕ} (Q : Fin d → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (x x' : Fin n → ZMod 2) : ∀ (l : List (Fin d)) (h h' : ℕ),
    fold (fun j _ => Q j) x l h = fold (fun j _ => Q j) x' l h' →
      h = h' ∧ ∀ j ∈ l, Q j x = Q j x' := by
  intro l
  induction l with
  | nil =>
    intro h h' H
    exact ⟨H, by simp⟩
  | cons j l ih =>
    intro h h' H
    have H' : fold (fun j _ => Q j) x l (2 * h + (if Q j x = 0 then 0 else 1))
        = fold (fun j _ => Q j) x' l (2 * h' + (if Q j x' = 0 then 0 else 1)) := H
    obtain ⟨h1, h2⟩ := ih _ _ H'
    obtain ⟨h3, h4⟩ := bit_inj _ _ _ _ h1
    refine ⟨h3, ?_⟩
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact h4
    · exact h2 j' hj'

theorem bwd {n t d : ℕ} (a b c : Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (u v e : Fin t → ZMod 2) (pick : Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (hpick : ∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i)
    (hrank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick)) ≤ d) :
    ∃ (ask : Fin d → ℕ → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      (readout : ℕ → Fin t → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      (bias : ℕ → Fin t → ZMod 2),
      ∀ x i, (a i x + u i) * (b i x + v i) + c i x + e i
        = readout (fold ask x (List.finRange d) 0) i x
          + bias (fold ask x (List.finRange d) 0) i := by
  obtain ⟨f0, -, hf0, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range pick)
  obtain ⟨Q, hQdef⟩ : ∃ Q : Fin d → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2),
      ∀ k : Fin (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick))),
        Q ⟨k.val, lt_of_lt_of_le k.2 hrank⟩ = f0 k :=
    ⟨fun j => if hj : j.val
        < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range pick))
      then f0 ⟨j.val, hj⟩ else 0, fun k => by simp⟩
  have hQ : ∀ x x' : Fin n → ZMod 2, (∀ j, Q j x = Q j x') → ∀ i, pick i x = pick i x' := by
    intro x x' hxx i
    have hall : ∀ s ∈ Submodule.span (ZMod 2) (Set.range f0), s x = s x' := by
      intro s hs
      induction hs using Submodule.span_induction with
      | mem s hs =>
        obtain ⟨k, rfl⟩ := hs
        rw [← hQdef k]
        exact hxx _
      | zero => simp
      | add s s' _ _ h1 h2 => simp [h1, h2]
      | smul c s _ h1 => simp [h1]
    apply hall
    rw [hf0]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hper : ∀ i, ∃ (ro : ZMod 2 → ((Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      (bi : ZMod 2 → ZMod 2),
      ∀ x, (a i x + u i) * (b i x + v i) + c i x + e i = ro (pick i x) x + bi (pick i x) := by
    intro i
    rcases hpick i with h | h | h
    · refine ⟨fun z => (z + u i) • b i + c i, fun z => (z + u i) * v i + e i, ?_⟩
      intro x
      simp only [h, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · refine ⟨fun z => (z + v i) • a i + c i, fun z => u i * (z + v i) + e i, ?_⟩
      intro x
      simp only [h, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · refine ⟨fun z => (1 + z + v i + u i) • a i + c i, fun z => u i * (z + v i) + e i, ?_⟩
      intro x
      simp only [h, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      exact key6 (a i x) (b i x) (u i) (v i) (c i x) (e i)
  choose ro bi hrb using hper
  classical
  refine ⟨fun j _ => Q j,
    fun h i => ro i (if hx : ∃ x : Fin n → ZMod 2,
      fold (fun j _ => Q j) x (List.finRange d) 0 = h then pick i (Classical.choose hx) else 0),
    fun h i => bi i (if hx : ∃ x : Fin n → ZMod 2,
      fold (fun j _ => Q j) x (List.finRange d) 0 = h then pick i (Classical.choose hx) else 0),
    ?_⟩
  intro x i
  have hx : ∃ x' : Fin n → ZMod 2, fold (fun j _ => Q j) x' (List.finRange d) 0
      = fold (fun j _ => Q j) x (List.finRange d) 0 := ⟨x, rfl⟩
  have hs := Classical.choose_spec hx
  have hj := (inj Q _ _ (List.finRange d) 0 0 hs).2
  have hp : pick i (Classical.choose hx) = pick i x :=
    hQ _ _ (fun j => hj j (List.mem_finRange j)) i
  have hd : (if hx : ∃ x' : Fin n → ZMod 2, fold (fun j _ => Q j) x' (List.finRange d) 0
      = fold (fun j _ => Q j) x (List.finRange d) 0 then pick i (Classical.choose hx) else 0)
      = pick i x := by
    rw [dite_eq_left_of_eq_true (eq_true hx)]
    exact hp
  simp only [hd]
  exact hrb i x

theorem main : ∀ (n t d : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let D := V →ₗ[F] F
  ∀ (a b c : Fin t → D) (u v e : Fin t → F),
    let target := fun (i : Fin t) (x : V) =>
      (a i x + u i) * (b i x + v i) + c i x + e i
    let run := fun (ask : Fin d → ℕ → D) (x : V) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin t → D)
        (bias : ℕ → Fin t → F),
      ∀ x i, target i x = readout (run ask x) i x + bias (run ask x) i) ↔
    (∃ pick : Fin t → D,
      (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      Module.finrank F (Submodule.span F (Set.range pick)) ≤ d) := by
  intro n t d F V D a b c u v e target run
  constructor
  · rintro ⟨ask, readout, bias, h⟩
    exact fwd a b c u v e ask readout bias h
  · rintro ⟨pick, hpick, hrank⟩
    exact bwd a b c u v e pick hpick hrank

end PEqualNP.Outside.L_lib_637_aux

theorem PEqualNP.Outside.L_lib_637 : (∀ (n t d : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let D := V →ₗ[F] F
  ∀ (a b c : Fin t → D) (u v e : Fin t → F),
    let target := fun (i : Fin t) (x : V) =>
      (a i x + u i) * (b i x + v i) + c i x + e i
    let run := fun (ask : Fin d → ℕ → D) (x : V) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    (∃ (ask : Fin d → ℕ → D) (readout : ℕ → Fin t → D)
        (bias : ℕ → Fin t → F),
      ∀ x i, target i x = readout (run ask x) i x + bias (run ask x) i) ↔
    (∃ pick : Fin t → D,
      (∀ i, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      Module.finrank F (Submodule.span F (Set.range pick)) ≤ d)) := by
  exact PEqualNP.Outside.L_lib_637_aux.main
