import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_687_aux

open PEqualNP.CircuitLowerBounds

def er (D : Finset ℕ) (v : List Bool) : List Bool :=
  ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false

def rn (D : Finset ℕ) (w : ℕ) : ℕ := w - (D.filter fun i => i < w).card

theorem lenL (D : Finset ℕ) : ∀ n : ℕ,
    ((List.range n).filter (fun i => decide (i ∉ D))).length
      = n - (D.filter (fun i => i < n)).card := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (D.filter (fun i => i < n)).card ≤ n := by
      calc (D.filter (fun i => i < n)).card ≤ (Finset.range n).card :=
            Finset.card_le_card (fun i hi => by
              rw [Finset.mem_filter] at hi
              exact Finset.mem_range.2 hi.2)
        _ = n := Finset.card_range n
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases hn : n ∈ D
    · have h2 : D.filter (fun i => i < n + 1) = insert n (D.filter (fun i => i < n)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h3⟩
          by_cases hj : j = n
          · exact Or.inl hj
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (h | ⟨h1, h3⟩)
          · exact ⟨h ▸ hn, by omega⟩
          · exact ⟨h1, by omega⟩
      rw [h2, Finset.card_insert_of_notMem (by simp)]
      simp [hn]
    · have h2 : D.filter (fun i => i < n + 1) = D.filter (fun i => i < n) := by
        ext j
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h3⟩
          refine ⟨h1, ?_⟩
          by_contra hge
          have hj : j = n := by omega
          exact hn (hj ▸ h1)
        · rintro ⟨h1, h3⟩
          exact ⟨h1, by omega⟩
      rw [h2]
      simp [hn]
      omega

theorem idxA (D : Finset ℕ) : ∀ (n i : ℕ), i < n → i ∉ D →
    ((List.range n).filter (fun j => decide (j ∉ D)))[i - (D.filter (fun j => j < i)).card]?
      = some i := by
  intro n
  induction n with
  | zero =>
    intro i hi
    omega
  | succ n ih =>
    intro i hi hiD
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · have h1 := ih i h hiD
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 h1
      rw [List.getElem?_append_left hlt]
      exact h1
    · subst h
      rw [List.getElem?_append_right (le_of_eq (lenL D i)), lenL]
      simp [hiD]

theorem getK (D : Finset ℕ) (w : List Bool) (hD : ∀ d ∈ D, d < w.length) (i : ℕ)
    (hi : i ∉ D) : (er D w).getD (rn D i) false = w.getD i false := by
  by_cases hlt : i < w.length
  · have h1 := idxA D w.length i hlt hi
    have h2 : (er D w)[rn D i]? = some (w.getD i false) := by
      simp only [er, rn, List.getElem?_map, h1, Option.map_some]
    rw [List.getD_eq_getElem?_getD, h2]
    rfl
  · have hlen : (er D w).length ≤ rn D i := by
      simp only [er, rn, List.length_map, lenL]
      have hc : D.filter (fun j => j < i) = D.filter (fun j => j < w.length) := by
        ext d
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, _⟩
          exact ⟨h1, hD d h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
      rw [hc]
      omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none hlen, List.getElem?_eq_none (by omega)]

theorem erAppend (D : Finset ℕ) (w : List Bool) (b : Bool) (hD : ∀ d ∈ D, d < w.length) :
    er D (w ++ [b]) = er D w ++ [b] := by
  have hn : w.length ∉ D := fun h => lt_irrefl _ (hD _ h)
  simp only [er, List.length_append, List.length_singleton, List.range_succ, List.filter_append,
    List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < w.length := List.mem_range.1 (List.mem_filter.1 hi).1
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']
  · simp [hn, List.getD_eq_getElem?_getD]

theorem wiresErase (D : Finset ℕ) : ∀ (gs : List Gate) (w : List Bool),
    (∀ d ∈ D, d < w.length) → (∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ D) →
    (gs.map (fun g => (⟨g.op, g.inputs.map (rn D)⟩ : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (er D w)
      = er D (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil =>
    intro w _ _
    rfl
  | cons g gs ih =>
    intro w hD hin
    simp only [List.map_cons, List.foldl_cons]
    have hargs : (g.inputs.map (rn D)).map (fun i => (er D w).getD i false)
        = g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact getK D w hD i (hin g (by simp) i hi)
    have hstep : er D w ++ [g.op.eval ((g.inputs.map (rn D)).map fun i => (er D w).getD i false)]
        = er D (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := by
      rw [erAppend D w _ hD, hargs]
    rw [hstep]
    apply ih
    · intro d hd
      rw [List.length_append]
      exact Nat.lt_add_right _ (hD d hd)
    · intro g' hg'
      exact hin g' (List.mem_cons_of_mem _ hg')

theorem main : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (D : Finset ℕ),
  (∀ i ∈ D, i < x.length) →
  (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ D) →
  let erase : List Bool → List Bool := fun v =>
    ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false
  let ren : ℕ → ℕ := fun w => w - (D.filter fun i => i < w).card
  let small : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ren⟩), ren C.output⟩
  small.wires (erase x) = erase (C.wires x) := by
  intro C x D hD hin erase ren small
  exact wiresErase D C.gates x hD hin

end PEqualNP.Outside.L_lib_687_aux

theorem PEqualNP.Outside.L_lib_687 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (D : Finset ℕ),
  (∀ i ∈ D, i < x.length) →
  (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ D) →
  let erase : List Bool → List Bool := fun v =>
    ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false
  let ren : ℕ → ℕ := fun w => w - (D.filter fun i => i < w).card
  let small : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ren⟩), ren C.output⟩
  small.wires (erase x) = erase (C.wires x)) := by
  exact PEqualNP.Outside.L_lib_687_aux.main
