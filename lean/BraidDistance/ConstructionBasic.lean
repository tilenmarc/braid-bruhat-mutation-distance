import BraidDistance.Construction
import BraidDistance.PathLemmas

/-!
# Unfolding lemmas for the construction

Bookkeeping facts relating the definitions of `Construction.lean` to each other: the factors are indexed like
the events, `arrAt` advances by `applyEv`, and the words `W G k ε` at `k = 0` and `k = J`.
-/

namespace BraidDistance

private theorem CB.getD_eq_getElem {α : Type} (l : List α) (d : α) {k : Nat} (hk : k < l.length) :
    l.getD k d = l[k] := by
  simp [List.getD, List.getElem?_eq_getElem hk]

private theorem CB.factorsFrom_length (arr : List Grp) (evs : List Ev) :
    (factorsFrom arr evs).length = evs.length := by
  induction evs generalizing arr with
  | nil => rfl
  | cons e es ih => simp [factorsFrom, ih]

private theorem CB.factorsFrom_getD (arr : List Grp) (evs : List Ev) (k : Nat) (hk : k < evs.length) :
    (factorsFrom arr evs).getD k [] =
      shiftW (wirePos ((evs.take k).foldl applyEv arr) (evTop (evs.getD k (.cell 0 0))))
        (evLocal (evs.getD k (.cell 0 0))) := by
  induction evs generalizing arr k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => simp [factorsFrom]
    | succ k =>
      simp only [List.length_cons] at hk
      have := ih (applyEv arr e) k (by omega)
      simpa [factorsFrom] using this

theorem factors_length (G : Graph) : (factors G).length = numFactors G := by
  simp [factors, numFactors, CB.factorsFrom_length]

/-- The `k`-th factor is the local word of the `k`-th event at the position of its top group. -/
theorem factors_getD (G : Graph) {k : Nat} (hk : k < numFactors G) :
    (factors G).getD k [] = shiftW (stepWindow G k) (evLocal (evAt G k)) := by
  unfold factors
  rw [CB.factorsFrom_getD _ _ _ hk]
  rfl

theorem arrAt_succ (G : Graph) {k : Nat} (hk : k < numFactors G) :
    arrAt G (k + 1) = applyEv (arrAt G k) (evAt G k) := by
  unfold arrAt evAt
  unfold numFactors at hk
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem hk]

theorem arrAt_zero (G : Graph) : arrAt G 0 = labelOrder G := rfl

theorem evAt_mem (G : Graph) {k : Nat} (hk : k < numFactors G) : evAt G k ∈ sweepEvents G := by
  unfold evAt
  unfold numFactors at hk
  rw [CB.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- Every event occurs at some index. -/
theorem exists_evAt (G : Graph) {ev : Ev} (h : ev ∈ sweepEvents G) :
    ∃ k, k < numFactors G ∧ evAt G k = ev := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp h
  refine ⟨k, hk, ?_⟩
  unfold evAt
  rw [CB.getD_eq_getElem _ _ hk, hke]

private theorem CB.factors_getElem (G : Graph) {k : Nat} (hk : k < (factors G).length) :
    (factors G)[k] = shiftW (stepWindow G k) (evLocal (evAt G k)) := by
  have h := factors_getD G (k := k) (by rw [← factors_length]; exact hk)
  rw [CB.getD_eq_getElem _ _ hk] at h
  exact h

/-- Splitting `Φ̂` at the `k`-th factor. -/
theorem factors_split (G : Graph) {k : Nat} (hk : k < numFactors G) :
    ((factors G).drop k).flatten =
      shiftW (stepWindow G k) (evLocal (evAt G k)) ++ ((factors G).drop (k + 1)).flatten := by
  have hk' : k < (factors G).length := by rw [factors_length]; exact hk
  rw [List.drop_eq_getElem_cons hk', List.flatten_cons, CB.factors_getElem G hk']

theorem factors_take_succ (G : Graph) {k : Nat} (hk : k < numFactors G) :
    ((factors G).take (k + 1)).flatten =
      ((factors G).take k).flatten ++ shiftW (stepWindow G k) (evLocal (evAt G k)) := by
  have hk' : k < (factors G).length := by rw [factors_length]; exact hk
  rw [List.take_add_one, List.getElem?_eq_getElem hk', List.flatten_append, CB.factors_getElem G hk']
  simp

/-- A sum over the events by index is the sum over the list of events. -/
theorem sum_range_evAt (G : Graph) (f : Ev → Nat) :
    ((List.range (numFactors G)).map fun k => f (evAt G k)).sum = ((sweepEvents G).map f).sum := by
  congr 1
  apply List.ext_getElem
  · simp [numFactors]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, evAt]
    simp at h2
    rw [CB.getD_eq_getElem _ _ h2]

/-- `W` depends on the bead types only through their values. -/
theorem W_congr (G : Graph) (k : Nat) {eps eps' : Nat → Bool} (h : ∀ u, u < G.n → eps u = eps' u) :
    W G k eps = W G k eps' := by
  unfold W beadsAt
  congr 2
  simp only [List.flatMap]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [h u (List.mem_range.mp hu)]

end BraidDistance
