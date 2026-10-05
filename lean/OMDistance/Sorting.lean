import OMDistance.Chirotope
import OMDistance.RSets

/-!
# Insertion sort and inversions

Facts about `isort` (insertion sort) and `inversions` used to pass between ordered tuples and sets
(Definition 6.1).  The key facts: `isort` returns the unique strictly increasing list with the same elements
(`isort_eq`), and the number of inversions of `σ ++ [x, y]` for an increasing `σ` and `x < y` outside `σ`
(`inversions_append_two`).
-/

namespace OMDistance

open BraidDistance (StrictIncr)

theorem mem_insertSorted {x y : Nat} {l : List Nat} : y ∈ insertSorted x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons a l ih =>
    unfold insertSorted
    split
    · simp
    · simp only [List.mem_cons, ih]
      exact or_left_comm

theorem mem_isort {x : Nat} {l : List Nat} : x ∈ isort l ↔ x ∈ l := by
  induction l with
  | nil => simp [isort]
  | cons a l ih => simp [isort, mem_insertSorted, ih]

private theorem length_insertSorted (x : Nat) (l : List Nat) :
    (insertSorted x l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertSorted]
  | cons a l ih =>
    unfold insertSorted
    split <;> simp [ih]

theorem length_isort (l : List Nat) : (isort l).length = l.length := by
  induction l with
  | nil => simp [isort]
  | cons a l ih => simp [isort, length_insertSorted, ih]

private theorem insertSorted_strictIncr {x : Nat} {l : List Nat} (h : StrictIncr l) (hx : x ∉ l) :
    StrictIncr (insertSorted x l) := by
  induction l with
  | nil => simp [insertSorted, StrictIncr]
  | cons a l ih =>
    unfold StrictIncr at h
    rw [List.pairwise_cons] at h
    simp only [List.mem_cons, not_or] at hx
    unfold insertSorted
    split
    · unfold StrictIncr
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, h.1, h.2⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · have := h.1 z hz; omega
    · unfold StrictIncr
      rw [List.pairwise_cons]
      refine ⟨?_, ih h.2 hx.2⟩
      intro z hz
      rw [mem_insertSorted] at hz
      rcases hz with rfl | hz
      · omega
      · exact h.1 z hz

/-- Sorting a list without repetitions gives a strictly increasing list. -/
theorem isort_strictIncr {l : List Nat} (h : l.Nodup) : StrictIncr (isort l) := by
  induction l with
  | nil => simp [isort, StrictIncr]
  | cons a l ih =>
    rw [List.nodup_cons] at h
    exact insertSorted_strictIncr (ih h.2) (fun hm => h.1 (mem_isort.1 hm))

/-- A strictly increasing list is already sorted. -/
theorem isort_of_strictIncr {l : List Nat} (h : StrictIncr l) : isort l = l := by
  induction l with
  | nil => simp [isort]
  | cons a l ih =>
    unfold StrictIncr at h
    rw [List.pairwise_cons] at h
    simp only [isort, ih h.2]
    cases l with
    | nil => simp [insertSorted]
    | cons b l =>
      have : a < b := h.1 b (by simp)
      simp [insertSorted, Nat.le_of_lt this]

private theorem strictIncr_ext' {L L' : List Nat} (h : StrictIncr L) (h' : StrictIncr L')
    (hmem : ∀ x, x ∈ L ↔ x ∈ L') : L = L' := by
  induction L generalizing L' with
  | nil =>
    cases L' with
    | nil => rfl
    | cons b L' => exact absurd ((hmem b).2 (by simp)) (by simp)
  | cons a L ih =>
    cases L' with
    | nil => exact absurd ((hmem a).1 (by simp)) (by simp)
    | cons b L' =>
      unfold StrictIncr at h h'
      rw [List.pairwise_cons] at h h'
      have hab : a = b := by
        have ha := (hmem a).1 (by simp)
        have hb := (hmem b).2 (by simp)
        simp only [List.mem_cons] at ha hb
        rcases ha with ha | ha
        · exact ha
        · rcases hb with hb | hb
          · exact hb.symm
          · have := h'.1 a ha; have := h.1 b hb; omega
      subst hab
      congr 1
      apply ih h.2 h'.2
      intro x
      constructor
      · intro hx
        have := (hmem x).1 (by simp [hx])
        simp only [List.mem_cons] at this
        rcases this with rfl | this
        · have := h.1 x hx; omega
        · exact this
      · intro hx
        have := (hmem x).2 (by simp [hx])
        simp only [List.mem_cons] at this
        rcases this with rfl | this
        · have := h'.1 x hx; omega
        · exact this

/-- `isort l` is the strictly increasing list with the elements of `l` (for `l` without repetitions). -/
theorem isort_eq {l L : List Nat} (hL : StrictIncr L) (hl : l.Nodup) (hmem : ∀ x, x ∈ l ↔ x ∈ L) :
    isort l = L :=
  strictIncr_ext' (isort_strictIncr hl) hL (fun x => by rw [mem_isort]; exact hmem x)

/-- An increasing list has no inversions. -/
theorem inversions_of_strictIncr {l : List Nat} (h : StrictIncr l) : inversions l = 0 := by
  induction l with
  | nil => simp [inversions]
  | cons a l ih =>
    unfold StrictIncr at h
    rw [List.pairwise_cons] at h
    simp only [inversions, ih h.2, Nat.add_zero]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro z hz
    have := h.1 z hz
    simp; omega

/-- The inversions of `σ ++ [x, y]` for increasing `σ` and `x < y`: every entry of `σ` larger than `x`, and every
entry of `σ` larger than `y`, gives one inversion. -/
theorem inversions_append_two {σ : List Nat} (h : StrictIncr σ) {x y : Nat} (hxy : x < y) :
    inversions (σ ++ [x, y]) =
      (σ.filter fun z => decide (x < z)).length + (σ.filter fun z => decide (y < z)).length := by
  induction σ with
  | nil =>
    simp [inversions]
    omega
  | cons a σ ih =>
    unfold StrictIncr at h
    rw [List.pairwise_cons] at h
    have hσ : (σ.filter fun z => decide (z < a)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro z hz
      have := h.1 z hz
      simp; omega
    simp only [List.cons_append, inversions, ih h.2, List.filter_append, hσ, List.nil_append,
      List.filter_cons]
    by_cases hx : x < a <;> by_cases hy : y < a <;> simp [hx, hy, List.filter] <;> omega

end OMDistance
