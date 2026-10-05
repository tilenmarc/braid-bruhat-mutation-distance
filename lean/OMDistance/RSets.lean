import OMDistance.Basic

/-!
# Finite sets as increasing lists: basic facts

Facts about `IsRSet` (an `r`-subset of `[M]` as a strictly increasing list) and the enumeration `rsets M r`.
The binomial coefficient `binom M r` counts the `r`-subsets of `[M]` (`length_rsets`).
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- One step of the recursion for `rsetsFrom`: the sets starting with `lo`, then those with all entries
above `lo`. -/
private theorem rsetsFrom_succ_lt (M r lo : Nat) (h : lo < M) :
    rsetsFrom M (r + 1) lo = (rsetsFrom M r (lo + 1)).map (lo :: ·) ++ rsetsFrom M (r + 1) (lo + 1) := by
  have hM : M - lo = (M - (lo + 1)) + 1 := by omega
  rw [rsetsFrom, hM, List.range'_succ, List.flatMap_cons, rsetsFrom]

private theorem rsetsFrom_succ_ge (M r lo : Nat) (h : M ≤ lo) : rsetsFrom M (r + 1) lo = [] := by
  have hM : M - lo = 0 := by omega
  rw [rsetsFrom, hM]
  rfl

private theorem length_rsetsFrom (M : Nat) :
    ∀ (n lo r : Nat), M - lo = n → (rsetsFrom M r lo).length = binom (M - lo) r := by
  intro n
  induction n with
  | zero =>
    intro lo r hn
    cases r with
    | zero => rw [hn]; rfl
    | succ r => rw [rsetsFrom_succ_ge M r lo (by omega), hn]; rfl
  | succ n ih =>
    intro lo r hn
    cases r with
    | zero => rw [hn]; rfl
    | succ r =>
      rw [rsetsFrom_succ_lt M r lo (by omega), List.length_append, List.length_map,
        ih (lo + 1) r (by omega), ih (lo + 1) (r + 1) (by omega), hn]
      have : M - (lo + 1) = n := by omega
      rw [this]
      rfl

private theorem nodup_rsetsFrom (M : Nat) :
    ∀ (n lo r : Nat), M - lo = n → (rsetsFrom M r lo).Nodup := by
  intro n
  induction n with
  | zero =>
    intro lo r hn
    cases r with
    | zero => simp [rsetsFrom]
    | succ r => rw [rsetsFrom_succ_ge M r lo (by omega)]; exact List.nodup_nil
  | succ n ih =>
    intro lo r hn
    cases r with
    | zero => simp [rsetsFrom]
    | succ r =>
      rw [rsetsFrom_succ_lt M r lo (by omega), List.nodup_append]
      refine ⟨?_, ih (lo + 1) (r + 1) (by omega), ?_⟩
      · have := ih (lo + 1) r (by omega)
        unfold List.Nodup at this ⊢
        rw [List.pairwise_map]
        exact this.imp (fun h1 h2 => h1 (List.cons.inj h2).2)
      · intro a ha b hb hab
        obtain ⟨X, _, rfl⟩ := List.mem_map.1 ha
        rw [mem_rsetsFrom] at hb
        have := (hb.2.2 lo (by rw [← hab]; exact List.mem_cons_self)).1
        omega

/-- The enumeration of the `r`-subsets of `[M]` has no repetitions. -/
theorem rsets_nodup (M r : Nat) : (rsets M r).Nodup :=
  nodup_rsetsFrom M M 0 r (by omega)

/-- There are `binom M r` subsets of `[M]` with `r` elements. -/
theorem length_rsets (M r : Nat) : (rsets M r).length = binom M r := by
  unfold rsets
  rw [length_rsetsFrom M M 0 r (by omega)]
  rfl

/-- An increasing list has no repetitions. -/
theorem IsRSet.nodup {M r : Nat} {X : List Nat} (h : IsRSet M r X) : X.Nodup :=
  h.2.1.imp (fun hab => Nat.ne_of_lt hab)

/-- Enlarging the ground set. -/
theorem IsRSet.mono {M M' r : Nat} {X : List Nat} (h : IsRSet M r X) (hM : M ≤ M') : IsRSet M' r X :=
  ⟨h.1, h.2.1, fun x hx => Nat.lt_of_lt_of_le (h.2.2 x hx) hM⟩

/-- Removing one entry of an `(r+1)`-set gives an `r`-set. -/
theorem IsRSet.eraseIdx {M r : Nat} {X : List Nat} (h : IsRSet M (r + 1) X) {i : Nat} (hi : i < r + 1) :
    IsRSet M r (X.eraseIdx i) := by
  refine ⟨?_, h.2.1.sublist (List.eraseIdx_sublist X i), fun x hx => h.2.2 x ((List.eraseIdx_sublist X i).subset hx)⟩
  rw [List.length_eraseIdx, h.1]
  simp [hi]

/-- Translating a set by `c`. -/
theorem IsRSet.map_add {M r : Nat} {X : List Nat} (h : IsRSet M r X) (c : Nat) :
    IsRSet (M + c) r (X.map (· + c)) := by
  refine ⟨by rw [List.length_map, h.1], ?_, ?_⟩
  · unfold StrictIncr
    rw [List.pairwise_map]
    exact h.2.1.imp (fun hab => by omega)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have := h.2.2 y hy
    omega

/-- A `q`-subset `Y` of `[c]` followed by the translate by `c` of an `r`-subset `Z` of `[M]` is a
`(q + r)`-subset of `[c + M]`. -/
theorem IsRSet.append_shift {c q M r : Nat} {Y Z : List Nat} (hY : IsRSet c q Y) (hZ : IsRSet M r Z) :
    IsRSet (c + M) (q + r) (Y ++ Z.map (· + c)) := by
  have hZ' := hZ.map_add c
  refine ⟨by rw [List.length_append, hY.1, hZ'.1], ?_, ?_⟩
  · unfold StrictIncr
    rw [List.pairwise_append]
    refine ⟨hY.2.1, hZ'.2.1, fun a ha b hb => ?_⟩
    have := hY.2.2 a ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hb
    omega
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · have := hY.2.2 x hx; omega
    · have := hZ'.2.2 x hx; omega

/-- Two strictly increasing lists with the same elements are equal. -/
theorem strictIncr_ext {L L' : List Nat} (h : StrictIncr L) (h' : StrictIncr L') (hmem : ∀ x, x ∈ L ↔ x ∈ L') :
    L = L' := by
  induction L generalizing L' with
  | nil =>
    cases L' with
    | nil => rfl
    | cons y ys => exact absurd ((hmem y).2 List.mem_cons_self) (List.not_mem_nil)
  | cons x xs ih =>
    cases L' with
    | nil => exact absurd ((hmem x).1 List.mem_cons_self) (List.not_mem_nil)
    | cons y ys =>
      unfold StrictIncr at h h'
      rw [List.pairwise_cons] at h h'
      have hxy : x = y := by
        have h1 := (hmem x).1 List.mem_cons_self
        have h2 := (hmem y).2 List.mem_cons_self
        rcases List.mem_cons.1 h1 with e | h1
        · exact e
        rcases List.mem_cons.1 h2 with e | h2
        · exact e.symm
        have := h'.1 x h1
        have := h.1 y h2
        omega
      subst hxy
      rw [ih h.2 h'.2 (fun z => ?_)]
      constructor
      · intro hz
        have hz' := (hmem z).1 (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.1 hz' with e | hz'
        · have := h.1 z hz; omega
        · exact hz'
      · intro hz
        have hz' := (hmem z).2 (List.mem_cons_of_mem _ hz)
        rcases List.mem_cons.1 hz' with e | hz'
        · have := h'.1 z hz; omega
        · exact hz'

private theorem rsetsFrom_succ_filter (M : Nat) :
    ∀ (n lo r : Nat), M + 1 - lo = n →
      (rsetsFrom (M + 1) r lo).filter (fun X => !X.contains M) = rsetsFrom M r lo := by
  intro n
  induction n with
  | zero =>
    intro lo r hn
    cases r with
    | zero => rfl
    | succ r =>
      rw [rsetsFrom_succ_ge (M + 1) r lo (by omega), rsetsFrom_succ_ge M r lo (by omega)]
      rfl
  | succ n ih =>
    intro lo r hn
    cases r with
    | zero => rfl
    | succ r =>
      rw [rsetsFrom_succ_lt (M + 1) r lo (by omega), List.filter_append, List.filter_map,
        ih (lo + 1) (r + 1) (by omega)]
      by_cases hlo : lo = M
      · subst hlo
        rw [rsetsFrom_succ_ge lo r lo (Nat.le_refl _), rsetsFrom_succ_ge lo r (lo + 1) (by omega)]
        have : (fun X : List Nat => !X.contains lo) ∘ (lo :: ·) = fun _ => false := by
          funext X
          simp
        rw [this]
        simp
      · rw [rsetsFrom_succ_lt M r lo (by omega)]
        have : (fun X : List Nat => !X.contains M) ∘ (lo :: ·) = fun X => !X.contains M := by
          funext X
          simp only [Function.comp, List.contains_cons]
          have : (M == lo) = false := by simp; omega
          rw [this, Bool.false_or]
        rw [this, ih (lo + 1) r (by omega)]

/-- The `r`-subsets of `[M]` are the `r`-subsets of `[M+1]` that do not contain `M`, in the same order. -/
theorem rsets_succ_filter (M r : Nat) : (rsets (M + 1) r).filter (fun X => !X.contains M) = rsets M r :=
  rsetsFrom_succ_filter M (M + 1) 0 r (by omega)

end OMDistance
