import OMDistance.SignMapLemmas

/-!
# The Hamming bound and parity for flip lists of r-sets (Lemma 2.5, any rank)

A walk of sign maps from `s` given by the list `Xs` of flipped `r`-sets (all valid), ending at a map agreeing
with `v`, flips every set of `D(s, v)` an odd number of times and every other `r`-set an even number of times.
Hence (Lemma 2.5): if `Ys` is a duplicate-free list of sets each flipped more often than necessary
(`count > [X ∈ D]`), then `|Xs| ≥ |D(s, v)| + 2|Ys|`.  These statements do not depend on any property of the
intermediate maps.
-/

namespace OMDistance

/-- Parity: a valid `r`-set is flipped an odd number of times iff `s` and `v` differ on it. -/
theorem count_parityR {M r : Nat} {s v : SignMap} {Xs : List (List Nat)}
    (hend : AgreeR M r (flipsR s Xs) v) {X : List Nat} (hX : IsRSet M r X) :
    Xs.count X % 2 = if s X = v X then 0 else 1 := by
  have e1 := flipsR_apply s Xs X
  rw [hend X hX] at e1
  have hmod : Xs.count X % 2 = 0 ∨ Xs.count X % 2 = 1 := by omega
  by_cases hsv : s X = v X
  · simp only [hsv, ↓reduceIte]
    rcases hmod with h | h
    · exact h
    · rw [h, hsv] at e1
      cases hv : v X <;> simp [hv] at e1
  · simp only [hsv, ↓reduceIte]
    rcases hmod with h | h
    · rw [h] at e1
      exact absurd (by simpa using e1.symm) hsv
    · exact h

private theorem sum_count_cons (x : List Nat) (ts L : List (List Nat)) :
    (L.map fun t => (x :: ts).count t).sum = (L.map fun t => ts.count t).sum + L.count x := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, @List.count_cons _ _ y x ts, @List.count_cons _ _ x y L]
    by_cases h : x = y
    · subst h; simp; omega
    · have h1 : (x == y) = false := by simpa using h
      have h2 : (y == x) = false := by simpa using Ne.symm h
      simp [h1, h2]; omega

private theorem count_le_one_of_nodup (x : List Nat) (L : List (List Nat)) (hL : L.Nodup) :
    L.count x ≤ 1 := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have hL' := List.nodup_cons.1 hL
    rw [List.count_cons]
    by_cases h : y = x
    · subst h
      have : L.count y = 0 := List.count_eq_zero.2 hL'.1
      simp [this]
    · have : (y == x) = false := by simpa using h
      simp only [this]
      have := ih hL'.2
      simp; omega

private theorem count_eq_one_of_nodup (x : List Nat) (L : List (List Nat)) (hL : L.Nodup) (hx : x ∈ L) :
    L.count x = 1 := by
  have h1 := count_le_one_of_nodup x L hL
  have h2 := List.count_pos_iff.2 hx
  omega

/-- The counts of distinct sets add up to at most the length of the list. -/
private theorem sum_count_le (ts L : List (List Nat)) (hL : L.Nodup) :
    (L.map fun t => ts.count t).sum ≤ ts.length := by
  induction ts with
  | nil => induction L with
    | nil => simp
    | cons y L ih => simp at ih ⊢; exact ih (List.nodup_cons.1 hL).2
  | cons x ts ih =>
    rw [sum_count_cons]
    have := count_le_one_of_nodup x L hL
    simp only [List.length_cons]
    omega

/-- If every entry of `ts` lies in the duplicate-free list `L`, the counts add up to the length. -/
private theorem sum_count_eq (ts L : List (List Nat)) (hL : L.Nodup) (hts : ∀ t ∈ ts, t ∈ L) :
    (L.map fun t => ts.count t).sum = ts.length := by
  induction ts with
  | nil => induction L with
    | nil => simp
    | cons y L ih => simp at ih ⊢; exact ih (List.nodup_cons.1 hL).2
  | cons x ts ih =>
    rw [sum_count_cons, ih (fun t ht => hts t (List.mem_cons_of_mem _ ht)),
      count_eq_one_of_nodup x L hL (hts x (List.mem_cons_self ..))]
    simp

private theorem sum_map_le_sum_map {L : List (List Nat)} {f g : List Nat → Nat}
    (h : ∀ t ∈ L, g t ≤ f t) : (L.map g).sum ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h y (List.mem_cons_self ..)
    have h2 := ih fun t ht => h t (List.mem_cons_of_mem _ ht)
    omega

private theorem sum_map_add {L : List (List Nat)} {f g : List Nat → Nat} :
    (L.map fun t => f t + g t).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_map_ind (L : List (List Nat)) (p : List Nat → Bool) :
    (L.map fun t => if p t then 1 else 0).sum = (L.filter p).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases p y <;> simp; omega

private theorem sum_map_const (L : List (List Nat)) (c : Nat) :
    (L.map fun _ => c).sum = c * L.length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; rw [Nat.mul_succ]; omega

private theorem length_filter_split (L : List (List Nat)) (p : List Nat → Bool) :
    L.length = (L.filter p).length + (L.filter fun t => !p t).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.filter_cons, List.length_cons]
    cases p y <;> simp <;> omega

private theorem nodup_filter {L : List (List Nat)} (p : List Nat → Bool) (h : L.Nodup) :
    (L.filter p).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at h ⊢
  exact h.filter _

private theorem parity_bound_aux (D : List (List Nat)) (hDn : D.Nodup) (ts Ys : List (List Nat))
    (hY : Ys.Nodup)
    (hpY : ∀ t ∈ Ys, ts.count t % 2 = (if t ∈ D then 1 else 0))
    (hpD : ∀ t ∈ D, ts.count t % 2 = 1)
    (hYc : ∀ t ∈ Ys, (if t ∈ D then 1 else 0) < ts.count t) :
    D.length + 2 * Ys.length ≤ ts.length := by
  have hLn : (Ys ++ D.filter fun t => !decide (t ∈ Ys)).Nodup := by
    rw [List.nodup_append]
    refine ⟨hY, nodup_filter _ hDn, ?_⟩
    intro a ha b hb hab
    subst hab
    have := (List.mem_filter.1 hb).2
    simp [ha] at this
  have hsum := sum_count_le ts _ hLn
  rw [List.map_append, List.sum_append] at hsum
  have hY1 : ∀ t ∈ Ys, (fun t => (if decide (t ∈ D) then 1 else 0) + 2) t ≤ ts.count t := by
    intro t ht
    have hp := hpY t ht
    have hc := hYc t ht
    by_cases hd : t ∈ D
    · simp only [hd, ite_true, decide_true] at hp hc ⊢
      omega
    · simp only [hd, ite_false, decide_false, Bool.false_eq_true] at hp hc ⊢
      omega
  have hS1 := sum_map_le_sum_map hY1
  rw [sum_map_add, sum_map_ind, sum_map_const] at hS1
  have hD1 : ∀ t ∈ D.filter (fun t => !decide (t ∈ Ys)), (fun _ => 1) t ≤ ts.count t := by
    intro t ht
    have hp := hpD t (List.mem_filter.1 ht).1
    simp only; omega
  have hS2 := sum_map_le_sum_map hD1
  rw [sum_map_const] at hS2
  have hcap := sum_count_le (Ys.filter fun t => decide (t ∈ D)) (D.filter fun t => decide (t ∈ Ys))
    (nodup_filter _ hDn)
  have hD3 : ∀ t ∈ D.filter (fun t => decide (t ∈ Ys)),
      (fun _ => 1) t ≤ (Ys.filter fun t => decide (t ∈ D)).count t := by
    intro t ht
    have h := List.mem_filter.1 ht
    have hm : t ∈ Ys.filter (fun t => decide (t ∈ D)) :=
      List.mem_filter.2 ⟨by simpa using h.2, by simpa using h.1⟩
    exact List.count_pos_iff.2 hm
  have hS3 := sum_map_le_sum_map hD3
  rw [sum_map_const] at hS3
  have hsplit := length_filter_split D (fun t => decide (t ∈ Ys))
  omega

/-- For a valid set, `s X = v X` iff the set is not in `D(s, v)`. -/
private theorem eq_iff_not_mem_diffR {M r : Nat} {s v : SignMap} {X : List Nat} (hX : IsRSet M r X) :
    s X = v X ↔ X ∉ diffR M r s v := by
  rw [mem_diffR]
  constructor
  · intro h ⟨_, hne⟩; exact hne h
  · intro h; exact Decidable.byContradiction fun hne => h ⟨hX, hne⟩

/-- Lemma 2.5: `|D(s, v)| + 2|Ys| ≤ |Xs|` for a duplicate-free list `Ys` of valid sets flipped more often than
necessary. -/
theorem parity_boundR {M r : Nat} {s v : SignMap} {Xs : List (List Nat)}
    (hXs : ∀ X ∈ Xs, IsRSet M r X) (hend : AgreeR M r (flipsR s Xs) v)
    (Ys : List (List Nat)) (hY : Ys.Nodup) (hYv : ∀ Y ∈ Ys, IsRSet M r Y)
    (hYc : ∀ Y ∈ Ys, (if s Y = v Y then 0 else 1) < Xs.count Y) :
    hamR M r s v + 2 * Ys.length ≤ Xs.length := by
  have _ := hXs
  have hind : ∀ Y, IsRSet M r Y →
      (if s Y = v Y then 0 else 1) = (if Y ∈ diffR M r s v then 1 else 0) := by
    intro Y hYr
    by_cases h : s Y = v Y
    · have := (eq_iff_not_mem_diffR hYr).1 h
      simp [h, this]
    · have : Y ∈ diffR M r s v := Decidable.byContradiction fun hn =>
        h ((eq_iff_not_mem_diffR hYr).2 hn)
      simp [h, this]
  refine parity_bound_aux (diffR M r s v) (diffR_nodup M r s v) Xs Ys hY
    (fun Y hYm => ?_) (fun Y hYm => ?_) (fun Y hYm => ?_)
  · rw [count_parityR hend (hYv Y hYm), hind Y (hYv Y hYm)]
  · have hYr := (mem_diffR.1 hYm).1
    rw [count_parityR hend hYr, hind Y hYr]
    simp [hYm]
  · rw [← hind Y (hYv Y hYm)]; exact hYc Y hYm

/-- The Hamming bound `|D(s, v)| ≤ |Xs|`. -/
theorem hamR_le_length {M r : Nat} {s v : SignMap} {Xs : List (List Nat)}
    (hXs : ∀ X ∈ Xs, IsRSet M r X) (hend : AgreeR M r (flipsR s Xs) v) :
    hamR M r s v ≤ Xs.length := by
  have := parity_boundR hXs hend [] List.nodup_nil (fun _ h => by simp at h) (fun _ h => by simp at h)
  simpa using this

/-- If no valid set is flipped more often than necessary, then `|Xs| ≤ |D(s, v)|`. -/
theorem length_le_hamR {M r : Nat} {s v : SignMap} {Xs : List (List Nat)}
    (hXs : ∀ X ∈ Xs, IsRSet M r X)
    (hc : ∀ X, IsRSet M r X → Xs.count X ≤ if s X = v X then 0 else 1) :
    Xs.length ≤ hamR M r s v := by
  rw [← sum_count_eq Xs (rsets M r) (rsets_nodup M r) (fun X hX => mem_rsets.2 (hXs X hX))]
  have h1 : ∀ X ∈ rsets M r, (fun X => Xs.count X) X ≤
      (fun X => if (s X != v X) then 1 else 0) X := by
    intro X hX
    have := hc X (mem_rsets.1 hX)
    by_cases h : s X = v X <;> simp_all
  have := sum_map_le_sum_map h1
  rw [sum_map_ind] at this
  exact this

/-- Every set of `D(s, v)` is flipped at least once; so for every predicate `p`, the flips of sets satisfying
`p` are at least as many as the sets of `D(s, v)` satisfying `p`. -/
theorem diffR_filter_le {M r : Nat} {s v : SignMap} {Xs : List (List Nat)}
    (hend : AgreeR M r (flipsR s Xs) v) (p : List Nat → Bool) :
    ((diffR M r s v).filter p).length ≤ (Xs.filter p).length := by
  have hsum := sum_count_le (Xs.filter p) ((diffR M r s v).filter p) (nodup_filter _ (diffR_nodup M r s v))
  have h1 : ∀ X ∈ (diffR M r s v).filter p, (fun _ => 1) X ≤ (Xs.filter p).count X := by
    intro X hX
    obtain ⟨hXd, hpX⟩ := List.mem_filter.1 hX
    obtain ⟨hXr, hne⟩ := mem_diffR.1 hXd
    have hpar := count_parityR hend hXr
    simp only [hne, ↓reduceIte] at hpar
    have hpos : 0 < Xs.count X := by omega
    have hmem : X ∈ Xs := List.count_pos_iff.1 hpos
    exact List.count_pos_iff.2 (List.mem_filter.2 ⟨hmem, hpX⟩)
  have := sum_map_le_sum_map h1
  rw [sum_map_const] at this
  omega

end OMDistance
