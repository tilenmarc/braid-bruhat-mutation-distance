import BraidDistance.Packets
import BraidDistance.HammingParity
import BraidDistance.Gadget

/-!
# The gadget lower bound (Lemma 3.3, Table 1)

Every walk of signotopes on the seven gadget wires from `g^s` to `g^v` flips some triple more often than
necessary: there is no walk of length `|D_κ| = 30`.

Proof (paper): in a walk without extra flips every triple of `D_κ` is flipped exactly once and no other triple
is flipped (parity).  For each of the six 4-sets of Table 1 the packet goes from `g^s[P]` to `g^v[P]`, which
differ in exactly three coordinates, so by `arc3_unique` the three triples are flipped in the forced order of
the table.  The six orders chain into the cycle `124 ≺ 146 ≺ 467 ≺ 456 ≺ 245 ≺ 234 ≺ 124` (1-based labels) of
positions in the flip list, a contradiction.

0-based, the six 4-sets and forced coordinate orders (coordinates `abc, abd, acd, bcd` = `0, 1, 2, 3`) are
`table1` below; e.g. the paper's row `1246: 124 ≺ 126 ≺ 146` is `(0,1,3,5)` with the order `[0, 1, 2]`.
-/

namespace BraidDistance

/-- Table 1 (0-based): the six 4-sets and the forced orders of their three differing coordinates. -/
def table1 : List ((Nat × Nat × Nat × Nat) × List Nat) :=
  [((0, 1, 3, 5), [0, 1, 2]), ((0, 3, 5, 6), [0, 3, 2]), ((3, 4, 5, 6), [2, 1, 0]),
   ((1, 3, 4, 5), [2, 3, 0]), ((1, 2, 3, 4), [2, 1, 0]), ((0, 1, 2, 3), [3, 2, 1])]

/-- Table 1: each listed order is an arc order from `g^s[P]` to `g^v[P]`, it flips exactly the three
differing coordinates, and it is an order of three distinct coordinates. -/
theorem table1_spec : ∀ P ∈ table1,
    P.2 ∈ orders3 ∧
    ArcSeq (packet gs P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2) P.2 ∧
    P.2.foldl flipCoord (packet gs P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2) =
      packet gv P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 ∧
    (∀ i < 4, (tri4 P.1.1 P.1.2.1 P.1.2.2.1 P.1.2.2.2 i ∈ Dkappa ↔ i ∈ P.2)) := by
  decide

/-- `g^s` is a signotope. -/
theorem gs_signotope : IsSignotope 7 gs := by decide

/-- `g^v` is a signotope. -/
theorem gv_signotope : IsSignotope 7 gv := by decide

/-- The coordinate of a triple in the packet of `abcd` is `i` exactly when it is the `i`-th triple. -/
private theorem coord4_eq_some {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (t : Triple) (i : Nat) : coord4 a b c d t = some i ↔ i < 4 ∧ t = tri4 a b c d i := by
  obtain ⟨x, y, z⟩ := t
  unfold coord4
  rcases i with _ | _ | _ | _ | i <;> simp only [tri4, Prod.mk.injEq] <;>
    repeat' split
  all_goals simp only [Option.some.injEq, reduceCtorEq, false_iff, true_iff] at *
  all_goals first | omega | (constructor <;> intro <;> first | trivial | omega)

private theorem tri4_valid {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 7)
    (i : Nat) : ValidTriple 7 (tri4 a b c d i) := by
  rcases i with _ | _ | _ | _ | i <;> simp only [tri4, ValidTriple] <;> omega

/-- Each coordinate occurs in `pcoords` as often as its triple occurs in the flip list. -/
private theorem count_pcoords {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ts : List Triple) {i : Nat} (hi : i < 4) :
    (pcoords a b c d ts).count i = ts.count (tri4 a b c d i) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold pcoords at ih ⊢
    rw [List.filterMap_cons, List.count_cons]
    cases h : coord4 a b c d t with
    | none =>
      simp only
      rw [ih]
      have hne : (t == tri4 a b c d i) = false := by
        cases e : (t == tri4 a b c d i)
        · rfl
        · have ht : t = tri4 a b c d i := by simpa using e
          rw [(coord4_eq_some hab hbc hcd t i).2 ⟨hi, ht⟩] at h
          cases h
      rw [hne]; rfl
    | some j =>
      simp only [List.count_cons]
      rw [ih]
      obtain ⟨hj, rfl⟩ := (coord4_eq_some hab hbc hcd t j).1 h
      by_cases hji : j = i
      · subst hji; simp
      · have hne : tri4 a b c d j ≠ tri4 a b c d i := by
          intro e
          have h2 := (coord4_eq_some hab hbc hcd (tri4 a b c d j) i).2 ⟨hi, e⟩
          rw [h] at h2
          exact hji (Option.some.inj h2)
        have e1 : (j == i) = false := by simpa using hji
        have e2 : (tri4 a b c d j == tri4 a b c d i) = false := by simpa using hne
        rw [e1, e2]

private theorem pcoords_lt {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ts : List Triple) : ∀ x ∈ pcoords a b c d ts, x < 4 := by
  intro x hx
  obtain ⟨t, _, ht⟩ := List.mem_filterMap.1 hx
  exact ((coord4_eq_some hab hbc hcd t x).1 ht).1

private theorem length_eq_counts (L : List Nat) (h : ∀ x ∈ L, x < 4) :
    L.length = L.count 0 + L.count 1 + L.count 2 + L.count 3 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.count_cons, List.length_cons]
    rcases x with _ | _ | _ | _ | x <;> simp <;> omega

private theorem orders3_sum : ∀ o ∈ orders3,
    (if 0 ∈ o then 1 else 0) + (if 1 ∈ o then 1 else 0) + (if 2 ∈ o then 1 else 0) +
      (if 3 ∈ o then 1 else 0) = 3 := by
  decide

private theorem orders3_perm : ∀ o ∈ orders3, ∀ x ∈ List.range 4, ∀ y ∈ List.range 4,
    ∀ z ∈ List.range 4,
    (∀ i ∈ List.range 4, [x, y, z].count i = if i ∈ o then 1 else 0) → [x, y, z] ∈ orders3 := by
  decide

/-- A list of coordinates containing each coordinate of an order of three distinct coordinates once,
and nothing else, is itself such an order. -/
private theorem mem_orders3_of_count {o L : List Nat} (ho : o ∈ orders3) (hL : ∀ x ∈ L, x < 4)
    (hc : ∀ i < 4, L.count i = if i ∈ o then 1 else 0) : L ∈ orders3 := by
  have hlen := length_eq_counts L hL
  rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
    orders3_sum o ho] at hlen
  match L, hlen with
  | [x, y, z], _ =>
    exact orders3_perm o ho x (List.mem_range.2 (hL x (by simp))) y (List.mem_range.2 (hL y (by simp)))
      z (List.mem_range.2 (hL z (by simp))) fun i hi => hc i (List.mem_range.1 hi)

/-- If the filtered list shows `i` immediately before `j` (with neither occurring earlier), then the
unique preimage of `i` occurs before the unique preimage of `j`. -/
private theorem idxOf_lt_of_filterMap {α β : Type} [BEq α] [LawfulBEq α] (f : α → Option β)
    {x y : α} {i j : β} (hx : ∀ t, f t = some i ↔ t = x) (hy : ∀ t, f t = some j ↔ t = y)
    (hij : i ≠ j) (l : List α) :
    ∀ (pre r : List β), i ∉ pre → j ∉ pre → l.filterMap f = pre ++ i :: j :: r →
      l.idxOf x < l.idxOf y := by
  induction l with
  | nil => intro pre r _ _ h; cases pre <;> simp at h
  | cons t l ih =>
    intro pre r hi hj h
    rw [List.filterMap_cons] at h
    rw [List.idxOf_cons, List.idxOf_cons]
    cases hft : f t with
    | none =>
      rw [hft] at h
      have htx : (t == x) = false := by
        cases e : (t == x)
        · rfl
        · have : t = x := by simpa using e
          rw [(hx t).2 this] at hft; cases hft
      have hty : (t == y) = false := by
        cases e : (t == y)
        · rfl
        · have : t = y := by simpa using e
          rw [(hy t).2 this] at hft; cases hft
      rw [htx, hty]
      have := ih pre r hi hj h
      simp only [Bool.false_eq_true, ite_false]
      omega
    | some k =>
      rw [hft] at h
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have htx : t = x := (hx t).1 hft
        have hty : (t == y) = false := by
          cases e : (t == y)
          · rfl
          · have : t = y := by simpa using e
            rw [(hy t).2 this] at hft
            exact absurd (Option.some.inj hft).symm hij
        rw [hty]
        simp [htx]
      | cons p pre =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h'⟩ := h
        have hi' : i ∉ pre := fun hm => hi (List.mem_cons_of_mem _ hm)
        have hj' : j ∉ pre := fun hm => hj (List.mem_cons_of_mem _ hm)
        have htx : (t == x) = false := by
          cases e : (t == x)
          · rfl
          · have : t = x := by simpa using e
            rw [(hx t).2 this] at hft
            exact absurd (List.mem_cons.2 (Or.inl (Option.some.inj hft))) hi
        have hty : (t == y) = false := by
          cases e : (t == y)
          · rfl
          · have : t = y := by simpa using e
            rw [(hy t).2 this] at hft
            exact absurd (List.mem_cons.2 (Or.inl (Option.some.inj hft))) hj
        rw [htx, hty]
        have := ih pre r hi' hj' h'
        simp only [Bool.false_eq_true, ite_false]
        omega

/-- In a walk without extra flips, the coordinates flipped in the packet of a row of Table 1 are exactly the
forced order of the row. -/
private theorem row_pcoords {ts : List Triple} (hw : FlipWalk 7 gs ts)
    (hend : Agree 7 (flipList gs ts) gv)
    (hc : ∀ t, ValidTriple 7 t → ts.count t = if t ∈ Dkappa then 1 else 0)
    {a b c d : Nat} {o : List Nat} (hP : ((a, b, c, d), o) ∈ table1)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 7) :
    pcoords a b c d ts = o := by
  obtain ⟨ho, harc, hfold, hmem⟩ := table1_spec _ hP
  have ho : o ∈ orders3 := ho
  have harc : ArcSeq (packet gs a b c d) o := harc
  have hfold : o.foldl flipCoord (packet gs a b c d) = packet gv a b c d := hfold
  have hmem : ∀ i < 4, (tri4 a b c d i ∈ Dkappa ↔ i ∈ o) := hmem
  have hL : pcoords a b c d ts ∈ orders3 := by
    refine mem_orders3_of_count ho (pcoords_lt hab hbc hcd ts) fun i hi => ?_
    rw [count_pcoords hab hbc hcd ts hi, hc _ (tri4_valid hab hbc hcd hd i)]
    by_cases h : i ∈ o
    · simp [h, (hmem i hi).2 h]
    · have h' : tri4 a b c d i ∉ Dkappa := fun h'' => h ((hmem i hi).1 h'')
      simp [h, h']
  refine arc3_unique (packet gs a b c d) (packet_mem_validPackets gs_signotope hab hbc hcd hd) _ hL _ ho
    (arcSeq_of_flipWalk hw hab hbc hcd hd) harc ?_
  rw [← packet_flipList gs ts hab hbc hcd, hfold]
  simp only [packet]
  rw [hend a b c hab hbc (by omega), hend a b d hab (by omega) hd, hend a c d (by omega) hcd hd,
    hend b c d hbc hcd hd]

/-- In a walk without extra flips, the three triples of a row of Table 1 are flipped in the forced order. -/
private theorem row_idx {ts : List Triple} (hw : FlipWalk 7 gs ts)
    (hend : Agree 7 (flipList gs ts) gv)
    (hc : ∀ t, ValidTriple 7 t → ts.count t = if t ∈ Dkappa then 1 else 0)
    {a b c d i j k : Nat} (hP : ((a, b, c, d), [i, j, k]) ∈ table1)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d < 7) (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ts.idxOf (tri4 a b c d i) < ts.idxOf (tri4 a b c d j) ∧
      ts.idxOf (tri4 a b c d j) < ts.idxOf (tri4 a b c d k) := by
  have h := row_pcoords hw hend hc hP hab hbc hcd hd
  unfold pcoords at h
  have hx := fun i (hi : i < 4) t => (coord4_eq_some hab hbc hcd t i).trans
    ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
  refine ⟨idxOf_lt_of_filterMap _ (hx i hi) (hx j hj) hij ts [] [k] (by simp) (by simp) h,
    idxOf_lt_of_filterMap _ (hx j hj) (hx k hk) hjk ts [i] [] (by simp; omega) (by simp; omega) h⟩

/-- Lemma 3.3: every walk of signotopes from `g^s` to `g^v` flips some triple more often than necessary. -/
theorem gadget_lower {ts : List Triple} (hw : FlipWalk 7 gs ts) (hend : Agree 7 (flipList gs ts) gv) :
    ∃ t : Triple, ValidTriple 7 t ∧ (if t ∈ Dkappa then 1 else 0) < ts.count t := by
  refine Classical.byContradiction fun hne => ?_
  have hc : ∀ t, ValidTriple 7 t → ts.count t = if t ∈ Dkappa then 1 else 0 := by
    intro t ht
    have h1 : ¬ (if t ∈ Dkappa then 1 else 0) < ts.count t := fun h => hne ⟨t, ht, h⟩
    have h2 : ts.count t % 2 = if t ∈ Dkappa then 1 else 0 := count_parity hend ht
    by_cases hd : t ∈ Dkappa <;> simp only [hd, ite_true, ite_false] at h1 h2 ⊢ <;> omega
  have r1 : ts.idxOf (0, 1, 3) < ts.idxOf (0, 1, 5) ∧ ts.idxOf (0, 1, 5) < ts.idxOf (0, 3, 5) :=
    row_idx (a := 0) (b := 1) (c := 3) (d := 5) (i := 0) (j := 1) (k := 2) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have r2 : ts.idxOf (0, 3, 5) < ts.idxOf (3, 5, 6) ∧ ts.idxOf (3, 5, 6) < ts.idxOf (0, 5, 6) :=
    row_idx (a := 0) (b := 3) (c := 5) (d := 6) (i := 0) (j := 3) (k := 2) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have r3 : ts.idxOf (3, 5, 6) < ts.idxOf (3, 4, 6) ∧ ts.idxOf (3, 4, 6) < ts.idxOf (3, 4, 5) :=
    row_idx (a := 3) (b := 4) (c := 5) (d := 6) (i := 2) (j := 1) (k := 0) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have r4 : ts.idxOf (1, 4, 5) < ts.idxOf (3, 4, 5) ∧ ts.idxOf (3, 4, 5) < ts.idxOf (1, 3, 4) :=
    row_idx (a := 1) (b := 3) (c := 4) (d := 5) (i := 2) (j := 3) (k := 0) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have r5 : ts.idxOf (1, 3, 4) < ts.idxOf (1, 2, 4) ∧ ts.idxOf (1, 2, 4) < ts.idxOf (1, 2, 3) :=
    row_idx (a := 1) (b := 2) (c := 3) (d := 4) (i := 2) (j := 1) (k := 0) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have r6 : ts.idxOf (1, 2, 3) < ts.idxOf (0, 2, 3) ∧ ts.idxOf (0, 2, 3) < ts.idxOf (0, 1, 3) :=
    row_idx (a := 0) (b := 1) (c := 2) (d := 3) (i := 3) (j := 2) (k := 1) hw hend hc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  omega

end BraidDistance
