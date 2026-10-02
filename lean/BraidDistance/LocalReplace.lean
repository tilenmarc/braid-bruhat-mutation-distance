import BraidDistance.Arrangement
import BraidDistance.BasicLemmas

/-!
# Local replacement (Lemma 2.3)

Let `W = A ++ shiftW q L ++ C` be a reduced word on `m` wires, where `L` is a reduced word on `r` wires, so that
`shiftW q L` acts on the window of positions `q, …, q+r-1` and swaps every pair of the wires `z` occupying the
window after `A`.

* (inside) If the wires of the window are in increasing order, the restriction of `s_W` to the triples inside `z`
  is `s_L`, read through the renumbering `z`.
* (outside) Replacing `L` by another reduced word `L'` on `r` wires keeps the word reduced and does not change
  `s_W` on triples not inside `z`.
-/

namespace BraidDistance

/-- The relabelling of a window: a pair of local positions `(i, j)` becomes the normalized pair of the wires at
the positions `q + i`, `q + j` of `arr`. -/
private def winRel (arr : List Nat) (q : Nat) (p : Nat × Nat) : Nat × Nat :=
  pairOf (arr.getD (q + p.1) 0) (arr.getD (q + p.2) 0)

/-- `idxOf` commutes with a map that is injective at `x` on the list. -/
private theorem idxOf_map_of_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (l : List α) (x : α) (hinj : ∀ y ∈ l, f y = f x → y = x) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.idxOf_cons]
    by_cases hy : y = x
    · subst hy; simp
    · have hf : f y ≠ f x := fun h => hy (hinj y (by simp) h)
      have ih' := ih (fun z hz => hinj z (by simp [hz]))
      simp [hf, hy, ih']

/-- The position of an element in `P ++ M ++ Q`, compared with its position in `P ++ M' ++ Q` for a
permutation `M'` of `M`: equal unless the element lies in `M` only, and then in the block of `M` in both. -/
private theorem idx_regions {α : Type} [BEq α] [LawfulBEq α] (P M M' Q : List α) (hp : M.Perm M') (x : α) :
    (x ∈ P ∧ (P ++ M ++ Q).idxOf x = (P ++ M' ++ Q).idxOf x ∧ (P ++ M ++ Q).idxOf x < P.length) ∨
    (x ∉ P ∧ x ∈ M ∧ P.length ≤ (P ++ M ++ Q).idxOf x ∧ (P ++ M ++ Q).idxOf x < P.length + M.length ∧
      P.length ≤ (P ++ M' ++ Q).idxOf x ∧ (P ++ M' ++ Q).idxOf x < P.length + M.length) ∨
    (x ∉ P ∧ x ∉ M ∧ (P ++ M ++ Q).idxOf x = (P ++ M' ++ Q).idxOf x ∧
      P.length + M.length ≤ (P ++ M ++ Q).idxOf x) := by
  have hmem : x ∈ M ↔ x ∈ M' := hp.mem_iff
  have hlen : M.length = M'.length := hp.length_eq
  by_cases hP : x ∈ P
  · left
    have e : ∀ N : List α, (P ++ N ++ Q).idxOf x = P.idxOf x := by
      intro N
      rw [List.idxOf_append, ite_eq_left (List.mem_append_left _ hP), List.idxOf_append, ite_eq_left hP]
    rw [e M, e M']
    exact ⟨hP, rfl, List.idxOf_lt_length_of_mem hP⟩
  · by_cases hM : x ∈ M
    · right; left
      have hM' : x ∈ M' := hmem.mp hM
      have e : ∀ N : List α, x ∈ N → (P ++ N ++ Q).idxOf x = N.idxOf x + P.length := by
        intro N hN
        rw [List.idxOf_append, ite_eq_left (List.mem_append_right _ hN), List.idxOf_append, ite_eq_right hP]
      rw [e M hM, e M' hM']
      have h1 := List.idxOf_lt_length_of_mem hM
      have h2 := List.idxOf_lt_length_of_mem hM'
      refine ⟨hP, hM, ?_, ?_, ?_, ?_⟩ <;> omega
    · right; right
      have hM' : x ∉ M' := fun h => hM (hmem.mpr h)
      have e : ∀ N : List α, x ∉ N → (P ++ N ++ Q).idxOf x = Q.idxOf x + (P.length + N.length) := by
        intro N hN
        rw [List.idxOf_append, ite_eq_right (by simp [hP, hN]), List.length_append]
      rw [e M hM, e M' hM']
      refine ⟨hP, hM, ?_, ?_⟩ <;> omega

/-- The swaps of `A ++ shiftW q L ++ C` for a reduced local word `L`. -/
private theorem swaps_decomp {m q r : Nat} {A L C : List Nat} (hL : Reduced r L) (hr : q + r ≤ m) :
    swaps m (A ++ shiftW q L ++ C) =
      swaps m A ++ (swaps r L).map (winRel (arrAfter m A) q) ++
        swapsFrom ((arrAfter m A).take q ++ ((List.range r).reverse).map (fun i => (arrAfter m A).getD (q + i) 0)
          ++ (arrAfter m A).drop (q + r)) C := by
  have hlen : q + r ≤ (arrAfter m A).length := by rw [arrAfter_length]; exact hr
  unfold swaps
  rw [swapsFrom_append, swapsFrom_append, arrFrom_append]
  change swapsFrom (List.range m) A ++ swapsFrom (arrAfter m A) (shiftW q L) ++
      swapsFrom (arrFrom (arrAfter m A) (shiftW q L)) C = _
  rw [swapsFrom_shift _ _ _ _ hL.1 hlen, arrFrom_shift _ _ _ _ hL.1 hlen, hL.arrAfter_eq]
  rfl

/-- A reduced word on `0` wires is empty. -/
private theorem reduced_zero {L : List Nat} (hL : Reduced 0 L) : L = [] := by
  cases L with
  | nil => rfl
  | cons i L => exact absurd (hL.1 i (by simp)) (by omega)

/-- Facts about the window `z` read off the arrangement after `A`. -/
private theorem window_get {m q r : Nat} {A z : List Nat} (hz : ((arrAfter m A).drop q).take r = z)
    (hzlen : z.length = r) {i : Nat} (hi : i < r) :
    (arrAfter m A).getD (q + i) 0 = z.getD i 0 := by
  subst hz
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi]

private theorem getD_mem_of_lt {z : List Nat} {i : Nat} (hi : i < z.length) : z.getD i 0 ∈ z := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

private theorem window_bound {m q r : Nat} {A z : List Nat} (hz : ((arrAfter m A).drop q).take r = z)
    (hzlen : z.length = r) (hr : 0 < r) : q + r ≤ m := by
  have h := congrArg List.length hz
  simp [List.length_take, List.length_drop, arrAfter_length, hzlen] at h
  omega

private theorem pairOf_mem {u v : Nat} {x : Nat × Nat} (h : pairOf u v = x) :
    (x.1 = u ∨ x.1 = v) ∧ (x.2 = u ∨ x.2 = v) := by
  subst h; unfold pairOf
  constructor
  · simp only [Nat.min_def]; split <;> simp
  · simp only [Nat.max_def]; split <;> simp

/-- An element of the relabelled local swaps is a pair of wires of the window. -/
private theorem mem_window_swaps {m q r : Nat} {A L z : List Nat} (hL : Reduced r L)
    (hz : ((arrAfter m A).drop q).take r = z) (hzlen : z.length = r) {x : Nat × Nat}
    (hx : x ∈ (swaps r L).map (winRel (arrAfter m A) q)) : x.1 ∈ z ∧ x.2 ∈ z := by
  rw [List.mem_map] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  have hv := swaps_valid hL.1 p hp
  have h1 : (arrAfter m A).getD (q + p.1) 0 ∈ z := by
    rw [window_get hz hzlen (by omega)]; exact getD_mem_of_lt (by omega)
  have h2 : (arrAfter m A).getD (q + p.2) 0 ∈ z := by
    rw [window_get hz hzlen (by omega)]; exact getD_mem_of_lt (by omega)
  obtain ⟨ha, hb⟩ := pairOf_mem hpx
  constructor
  · rcases ha with h | h <;> rw [h] <;> assumption
  · rcases hb with h | h <;> rw [h] <;> assumption

/-- Two reduced words on `r` wires have the same swaps up to order. -/
private theorem swaps_perm {r : Nat} {L L' : List Nat} (hL : Reduced r L) (hL' : Reduced r L') :
    (swaps r L).Perm (swaps r L') := by
  rw [List.perm_iff_count]
  intro x
  by_cases hx : x.1 < x.2 ∧ x.2 < r
  · obtain ⟨a, b⟩ := x
    rw [hL.2 b hx.2 a hx.1, hL'.2 b hx.2 a hx.1]
  · rw [List.count_eq_zero.mpr (fun h => hx (swaps_valid hL.1 x h)),
      List.count_eq_zero.mpr (fun h => hx (swaps_valid hL'.1 x h))]

/-- Lemma 2.3, last statement: inside the window the sign vector is that of the local word. -/
theorem local_sign_inside {m q r : Nat} {A L C z : List Nat}
    (hred : Reduced m (A ++ shiftW q L ++ C)) (hL : Reduced r L)
    (hz : ((arrAfter m A).drop q).take r = z) (hzinc : StrictIncr z) (hzlen : z.length = r) :
    Agree r (pull z (signVec m (A ++ shiftW q L ++ C))) (signVec r L) := by
  intro i j k hij hjk hk
  have hr : q + r ≤ m := window_bound hz hzlen (by omega)
  -- the window is increasing
  have hlt : ∀ a b, a < b → b < r → z.getD a 0 < z.getD b 0 := by
    intro a b hab hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.pairwise_iff_getElem.mp hzinc a b (by omega) (by omega) hab
  have hinj : ∀ a b, a < r → b < r → z.getD a 0 = z.getD b 0 → a = b := by
    intro a b ha hb h
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · have := hlt a b h' hb; omega
    · exact h'
    · have := hlt b a h' ha; omega
  -- the wires of the window are wires of `[m]`
  have hzm : ∀ a, a < r → z.getD a 0 < m := by
    intro a ha
    have hsub : ∀ x ∈ z, x ∈ arrAfter m A := by
      rw [← hz]; intro x hx; exact List.mem_of_mem_drop (List.mem_of_mem_take hx)
    have h1 : z.getD a 0 ∈ arrAfter m A := hsub _ (getD_mem_of_lt (by omega))
    have h2 := (arrFrom_perm (List.range m) A).mem_iff.mp h1
    exact List.mem_range.mp h2
  let f : Nat × Nat → Nat × Nat := fun p => (z.getD p.1 0, z.getD p.2 0)
  have hρ : (swaps r L).map (winRel (arrAfter m A) q) = (swaps r L).map f := by
    apply List.map_congr_left
    intro p hp
    have hv := swaps_valid hL.1 p hp
    have := hlt p.1 p.2 hv.1 hv.2
    simp only [winRel, f, window_get hz hzlen (show p.1 < r by omega),
      window_get hz hzlen hv.2, pairOf, Nat.min_eq_left (Nat.le_of_lt this),
      Nat.max_eq_right (Nat.le_of_lt this)]
  have hS := swaps_decomp (A := A) (C := C) hL hr
  rw [hρ] at hS
  -- key fact: the position of a local pair
  have key : ∀ a b, a < b → b < r →
      (swaps m (A ++ shiftW q L ++ C)).idxOf (z.getD a 0, z.getD b 0) =
        (swaps r L).idxOf (a, b) + (swaps m A).length := by
    intro a b hab hb
    have hmemL : (a, b) ∈ swaps r L := List.count_pos_iff.mp (by rw [hL.2 b hb a hab]; omega)
    have hmemM : (z.getD a 0, z.getD b 0) ∈ (swaps r L).map f := List.mem_map.mpr ⟨(a, b), hmemL, rfl⟩
    have hcount := hred.2 (z.getD b 0) (hzm b hb) (z.getD a 0) (hlt a b hab hb)
    rw [hS, List.count_append, List.count_append] at hcount
    have hpos := List.count_pos_iff.mpr hmemM
    have hnA : (z.getD a 0, z.getD b 0) ∉ swaps m A := by
      intro h; have := List.count_pos_iff.mpr h; omega
    have hidx : ((swaps r L).map f).idxOf (f (a, b)) = (swaps r L).idxOf (a, b) := by
      apply idxOf_map_of_inj
      intro y hy hfy
      have hv := swaps_valid hL.1 y hy
      simp only [f, Prod.mk.injEq] at hfy
      have e1 := hinj y.1 a (by omega) (by omega) hfy.1
      have e2 := hinj y.2 b hv.2 hb hfy.2
      cases y; simp_all
    rw [hS, List.idxOf_append, ite_eq_left (List.mem_append.mpr (Or.inr hmemM)), List.idxOf_append,
      ite_eq_right hnA]
    exact congrArg (· + (swaps m A).length) hidx
  show decide (_ < _) = decide (_ < _)
  rw [key i j hij (by omega), key j k hjk hk]
  simp

/-- Lemma 2.3, first statement: replacing the local word keeps the word reduced and the sign vector outside
the window. -/
theorem local_sign_outside {m q r : Nat} {A L L' C z : List Nat}
    (hred : Reduced m (A ++ shiftW q L ++ C)) (hL : Reduced r L) (hL' : Reduced r L')
    (hz : ((arrAfter m A).drop q).take r = z) (hzlen : z.length = r) :
    Reduced m (A ++ shiftW q L' ++ C) ∧
      ∀ t : Triple, ValidTriple m t → ¬ Inside z t →
        (signVec m (A ++ shiftW q L' ++ C)).at t = (signVec m (A ++ shiftW q L ++ C)).at t := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · subst hr0
    obtain rfl := reduced_zero hL
    obtain rfl := reduced_zero hL'
    exact ⟨hred, fun _ _ _ => rfl⟩
  have hr : q + r ≤ m := window_bound hz hzlen hrpos
  have hS := swaps_decomp (A := A) (C := C) hL hr
  have hS' := swaps_decomp (A := A) (C := C) hL' hr
  have hperm : ((swaps r L).map (winRel (arrAfter m A) q)).Perm
      ((swaps r L').map (winRel (arrAfter m A) q)) := (swaps_perm hL hL').map _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp only [List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact hred.1 i (by simp [hi])
    · simp only [shiftW, List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have := hL'.1 j hj
      omega
    · exact hred.1 i (by simp [hi])
  · intro b hb a hab
    rw [hS', ← hred.2 b hb a hab, hS]
    exact ((hperm.append_left _).append_right _).count_eq _ |>.symm
  · intro t _ hout
    obtain ⟨a, b, c⟩ := t
    show decide (_ < _) = decide (_ < _)
    dsimp only
    rw [hS, hS']
    have hx := idx_regions (swaps m A) _ _ (swapsFrom ((arrAfter m A).take q ++
      ((List.range r).reverse).map (fun i => (arrAfter m A).getD (q + i) 0) ++
        (arrAfter m A).drop (q + r)) C) hperm (a, b)
    have hy := idx_regions (swaps m A) _ _ (swapsFrom ((arrAfter m A).take q ++
      ((List.range r).reverse).map (fun i => (arrAfter m A).getD (q + i) 0) ++
        (arrAfter m A).drop (q + r)) C) hperm (b, c)
    have hnot : ¬ ((a, b) ∈ (swaps r L).map (winRel (arrAfter m A) q) ∧
        (b, c) ∈ (swaps r L).map (winRel (arrAfter m A) q)) := by
      rintro ⟨h1, h2⟩
      have m1 := mem_window_swaps hL hz hzlen h1
      have m2 := mem_window_swaps hL hz hzlen h2
      exact hout ⟨m1.1, m1.2, m2.2⟩
    rw [decide_eq_decide]
    rcases hx with ⟨_, ex, lx⟩ | ⟨_, mx, l1x, l2x, l3x, l4x⟩ | ⟨_, _, ex, lx⟩ <;>
      rcases hy with ⟨_, ey, ly⟩ | ⟨_, my, l1y, l2y, l3y, l4y⟩ | ⟨_, _, ey, ly⟩
    · rw [ex, ey]
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
    · exact absurd ⟨mx, my⟩ hnot
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
    · rw [ex, ey]

end BraidDistance
