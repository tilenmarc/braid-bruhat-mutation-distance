import BraidDistance.Words

/-!
# Arrangements and swaps

Basic behaviour of `arrFrom` and `swapsFrom`: both are compatible with concatenation of words, a word permutes
the arrangement, and a word acting on a window of consecutive positions acts on the wires in the window as the
unshifted word acts on `[0, …, r-1]`, relabelled by the window (the computation behind Lemma 2.3).  The relative
order of two wires changes exactly when they are swapped (the invariant behind Definition 2.1), so a reduced word
reverses the arrangement.
-/

namespace BraidDistance

/-! ### The single letter `swapAdj` -/

private theorem swapAdj_of_drop {arr : List Nat} {i a b : Nat} {rest : List Nat}
    (h : arr.drop i = a :: b :: rest) : swapAdj arr i = arr.take i ++ b :: a :: rest := by
  unfold swapAdj; rw [h]

private theorem drop_eq_cons_cons {arr : List Nat} {i : Nat} (h : i + 1 < arr.length) :
    arr.drop i = arr[i] :: arr[i + 1] :: arr.drop (i + 2) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]

private theorem swapAdj_perm (arr : List Nat) (i : Nat) : (swapAdj arr i).Perm arr := by
  unfold swapAdj
  split
  · rename_i a b rest heq
    conv => rhs; rw [← List.take_append_drop i arr, heq]
    exact List.Perm.append_left _ (List.Perm.swap a b rest)
  · exact List.Perm.refl _

private theorem swapAdj_map (f : Nat → Nat) (arr : List Nat) (i : Nat) :
    swapAdj (arr.map f) i = (swapAdj arr i).map f := by
  unfold swapAdj
  rw [← List.map_drop]
  rcases h : arr.drop i with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [List.map_take]

/-- The transposition of the positions `i` and `i+1`. -/
private def tau (i j : Nat) : Nat := if j = i then i + 1 else if j = i + 1 then i else j

private theorem tau_tau (i j : Nat) : tau i (tau i j) = j := by
  unfold tau; split <;> split <;> (try split) <;> omega

private theorem getElem?_mid_swap (l₁ rest : List Nat) (a b j : Nat) :
    (l₁ ++ b :: a :: rest)[j]? = (l₁ ++ a :: b :: rest)[tau l₁.length j]? := by
  unfold tau
  by_cases h1 : j < l₁.length
  · simp only [Nat.ne_of_lt h1, show j ≠ l₁.length + 1 by omega, ↓reduceIte]
    rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
  · split
    · subst_vars
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      simp
    · split
      · subst_vars
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        obtain ⟨k, hk⟩ : ∃ k, j - l₁.length = k + 2 := ⟨j - l₁.length - 2, by omega⟩
        rw [hk]; simp

private theorem getElem?_swapAdj {arr : List Nat} {i : Nat} (h : i + 1 < arr.length) (j : Nat) :
    (swapAdj arr i)[j]? = arr[tau i j]? := by
  have hd := drop_eq_cons_cons h
  rw [swapAdj_of_drop hd]
  have hl : (arr.take i).length = i := by simp; omega
  have e : arr = arr.take i ++ arr[i] :: arr[i + 1] :: arr.drop (i + 2) := by
    rw [← hd, List.take_append_drop]
  have := getElem?_mid_swap (arr.take i) (arr.drop (i + 2)) arr[i] arr[i + 1] j
  rw [hl] at this
  rw [this, ← e]

private theorem idxOf_of_getElem? {l : List Nat} (hl : l.Nodup) {n x : Nat} (h : l[n]? = some x) :
    l.idxOf x = n := by
  obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.Nodup.idxOf_getElem hl n hn

private theorem getElem?_idxOf {l : List Nat} {x : Nat} (hx : x ∈ l) : l[l.idxOf x]? = some x := by
  have := List.idxOf_lt_length_of_mem hx
  rw [List.getElem?_eq_getElem this, List.getElem_idxOf this]

private theorem idxOf_swapAdj {arr : List Nat} (hnd : arr.Nodup) {i : Nat} (h : i + 1 < arr.length)
    {x : Nat} (hx : x ∈ arr) : (swapAdj arr i).idxOf x = tau i (arr.idxOf x) := by
  apply idxOf_of_getElem? ((swapAdj_perm arr i).nodup_iff.2 hnd)
  rw [getElem?_swapAdj h, tau_tau]
  exact getElem?_idxOf hx

private theorem idxOf_range {m a : Nat} (h : a < m) : (List.range m).idxOf a = a :=
  idxOf_of_getElem? List.nodup_range (List.getElem?_range h)

/-! ### A word on a window -/

private theorem swapAdj_window (pre win post : List Nat) {i : Nat} (h : i + 1 < win.length) :
    swapAdj (pre ++ win ++ post) (i + pre.length) = pre ++ swapAdj win i ++ post := by
  have hd := drop_eq_cons_cons h
  rw [swapAdj_of_drop hd]
  have hd' : (pre ++ win ++ post).drop (i + pre.length) = win[i] :: win[i + 1] :: (win.drop (i + 2) ++ post) := by
    rw [Nat.add_comm, List.append_assoc, List.drop_length_add_append,
      List.drop_append_of_le_length (by omega), hd]; rfl
  rw [swapAdj_of_drop hd', Nat.add_comm, List.append_assoc, List.take_length_add_append,
    List.take_append_of_le_length (by omega)]
  simp

private theorem getD_window (pre win post : List Nat) {i : Nat} (h : i < win.length) :
    (pre ++ win ++ post).getD (i + pre.length) 0 = win.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel, List.getElem?_append_left h]

private theorem arrFrom_window (pre win post L : List Nat) (hL : ValidWord win.length L) :
    arrFrom (pre ++ win ++ post) (shiftW pre.length L) = pre ++ arrFrom win L ++ post := by
  induction L generalizing win with
  | nil => rfl
  | cons i L ih =>
    have hi : i + 1 < win.length := hL i (List.mem_cons_self ..)
    show arrFrom (swapAdj (pre ++ win ++ post) (i + pre.length)) (shiftW pre.length L) =
      pre ++ arrFrom (swapAdj win i) L ++ post
    rw [swapAdj_window pre win post hi]
    apply ih
    rw [(swapAdj_perm win i).length_eq]
    exact fun j hj => hL j (List.mem_cons_of_mem _ hj)

private theorem swapsFrom_window (pre win post L : List Nat) (hL : ValidWord win.length L) :
    swapsFrom (pre ++ win ++ post) (shiftW pre.length L) = swapsFrom win L := by
  induction L generalizing win with
  | nil => rfl
  | cons i L ih =>
    have hi : i + 1 < win.length := hL i (List.mem_cons_self ..)
    show pairOf ((pre ++ win ++ post).getD (i + pre.length) 0)
        ((pre ++ win ++ post).getD (i + pre.length + 1) 0) ::
        swapsFrom (swapAdj (pre ++ win ++ post) (i + pre.length)) (shiftW pre.length L) =
      pairOf (win.getD i 0) (win.getD (i + 1) 0) :: swapsFrom (swapAdj win i) L
    rw [swapAdj_window pre win post hi, getD_window pre win post (by omega),
      show i + pre.length + 1 = (i + 1) + pre.length by omega, getD_window pre win post hi]
    congr 1
    apply ih
    rw [(swapAdj_perm win i).length_eq]
    exact fun j hj => hL j (List.mem_cons_of_mem _ hj)

private theorem arrFrom_map (f : Nat → Nat) (arr L : List Nat) :
    arrFrom (arr.map f) L = (arrFrom arr L).map f := by
  induction L generalizing arr with
  | nil => rfl
  | cons i L ih =>
    show arrFrom (swapAdj (arr.map f) i) L = (arrFrom (swapAdj arr i) L).map f
    rw [swapAdj_map, ih]

private theorem pairOf_minmax (f : Nat → Nat) (x y : Nat) :
    pairOf (f (pairOf x y).1) (f (pairOf x y).2) = pairOf (f x) (f y) := by
  by_cases h : x ≤ y
  · simp only [pairOf, Nat.min_eq_left h, Nat.max_eq_right h]
  · simp only [pairOf, Nat.min_eq_right (Nat.le_of_not_le h), Nat.max_eq_left (Nat.le_of_not_le h)]
    rw [Nat.min_comm, Nat.max_comm]

private theorem swapsFrom_map (f : Nat → Nat) (arr L : List Nat) (hL : ValidWord arr.length L) :
    swapsFrom (arr.map f) L = (swapsFrom arr L).map (fun p => pairOf (f p.1) (f p.2)) := by
  induction L generalizing arr with
  | nil => rfl
  | cons i L ih =>
    have hi : i + 1 < arr.length := hL i (List.mem_cons_self ..)
    show pairOf ((arr.map f).getD i 0) ((arr.map f).getD (i + 1) 0) :: swapsFrom (swapAdj (arr.map f) i) L =
      pairOf (f (pairOf (arr.getD i 0) (arr.getD (i + 1) 0)).1)
        (f (pairOf (arr.getD i 0) (arr.getD (i + 1) 0)).2) ::
        (swapsFrom (swapAdj arr i) L).map (fun p => pairOf (f p.1) (f p.2))
    rw [pairOf_minmax, swapAdj_map, ih]
    · congr 2
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by omega)]; rfl
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem (by omega)]; rfl
    · rw [(swapAdj_perm arr i).length_eq]
      exact fun j hj => hL j (List.mem_cons_of_mem _ hj)

/-- The window `q, …, q+r-1` of `arr`, written as a relabelling of `[0, …, r-1]`. -/
private theorem window_decomp (arr : List Nat) (q r : Nat) (hr : q + r ≤ arr.length) :
    arr = arr.take q ++ (List.range r).map (fun i => arr.getD (q + i) 0) ++ arr.drop (q + r) := by
  have e1 : (arr.drop q).take r = (List.range r).map (fun i => arr.getD (q + i) 0) := by
    apply List.ext_getElem
    · simp; omega
    · intro n h1 h2
      simp [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp at h1; omega)]; rfl
  rw [← e1, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem arrFrom_append (arr w₁ w₂ : List Nat) :
    arrFrom arr (w₁ ++ w₂) = arrFrom (arrFrom arr w₁) w₂ := by
  unfold arrFrom; exact List.foldl_append

theorem swapsFrom_append (arr w₁ w₂ : List Nat) :
    swapsFrom arr (w₁ ++ w₂) = swapsFrom arr w₁ ++ swapsFrom (arrFrom arr w₁) w₂ := by
  induction w₁ generalizing arr with
  | nil => rfl
  | cons i w ih => exact congrArg (List.cons _) (ih (swapAdj arr i))

theorem swapsFrom_length (arr w : List Nat) : (swapsFrom arr w).length = w.length := by
  induction w generalizing arr with
  | nil => rfl
  | cons i w ih => exact congrArg (· + 1) (ih (swapAdj arr i))

theorem arrFrom_perm (arr w : List Nat) : (arrFrom arr w).Perm arr := by
  induction w generalizing arr with
  | nil => exact List.Perm.refl _
  | cons i w ih => exact (ih (swapAdj arr i)).trans (swapAdj_perm arr i)

theorem arrFrom_length (arr w : List Nat) : (arrFrom arr w).length = arr.length := by
  exact (arrFrom_perm arr w).length_eq

theorem arrAfter_length (m : Nat) (w : List Nat) : (arrAfter m w).length = m := by
  rw [arrAfter, arrFrom_length, List.length_range]

/-- A word on a window: the arrangement. -/
theorem arrFrom_shift (arr L : List Nat) (q r : Nat) (hL : ValidWord r L) (hr : q + r ≤ arr.length) :
    arrFrom arr (shiftW q L) =
      arr.take q ++ (arrAfter r L).map (fun i => arr.getD (q + i) 0) ++ arr.drop (q + r) := by
  have hq : (arr.take q).length = q := by simp; omega
  conv => lhs; rw [window_decomp arr q r hr]
  conv => lhs; arg 2; rw [← hq]
  rw [arrFrom_window _ _ _ _ (by simpa using hL), arrFrom_map]; rfl

/-- A word on a window: the swaps are those of the unshifted word, relabelled by the window. -/
theorem swapsFrom_shift (arr L : List Nat) (q r : Nat) (hL : ValidWord r L) (hr : q + r ≤ arr.length) :
    swapsFrom arr (shiftW q L) =
      (swaps r L).map (fun p => pairOf (arr.getD (q + p.1) 0) (arr.getD (q + p.2) 0)) := by
  have hq : (arr.take q).length = q := by simp; omega
  conv => lhs; rw [window_decomp arr q r hr]
  conv => lhs; arg 2; rw [← hq]
  rw [swapsFrom_window _ _ _ _ (by simpa using hL), swapsFrom_map _ _ _ (by simpa using hL)]; rfl

private theorem swapsFrom_valid (m : Nat) (w : List Nat) : ∀ (arr : List Nat), arr.Nodup →
    (∀ x ∈ arr, x < m) → ValidWord arr.length w → ∀ p ∈ swapsFrom arr w, p.1 < p.2 ∧ p.2 < m := by
  induction w with
  | nil => intro _ _ _ _ p hp; cases hp
  | cons i w ih =>
    intro arr hnd hlt hv p hp
    have hi : i + 1 < arr.length := hv i (List.mem_cons_self ..)
    have hperm := swapAdj_perm arr i
    rcases List.mem_cons.1 hp with rfl | hp
    · have hx : arr.getD i 0 = arr[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hy : arr.getD (i + 1) 0 = arr[i + 1] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      have hne : arr[i] ≠ arr[i + 1] := by
        intro h
        have e1 := List.Nodup.idxOf_getElem hnd i (by omega)
        have e2 := List.Nodup.idxOf_getElem hnd (i + 1) hi
        rw [h] at e1
        omega
      have h1 := hlt _ (List.getElem_mem (show i < arr.length by omega))
      have h2 := hlt _ (List.getElem_mem hi)
      rw [hx, hy]
      simp only [pairOf]
      omega
    · refine ih (swapAdj arr i) (hperm.nodup_iff.2 hnd) (fun x hx => hlt x (hperm.mem_iff.1 hx)) ?_ p hp
      rw [hperm.length_eq]
      exact fun j hj => hv j (List.mem_cons_of_mem _ hj)

private theorem getElem_eq_iff_idxOf {arr : List Nat} (hnd : arr.Nodup) {x : Nat} (hx : x ∈ arr) {i : Nat}
    (hi : i < arr.length) : arr[i] = x ↔ arr.idxOf x = i := by
  constructor
  · intro h; subst h; exact List.Nodup.idxOf_getElem hnd i hi
  · intro h; subst h; exact List.getElem_idxOf _

private theorem order_gen (w : List Nat) : ∀ (arr : List Nat), arr.Nodup → ValidWord arr.length w →
    ∀ {a b : Nat}, a < b → a ∈ arr → b ∈ arr →
    ((arrFrom arr w).idxOf a < (arrFrom arr w).idxOf b ↔
      (arr.idxOf a < arr.idxOf b ↔ (swapsFrom arr w).count (a, b) % 2 = 0)) := by
  induction w with
  | nil => intro arr _ _ a b _ _ _; simp [arrFrom, swapsFrom]
  | cons i w ih =>
    intro arr hnd hv a b hab ha hb
    have hi : i + 1 < arr.length := hv i (List.mem_cons_self ..)
    have hp := swapAdj_perm arr i
    have hv' : ValidWord (swapAdj arr i).length w := by
      rw [hp.length_eq]; exact fun j hj => hv j (List.mem_cons_of_mem _ hj)
    have key := ih (swapAdj arr i) (hp.nodup_iff.2 hnd) hv' hab (hp.mem_iff.2 ha) (hp.mem_iff.2 hb)
    have e1 : arrFrom arr (i :: w) = arrFrom (swapAdj arr i) w := rfl
    have e2 : swapsFrom arr (i :: w) =
        pairOf (arr.getD i 0) (arr.getD (i + 1) 0) :: swapsFrom (swapAdj arr i) w := rfl
    have hx : arr.getD i 0 = arr[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hy : arr.getD (i + 1) 0 = arr[i + 1] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
    rw [e1, e2, key, idxOf_swapAdj hnd hi ha, idxOf_swapAdj hnd hi hb, List.count_cons, hx, hy]
    have hia := (getElem_eq_iff_idxOf hnd ha (i := i) (by omega))
    have hib := (getElem_eq_iff_idxOf hnd hb (i := i) (by omega))
    have hia' := (getElem_eq_iff_idxOf hnd ha hi)
    have hib' := (getElem_eq_iff_idxOf hnd hb hi)
    have hab' : arr.idxOf a ≠ arr.idxOf b := by
      intro h
      have := congrArg (arr[·]?) h
      simp only [getElem?_idxOf ha, getElem?_idxOf hb, Option.some.injEq] at this
      omega
    have hpair' : pairOf arr[i] arr[i + 1] = (a, b) ↔
        ((arr.idxOf a = i ∧ arr.idxOf b = i + 1) ∨ (arr.idxOf a = i + 1 ∧ arr.idxOf b = i)) := by
      rw [← hia, ← hib, ← hia', ← hib']
      simp only [pairOf, Prod.mk.injEq]
      omega
    have hpair : (pairOf arr[i] arr[i + 1] == (a, b)) =
        decide ((arr.idxOf a = i ∧ arr.idxOf b = i + 1) ∨ (arr.idxOf a = i + 1 ∧ arr.idxOf b = i)) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact hpair'
    rw [hpair]
    generalize arr.idxOf a = ia at *
    generalize arr.idxOf b = ib at *
    generalize (swapsFrom (swapAdj arr i) w).count (a, b) = c
    unfold tau
    by_cases h1 : ia = i ∧ ib = i + 1
    · obtain ⟨rfl, rfl⟩ := h1
      simp
      omega
    · by_cases h2 : ia = i + 1 ∧ ib = i
      · obtain ⟨rfl, rfl⟩ := h2
        simp
        omega
      · have : ¬((ia = i ∧ ib = i + 1) ∨ (ia = i + 1 ∧ ib = i)) := by omega
        simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have ht : ((if ia = i then i + 1 else if ia = i + 1 then i else ia) <
            (if ib = i then i + 1 else if ib = i + 1 then i else ib)) ↔ ia < ib := by
          split <;> split <;> (try split) <;> (try split) <;> omega
        rw [ht]

/-- The swaps of a valid word are pairs `a < b < m`. -/
theorem swaps_valid {m : Nat} {w : List Nat} (hw : ValidWord m w) :
    ∀ p ∈ swaps m w, p.1 < p.2 ∧ p.2 < m := by
  exact swapsFrom_valid m w (List.range m) List.nodup_range (fun x hx => List.mem_range.1 hx)
    (by rw [List.length_range]; exact hw)

/-- The inversion invariant: two wires `a < b` are in their initial order after `w` iff they have been swapped
an even number of times. -/
theorem arrAfter_order {m : Nat} {w : List Nat} (hw : ValidWord m w) {a b : Nat} (hab : a < b)
    (hb : b < m) :
    (arrAfter m w).idxOf a < (arrAfter m w).idxOf b ↔ (swaps m w).count (a, b) % 2 = 0 := by
  have h := order_gen w (List.range m) List.nodup_range (by rw [List.length_range]; exact hw) hab
    (List.mem_range.2 (by omega)) (List.mem_range.2 hb)
  rw [idxOf_range (by omega), idxOf_range hb] at h
  rw [arrAfter, swaps, h]
  exact ⟨fun e => e.1 hab, fun e => ⟨fun _ => e, fun _ => hab⟩⟩

/-- A reduced word reverses the arrangement. -/
theorem Reduced.arrAfter_eq {m : Nat} {w : List Nat} (h : Reduced m w) :
    arrAfter m w = (List.range m).reverse := by
  have hperm : (arrAfter m w).Perm (List.range m) := arrFrom_perm _ _
  have hnd : (arrAfter m w).Nodup := hperm.nodup_iff.2 List.nodup_range
  apply List.Perm.eq_of_pairwise (le := fun x y => x > y)
  · intro x y _ _ h1 h2; omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hx : (arrAfter m w)[i] < m := List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hi))
    have hy : (arrAfter m w)[j] < m := List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hj))
    have ei := List.Nodup.idxOf_getElem hnd i hi
    have ej := List.Nodup.idxOf_getElem hnd j hj
    have hne : (arrAfter m w)[i] ≠ (arrAfter m w)[j] := by
      intro e; rw [e] at ei; omega
    show (arrAfter m w)[i] > (arrAfter m w)[j]
    refine Nat.lt_of_le_of_ne (Nat.le_of_not_lt fun hlt => ?_) (Ne.symm hne)
    have := (arrAfter_order h.1 hlt hy).1 (by rw [ei, ej]; exact hij)
    rw [h.2 _ hy _ hlt] at this
    exact absurd this (by decide)
  · rw [List.pairwise_reverse]; exact List.pairwise_lt_range
  · exact hperm.trans (List.reverse_perm _).symm

/-- In a reduced word no pair is swapped twice. -/
theorem Reduced.swaps_nodup {m : Nat} {w : List Nat} (h : Reduced m w) : (swaps m w).Nodup := by
  rw [List.nodup_iff_count]
  intro p
  by_cases hp : p ∈ swaps m w
  · have hv := swaps_valid h.1 p hp
    have := h.2 p.2 hv.2 p.1 hv.1
    rw [this]; exact Nat.le_refl 1
  · rw [List.count_eq_zero_of_not_mem hp]; exact Nat.zero_le _

end BraidDistance
