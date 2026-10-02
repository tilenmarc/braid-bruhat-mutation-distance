import BraidDistance.SignVector
import BraidDistance.BasicLemmas

/-!
# Braid moves flip one triple, and `d_B ≤ d_br` (Lemma 2.4)

A braid move replaces three consecutive letters `i, i+1, i` that swap the three pairs of the wires `T` at the
positions `i, i+1, i+2` by `i+1, i, i+1`, which swap the same pairs in the opposite order and leave the same
arrangement.  So the result is reduced and its sign vector differs from the old one exactly at `T`.

Consequently a sequence of commutations and braid moves from a reduced word induces a walk of signotopes of the
same length (the number of braid moves): `path_to_walk`, which gives `d_B(s_W, s_W') ≤ d_br([W], [W'])`.

`Step.braid_reduced` is proved directly from the definitions (its private helpers recompute the arrangement
and the swaps of the three-letter block), so it uses no other lemma of the library; the rest of the file is
proved from it and from `Step.comm_reduced` and `Reduced.signotope` (Lemma 2.2).
-/

namespace BraidDistance

/-! ### Helpers for Lemma 2.4 -/

private theorem bf_swapsFrom_append (arr w₁ w₂ : List Nat) :
    swapsFrom arr (w₁ ++ w₂) = swapsFrom arr w₁ ++ swapsFrom (arrFrom arr w₁) w₂ := by
  induction w₁ generalizing arr with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, swapsFrom, ih]; rfl

private theorem bf_swapAdj_perm (arr : List Nat) (i : Nat) : (swapAdj arr i).Perm arr := by
  unfold swapAdj
  split
  · rename_i a b rest h
    have h2 := List.take_append_drop i arr
    rw [h] at h2
    exact (List.Perm.append_left _ (List.Perm.swap a b rest)).trans (List.Perm.of_eq h2)
  · exact List.Perm.refl _

private theorem bf_arrFrom_perm (arr w : List Nat) : (arrFrom arr w).Perm arr := by
  induction w generalizing arr with
  | nil => exact List.Perm.refl _
  | cons i w ih => exact (ih (swapAdj arr i)).trans (bf_swapAdj_perm arr i)

private theorem bf_swapAdj_app (P R : List Nat) (a b : Nat) :
    swapAdj (P ++ a :: b :: R) P.length = P ++ b :: a :: R := by
  simp [swapAdj]

private theorem bf_swapAdj_app1 (P R : List Nat) (a b c : Nat) :
    swapAdj (P ++ a :: b :: c :: R) (P.length + 1) = P ++ a :: c :: b :: R := by
  have := bf_swapAdj_app (P ++ [a]) R b c
  simpa using this

private theorem bf_getElem?_app (P L : List Nat) (k : Nat) :
    (P ++ L)[P.length + k]? = L[k]? := by
  rw [List.getElem?_append_right (by omega)]; simp

private theorem bf_getElem?_app2 (P L : List Nat) :
    (P ++ L)[P.length + 1 + 1]? = L[2]? := bf_getElem?_app P L 2

private theorem bf_block_up (P R : List Nat) (x y z : Nat) :
    swapsFrom (P ++ x :: y :: z :: R) [P.length, P.length + 1, P.length] =
      [pairOf x y, pairOf x z, pairOf y z] ∧
    arrFrom (P ++ x :: y :: z :: R) [P.length, P.length + 1, P.length] = P ++ z :: y :: x :: R := by
  constructor
  · simp [swapsFrom, bf_swapAdj_app, bf_swapAdj_app1, pairOf, List.getD_eq_getElem?_getD,
      bf_getElem?_app2]
  · simp [arrFrom, bf_swapAdj_app, bf_swapAdj_app1]


private theorem bf_block_down (P R : List Nat) (x y z : Nat) :
    swapsFrom (P ++ x :: y :: z :: R) [P.length + 1, P.length, P.length + 1] =
      [pairOf y z, pairOf x z, pairOf x y] ∧
    arrFrom (P ++ x :: y :: z :: R) [P.length + 1, P.length, P.length + 1] = P ++ z :: y :: x :: R := by
  constructor
  · simp [swapsFrom, bf_swapAdj_app, bf_swapAdj_app1, pairOf, List.getD_eq_getElem?_getD,
      bf_getElem?_app2]
  · simp [arrFrom, bf_swapAdj_app, bf_swapAdj_app1]

private theorem bf_classify (SA SC : List (Nat × Nat)) (p1 p2 p3 q : Nat × Nat) :
    (q ∈ SA ∧ (SA ++ [p1, p2, p3] ++ SC).idxOf q = SA.idxOf q ∧
      (SA ++ [p3, p2, p1] ++ SC).idxOf q = SA.idxOf q ∧ SA.idxOf q < SA.length) ∨
    (q ∉ SA ∧ q ∈ [p1, p2, p3] ∧ SA.length ≤ (SA ++ [p1, p2, p3] ++ SC).idxOf q ∧
      (SA ++ [p1, p2, p3] ++ SC).idxOf q < SA.length + 3 ∧
      SA.length ≤ (SA ++ [p3, p2, p1] ++ SC).idxOf q ∧
      (SA ++ [p3, p2, p1] ++ SC).idxOf q < SA.length + 3) ∨
    (q ∉ SA ∧ (SA ++ [p1, p2, p3] ++ SC).idxOf q = (SA ++ [p3, p2, p1] ++ SC).idxOf q ∧
      SA.length + 3 ≤ (SA ++ [p1, p2, p3] ++ SC).idxOf q) := by
  by_cases hA : q ∈ SA
  · left
    refine ⟨hA, ?_, ?_, List.idxOf_lt_length_of_mem hA⟩
    · simp only [List.append_assoc, List.idxOf_append, hA, ite_true]
    · simp only [List.append_assoc, List.idxOf_append, hA, ite_true]
  · right
    by_cases hM : q ∈ [p1, p2, p3]
    · left
      have hM' : q ∈ [p3, p2, p1] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hM ⊢
        rcases hM with h | h | h <;> simp [h]
      have h1 := List.idxOf_lt_length_of_mem hM
      have h2 := List.idxOf_lt_length_of_mem hM'
      simp only [List.length_cons, List.length_nil] at h1 h2
      refine ⟨hA, hM, ?_⟩
      simp only [List.append_assoc, List.idxOf_append, hA, hM, hM', ite_true, ite_false]
      omega
    · right
      have hM' : q ∉ [p3, p2, p1] := by
        intro h; apply hM
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h <;> simp [h]
      refine ⟨hA, ?_⟩
      simp only [List.append_assoc, List.idxOf_append, hA, hM, hM', ite_false,
        List.length_cons, List.length_nil, true_and]
      omega


private theorem bf_idx_iff (SA SC : List (Nat × Nat)) (p1 p2 p3 q r : Nat × Nat)
    (h : ¬ ((q ∉ SA ∧ q ∈ [p1, p2, p3]) ∧ (r ∉ SA ∧ r ∈ [p1, p2, p3]))) :
    ((SA ++ [p1, p2, p3] ++ SC).idxOf q < (SA ++ [p1, p2, p3] ++ SC).idxOf r ↔
      (SA ++ [p3, p2, p1] ++ SC).idxOf q < (SA ++ [p3, p2, p1] ++ SC).idxOf r) := by
  have hq := bf_classify SA SC p1 p2 p3 q
  have hr := bf_classify SA SC p1 p2 p3 r
  rcases hq with ⟨hq1, hq2, hq3⟩ | ⟨hq1, hq2, hq3⟩ | ⟨hq1, hq2, hq3⟩ <;>
  rcases hr with ⟨hr1, hr2, hr3⟩ | ⟨hr1, hr2, hr3⟩ | ⟨hr1, hr2, hr3⟩
  all_goals first
    | omega
    | exact absurd ⟨⟨hq1, hq2⟩, ⟨hr1, hr2⟩⟩ h

private theorem bf_idx_flip (SA SC : List (Nat × Nat)) (p1 p2 p3 q r : Nat × Nat)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (hq : q ∈ [p1, p2, p3]) (hr : r ∈ [p1, p2, p3])
    (hqA : q ∉ SA) (hrA : r ∉ SA) (hqr : q ≠ r) :
    ((SA ++ [p1, p2, p3] ++ SC).idxOf q < (SA ++ [p1, p2, p3] ++ SC).idxOf r ↔
      ¬ ((SA ++ [p3, p2, p1] ++ SC).idxOf q < (SA ++ [p3, p2, p1] ++ SC).idxOf r)) := by
  have hq' : q ∈ [p3, p2, p1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with h | h | h <;> simp [h]
  have hr' : r ∈ [p3, p2, p1] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]
  simp only [List.append_assoc, List.idxOf_append, hqA, hrA, hq, hr, hq', hr', ite_true, ite_false]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq hr
  rcases hq with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
    simp_all [List.idxOf_cons, Ne.symm h12, Ne.symm h13, Ne.symm h23]

private theorem bf_sort {m x y z : Nat} (hx : x < m) (hy : y < m) (hz : z < m) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c, a < b ∧ b < c ∧ c < m ∧
      ∀ q, q ∈ [pairOf x y, pairOf x z, pairOf y z] ↔ (q = (a, b) ∨ q = (a, c) ∨ q = (b, c)) := by
  refine ⟨min (min x y) z, x + y + z - min (min x y) z - max (max x y) z, max (max x y) z,
    by omega, by omega, by omega, ?_⟩
  intro ⟨q1, q2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, pairOf, Prod.mk.injEq]
  omega


private theorem bf_core {m : Nat} {w w' : List Nat} (h : Reduced m w) (hv : ValidWord m w')
    {SA SC : List (Nat × Nat)} {p1 p2 p3 : Nat × Nat}
    (hw : swaps m w = SA ++ [p1, p2, p3] ++ SC) (hw' : swaps m w' = SA ++ [p3, p2, p1] ++ SC)
    {a b c : Nat} (hab : a < b) (hbc : b < c) (hc : c < m)
    (hM : ∀ q, q ∈ [p1, p2, p3] ↔ (q = (a, b) ∨ q = (a, c) ∨ q = (b, c))) :
    Reduced m w' ∧ DiffersInOne m (signVec m w) (signVec m w') := by
  have hperm : (SA ++ [p3, p2, p1] ++ SC).Perm (SA ++ [p1, p2, p3] ++ SC) :=
    List.Perm.append_right SC (List.Perm.append_left SA (List.reverse_perm [p1, p2, p3]))
  have hcnt : ∀ q, (swaps m w').count q = (swaps m w).count q := by
    intro q; rw [hw, hw']; exact hperm.count_eq q
  have hone : ∀ q ∈ [p1, p2, p3], (SA ++ [p1, p2, p3] ++ SC).count q = 1 := by
    intro q hq
    rw [← hw]
    rcases (hM q).1 hq with rfl | rfl | rfl
    · exact h.2 b (by omega) a hab
    · exact h.2 c hc a (by omega)
    · exact h.2 c hc b hbc
  have hnotA : ∀ q ∈ [p1, p2, p3], q ∉ SA := by
    intro q hq hA
    have h1 := hone q hq
    have h2 := List.count_pos_iff.2 hA
    have h3 := List.count_pos_iff.2 hq
    simp only [List.count_append] at h1
    omega
  have hp1 : p1 ∈ [p1, p2, p3] := by simp
  have hp2 : p2 ∈ [p1, p2, p3] := by simp
  have h12 : p1 ≠ p2 := by
    intro he
    have h1 := hone p1 hp1
    rw [← he] at h1
    simp only [List.count_append, List.count_cons_self] at h1
    omega
  have h13 : p1 ≠ p3 := by
    intro he
    have h1 := hone p1 hp1
    rw [← he] at h1
    simp only [List.count_append, List.count_cons_self, List.count_cons] at h1
    simp at h1
    omega
  have h23 : p2 ≠ p3 := by
    intro he
    have h1 := hone p2 hp2
    rw [← he] at h1
    simp only [List.count_append, List.count_cons_self, List.count_cons] at h1
    simp at h1
    omega
  refine ⟨⟨hv, fun b' hb' a' ha' => by rw [hcnt]; exact h.2 b' hb' a' ha'⟩, (a, b, c),
    ⟨hab, hbc, hc⟩, ?_, ?_⟩
  · have hq : (a, b) ∈ [p1, p2, p3] := (hM _).2 (Or.inl rfl)
    have hr : (b, c) ∈ [p1, p2, p3] := (hM _).2 (Or.inr (Or.inr rfl))
    have hqr : (a, b) ≠ (b, c) := by intro he; simp only [Prod.mk.injEq] at he; omega
    have key := bf_idx_flip SA SC p1 p2 p3 _ _ h12 h13 h23 hq hr (hnotA _ hq) (hnotA _ hr) hqr
    simp only [SMap.at, signVec, hw, hw']
    intro he
    have := decide_eq_decide.1 he
    by_cases hh : (SA ++ [p3, p2, p1] ++ SC).idxOf (a, b) < (SA ++ [p3, p2, p1] ++ SC).idxOf (b, c)
    · exact key.1 (this.2 hh) hh
    · exact hh (this.1 (key.2 hh))
  · intro ⟨a', b', c'⟩ ⟨ha', hb', hc'⟩ hne
    simp only [SMap.at, signVec, hw, hw']
    apply decide_eq_decide.2
    apply bf_idx_iff
    intro ⟨⟨_, hq⟩, ⟨_, hr⟩⟩
    apply hne
    rcases (hM _).1 hq with he | he | he <;> rcases (hM _).1 hr with he' | he' | he' <;>
      simp only [Prod.mk.injEq] at he he' ⊢ <;> omega


/-- The arrangement after a prefix `A`, split around the three positions `i, i+1, i+2`. -/
private theorem bf_split {m : Nat} (A : List Nat) {i : Nat} (hi : i + 2 < m) :
    ∃ P R x y z, P.length = i ∧ arrFrom (List.range m) A = P ++ x :: y :: z :: R ∧
      x < m ∧ y < m ∧ z < m ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hp := bf_arrFrom_perm (List.range m) A
  have hlen : (arrFrom (List.range m) A).length = m := by simpa using hp.length_eq
  have hnd : (arrFrom (List.range m) A).Nodup := hp.nodup_iff.2 List.nodup_range
  have hmem : ∀ v ∈ arrFrom (List.range m) A, v < m := fun v hv => by
    simpa using hp.mem_iff.1 hv
  have hdl : (arrFrom (List.range m) A |>.drop i).length = m - i := by simp [hlen]
  obtain ⟨x, y, z, R, hd⟩ : ∃ x y z R, (arrFrom (List.range m) A).drop i = x :: y :: z :: R := by
    rcases hdr : (arrFrom (List.range m) A).drop i with _ | ⟨x, _ | ⟨y, _ | ⟨z, R⟩⟩⟩ <;>
      rw [hdr] at hdl <;> simp at hdl
    all_goals first | omega | exact ⟨x, y, z, R, rfl⟩
  have harr := List.take_append_drop i (arrFrom (List.range m) A)
  rw [hd] at harr
  refine ⟨(arrFrom (List.range m) A).take i, R, x, y, z, by simp [hlen]; omega, harr.symm, ?_⟩
  rw [← harr] at hnd hmem
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.mem_append] at hnd hmem
  refine ⟨hmem x (by simp), hmem y (by simp), hmem z (by simp), ?_, ?_, ?_⟩ <;>
    (intro he; subst he; simp_all)

/-- Lemma 2.4: a braid move on a reduced word gives a reduced word whose sign vector differs in exactly one
triple. -/
theorem Step.braid_reduced {m : Nat} {w w' : List Nat} (h : Reduced m w) (hs : Step w w' 1) :
    Reduced m w' ∧ DiffersInOne m (signVec m w) (signVec m w') := by
  cases hs with
  | braidUp A C i =>
    have hi : i + 2 < m := h.1 (i + 1) (by simp)
    have hv : ValidWord m (A ++ (i + 1) :: i :: (i + 1) :: C) := by
      intro j hj; apply h.1; simp only [List.mem_append, List.mem_cons] at hj ⊢
      rcases hj with hj | hj | hj | hj | hj <;> simp [hj]
    obtain ⟨P, R, x, y, z, hP, harr, hx, hy, hz, hxy, hxz, hyz⟩ := bf_split A hi
    obtain ⟨a, b, c, hab, hbc, hc, hM⟩ := bf_sort hx hy hz hxy hxz hyz
    obtain ⟨hs1, ha1⟩ := bf_block_up P R x y z
    obtain ⟨hs2, ha2⟩ := bf_block_down P R x y z
    subst hP
    refine bf_core h hv (SA := swaps m A) (SC := swapsFrom (P ++ z :: y :: x :: R) C) ?_ ?_
      hab hbc hc hM
    · show swapsFrom _ (A ++ ([P.length, P.length + 1, P.length] ++ C)) = _
      rw [bf_swapsFrom_append, bf_swapsFrom_append, harr, hs1, ha1]; simp [swaps]
    · show swapsFrom _ (A ++ ([P.length + 1, P.length, P.length + 1] ++ C)) = _
      rw [bf_swapsFrom_append, bf_swapsFrom_append, harr, hs2, ha2]; simp [swaps]
  | braidDown A C i =>
    have hi : i + 2 < m := h.1 (i + 1) (by simp)
    have hv : ValidWord m (A ++ i :: (i + 1) :: i :: C) := by
      intro j hj; apply h.1; simp only [List.mem_append, List.mem_cons] at hj ⊢
      rcases hj with hj | hj | hj | hj | hj <;> simp [hj]
    obtain ⟨P, R, x, y, z, hP, harr, hx, hy, hz, hxy, hxz, hyz⟩ := bf_split A hi
    obtain ⟨a, b, c, hab, hbc, hc, hM⟩ := bf_sort hx hy hz hxy hxz hyz
    have hM' : ∀ q, q ∈ [pairOf y z, pairOf x z, pairOf x y] ↔
        (q = (a, b) ∨ q = (a, c) ∨ q = (b, c)) := by
      intro q
      rw [← hM q]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor <;> intro hq <;> rcases hq with hq | hq | hq <;> simp [hq]
    obtain ⟨hs1, ha1⟩ := bf_block_up P R x y z
    obtain ⟨hs2, ha2⟩ := bf_block_down P R x y z
    subst hP
    refine bf_core h hv (SA := swaps m A) (SC := swapsFrom (P ++ z :: y :: x :: R) C) ?_ ?_
      hab hbc hc hM'
    · show swapsFrom _ (A ++ ([P.length + 1, P.length, P.length + 1] ++ C)) = _
      rw [bf_swapsFrom_append, bf_swapsFrom_append, harr, hs2, ha2]; simp [swaps]
    · show swapsFrom _ (A ++ ([P.length, P.length + 1, P.length] ++ C)) = _
      rw [bf_swapsFrom_append, bf_swapsFrom_append, harr, hs1, ha1]; simp [swaps]

/-- One step on a reduced word. -/
theorem Step.reduced_cases {m : Nat} {w w' : List Nat} {k : Nat} (h : Reduced m w) (hs : Step w w' k) :
    Reduced m w' ∧ ((k = 0 ∧ signVec m w' = signVec m w) ∨
      (k = 1 ∧ DiffersInOne m (signVec m w) (signVec m w'))) := by
  cases hs with
  | comm A C i j hij =>
    have := Step.comm_reduced h (Step.comm A C i j hij)
    exact ⟨this.1, Or.inl ⟨rfl, this.2⟩⟩
  | braidUp A C i =>
    have := Step.braid_reduced h (Step.braidUp A C i)
    exact ⟨this.1, Or.inr ⟨rfl, this.2⟩⟩
  | braidDown A C i =>
    have := Step.braid_reduced h (Step.braidDown A C i)
    exact ⟨this.1, Or.inr ⟨rfl, this.2⟩⟩

/-- Paths preserve reducedness. -/
theorem Path.reduced {m : Nat} {w w' : List Nat} {k : Nat} (h : Reduced m w) (hp : Path w w' k) :
    Reduced m w' := by
  induction hp with
  | refl _ => exact h
  | cons hs _ ih => exact ih (Step.reduced_cases h hs).1

/-- A path without braid moves keeps the sign vector. -/
theorem Path.zero_sign {m : Nat} {w w' : List Nat} (h : Reduced m w) (hp : Path w w' 0) :
    signVec m w' = signVec m w := by
  generalize hk : (0 : Nat) = k at hp
  induction hp with
  | refl _ => rfl
  | cons hs _ ih =>
    rename_i a b
    have hc := Step.reduced_cases h hs
    rcases hc with ⟨hred, ⟨ha, hsv⟩ | ⟨ha, _⟩⟩
    · rw [ih hred (by omega), hsv]
    · omega

/-- `d_B ≤ d_br`: the sign vectors along a path form a walk of signotopes whose length is the number of braid
moves. -/
theorem path_to_walk {m : Nat} {w w' : List Nat} {k : Nat} (h : Reduced m w) (hp : Path w w' k) :
    Walk m (signVec m w) (signVec m w') k := by
  induction hp with
  | refl _ => exact Walk.nil (Reduced.signotope h) (Agree.refl _ _)
  | cons hs _ ih =>
    rename_i a b
    rcases Step.reduced_cases h hs with ⟨hred, ⟨ha, hsv⟩ | ⟨ha, hd⟩⟩
    · subst ha
      rw [← hsv]
      simpa using ih hred
    · subst ha
      rw [Nat.add_comm]
      exact Walk.cons (Reduced.signotope h) hd (ih hred)

end BraidDistance
