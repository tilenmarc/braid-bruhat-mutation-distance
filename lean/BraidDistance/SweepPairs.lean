import BraidDistance.Sweep

/-!
# The shadow sweep exchanges every pair of groups once (Lemma 4.2)

* Lemma 4.2: every pair of distinct groups is exchanged exactly once, and always from label order: listing for
  each event the pairs of groups it exchanges (`evPairs`, each pair in label order) gives a permutation of the
  list of all pairs of groups in label order (`sweep_pairs`).
* The cells are exactly the cells of the edges (`sweep_cell_iff`).
-/

namespace BraidDistance

/-! ### Generic permutation lemmas -/

/-- Pointwise permutations inside a `flatMap`. -/
private theorem SP.flatMap_perm_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih fun b hb => h b (by simp [hb]))

private theorem SP.flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- A `flatMap` of concatenations splits into two `flatMap`s. -/
private theorem SP.flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    have h1 := (ih.append_left (f a ++ g a))
    refine h1.trans ?_
    simp only [List.append_assoc]
    refine List.Perm.append_left (f a) ?_
    simp only [← List.append_assoc]
    exact (List.perm_append_comm.append_right _)

/-- The pairs `(g, h)` with `g ∈ A`, `h ∈ B`, listed column by column. -/
private def SP.prod {α : Type} (A B : List α) : List (α × α) :=
  B.flatMap fun h => A.map fun g => (g, h)

private theorem SP.flatMap_singleton_map {α β : Type} (l : List α) (f : α → β) :
    (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem SP.flatMap_nil {α β : Type} (l : List α) : (l.flatMap fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem SP.prod_cons {α : Type} (x : α) (A B : List α) :
    (SP.prod (x :: A) B).Perm (B.map (fun h => (x, h)) ++ SP.prod A B) := by
  unfold SP.prod
  have := SP.flatMap_append_perm B (fun h => [(x, h)]) (fun h => A.map fun g => (g, h))
  simp only [List.map_cons]
  refine (List.Perm.of_eq ?_).trans (this.trans (List.Perm.of_eq ?_))
  · rfl
  · rw [SP.flatMap_singleton_map]

private theorem SP.orderedPairs_append {α : Type} [DecidableEq α] (A B : List α) :
    (orderedPairs (A ++ B)).Perm (orderedPairs A ++ orderedPairs B ++ SP.prod A B) := by
  induction A with
  | nil => simp [orderedPairs, SP.prod, SP.flatMap_nil]
  | cons x A ih =>
    simp only [List.cons_append, orderedPairs, List.map_append]
    have h2 := SP.prod_cons x A B
    rw [List.perm_iff_count] at ih h2 ⊢
    intro c
    simp only [List.count_append] at ih h2 ⊢
    rw [ih c, h2 c]
    omega

private theorem SP.prod_flatMap {α β : Type} (A : List α) (l : List β) (f : β → List α) :
    SP.prod A (l.flatMap f) = l.flatMap fun w => SP.prod A (f w) := by
  unfold SP.prod
  rw [List.flatMap_assoc]

/-- The ordered pairs of a concatenation of blocks: the pairs inside each block, and the pairs of a block with
every later block. -/
private theorem SP.orderedPairs_flatMap_range' {α : Type} [DecidableEq α] (f : Nat → List α) (k : Nat) :
    ∀ s, (orderedPairs ((List.range' s k).flatMap f)).Perm
      ((List.range' s k).flatMap fun u =>
        orderedPairs (f u) ++ (List.range' (u + 1) (s + k - (u + 1))).flatMap fun w => SP.prod (f u) (f w)) := by
  induction k with
  | zero => intro s; simp [orderedPairs]
  | succ k ih =>
    intro s
    simp only [List.range'_succ, List.flatMap_cons]
    refine (SP.orderedPairs_append _ _).trans ?_
    have hk : s + (k + 1) - (s + 1) = k := by omega
    rw [hk, SP.prod_flatMap]
    have e : (List.range' (s + 1) k).flatMap (fun u =>
        orderedPairs (f u) ++ (List.range' (u + 1) (s + (k + 1) - (u + 1))).flatMap fun w => SP.prod (f u) (f w)) =
        (List.range' (s + 1) k).flatMap (fun u =>
        orderedPairs (f u) ++ (List.range' (u + 1) (s + 1 + k - (u + 1))).flatMap fun w => SP.prod (f u) (f w)) := by
      have : s + (k + 1) = s + 1 + k := by omega
      rw [this]
    rw [e]
    have h1 := ih (s + 1)
    rw [List.perm_iff_count] at h1 ⊢
    intro c
    simp only [List.count_append] at h1 ⊢
    rw [h1 c]
    omega

/-- The pairs of a list listed column by column (the `j`-th element with every element above it). -/
private theorem SP.colPairs_snoc {α : Type} [DecidableEq α] (d : α) (l : List α) :
    ((List.range l.reverse.length).flatMap fun j =>
        (l.reverse.take j).map fun g => (g, l.reverse.getD j d)).Perm (orderedPairs l.reverse) := by
  induction l with
  | nil => simp [orderedPairs]
  | cons x l ih =>
    simp only [List.reverse_cons, List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e1 : ((List.range l.reverse.length).flatMap fun j =>
        ((l.reverse ++ [x]).take j).map fun g => (g, (l.reverse ++ [x]).getD j d)) =
        ((List.range l.reverse.length).flatMap fun j =>
        (l.reverse.take j).map fun g => (g, l.reverse.getD j d)) := by
      apply SP.flatMap_congr
      intro j hj
      rw [List.mem_range] at hj
      rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [e1]
    have e2 : (l.reverse ++ [x]).take l.reverse.length = l.reverse := by simp
    have e3 : (l.reverse ++ [x]).getD l.reverse.length d = x := by simp [List.getD_eq_getElem?_getD]
    rw [e2, e3]
    refine (ih.append_right _).trans ?_
    refine List.Perm.trans ?_ (SP.orderedPairs_append _ _).symm
    simp [orderedPairs, SP.prod]

/-! ### The pairs of one pass -/

private theorem SP.count_filter_ite {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) (x : α) :
    (l.filter p).count x = if p x then l.count x else 0 := by
  by_cases h : p x
  · simp [h, List.count_filter]
  · simp only [h]
    exact List.count_eq_zero.2 fun hm => h (List.mem_filter.1 hm).2

private theorem SP.split_perm (l : List Nat) (hl : l.Nodup) {w : Nat} (hw : w ∈ l) :
    l.Perm (l.filter (· < w) ++ w :: l.filter (w < ·)) := by
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append, List.count_cons, SP.count_filter_ite]
  by_cases h1 : x < w
  · have : (w == x) = false := by simp; omega
    simp [h1, this]; omega
  · by_cases h2 : x = w
    · subst h2
      simp [hl.count_of_mem hw]
    · have : (w == x) = false := by simp; omega
      have h3 : w < x := by omega
      simp [h1, h3, this]

private theorem SP.mvs_pairs (l : List Grp) (h : Grp) :
    (l.map fun g => Ev.mv g h).flatMap evPairs = l.map fun g => (g, h) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, evPairs]

private theorem SP.pass_edge_abstract (Xu Xw puw : Grp) (Bl Ab Pu Pw : List Grp)
    (hP : Pu.Perm (Bl ++ puw :: Ab)) :
    ((Ab.reverse.map fun g => (g, Xw)) ++ [(Xu, puw), (Xu, Xw), (puw, Xw)] ++
        (Bl.reverse.map fun g => (g, Xw)) ++
        Pw.flatMap (fun x => (Bl ++ [puw, Xu] ++ Ab).reverse.map fun g => (g, x))).Perm
      (SP.prod (Xu :: Pu) (Xw :: Pw) ++ [(Xu, puw)]) := by
  have L1 : (Bl ++ [puw, Xu] ++ Ab).reverse.Perm (Xu :: Pu) := by
    rw [List.perm_iff_count]; intro c
    have := hP.count_eq c
    simp only [List.count_reverse, List.count_append, List.count_cons, List.count_nil] at this ⊢
    omega
  have L2 : (Ab.reverse ++ [Xu, puw] ++ Bl.reverse).Perm (Xu :: Pu) := by
    rw [List.perm_iff_count]; intro c
    have := hP.count_eq c
    simp only [List.count_reverse, List.count_append, List.count_cons, List.count_nil] at this ⊢
    omega
  have Q : (Pw.flatMap fun x => (Bl ++ [puw, Xu] ++ Ab).reverse.map fun g => (g, x)).Perm
      (Pw.flatMap fun x => (Xu :: Pu).map fun g => (g, x)) :=
    SP.flatMap_perm_congr fun x _ => L1.map _
  have P := L2.map (fun g => (g, Xw))
  unfold SP.prod
  simp only [List.flatMap_cons]
  rw [List.perm_iff_count]; intro c
  have h1 := P.count_eq c
  have h2 := Q.count_eq c
  simp only [List.map_append, List.count_append, List.map_cons, List.map_nil, List.count_cons,
    List.count_nil] at h1 h2 ⊢
  omega

private theorem SP.pass_nonedge_abstract (Xu Xw : Grp) (Bl Ab Pu Pw : List Grp)
    (hP : Pu.Perm (Bl ++ Ab)) :
    ((Ab.reverse.map fun g => (g, Xw)) ++ [(Xu, Xw)] ++
        (Bl.reverse.map fun g => (g, Xw)) ++
        Pw.flatMap (fun x => (Bl ++ [Xu] ++ Ab).reverse.map fun g => (g, x))).Perm
      (SP.prod (Xu :: Pu) (Xw :: Pw)) := by
  have L1 : (Bl ++ [Xu] ++ Ab).reverse.Perm (Xu :: Pu) := by
    rw [List.perm_iff_count]; intro c
    have := hP.count_eq c
    simp only [List.count_reverse, List.count_append, List.count_cons, List.count_nil] at this ⊢
    omega
  have L2 : (Ab.reverse ++ [Xu] ++ Bl.reverse).Perm (Xu :: Pu) := by
    rw [List.perm_iff_count]; intro c
    have := hP.count_eq c
    simp only [List.count_reverse, List.count_append, List.count_cons, List.count_nil] at this ⊢
    omega
  have Q : (Pw.flatMap fun x => (Bl ++ [Xu] ++ Ab).reverse.map fun g => (g, x)).Perm
      (Pw.flatMap fun x => (Xu :: Pu).map fun g => (g, x)) :=
    SP.flatMap_perm_congr fun x _ => L1.map _
  have P := L2.map (fun g => (g, Xw))
  unfold SP.prod
  simp only [List.flatMap_cons]
  rw [List.perm_iff_count]; intro c
  have h1 := P.count_eq c
  have h2 := Q.count_eq c
  simp only [List.map_append, List.count_append, List.map_cons, List.map_nil, List.count_cons,
    List.count_nil] at h1 h2 ⊢
  omega

private theorem SP.up_nodup (G : Graph) (u : Nat) : (G.up u).Nodup :=
  List.Nodup.sublist (List.filter_sublist) List.nodup_range

private theorem SP.mem_up (G : Graph) (u w : Nat) :
    w ∈ G.up u ↔ w < G.n ∧ u < w ∧ G.isEdge u w = true := by
  simp [Graph.up]

private theorem SP.pass_pairs (G : Graph) (u w : Nat) (huw : u < w) (hw : w < G.n) :
    ((passEvents G u w).flatMap evPairs).Perm
      (SP.prod (bundle G u) (bundle G w) ++ if G.isEdge u w then [(Grp.X u, Grp.p u w)] else []) := by
  unfold passEvents bundle
  by_cases he : G.isEdge u w
  · simp only [he, ite_true, List.flatMap_append, SP.mvs_pairs, List.flatMap_assoc, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, evPairs]
    have hwu : w ∈ G.up u := (SP.mem_up G u w).2 ⟨hw, huw, he⟩
    have hP := (SP.split_perm (G.up u) (SP.up_nodup G u) hwu).map (Grp.p u)
    simp only [List.map_append, List.map_cons] at hP
    exact SP.pass_edge_abstract _ _ _ _ _ _ _ hP
  · simp only [he, Bool.false_eq_true, ite_false, List.flatMap_append, SP.mvs_pairs, List.flatMap_assoc,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, evPairs]
    have hP := (List.filter_append_perm (fun x => decide (x < w)) (G.up u)).symm.map (Grp.p u)
    have e : (G.up u).filter (fun x => !decide (x < w)) = (G.up u).filter (fun x => decide (w ≤ x)) :=
      List.filter_congr fun x _ => by by_cases h : x < w <;> simp [h] <;> omega
    rw [e] at hP
    simp only [List.map_append] at hP
    exact SP.pass_nonedge_abstract _ _ _ _ _ _ hP

/-! ### The completion and the cells -/

private theorem SP.colPairs {α : Type} [DecidableEq α] (d : α) (ps : List α) :
    ((List.range ps.length).flatMap fun j =>
        (ps.take j).map fun g => (g, ps.getD j d)).Perm (orderedPairs ps) := by
  have := SP.colPairs_snoc d ps.reverse
  rw [List.reverse_reverse] at this
  exact this

private theorem SP.completion_pairs (G : Graph) (u : Nat) :
    ((completionEvents G u).flatMap evPairs).Perm (orderedPairs ((G.up u).map (Grp.p u))) := by
  unfold completionEvents
  simp only [List.flatMap_assoc]
  rw [SP.flatMap_congr fun j _ => SP.mvs_pairs _ _]
  exact SP.colPairs _ _

private theorem SP.filter_map_eq {α β : Type} (l : List α) (p : α → Bool) (F : α → β) :
    (l.filter p).map F = l.flatMap fun w => if p w then [F w] else [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

/-- The pairs `(X_u, p_{uw})` exchanged in the cells of round `u`. -/
private theorem SP.cells_pairs (G : Graph) {u : Nat} (hu : u < G.n) :
    ((List.range' (u + 1) (G.n - (u + 1))).flatMap fun w =>
        if G.isEdge u w then [(Grp.X u, Grp.p u w)] else []) =
      ((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h) := by
  rw [List.map_map]
  have e : G.up u = (List.range' (u + 1) (G.n - (u + 1))).filter (G.isEdge u) := by
    unfold Graph.up
    rw [List.range_eq_range']
    have : G.n = (u + 1) + (G.n - (u + 1)) := by omega
    conv => lhs; rw [this]
    rw [← @List.range'_append 0 (u + 1) (G.n - (u + 1)) 1, List.filter_append]
    have h0 : (List.range' 0 (u + 1)).filter (fun w => decide (u < w) && G.isEdge u w) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      rw [List.mem_range'_1] at ha
      simp; omega
    rw [h0, List.nil_append]
    simp only [Nat.one_mul, Nat.zero_add]
    apply List.filter_congr
    intro a ha
    rw [List.mem_range'_1] at ha
    simp; omega
  rw [e, SP.filter_map_eq]
  rfl

end BraidDistance

namespace BraidDistance

private theorem SP.cell_mem_pass (G : Graph) (u w a b : Nat) :
    Ev.cell a b ∈ passEvents G u w ↔ G.isEdge u w = true ∧ a = u ∧ b = w := by
  unfold passEvents
  by_cases he : G.isEdge u w
  · simp [he, List.mem_flatMap]
  · simp [he, List.mem_flatMap]

private theorem SP.cell_not_mem_completion (G : Graph) (u a b : Nat) :
    Ev.cell a b ∉ completionEvents G u := by
  unfold completionEvents
  simp only [List.mem_flatMap, List.mem_map, not_exists, not_and]
  intro j _ g _ h
  cases h

/-- Lemma 4.2: every pair of groups is exchanged exactly once, from label order. -/
theorem sweep_pairs (G : Graph) (_hG : G.Valid) :
    ((sweepEvents G).flatMap evPairs).Perm (orderedPairs (labelOrder G)) := by
  have hL : ((sweepEvents G).flatMap evPairs).Perm
      ((List.range G.n).flatMap (fun u =>
          ((List.range' (u + 1) (G.n - (u + 1))).flatMap fun w => SP.prod (bundle G u) (bundle G w)) ++
          (((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h))) ++
        (List.range G.n).flatMap (fun u => orderedPairs ((G.up u).map (Grp.p u)))) := by
    unfold sweepEvents
    rw [List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
    refine List.Perm.append ?_ (SP.flatMap_perm_congr fun u _ => SP.completion_pairs G u)
    refine SP.flatMap_perm_congr fun u hu => ?_
    have hu' : u < G.n := List.mem_range.1 hu
    unfold roundEvents
    rw [List.flatMap_assoc]
    refine (SP.flatMap_perm_congr fun w hw => SP.pass_pairs G u w ?_ ?_).trans ?_
    · rw [List.mem_range'_1] at hw; omega
    · rw [List.mem_range'_1] at hw; omega
    refine (SP.flatMap_append_perm _ _ _).trans ?_
    rw [SP.cells_pairs G hu']
  have hR : (orderedPairs (labelOrder G)).Perm
      ((List.range G.n).flatMap (fun u =>
          ((((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h)) ++ orderedPairs ((G.up u).map (Grp.p u))) ++
          ((List.range' (u + 1) (G.n - (u + 1))).flatMap fun w => SP.prod (bundle G u) (bundle G w)))) := by
    unfold labelOrder
    rw [List.range_eq_range']
    have := SP.orderedPairs_flatMap_range' (bundle G) G.n 0
    simp only [Nat.zero_add] at this
    exact this
  refine hL.trans (List.Perm.trans ?_ hR.symm)
  have h1 := SP.flatMap_append_perm (List.range G.n)
    (fun u => (List.range' (u + 1) (G.n - (u + 1))).flatMap fun w => SP.prod (bundle G u) (bundle G w))
    (fun u => ((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h))
  have h2 := SP.flatMap_append_perm (List.range G.n)
    (fun u => (((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h)) ++ orderedPairs ((G.up u).map (Grp.p u)))
    (fun u => (List.range' (u + 1) (G.n - (u + 1))).flatMap fun w => SP.prod (bundle G u) (bundle G w))
  have h3 := SP.flatMap_append_perm (List.range G.n)
    (fun u => ((G.up u).map (Grp.p u)).map fun h => (Grp.X u, h))
    (fun u => orderedPairs ((G.up u).map (Grp.p u)))
  rw [List.perm_iff_count]
  intro c
  rw [List.count_append, h1.count_eq, h2.count_eq, List.count_append, List.count_append, h3.count_eq,
    List.count_append]
  omega

/-- The cells of the sweep are the cells of the edges. -/
theorem sweep_cell_iff (G : Graph) (hG : G.Valid) (u w : Nat) :
    Ev.cell u w ∈ sweepEvents G ↔ (u, w) ∈ G.edges := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨u', _, h'⟩ := List.mem_flatMap.1 h
      unfold roundEvents at h'
      obtain ⟨w', _, h''⟩ := List.mem_flatMap.1 h'
      obtain ⟨he, rfl, rfl⟩ := (SP.cell_mem_pass G u' w' u w).1 h''
      exact List.contains_iff_mem.1 he
    · obtain ⟨u', _, h'⟩ := List.mem_flatMap.1 h
      exact absurd h' (SP.cell_not_mem_completion G u' u w)
  · intro h
    have hb := hG.2 _ h
    simp only at hb
    refine List.mem_append_left _ (List.mem_flatMap.2 ⟨u, List.mem_range.2 (by omega), ?_⟩)
    unfold roundEvents
    refine List.mem_flatMap.2 ⟨w, List.mem_range'_1.2 ⟨by omega, by omega⟩, ?_⟩
    exact (SP.cell_mem_pass G u w u w).2 ⟨List.contains_iff_mem.2 h, rfl, rfl⟩

end BraidDistance
