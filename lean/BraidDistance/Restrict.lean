import BraidDistance.BasicLemmas

/-!
# Restricting signotopes and walks to a subset (deleting elements)

For a strictly increasing list `z` of elements of `[m]` (the kept elements, renumbered `0, …, r-1`):

* the restriction `pull z u` of a signotope is a signotope (its packets are packets of `u`);
* a flip walk restricts to a flip walk on `[r]`: keep the flips of triples inside `z`, renumbered
  (`localize z ts`); the other flips do not change the restriction.  This is the signotope form of Lemma 2.6
  (deleting wires), with one flip for each flip of the original walk inside `z`;
* a local triple is flipped as often as its image in the original walk;
* if two maps agree outside the triples of `z`, their Hamming distance is that of the restrictions.
-/

namespace BraidDistance

private theorem R_getD_eq {z : List Nat} {i : Nat} (h : i < z.length) : z.getD i 0 = z[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem R_getD_lt {z : List Nat} (hz : StrictIncr z) {i j : Nat} (hij : i < j)
    (hj : j < z.length) : z.getD i 0 < z.getD j 0 := by
  rw [R_getD_eq (Nat.lt_trans hij hj), R_getD_eq hj]
  exact List.pairwise_iff_getElem.1 hz i j (Nat.lt_trans hij hj) hj hij

private theorem R_getD_mem {z : List Nat} {i : Nat} (h : i < z.length) : z.getD i 0 ∈ z := by
  rw [R_getD_eq h]; exact List.getElem_mem h

private theorem R_nodup {z : List Nat} (hz : StrictIncr z) : z.Nodup :=
  List.Pairwise.imp (fun h => Nat.ne_of_lt h) hz

private theorem R_idxOf_getD {z : List Nat} (hz : StrictIncr z) {i : Nat} (h : i < z.length) :
    z.idxOf (z.getD i 0) = i := by
  rw [R_getD_eq h]; exact (R_nodup hz).idxOf_getElem i h

private theorem R_idxOf_lt {z : List Nat} {x : Nat} (h : x ∈ z) : z.idxOf x < z.length :=
  List.idxOf_lt_length_of_mem h

private theorem R_getD_idxOf {z : List Nat} {x : Nat} (h : x ∈ z) : z.getD (z.idxOf x) 0 = x := by
  rw [R_getD_eq (R_idxOf_lt h)]; exact List.getElem_idxOf _

private theorem R_idxOf_mono {z : List Nat} (hz : StrictIncr z) {x y : Nat} (hx : x ∈ z) (hy : y ∈ z)
    (hxy : x < y) : z.idxOf x < z.idxOf y := by
  rcases Nat.lt_trichotomy (z.idxOf x) (z.idxOf y) with h | h | h
  · exact h
  · have := congrArg (fun i => z.getD i 0) h
    simp only [R_getD_idxOf hx, R_getD_idxOf hy] at this
    omega
  · have := R_getD_lt hz h (R_idxOf_lt hx)
    rw [R_getD_idxOf hx, R_getD_idxOf hy] at this
    omega

/-- The renumbering of a triple inside `z` (the map used by `localize`). -/
private def R_loc (z : List Nat) (t : Triple) : Triple := (z.idxOf t.1, z.idxOf t.2.1, z.idxOf t.2.2)

private theorem R_loc_spec {z : List Nat} (hz : StrictIncr z) {t : Triple} (h12 : t.1 < t.2.1)
    (h23 : t.2.1 < t.2.2) (hin : Inside z t) :
    ValidTriple z.length (R_loc z t) ∧ embT z (R_loc z t) = t := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc⟩ := hin
  refine ⟨⟨R_idxOf_mono hz ha hb h12, R_idxOf_mono hz hb hc h23, R_idxOf_lt hc⟩, ?_⟩
  simp only [embT, R_loc, R_getD_idxOf ha, R_getD_idxOf hb, R_getD_idxOf hc]

private theorem R_loc_embT {z : List Nat} (hz : StrictIncr z) {t : Triple}
    (ht : ValidTriple z.length t) : R_loc z (embT z t) = t := by
  obtain ⟨i, j, k⟩ := t
  obtain ⟨h1, h2, h3⟩ := ht
  simp only [embT, R_loc, R_idxOf_getD hz h3, R_idxOf_getD hz (Nat.lt_trans h2 h3),
    R_idxOf_getD hz (Nat.lt_trans h1 (Nat.lt_trans h2 h3))]

private theorem R_localize_cons (z : List Nat) (t : Triple) (ts : List Triple) :
    localize z (t :: ts) = if Inside z t then R_loc z t :: localize z ts else localize z ts := by
  unfold localize
  rw [List.filterMap_cons]
  by_cases h : Inside z t <;> simp [h, R_loc]

private theorem R_prefix (z : List Nat) (ts : List Triple) (i : Nat) :
    ∃ j, j ≤ ts.length ∧ localize z (ts.take j) = (localize z ts).take i := by
  induction ts generalizing i with
  | nil => exact ⟨0, Nat.le_refl _, by simp [localize]⟩
  | cons t0 ts ih =>
    cases i with
    | zero => exact ⟨0, Nat.zero_le _, by simp [localize]⟩
    | succ i =>
      by_cases hin : Inside z t0
      · obtain ⟨j, hj, he⟩ := ih i
        refine ⟨j + 1, by simp; omega, ?_⟩
        rw [List.take_succ_cons, R_localize_cons, R_localize_cons]
        simp only [hin, ↓reduceIte]
        rw [List.take_succ_cons, he]
      · obtain ⟨j, hj, he⟩ := ih (i + 1)
        refine ⟨j + 1, by simp; omega, ?_⟩
        rw [List.take_succ_cons, R_localize_cons, R_localize_cons]
        simp only [hin, ↓reduceIte]
        rw [he]

theorem embT_valid {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m) {t : Triple}
    (ht : ValidTriple z.length t) : ValidTriple m (embT z t) ∧ Inside z (embT z t) := by
  obtain ⟨i, j, k⟩ := t
  obtain ⟨h1, h2, h3⟩ := ht
  refine ⟨⟨R_getD_lt hz h1 (Nat.lt_trans h2 h3), R_getD_lt hz h2 h3, hzm _ (R_getD_mem h3)⟩,
    R_getD_mem (Nat.lt_trans h1 (Nat.lt_trans h2 h3)), R_getD_mem (Nat.lt_trans h2 h3), R_getD_mem h3⟩

theorem embT_inj {z : List Nat} (hz : StrictIncr z) {t t' : Triple} (ht : ValidTriple z.length t)
    (ht' : ValidTriple z.length t') (h : embT z t = embT z t') : t = t' := by
  rw [← R_loc_embT hz ht, ← R_loc_embT hz ht', h]

/-- Every valid triple inside `z` is the image of a local triple. -/
theorem exists_embT {m : Nat} {z : List Nat} (hz : StrictIncr z) {t : Triple} (ht : ValidTriple m t)
    (hin : Inside z t) : ∃ t', ValidTriple z.length t' ∧ embT z t' = t := by
  exact ⟨R_loc z t, R_loc_spec hz ht.1 ht.2.1 hin⟩

theorem pull_at (z : List Nat) (u : SMap) (t : Triple) : (pull z u).at t = u.at (embT z t) := rfl

theorem pull_agree {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m) {u u' : SMap}
    (h : Agree m u u') : Agree z.length (pull z u) (pull z u') := by
  intro a b c h1 h2 h3
  have hv := (embT_valid hz hzm (t := (a, b, c)) ⟨h1, h2, h3⟩).1
  exact h _ _ _ hv.1 hv.2.1 hv.2.2

theorem pull_signotope {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m) {u : SMap}
    (hu : IsSignotope m u) : IsSignotope z.length (pull z u) := by
  intro d hd c hc b hb a ha
  exact hu (z.getD d 0) (hzm _ (R_getD_mem hd)) (z.getD c 0) (R_getD_lt hz hc hd) (z.getD b 0)
    (R_getD_lt hz hb (Nat.lt_trans hc hd)) (z.getD a 0)
    (R_getD_lt hz ha (Nat.lt_trans hb (Nat.lt_trans hc hd)))

private theorem R_count_localize {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m)
    {ts : List Triple} (hv : ∀ t ∈ ts, ValidTriple m t) {t : Triple} (ht : ValidTriple z.length t) :
    (localize z ts).count t = ts.count (embT z t) := by
  induction ts with
  | nil => rfl
  | cons t0 ts ih =>
    have ih' := ih (fun t h => hv t (List.mem_cons_of_mem _ h))
    rw [R_localize_cons]
    by_cases hin : Inside z t0
    · simp only [hin, ↓reduceIte]
      rw [List.count_cons, List.count_cons, ih']
      have hiff : R_loc z t0 = t ↔ t0 = embT z t := by
        constructor
        · intro h
          have hv0 := hv t0 (List.mem_cons_self ..)
          rw [← h, (R_loc_spec hz hv0.1 hv0.2.1 hin).2]
        · intro h
          rw [h, R_loc_embT hz ht]
      by_cases h : t0 = embT z t
      · simp [h, R_loc_embT hz ht]
      · have h' : ¬ R_loc z t0 = t := fun h' => h (hiff.1 h')
        simp [h, h']
    · simp only [hin, ↓reduceIte]
      rw [List.count_cons, ih']
      have : t0 ≠ embT z t := fun h => hin (h ▸ (embT_valid hz hzm ht).2)
      simp [this]

/-- Restriction commutes with flipping. -/
theorem pull_flipList {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m) (u : SMap)
    {ts : List Triple} (hv : ∀ t ∈ ts, ValidTriple m t) :
    Agree z.length (pull z (flipList u ts)) (flipList (pull z u) (localize z ts)) := by
  intro a b c h1 h2 h3
  have e1 := flipList_at u ts (embT z (a, b, c))
  have e2 := flipList_at (pull z u) (localize z ts) (a, b, c)
  rw [R_count_localize hz hzm hv ⟨h1, h2, h3⟩] at e2
  show (flipList u ts).at (embT z (a, b, c)) = (flipList (pull z u) (localize z ts)).at (a, b, c)
  rw [e1, e2]
  rfl

/-- A flip walk restricts to a flip walk. -/
theorem flipWalk_restrict {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m)
    {s : SMap} {ts : List Triple} (hw : FlipWalk m s ts) :
    FlipWalk z.length (pull z s) (localize z ts) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    unfold localize at ht
    rw [List.mem_filterMap] at ht
    obtain ⟨t0, ht0, he⟩ := ht
    by_cases hin : Inside z t0
    · simp only [hin, ↓reduceIte] at he
      cases he
      have hv0 := hw.1 t0 ht0
      exact (R_loc_spec hz hv0.1 hv0.2.1 hin).1
    · simp only [hin, ↓reduceIte] at he
      cases he
  · intro i _
    obtain ⟨j, hj, he⟩ := R_prefix z ts i
    rw [← he]
    exact IsSignotope.congr
      (pull_flipList hz hzm s (fun t h => hw.1 t (List.mem_of_mem_take h)))
      (pull_signotope hz hzm (hw.2 j hj))

/-- A local triple is flipped as often as its image. -/
theorem count_localize {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m)
    {ts : List Triple} (hv : ∀ t ∈ ts, ValidTriple m t) {t : Triple} (ht : ValidTriple z.length t) :
    (localize z ts).count t = ts.count (embT z t) := by
  exact R_count_localize hz hzm hv ht

/-- Maps agreeing outside `z` have the Hamming distance of their restrictions to `z`. -/
theorem hamming_pull {m : Nat} {z : List Nat} (hz : StrictIncr z) (hzm : ∀ x ∈ z, x < m) {u v : SMap}
    (hout : ∀ t : Triple, ValidTriple m t → ¬ Inside z t → u.at t = v.at t) :
    hamming m u v = hamming z.length (pull z u) (pull z v) := by
  unfold hamming
  have hnd : ((diffList z.length (pull z u) (pull z v)).map (embT z)).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (diffList_nodup z.length (pull z u) (pull z v))
    intro a b ha hb hab he
    exact hab (embT_inj hz (mem_diffList.1 ha).1 (mem_diffList.1 hb).1 he)
  have hperm : (diffList m u v).Perm ((diffList z.length (pull z u) (pull z v)).map (embT z)) := by
    rw [List.perm_ext_iff_of_nodup (diffList_nodup _ _ _) hnd]
    intro t
    rw [mem_diffList, List.mem_map]
    constructor
    · rintro ⟨hvt, hne⟩
      have hin : Inside z t := Classical.byContradiction fun h => hne (hout t hvt h)
      obtain ⟨t', ht', rfl⟩ := exists_embT hz hvt hin
      exact ⟨t', mem_diffList.2 ⟨ht', hne⟩, rfl⟩
    · rintro ⟨t', ht', rfl⟩
      rw [mem_diffList] at ht'
      exact ⟨(embT_valid hz hzm ht'.1).1, ht'.2⟩
  rw [hperm.length_eq, List.length_map]

end BraidDistance
