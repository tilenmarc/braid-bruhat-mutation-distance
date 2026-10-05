import OMDistance.ChiroSetForm
import OMDistance.Signotope
import OMDistance.WalkLemmas

/-!
# Signotopes of rank r: packets and triples of values

* Being a signotope depends only on the values on `r`-sets (`isSignotopeR_agreeInv`).
* For an `(r-2)`-set `σ` and `x < y < z` outside `σ`, the values `u(σ∪xy), u(σ∪xz), u(σ∪yz)` occur in this order in
  the packet of `P = σ ∪ {x, y, z}` (they are `u(P∖z), u(P∖y), u(P∖x)`, and removing a larger element gives a
  lexicographically smaller set).  So for a signotope they have at most one sign change
  (`signotope_triple`).  Conversely, a sequence of signs has at most one sign change iff each of its
  subsequences of length three has, so these conditions for all `σ, x, y, z` characterize signotopes
  (`signotope_of_triples`).  Sets are written as sorted lists via `setVal u σ x y = u (isort (σ ++ [x, y]))`.
-/

namespace OMDistance

open BraidDistance (StrictIncr signChanges oneChange)

/-! ### Sign changes and subsequences -/

private theorem signChanges_le_cons (b : Bool) (l : List Bool) : signChanges l ≤ signChanges (b :: l) := by
  cases l with
  | nil => simp [signChanges]
  | cons c l => simp only [signChanges]; omega

private theorem signChanges_tri (a b : Bool) (l : List Bool) :
    signChanges (a :: l) ≤ (if a = b then 0 else 1) + signChanges (b :: l) := by
  cases l with
  | nil => simp [signChanges]
  | cons c l =>
    simp only [signChanges]
    cases a <;> cases b <;> cases c <;> simp <;> omega

private theorem signChanges_sublist_aux {l₁ l₂ : List Bool} (h : l₁.Sublist l₂) :
    signChanges l₁ ≤ signChanges l₂ ∧ ∀ a, signChanges (a :: l₁) ≤ signChanges (a :: l₂) := by
  induction h with
  | slnil => exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩
  | @cons l₁ l₂ b _ ih =>
    refine ⟨Nat.le_trans ih.1 (signChanges_le_cons b l₂), fun a => ?_⟩
    have h1 := ih.2 a
    have h2 := signChanges_tri a b l₂
    simp only [signChanges]
    omega
  | @cons_cons l₁ l₂ b _ ih =>
    refine ⟨ih.2 b, fun a => ?_⟩
    have := ih.2 b
    simp only [signChanges]
    omega

/-- A subsequence has at most as many sign changes. -/
private theorem signChanges_sublist {l₁ l₂ : List Bool} (h : l₁.Sublist l₂) :
    signChanges l₁ ≤ signChanges l₂ :=
  (signChanges_sublist_aux h).1

private theorem signChanges_const (y : Bool) (l : List Bool) (h : ∀ w ∈ l, w = y) :
    signChanges (y :: l) = 0 := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c = y := h c List.mem_cons_self
    subst hc
    simp only [signChanges, ite_true, Nat.zero_add]
    exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- At least two sign changes give an alternating subsequence of length three. -/
private theorem exists_alt_of_two (l : List Bool) (h : 2 ≤ signChanges l) :
    ∃ a b c : Bool, [a, b, c].Sublist l ∧ a ≠ b ∧ b ≠ c := by
  induction l with
  | nil => simp [signChanges] at h
  | cons x rest ih =>
    cases rest with
    | nil => simp [signChanges] at h
    | cons y rest' =>
      simp only [signChanges] at h
      by_cases h2 : 2 ≤ signChanges (y :: rest')
      · obtain ⟨a, b, c, hs, hab, hbc⟩ := ih h2
        exact ⟨a, b, c, hs.cons x, hab, hbc⟩
      · have hxy : x ≠ y := by
          intro e; simp [e] at h; omega
        have h1 : signChanges (y :: rest') ≠ 0 := by
          intro e; simp only [hxy, ite_false] at h; omega
        have : ∃ w ∈ rest', w ≠ y := by
          apply Classical.byContradiction
          intro hn
          apply h1
          apply signChanges_const
          intro w hw
          apply Classical.byContradiction
          intro hwy
          exact hn ⟨w, hw, hwy⟩
        obtain ⟨w, hw, hwy⟩ := this
        refine ⟨x, y, w, ?_, hxy, fun e => hwy e.symm⟩
        exact ((List.singleton_sublist.2 hw).cons_cons y).cons_cons x

private theorem oneChange_three (a b c : Bool) : oneChange [a, b, c] = true ↔ ¬ (a ≠ b ∧ b ≠ c) := by
  revert a b c; decide

/-! ### Packets as lists indexed by the removed element -/

private theorem map_eraseIdx_range (P : List Nat) (hP : P.Nodup) :
    (List.range P.length).map (fun i => P.eraseIdx i) = P.map (fun p => P.erase p) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    rw [List.nodup_cons] at hP
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
    simp only [List.eraseIdx_cons_zero, List.erase_cons_head]
    congr 1
    have e1 : ((fun i => (a :: P).eraseIdx i) ∘ Nat.succ) = fun i => a :: P.eraseIdx i := by
      funext i; simp
    rw [e1]
    have e2 : P.map (fun p => (a :: P).erase p) = P.map (fun p => a :: P.erase p) := by
      apply List.map_congr_left
      intro p hp
      have hpa : p ≠ a := fun e => hP.1 (e ▸ hp)
      rw [List.erase_cons_tail (by simpa using (Ne.symm hpa))]
    rw [e2]
    have := congrArg (List.map (a :: ·)) (ih hP.2)
    simpa [List.map_map, Function.comp_def] using this

/-- The packet of a set `P` without repetitions, indexed by the removed element, in decreasing order. -/
private theorem rpacket_eq (u : SignMap) (P : List Nat) (hP : P.Nodup) :
    rpacket u P = P.reverse.map (fun p => u (P.erase p)) := by
  unfold rpacket
  have := congrArg (List.map u) (map_eraseIdx_range P hP)
  rw [List.map_map, List.map_map] at this
  rw [List.map_reverse, List.map_reverse]
  exact congrArg List.reverse this

/-- A strictly increasing list whose entries lie in a strictly increasing list `P` is a subsequence of `P`. -/
private theorem strictIncr_sublist {L P : List Nat} (hL : StrictIncr L) (hP : StrictIncr P)
    (hmem : ∀ a ∈ L, a ∈ P) : L.Sublist P := by
  induction P generalizing L with
  | nil =>
    cases L with
    | nil => exact List.Sublist.slnil
    | cons a L => exact absurd (hmem a List.mem_cons_self) List.not_mem_nil
  | cons p P ih =>
    unfold StrictIncr at hP
    rw [List.pairwise_cons] at hP
    cases L with
    | nil => exact List.nil_sublist _
    | cons a L =>
      unfold StrictIncr at hL
      rw [List.pairwise_cons] at hL
      by_cases hap : a = p
      · subst hap
        apply List.Sublist.cons_cons
        apply ih hL.2 hP.2
        intro b hb
        have hab := hL.1 b hb
        rcases List.mem_cons.1 (hmem b (List.mem_cons_of_mem _ hb)) with e | e
        · omega
        · exact e
      · have haP : a ∈ P := by
          rcases List.mem_cons.1 (hmem a List.mem_cons_self) with e | e
          · exact absurd e hap
          · exact e
        have hpa := hP.1 a haP
        apply List.Sublist.cons
        apply ih (by unfold StrictIncr; exact List.pairwise_cons.2 hL) hP.2
        intro b hb
        rcases List.mem_cons.1 hb with e | hb
        · subst e; exact haP
        · have hab := hL.1 b hb
          rcases List.mem_cons.1 (hmem b (List.mem_cons_of_mem _ hb)) with e | e
          · omega
          · exact e

/-- Sorting `l` gives `P ∖ a` when `P` consists of the entries of `l` and `a`. -/
private theorem isort_eq_erase {P l : List Nat} {a : Nat} (hP : StrictIncr P) (hl : l.Nodup) (ha : a ∉ l)
    (hmem : ∀ w, w ∈ P ↔ w ∈ l ∨ w = a) : isort l = P.erase a := by
  have hPn : P.Nodup := hP.imp (fun h => Nat.ne_of_lt h)
  apply isort_eq (hP.sublist List.erase_sublist) hl
  intro w
  rw [hPn.mem_erase_iff, hmem]
  constructor
  · intro hw
    exact ⟨fun e => ha (e ▸ hw), Or.inl hw⟩
  · rintro ⟨hne, hw | hw⟩
    · exact hw
    · exact absurd hw hne

/-- Being a signotope depends only on the values on the `r`-subsets. -/
theorem isSignotopeR_agreeInv (M r : Nat) : AgreeInv M r (IsSignotopeR M r) := by
  intro u u' hag hu P hP
  have e : rpacket u P = rpacket u' P := by
    unfold rpacket
    apply List.map_congr_left
    intro i hi
    rw [List.mem_reverse, List.mem_range, hP.1] at hi
    exact hag _ (hP.eraseIdx hi)
  rw [← e]
  exact hu P hP

/-- In a signotope of rank `r ≥ 2`, the values `u(σ∪xy), u(σ∪xz), u(σ∪yz)` have at most one sign change. -/
theorem signotope_triple {M r : Nat} (hr : 2 ≤ r) {u : SignMap} (hu : IsSignotopeR M r u) {σ : List Nat}
    (hσ : IsRSet M (r - 2) σ) {x y z : Nat} (hxy : x < y) (hyz : y < z) (hzM : z < M) (hx : x ∉ σ) (hy : y ∉ σ)
    (hz : z ∉ σ) :
    BraidDistance.oneChange [setVal u σ x y, setVal u σ x z, setVal u σ y z] = true := by
  have hσn : σ.Nodup := hσ.nodup
  have hxy' : x ≠ y := Nat.ne_of_lt hxy
  have hyz' : y ≠ z := Nat.ne_of_lt hyz
  have hxz' : x ≠ z := Nat.ne_of_lt (Nat.lt_trans hxy hyz)
  have hn : (σ ++ [x, y, z]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hσn, by simp [hxy', hyz', hxz'], ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> contradiction
  let P := isort (σ ++ [x, y, z])
  have hPs : StrictIncr P := isort_strictIncr hn
  have hPmem : ∀ w, w ∈ P ↔ w ∈ σ ∨ w = x ∨ w = y ∨ w = z := by
    intro w; simp [P, mem_isort]
  have hP : IsRSet M (r + 1) P := by
    refine ⟨?_, hPs, ?_⟩
    · simp only [P, length_isort, List.length_append, hσ.1, List.length_cons, List.length_nil]
      omega
    · intro w hw
      rcases (hPmem w).1 hw with h | rfl | rfl | rfl
      · exact hσ.2.2 w h
      · omega
      · omega
      · exact hzM
  have hPn : P.Nodup := hP.nodup
  have h1 : setVal u σ x y = u (P.erase z) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [x, y])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hxy'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hz, Ne.symm hxz', Ne.symm hyz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  have h2 : setVal u σ x z = u (P.erase y) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [x, z])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hxz'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hy, Ne.symm hxy', hyz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  have h3 : setVal u σ y z = u (P.erase x) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [y, z])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hyz'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hx, hxy', hxz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  have hsub : [x, y, z].Sublist P := by
    apply strictIncr_sublist _ hPs
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rw [hPmem]
      rcases hw with rfl | rfl | rfl <;> simp
    · unfold StrictIncr; simp; omega
  have hsub' : [z, y, x].Sublist P.reverse := by
    have := List.reverse_sublist.2 hsub
    simpa using this
  have hsub'' := hsub'.map (fun p => u (P.erase p))
  rw [← rpacket_eq u P hPn] at hsub''
  have hpk := hu P hP
  unfold oneChange at hpk ⊢
  rw [h1, h2, h3]
  have := signChanges_sublist hsub''
  simp only [List.map_cons, List.map_nil] at this
  simp only [decide_eq_true_eq] at hpk ⊢
  omega

/-- A map all of whose triples `u(σ∪xy), u(σ∪xz), u(σ∪yz)` have at most one sign change is a signotope of
rank `r ≥ 2`. -/
theorem signotope_of_triples {M r : Nat} (hr : 2 ≤ r) {u : SignMap}
    (h : ∀ σ, IsRSet M (r - 2) σ → ∀ z < M, ∀ y < z, ∀ x < y, x ∉ σ → y ∉ σ → z ∉ σ →
      BraidDistance.oneChange [setVal u σ x y, setVal u σ x z, setVal u σ y z] = true) :
    IsSignotopeR M r u := by
  intro P hP
  have hPs : StrictIncr P := hP.2.1
  have hPn : P.Nodup := hP.nodup
  cases hoc : oneChange (rpacket u P) with
  | true => rfl
  | false =>
  exfalso
  have h2 : 2 ≤ signChanges (rpacket u P) := by
    unfold oneChange at hoc
    simp only [decide_eq_false_iff_not] at hoc
    omega
  obtain ⟨a, b, c, hs, hab, hbc⟩ := exists_alt_of_two _ h2
  rw [rpacket_eq u P hPn, List.sublist_map_iff] at hs
  obtain ⟨l', hl', hl'eq⟩ := hs
  match l', hl', hl'eq with
  | [z, y, x], hl', hl'eq =>
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl'eq
  obtain ⟨rfl, rfl, rfl⟩ := hl'eq
  have hsub : [x, y, z].Sublist P := by
    have := List.reverse_sublist.2 hl'
    simpa using this
  have hinc : StrictIncr [x, y, z] := hPs.sublist hsub
  have hxy : x < y := by unfold StrictIncr at hinc; simp at hinc; omega
  have hyz : y < z := by unfold StrictIncr at hinc; simp at hinc; omega
  have hxP : x ∈ P := hsub.subset (by simp)
  have hyP : y ∈ P := hsub.subset (by simp)
  have hzP : z ∈ P := hsub.subset (by simp)
  have hzM : z < M := hP.2.2 z hzP
  let σ := ((P.erase x).erase y).erase z
  have hn1 : (P.erase x).Nodup := hPn.erase x
  have hn2 : ((P.erase x).erase y).Nodup := hn1.erase y
  have hσmem : ∀ w, w ∈ σ ↔ w ≠ z ∧ w ≠ y ∧ w ≠ x ∧ w ∈ P := by
    intro w
    simp only [σ, hn2.mem_erase_iff, hn1.mem_erase_iff, hPn.mem_erase_iff]
  have hxy' : x ≠ y := Nat.ne_of_lt hxy
  have hyz' : y ≠ z := Nat.ne_of_lt hyz
  have hxz' : x ≠ z := Nat.ne_of_lt (Nat.lt_trans hxy hyz)
  have hσ : IsRSet M (r - 2) σ := by
    refine ⟨?_, ?_, ?_⟩
    · have e1 := List.length_erase_of_mem hxP
      have e2 := List.length_erase_of_mem ((hPn.mem_erase_iff).2 ⟨Ne.symm hxy', hyP⟩)
      have e3 := List.length_erase_of_mem
        ((hn1.mem_erase_iff).2 ⟨Ne.symm hyz', (hPn.mem_erase_iff).2 ⟨Ne.symm hxz', hzP⟩⟩)
      simp only [σ]
      rw [e3, e2, e1, hP.1]
      omega
    · exact hPs.sublist ((List.erase_sublist).trans ((List.erase_sublist).trans List.erase_sublist))
    · intro w hw
      exact hP.2.2 w ((hσmem w).1 hw).2.2.2
  have hσn : σ.Nodup := hσ.nodup
  have hx : x ∉ σ := fun h => ((hσmem x).1 h).2.2.1 rfl
  have hy : y ∉ σ := fun h => ((hσmem y).1 h).2.1 rfl
  have hz : z ∉ σ := fun h => ((hσmem z).1 h).1 rfl
  have key := h σ hσ z hzM y hyz x hxy hx hy hz
  have hPmem : ∀ w, w ∈ P ↔ w ∈ σ ∨ w = x ∨ w = y ∨ w = z := by
    intro w
    rw [hσmem]
    constructor
    · intro hw
      by_cases e1 : w = z
      · exact Or.inr (Or.inr (Or.inr e1))
      by_cases e2 : w = y
      · exact Or.inr (Or.inr (Or.inl e2))
      by_cases e3 : w = x
      · exact Or.inr (Or.inl e3)
      exact Or.inl ⟨e1, e2, e3, hw⟩
    · rintro (h | rfl | rfl | rfl)
      · exact h.2.2.2
      · exact hxP
      · exact hyP
      · exact hzP
  have h1 : setVal u σ x y = u (P.erase z) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [x, y])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hxy'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hz, Ne.symm hxz', Ne.symm hyz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  have h2 : setVal u σ x z = u (P.erase y) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [x, z])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hxz'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hy, Ne.symm hxy', hyz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  have h3 : setVal u σ y z = u (P.erase x) := by
    unfold setVal
    rw [isort_eq_erase hPs (l := σ ++ [y, z])]
    · rw [List.nodup_append]
      refine ⟨hσn, by simp [hyz'], ?_⟩
      intro a ha b hb e; subst e
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> contradiction
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hx, hxy', hxz'⟩
    · intro w; rw [hPmem]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (h | h | h | h) <;> simp [h]
      · rintro ((h | h | h) | h) <;> simp [h]
  rw [h1, h2, h3, oneChange_three] at key
  exact key ⟨hab, hbc⟩

end OMDistance
