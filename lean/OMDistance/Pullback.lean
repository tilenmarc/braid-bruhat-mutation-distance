import OMDistance.WalkLemmas

/-!
# Pulling walks back along a relabelling of bases (the mechanism of Lemma 6.6)

Restriction, deletion and contraction of sign maps all have the form `u ↦ u ∘ φ`, where `φ` maps the
`r'`-subsets of a ground set `[M']` injectively to `r`-subsets of `[M]` (`Relabel M' r' M r φ`):

* restriction to an increasing list `z` (Lemma 6.6, restriction): `φ X = X.map (z.getD · 0)`, `r' = r`;
* the minor `χ_Y` of Proposition 8.5 (contract the elements of a `q`-set `Y ⊆ [c]` and delete the rest of
  `[c]`): `φ Z = Y ++ Z.map (· + c)`, `r = q + r'`.

A flip list `Xs` from `u` induces the flip list `preimages M' r' φ Xs` from `u ∘ φ`: the steps flipping a set in
the image of `φ` survive (as the flip of its preimage), the other steps disappear.  So a walk gives a walk on the
minor, with one step for each step flipping a set in the image (Lemma 6.6).
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- `φ` maps the `r'`-subsets of `[M']` injectively to `r`-subsets of `[M]`. -/
def Relabel (M' r' M r : Nat) (φ : List Nat → List Nat) : Prop :=
  (∀ X, IsRSet M' r' X → IsRSet M r (φ X)) ∧
    ∀ X Y, IsRSet M' r' X → IsRSet M' r' Y → φ X = φ Y → X = Y

/-- The preimages of the flipped sets lying in the image of `φ`, in order. -/
def preimages (M' r' : Nat) (φ : List Nat → List Nat) (Xs : List (List Nat)) : List (List Nat) :=
  Xs.filterMap fun B => (rsets M' r').find? fun X => φ X == B

/-- `find?` on `rsets` along a relabelling returns a valid set mapping to the target. -/
private theorem find_some_valid {M' r' : Nat} {φ : List Nat → List Nat} {B Y : List Nat}
    (hf : (rsets M' r').find? (fun X => φ X == B) = some Y) : IsRSet M' r' Y ∧ φ Y = B := by
  refine ⟨mem_rsets.1 (List.mem_of_find?_eq_some hf), ?_⟩
  have := List.find?_some hf
  simpa using this

/-- `find?` on `rsets` returns `X` exactly when `φ X = B`, by injectivity of `φ` on valid sets. -/
private theorem find_rsets_eq_some {M' r' M r : Nat} {φ : List Nat → List Nat} (hφ : Relabel M' r' M r φ)
    {X : List Nat} (hX : IsRSet M' r' X) (B : List Nat) :
    (rsets M' r').find? (fun X => φ X == B) = some X ↔ φ X = B := by
  constructor
  · intro h
    exact (find_some_valid h).2
  · intro h
    cases hf : (rsets M' r').find? (fun X => φ X == B) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simpa using h) (hf X (mem_rsets.2 hX))
    | some Y =>
      obtain ⟨hY, hYB⟩ := find_some_valid hf
      rw [hφ.2 Y X hY hX (hYB.trans h.symm)]

theorem preimages_valid {M' r' : Nat} {φ : List Nat → List Nat} (Xs : List (List Nat)) :
    ∀ X ∈ preimages M' r' φ Xs, IsRSet M' r' X := by
  intro X hX
  unfold preimages at hX
  obtain ⟨B, -, hB⟩ := List.mem_filterMap.1 hX
  exact (find_some_valid hB).1

/-- A valid `r'`-set occurs in the preimage list as often as its image occurs in `Xs`. -/
theorem count_preimages {M' r' M r : Nat} {φ : List Nat → List Nat} (hφ : Relabel M' r' M r φ)
    (Xs : List (List Nat)) {X : List Nat} (hX : IsRSet M' r' X) :
    (preimages M' r' φ Xs).count X = Xs.count (φ X) := by

  induction Xs with
  | nil => simp [preimages]
  | cons B Xs ih =>
    unfold preimages at ih ⊢
    rw [List.filterMap_cons, List.count_cons]
    cases hf : (rsets M' r').find? (fun X => φ X == B) with
    | none =>
      simp only
      rw [ih]
      have : ¬ B = φ X := fun h => by rw [(find_rsets_eq_some hφ hX B).2 h.symm] at hf; cases hf
      simp [this]
    | some Y =>
      obtain ⟨hY, hYB⟩ := find_some_valid hf
      simp only [List.count_cons, ih]
      by_cases h : Y = X
      · subst h; simp [hYB]
      · have : B ≠ φ X := fun e => h (hφ.2 Y X hY hX (hYB.trans e))
        simp [h, this]

/-- The length of the preimage list: the number of flips of sets in the image of `φ`. -/
theorem length_preimages (M' r' : Nat) (φ : List Nat → List Nat) (Xs : List (List Nat)) :
    (preimages M' r' φ Xs).length = (Xs.filter fun B => (rsets M' r').any fun X => φ X == B).length := by

  induction Xs with
  | nil => simp [preimages]
  | cons B Xs ih =>
    unfold preimages at ih ⊢
    rw [List.filterMap_cons, List.filter_cons]
    cases hf : (rsets M' r').find? (fun X => φ X == B) with
    | none =>
      have : ((rsets M' r').any fun X => φ X == B) = false := by
        rw [List.any_eq_false]; exact List.find?_eq_none.1 hf
      simp only [this]
      exact ih
    | some Y =>
      have : ((rsets M' r').any fun X => φ X == B) = true := by
        rw [List.any_eq_true]; exact ⟨Y, List.mem_of_find?_eq_some hf, List.find?_some (p := fun X => φ X == B) hf⟩
      simp only [this, ite_true, List.length_cons]
      rw [ih]

/-- Pulling back commutes with flipping. -/
theorem flipsR_pullback {M' r' M r : Nat} {φ : List Nat → List Nat} (hφ : Relabel M' r' M r φ)
    (u : SignMap) (Xs : List (List Nat)) :
    AgreeR M' r' (fun X => flipsR u Xs (φ X)) (flipsR (fun X => u (φ X)) (preimages M' r' φ Xs)) := by

  intro X hX
  show flipsR u Xs (φ X) = _
  rw [flipsR_apply, flipsR_apply, count_preimages hφ Xs hX]

/-- Every prefix of a preimage list is the preimage list of a prefix. -/
private theorem take_preimages (M' r' : Nat) (φ : List Nat → List Nat) (Xs : List (List Nat)) :
    ∀ i, i ≤ (preimages M' r' φ Xs).length →
      ∃ j, j ≤ Xs.length ∧ (preimages M' r' φ Xs).take i = preimages M' r' φ (Xs.take j) := by
  induction Xs with
  | nil => intro i _; exact ⟨0, Nat.le_refl _, by simp [preimages]⟩
  | cons B Xs ih =>
    intro i hi
    unfold preimages at ih hi ⊢
    rw [List.filterMap_cons] at hi ⊢
    cases hf : (rsets M' r').find? (fun X => φ X == B) with
    | none =>
      rw [hf] at hi
      obtain ⟨j, hj, he⟩ := ih i hi
      refine ⟨j + 1, by simp; omega, ?_⟩
      simp only [List.take_succ_cons, List.filterMap_cons, hf]
      exact he
    | some Y =>
      rw [hf] at hi
      cases i with
      | zero => exact ⟨0, Nat.zero_le _, by simp⟩
      | succ k =>
        simp only [List.length_cons] at hi
        obtain ⟨j, hj, he⟩ := ih k (by omega)
        refine ⟨j + 1, by simp; omega, ?_⟩
        simp only [List.take_succ_cons, List.filterMap_cons, hf]
        rw [he]

/-- A flip walk of maps satisfying `P` pulls back to a flip walk of maps satisfying `Q`, if `P u` implies
`Q (u ∘ φ)` and `Q` depends only on the values on `r'`-subsets of `[M']`. -/
theorem flipWalk_pullback {M' r' M r : Nat} {φ : List Nat → List Nat} (hφ : Relabel M' r' M r φ)
    {P Q : SignMap → Prop} (hPQ : ∀ u, P u → Q (fun X => u (φ X))) (hQ : AgreeInv M' r' Q)
    {s : SignMap} {Xs : List (List Nat)} (hw : FlipWalkR M r P s Xs) :
    FlipWalkR M' r' Q (fun X => s (φ X)) (preimages M' r' φ Xs) := by

  refine ⟨preimages_valid Xs, fun i hi => ?_⟩
  obtain ⟨j, hj, he⟩ := take_preimages M' r' φ Xs i hi
  rw [he]
  exact hQ _ _ (flipsR_pullback hφ s (Xs.take j)) (hPQ _ (hw.2 j hj))

/-- Lemma 6.6 in walk form: a walk from `s` to `v` given by the flip list `Xs` induces a walk from `s ∘ φ` to
`v ∘ φ` with one step for each flip of a set in the image of `φ`. -/
theorem rwalk_pullback {M' r' M r : Nat} {φ : List Nat → List Nat} (hφ : Relabel M' r' M r φ)
    {P Q : SignMap → Prop} (hPQ : ∀ u, P u → Q (fun X => u (φ X))) (hQ : AgreeInv M' r' Q)
    {s v : SignMap} {Xs : List (List Nat)} (hw : FlipWalkR M r P s Xs) (hend : AgreeR M r (flipsR s Xs) v) :
    RWalk M' r' Q (fun X => s (φ X)) (fun X => v (φ X)) (preimages M' r' φ Xs).length := by

  refine flips_to_rwalk (flipWalk_pullback hφ hPQ hQ hw) ?_
  intro X hX
  rw [← flipsR_pullback hφ s Xs X hX]
  exact hend (φ X) (hφ.1 X hX)

/-- `map` is injective on lists whose entries are pairwise identified only when equal. -/
private theorem map_inj_of {g : Nat → Nat} : ∀ {X Y : List Nat},
    (∀ x ∈ X, ∀ y ∈ Y, g x = g y → x = y) → X.map g = Y.map g → X = Y
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: X, y :: Y, hinj, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hinj x (by simp) y (by simp) h.1,
      map_inj_of (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb])) h.2]

/-- An increasing list is strictly monotone as a function of the index. -/
private theorem getD_lt_getD {z : List Nat} (hz : StrictIncr z) {a b : Nat} (ha : a < z.length)
    (hb : b < z.length) (hab : a < b) : z.getD a 0 < z.getD b 0 := by
  have := List.pairwise_iff_getElem.1 hz a b ha hb hab
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] using this

private theorem getD_mem {z : List Nat} {a : Nat} (ha : a < z.length) : z.getD a 0 ∈ z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem_mem ha]

/-- Restriction to an increasing list `z` of elements of `[M]`, relabelled by `[z.length]`. -/
theorem relabel_restrict {M r : Nat} {z : List Nat} (hz : StrictIncr z) (hzM : ∀ x ∈ z, x < M) :
    Relabel z.length r M r (fun X => X.map fun i => z.getD i 0) := by

  refine ⟨fun X hX => ⟨by simp [hX.1], ?_, ?_⟩, fun X Y hX hY h => ?_⟩
  · unfold StrictIncr
    rw [List.pairwise_map]
    exact hX.2.1.imp_of_mem fun ha hb hab => getD_lt_getD hz (hX.2.2 _ ha) (hX.2.2 _ hb) hab
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hzM _ (getD_mem (hX.2.2 a ha))
  · refine map_inj_of (fun a ha b hb hab => ?_) h
    have h1 := hX.2.2 a ha
    have h2 := hY.2.2 b hb
    rcases Nat.lt_trichotomy a b with h3 | h3 | h3
    · have := getD_lt_getD hz h1 h2 h3; omega
    · exact h3
    · have := getD_lt_getD hz h2 h1 h3; omega

/-- The minor of Proposition 8.5: `Z ↦ Y ++ (Z + c)` for a `q`-subset `Y` of `[c]`. -/
theorem relabel_minor {c q M r : Nat} {Y : List Nat} (hY : IsRSet c q Y) :
    Relabel M r (c + M) (q + r) (fun Z => Y ++ Z.map (· + c)) := by

  refine ⟨fun Z hZ => hY.append_shift hZ, fun X Z _ _ h => ?_⟩
  exact map_inj_of (fun a _ b _ hab => by omega) (List.append_cancel_left h)

/-- An increasing list is its entries below `c` followed by its entries at least `c`. -/
private theorem split_filter {B : List Nat} (hB : StrictIncr B) (c : Nat) :
    B = B.filter (fun x => decide (x < c)) ++ B.filter (fun x => !decide (x < c)) := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    unfold StrictIncr at hB
    rw [List.pairwise_cons] at hB
    by_cases hb : b < c
    · simp only [List.filter_cons, hb, decide_true, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        List.cons_append]
      rw [← ih hB.2]
    · rw [List.filter_eq_nil_iff.2, List.filter_eq_self.2, List.nil_append]
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · simp [hb]
        · have := hB.1 a ha; simp; omega
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · simp [hb]
        · have := hB.1 a ha; simp; omega

/-- Shifting down by `c` and back up is the identity on entries at least `c`. -/
private theorem map_sub_add {c : Nat} : ∀ {L : List Nat}, (∀ w ∈ L, c ≤ w) → (L.map (· - c)).map (· + c) = L
  | [], _ => rfl
  | w :: L, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by have := h w (by simp); omega, map_sub_add fun x hx => h x (by simp [hx])⟩

/-- A valid `(q + r)`-subset `B` of `[c + M]` lies in the image of the minor relabelling of `Y` iff its elements
below `c` are exactly `Y`. -/
theorem minor_image_iff {c q M r : Nat} {Y B : List Nat} (hY : IsRSet c q Y) (hB : IsRSet (c + M) (q + r) B) :
    ((rsets M r).any fun Z => (Y ++ Z.map (· + c)) == B) = true ↔
      B.filter (fun x => decide (x < c)) = Y := by

  have hYc : ∀ y ∈ Y, y < c := hY.2.2
  constructor
  · intro h
    obtain ⟨Z, -, hZ⟩ := List.any_eq_true.1 h
    have hZB : Y ++ Z.map (· + c) = B := by simpa using hZ
    subst hZB
    rw [List.filter_append, List.filter_eq_self.2 (fun a ha => by simpa using hYc a ha),
      List.filter_eq_nil_iff.2 (fun a ha => by obtain ⟨z, _, rfl⟩ := List.mem_map.1 ha; simp),
      List.append_nil]
  · intro h
    have hsplit := split_filter hB.2.1 c
    have hWsub : (B.filter (fun x => !decide (x < c))).Sublist B := List.filter_sublist
    have hWc : ∀ w ∈ B.filter (fun x => !decide (x < c)), c ≤ w := by
      intro w hw
      have := (List.mem_filter.1 hw).2
      simp at this
      exact this
    have hlen : (B.filter (fun x => !decide (x < c))).length = r := by
      have h1 := congrArg List.length hsplit
      rw [List.length_append, h, hB.1, hY.1] at h1
      omega
    have hZ : IsRSet M r ((B.filter (fun x => !decide (x < c))).map (· - c)) := by
      refine ⟨by rw [List.length_map, hlen], ?_, ?_⟩
      · unfold StrictIncr
        rw [List.pairwise_map]
        refine ((hB.2.1.sublist hWsub).imp_of_mem fun {a b} ha hb hab => ?_)
        have := hWc a ha
        have := hWc b hb
        omega
      · intro x hx
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        have := hWc w hw
        have := hB.2.2 w (hWsub.subset hw)
        omega
    refine List.any_eq_true.2 ⟨_, mem_rsets.2 hZ, ?_⟩
    rw [map_sub_add hWc, ← h, ← hsplit]
    simp

end OMDistance
