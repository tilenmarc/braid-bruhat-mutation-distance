import OMDistance.LiftBasic
import OMDistance.SignMapLemmas
import OMDistance.Binom

/-!
# The Hamming distance of lifts (proof of Proposition 8.5)

Since `(L s)(X) = ŝ(top X)`, the lifts `L s` and `L t` differ exactly on the sets `T ∪ Y` with `T ∈ D(s, t)` and
`Y` a `q`-subset of `N ∪ {x ∈ S : x < min T}` (0-based: `Y ++ (T + c)` with `Y` a `q`-subset of `[c + min T]`).
Hence

* `H = |D(L s, L t)| = Σ_{T ∈ D(s,t)} binom(c + min T, q)` (`hamR_lift`), so `H ≤ μ h` with
  `μ = binom(c + m - 3, q)`, `h = |D(s, t)|` (`hamR_lift_le`);
* the sets of `D(L s, L t)` with exactly `q` elements in `N` are the `λ h` sets `Y ++ (T + c)` with `Y ⊆ N`,
  `λ = binom(c, q)` (`diffR_lift_filter`), and `H = λ h + #{B ∈ D(L s, L t) : |B ∩ N| ≠ q}` (`hamR_lift_split`).
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- Two duplicate-free lists with the same members have the same length. -/
private theorem length_eq_of_mem_iff {α : Type} {L L' : List α} (hL : L.Nodup) (hL' : L'.Nodup)
    (h : ∀ x, x ∈ L ↔ x ∈ L') : L.length = L'.length :=
  ((List.perm_ext_iff_of_nodup hL hL').2 h).length_eq

/-- The sets `Y ++ (T + c)` with `T ∈ D` and `Y` a `q`-subset of `[A T]`. -/
private def liftSets (c q : Nat) (D : List (List Nat)) (A : List Nat → Nat) : List (List Nat) :=
  D.flatMap fun T => (rsets (A T) q).map fun Y => Y ++ T.map (· + c)

private theorem mem_liftSets {c q : Nat} {D : List (List Nat)} {A : List Nat → Nat} {X : List Nat} :
    X ∈ liftSets c q D A ↔ ∃ T ∈ D, ∃ Y, IsRSet (A T) q Y ∧ X = Y ++ T.map (· + c) := by
  unfold liftSets
  simp only [List.mem_flatMap, List.mem_map, mem_rsets]
  constructor
  · rintro ⟨T, hT, Y, hY, rfl⟩
    exact ⟨T, hT, Y, hY, rfl⟩
  · rintro ⟨T, hT, Y, hY, rfl⟩
    exact ⟨T, hT, Y, hY, rfl⟩

private theorem map_add_inj {c : Nat} {T T' : List Nat} (h : T.map (· + c) = T'.map (· + c)) : T = T' := by
  have := congrArg (List.map (· - c)) h
  simpa [List.map_map, Function.comp_def] using this

private theorem liftSets_nodup {c q : Nat} {D : List (List Nat)} (A : List Nat → Nat) (hD : D.Nodup) :
    (liftSets c q D A).Nodup := by
  unfold liftSets List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun T _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (rsets_nodup (A T) q).imp fun {a b} hab heq => hab (List.append_cancel_right heq)
  · refine hD.imp fun {T T'} hTT' => ?_
    intro x hx y hy hxy
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hx
    obtain ⟨Y', hY', rfl⟩ := List.mem_map.1 hy
    have h1 := (mem_rsets.1 hY).1
    have h2 := (mem_rsets.1 hY').1
    have := (List.append_inj hxy (by rw [h1, h2])).2
    exact hTT' (map_add_inj this)

private theorem length_liftSets (c q : Nat) (D : List (List Nat)) (A : List Nat → Nat) :
    (liftSets c q D A).length = (D.map fun T => binom (A T) q).sum := by
  unfold liftSets
  induction D with
  | nil => rfl
  | cons T D ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_map, length_rsets]
    simp

private theorem headD_le {T : List Nat} (h : StrictIncr T) {x : Nat} (hx : x ∈ T) : T.headD 0 ≤ x := by
  cases T with
  | nil => simp at hx
  | cons a T =>
    unfold StrictIncr at h
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (h.1 x hx)

/-- The value of the lift at `Y ++ Z` with `Z` three elements of `S`. -/
private theorem lift_append {c : Nat} (s : SignMap) (Y Z : List Nat) (hZ : Z.length = 3) (hc : ∀ z ∈ Z, c ≤ z) :
    lift c s (Y ++ Z) = s (Z.map (· - c)) := by
  unfold lift
  have h3 : 3 ≤ ((Y ++ Z).filter fun x => decide (c ≤ x)).length := by
    rw [List.filter_append, List.length_append]
    have : (Z.filter fun x => decide (c ≤ x)).length = Z.length :=
      List.length_filter_eq_length_iff.2 fun a ha => by simpa using hc a ha
    omega
  simp only [h3, ↓reduceIte]
  rw [List.length_append, hZ, Nat.add_sub_cancel, List.drop_left]

/-- `T + c` has elements `≥ c`, and `(T + c) - c = T`. -/
private theorem map_add_sub (c : Nat) (T : List Nat) : (T.map (· + c)).map (· - c) = T := by
  simp [List.map_map, Function.comp_def]

/-- Members of `D(L s, L t)`: the sets `Y ++ (T + c)` with `T ∈ D(s, t)`, `Y` a `q`-subset of `[c + min T]`. -/
private theorem mem_diffR_lift {m c q : Nat} {s t : SignMap} {X : List Nat} :
    X ∈ diffR (c + m) (q + 3) (lift c s) (lift c t) ↔
      ∃ T ∈ diffR m 3 s t, ∃ Y, IsRSet (c + T.headD 0) q Y ∧ X = Y ++ T.map (· + c) := by
  rw [mem_diffR]
  constructor
  · rintro ⟨hX, hne⟩
    -- the three largest elements lie in `S`
    have hge : 3 ≤ (X.filter fun x => decide (c ≤ x)).length := by
      unfold lift at hne
      by_cases h : 3 ≤ (X.filter fun x => decide (c ≤ x)).length
      · exact h
      · simp only [h, ↓reduceIte] at hne; exact absurd rfl hne
    have hsplit : X = X.take q ++ X.drop q := (List.take_append_drop q X).symm
    have hlenX := hX.1
    have hZlen : (X.drop q).length = 3 := by rw [List.length_drop]; omega
    have hYlen : (X.take q).length = q := by rw [List.length_take]; omega
    have hinc : StrictIncr (X.take q ++ X.drop q) := hsplit ▸ hX.2.1
    unfold StrictIncr at hinc
    rw [List.pairwise_append] at hinc
    obtain ⟨hYinc, hZinc, hYZ⟩ := hinc
    have hZc : ∀ z ∈ X.drop q, c ≤ z := by
      intro z hz
      apply Classical.byContradiction
      intro hzc
      have hYf : ((X.take q).filter fun x => decide (c ≤ x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have := hYZ y hy z hz
        simp; omega
      have hZf : ((X.drop q).filter fun x => decide (c ≤ x)).length < (X.drop q).length :=
        List.length_filter_lt_length_iff_exists.2 ⟨z, hz, by simpa using hzc⟩
      rw [hsplit, List.filter_append, List.length_append, hYf] at hge
      simp only [List.length_nil] at hge
      omega
    have hXmem : ∀ x ∈ X, x < c + m := hX.2.2
    refine ⟨(X.drop q).map (· - c), ?_, X.take q, ?_, ?_⟩
    · rw [mem_diffR]
      refine ⟨⟨by rw [List.length_map, hZlen], ?_, ?_⟩, ?_⟩
      · unfold StrictIncr
        rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ hZinc
        intro a b ha hb hab
        have := hZc a ha; have := hZc b hb; omega
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
        have := hXmem z (List.mem_of_mem_drop hz)
        have := hZc z hz
        omega
      · rw [hsplit, lift_append s _ _ hZlen hZc, lift_append t _ _ hZlen hZc] at hne
        exact hne
    · refine ⟨hYlen, hYinc, fun y hy => ?_⟩
      cases h : X.drop q with
      | nil => rw [h] at hZlen; simp at hZlen
      | cons z Z =>
        have hzm : z ∈ X.drop q := by rw [h]; exact List.mem_cons_self
        have := hYZ y hy z hzm
        have := hZc z hzm
        simp only [List.map_cons, List.headD_cons]
        omega
    · have : ((X.drop q).map (· - c)).map (· + c) = X.drop q := by
        rw [List.map_map]
        conv => rhs; rw [← List.map_id (X.drop q)]
        apply List.map_congr_left
        intro z hz
        have := hZc z hz
        simp; omega
      rw [this]
      exact hsplit
  · rintro ⟨T, hT, Y, hY, rfl⟩
    obtain ⟨⟨hTlen, hTinc, hTm⟩, hst⟩ := mem_diffR.1 hT
    have hTc : ∀ z ∈ T.map (· + c), c ≤ z := by
      intro z hz
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hz
      omega
    have hTlen' : (T.map (· + c)).length = 3 := by rw [List.length_map, hTlen]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.length_append, hY.1, hTlen']
    · unfold StrictIncr
      rw [List.pairwise_append]
      refine ⟨hY.2.1, ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hTinc.imp fun hab => by omega
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
        have := hY.2.2 a ha
        have := headD_le hTinc hx
        omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · have hx' := hY.2.2 x hx
        cases T with
        | nil => simp at hTlen
        | cons a T =>
          have := hTm a List.mem_cons_self
          simp only [List.headD_cons] at hx'
          omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have := hTm y hy
        omega
    · rw [lift_append s _ _ hTlen' hTc, lift_append t _ _ hTlen' hTc, map_add_sub]
      exact hst

/-- `D(L s, L t)` lists the same sets as `liftSets` with `A T = c + min T`. -/
private theorem hamR_lift_eq (m c q : Nat) (s t : SignMap) :
    hamR (c + m) (q + 3) (lift c s) (lift c t) =
      (liftSets c q (diffR m 3 s t) fun T => c + T.headD 0).length := by
  unfold hamR
  apply length_eq_of_mem_iff (diffR_nodup _ _ _ _) (liftSets_nodup _ (diffR_nodup _ _ _ _))
  intro X
  rw [mem_diffR_lift, mem_liftSets]

private theorem sum_map_le {f : List Nat → Nat} {k : Nat} :
    ∀ (D : List (List Nat)), (∀ T ∈ D, f T ≤ k) → (D.map f).sum ≤ k * D.length
  | [], _ => by simp
  | T :: D, h => by
    have h1 := h T List.mem_cons_self
    have h2 := sum_map_le D fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

private theorem sum_map_const (k : Nat) :
    ∀ (D : List (List Nat)), (D.map fun _ => k).sum = k * D.length
  | [] => by simp
  | _ :: D => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ, sum_map_const k D]
    omega

theorem hamR_lift (m c q : Nat) (s t : SignMap) :
    hamR (c + m) (q + 3) (lift c s) (lift c t) = ((diffR m 3 s t).map fun T => binom (c + T.headD 0) q).sum := by
  rw [hamR_lift_eq, length_liftSets]

theorem hamR_lift_le (m c q : Nat) (s t : SignMap) :
    hamR (c + m) (q + 3) (lift c s) (lift c t) ≤ binom (c + m - 3) q * hamR m 3 s t := by
  rw [hamR_lift]
  apply sum_map_le
  intro T hT
  obtain ⟨⟨hTlen, hTinc, hTm⟩, _⟩ := mem_diffR.1 hT
  apply binom_mono
  match T, hTlen, hTinc, hTm with
  | [a, b, d], _, hinc, hm =>
    have hd := hm d (by simp)
    simp [StrictIncr] at hinc
    simp only [List.headD_cons]
    omega

/-- The sets of `D(L s, L t)` with exactly `q` elements in `N = [c]`: there are `binom(c, q) · |D(s, t)|`. -/
theorem diffR_lift_filter (m c q : Nat) (s t : SignMap) :
    ((diffR (c + m) (q + 3) (lift c s) (lift c t)).filter
      fun B => (B.filter fun x => decide (x < c)).length == q).length = binom c q * hamR m 3 s t := by
  have hcount : ∀ (Y T : List Nat), Y.length = q →
      ((((Y ++ T.map (· + c)).filter fun x => decide (x < c)).length == q) = true ↔ ∀ y ∈ Y, y < c) := by
    intro Y T hY
    have hT : ((T.map (· + c)).filter fun x => decide (x < c)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
      simp
    rw [List.filter_append, hT, List.append_nil, beq_iff_eq]
    conv => lhs; rhs; rw [← hY]
    rw [List.length_filter_eq_length_iff]
    simp
  have e : ((diffR (c + m) (q + 3) (lift c s) (lift c t)).filter
      fun B => (B.filter fun x => decide (x < c)).length == q).length =
      (liftSets c q (diffR m 3 s t) fun _ => c).length := by
    apply length_eq_of_mem_iff ((diffR_nodup _ _ _ _).filter _) (liftSets_nodup _ (diffR_nodup _ _ _ _))
    intro X
    rw [List.mem_filter, mem_diffR_lift, mem_liftSets]
    constructor
    · rintro ⟨⟨T, hT, Y, hY, rfl⟩, hq⟩
      exact ⟨T, hT, Y, ⟨hY.1, hY.2.1, (hcount Y T hY.1).1 hq⟩, rfl⟩
    · rintro ⟨T, hT, Y, hY, rfl⟩
      exact ⟨⟨T, hT, Y, hY.mono (Nat.le_add_right _ _), rfl⟩, (hcount Y T hY.1).2 hY.2.2⟩
  rw [e, length_liftSets, sum_map_const]
  rfl

theorem hamR_lift_split (m c q : Nat) (s t : SignMap) :
    hamR (c + m) (q + 3) (lift c s) (lift c t) = binom c q * hamR m 3 s t +
      ((diffR (c + m) (q + 3) (lift c s) (lift c t)).filter
        fun B => (B.filter fun x => decide (x < c)).length != q).length := by
  rw [← diffR_lift_filter m c q s t]
  unfold hamR
  generalize diffR (c + m) (q + 3) (lift c s) (lift c t) = L
  induction L with
  | nil => rfl
  | cons X L ih =>
    simp only [bne] at ih ⊢
    rw [List.filter_cons, List.filter_cons]
    cases h : (X.filter fun x => decide (x < c)).length == q
    · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

end OMDistance
