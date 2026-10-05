import OMDistance.LiftBasic
import OMDistance.OneStepWalk
import OMDistance.RSets

/-!
# Lifting a flip (Lemma 8.4)

Let `s` and `s^T` be rank-3 signotopes on `S` (`T` a 3-subset of `[m]`), `r = q + 3`, `c ≥ q`.  There is a walk in
`B(N ∪ S, r-1)` from `L s` to `L s^T` that flips each set `T ∪ Y`, `Y` a `q`-subset of `N ∪ {x ∈ S : x < min T}`,
exactly once and flips nothing else; it has length `binom(c + a, q)` with `a = min T` (0-based).

Proof (induction on `q`): for `q = 0` the two paddings differ only at `T + c`.  For `q ≥ 1`, write
`L^r_N s = (L^{r-1}_{N₁} s)'` with `N₁ = N ∖ min N` (`lift_succ`); by induction there is a walk
`v₀, …, v_p` from `L^{r-1}_{N₁} s` to `L^{r-1}_{N₁} s^T`; Lemma 8.1(b) (`onestep_b`) replaces each step `v_{i-1} → v_i`
flipping `X_i` by a walk from `v_{i-1}'` to `v_i'` flipping each `{x} ∪ X_i`, `x ∈ Λ_i`, once.  Each set `T ∪ Y` is
`{x} ∪ X` for exactly one flipped `X = T ∪ (Y ∖ min Y)`, with `x = min Y`.
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-! ### Helpers -/

/-- Being a signotope depends only on the values on the `r`-subsets. -/
private theorem sig_agree {M r : Nat} {u u' : SignMap} (hag : AgreeR M r u u') (hu : IsSignotopeR M r u) :
    IsSignotopeR M r u' := by
  intro P hP
  have e : rpacket u P = rpacket u' P := by
    unfold rpacket
    apply List.map_congr_left
    intro i hi
    rw [List.mem_reverse, List.mem_range, hP.1] at hi
    exact hag _ (hP.eraseIdx hi)
  rw [← e]
  exact hu P hP

/-- In a list without repetitions every entry occurs once. -/
private theorem count_nodup {α : Type} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α}, l.Nodup → l.count a = if a ∈ l then 1 else 0
  | [], _ => by simp
  | b :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.count_cons, count_nodup h.2]
    by_cases hab : a = b
    · subst hab
      simp [h.1]
    · have hb : (b == a) = false := by simp; exact fun e => hab e.symm
      simp [hab, hb]

/-- A flip walk of signotopes may start at any map agreeing with its start. -/
private theorem flipWalk_congr {M r : Nat} {u u' : SignMap} {Zs : List (List Nat)}
    (hw : FlipWalkR M r (IsSignotopeR M r) u Zs) (h : AgreeR M r u u') :
    FlipWalkR M r (IsSignotopeR M r) u' Zs :=
  ⟨hw.1, fun i hi => sig_agree (flipsR_congr h _) (hw.2 i hi)⟩

/-- Replacing each flip `X` of a walk of signotopes by the walk of Lemma 8.1(b) gives a walk from `v'` flipping
the sets `qsets X`. -/
private theorem expand_walk {M k : Nat} (hk : 2 ≤ k) : ∀ (Ws : List (List Nat)) (u : SignMap),
    FlipWalkR M k (IsSignotopeR M k) u Ws →
    ∃ Zs : List (List Nat), FlipWalkR (M + 1) (k + 1) (IsSignotopeR (M + 1) (k + 1)) (expand u) Zs ∧
      AgreeR (M + 1) (k + 1) (flipsR (expand u) Zs) (expand (flipsR u Ws)) ∧
      ∀ Z, Zs.count Z = (Ws.flatMap qsets).count Z
  | [], u, hw => by
    have hu : IsSignotopeR M k u := by simpa [flipsR_nil] using hw.2 0 (Nat.zero_le _)
    refine ⟨[], ⟨fun X h => by simp at h, fun i hi => ?_⟩, AgreeR.refl _ _ _, fun Z => by simp⟩
    have : i = 0 := by simpa using hi
    subst this
    simpa [flipsR_nil] using onestep_a hu
  | X :: Ws, u, hw => by
    obtain ⟨hXs, hpre⟩ := hw
    have hu : IsSignotopeR M k u := by simpa [flipsR_nil] using hpre 0 (Nat.zero_le _)
    have hX : IsRSet M k X := hXs X (by simp)
    have hu1 : IsSignotopeR M k (flipR u X) := by
      simpa [flipsR_cons, flipsR_nil] using hpre 1 (by simp)
    have hw' : FlipWalkR M k (IsSignotopeR M k) (flipR u X) Ws := by
      refine ⟨fun Y hY => hXs Y (by simp [hY]), fun i hi => ?_⟩
      have := hpre (i + 1) (by simp; omega)
      simpa [List.take_succ_cons, flipsR_cons] using this
    obtain ⟨Zs1, ⟨h1m, h1p⟩, h1a, h1c⟩ := onestep_b hk hX hu hu1
    obtain ⟨Zs2, ⟨h2m, h2p⟩, h2a, h2c⟩ := expand_walk hk Ws (flipR u X) hw'
    refine ⟨Zs1 ++ Zs2, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro Z hZ
      rcases List.mem_append.1 hZ with h | h
      · exact h1m Z h
      · exact h2m Z h
    · intro i hi
      by_cases hle : i ≤ Zs1.length
      · rw [List.take_append_of_le_length hle]
        exact h1p i hle
      · obtain ⟨j, rfl⟩ : ∃ j, i = Zs1.length + j := ⟨i - Zs1.length, by omega⟩
        rw [List.take_length_add_append, flipsR_append]
        rw [List.length_append] at hi
        exact sig_agree (flipsR_congr h1a _).symm (h2p j (by omega))
    · rw [flipsR_append, flipsR_cons]
      exact (flipsR_congr h1a Zs2).trans h2a
    · intro Z
      rw [List.count_append, List.flatMap_cons, List.count_append, h1c, h2c]

/-! ### The flipped sets -/

/-- The sets `Y ++ (T + c)`, `Y ∈ binom([c + min T], q)`. -/
private def Lset (T : List Nat) (c q : Nat) : List (List Nat) :=
  (rsets (c + T.headD 0) q).map fun Y => Y ++ T.map (· + c)

private theorem mem_Lset {T : List Nat} {c q : Nat} {Z : List Nat} :
    Z ∈ Lset T c q ↔ ∃ Y, IsRSet (c + T.headD 0) q Y ∧ Z = Y ++ T.map (· + c) := by
  unfold Lset
  rw [List.mem_map]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨Y, mem_rsets.1 hY, rfl⟩
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨Y, mem_rsets.2 hY, rfl⟩

private theorem Lset_nodup (T : List Nat) (c q : Nat) : (Lset T c q).Nodup := by
  unfold Lset List.Nodup
  rw [List.pairwise_map]
  exact (rsets_nodup _ _).imp fun h e => h (List.append_cancel_right e)

private theorem qsets_tail {W Z : List Nat} (h : Z ∈ qsets W) : Z.tail = W.map (· + 1) := by
  unfold qsets at h
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 h
  rfl

private theorem map_succ_inj {W W' : List Nat} (h : W.map (· + 1) = W'.map (· + 1)) : W = W' := by
  have := congrArg (List.map (· - 1)) h
  have hid : ((fun x => x - 1) ∘ fun x : Nat => x + 1) = id := by funext x; simp
  rw [List.map_map, List.map_map, hid, List.map_id, List.map_id] at this
  exact this

private theorem qsets_nodup (W : List Nat) : (qsets W).Nodup := by
  unfold qsets List.Nodup
  rw [List.pairwise_map]
  exact List.nodup_range.imp fun h e => h (List.cons.inj e).1

private theorem flat_qsets_nodup : ∀ {Ws : List (List Nat)}, Ws.Nodup → (Ws.flatMap qsets).Nodup
  | [], _ => by simp
  | W :: Ws, h => by
    rw [List.nodup_cons] at h
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨qsets_nodup W, flat_qsets_nodup h.2, fun a ha b hb hab => ?_⟩
    obtain ⟨W', hW', hb'⟩ := List.mem_flatMap.1 hb
    have e : W = W' := map_succ_inj ((qsets_tail ha).symm.trans (hab ▸ qsets_tail hb'))
    exact h.1 (e ▸ hW')

/-- The bijection `(X, x) ↦ x :: (X + 1)` onto the `(q+1)`-subsets `Y` of `[c + 1 + min T]`. -/
private theorem mem_flat_iff {m c q : Nat} {T : List Nat} (hT : IsRSet m 3 T) (Z : List Nat) :
    Z ∈ (Lset T c q).flatMap qsets ↔ Z ∈ Lset T (c + 1) (q + 1) := by
  obtain ⟨hTl, -, -⟩ := hT
  match T, hTl with
  | [t0, t1, t2], _ =>
  rw [List.mem_flatMap, mem_Lset]
  simp only [List.headD_cons, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨W, hW, hZ⟩
    obtain ⟨Y, hY, rfl⟩ := mem_Lset.1 hW
    simp only [List.headD_cons] at hY
    unfold qsets at hZ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hZ
    rw [List.mem_range] at hx
    simp only [List.map_cons, List.map_nil] at hx ⊢
    obtain ⟨hYl, hYi, hYb⟩ := hY
    refine ⟨x :: Y.map (· + 1), ⟨by simp [hYl], ?_, ?_⟩, ?_⟩
    · unfold StrictIncr at hYi ⊢
      rw [List.pairwise_cons, List.pairwise_map]
      refine ⟨?_, hYi.imp fun h => by omega⟩
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
      cases Y with
      | nil => simp at hy'
      | cons y0 Y0 =>
        rw [List.pairwise_cons] at hYi
        simp only [List.cons_append, List.headD_cons] at hx
        rcases List.mem_cons.1 hy' with e | hy'
        · omega
        · have := hYi.1 y' hy'; omega
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · cases Y with
        | nil => simp only [List.nil_append, List.headD_cons] at hx; omega
        | cons y0 Y0 =>
          simp only [List.cons_append, List.headD_cons] at hx
          have := hYb y0 (by simp); omega
      · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
        have := hYb y' hy'; omega
    · simp only [List.map_append, List.cons_append, List.map_cons, List.map_nil]
      simp only [List.cons.injEq, List.append_cancel_left_eq, true_and]
      exact ⟨by omega, by omega, by omega, trivial⟩
  · rintro ⟨Y', ⟨hYl, hYi, hYb⟩, rfl⟩
    match Y', hYl, hYi, hYb with
    | y0 :: Y'', hYl, hYi, hYb =>
    simp only [List.length_cons] at hYl
    unfold StrictIncr at hYi
    rw [List.pairwise_cons] at hYi
    have hpos : ∀ y ∈ Y'', 1 ≤ y := fun y hy => by have := hYi.1 y hy; omega
    have hback : (Y''.map (· - 1)).map (· + 1) = Y'' := by
      rw [List.map_map]
      conv => rhs; rw [← List.map_id Y'']
      apply List.map_congr_left
      intro y hy
      have := hpos y hy
      simp only [Function.comp, id]
      omega
    have hY : IsRSet (c + t0) q (Y''.map (· - 1)) := by
      refine ⟨by simp at hYl ⊢; omega, ?_, ?_⟩
      · unfold StrictIncr
        rw [List.pairwise_map]
        exact (List.Pairwise.and_mem.1 hYi.2).imp fun {a b} h => by
          have := hpos a h.1; have := h.2.2; omega
      · intro y hy
        obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
        have := hYb y' (by simp [hy']); have := hpos y' hy'; omega
    refine ⟨Y''.map (· - 1) ++ [t0 + c, t1 + c, t2 + c], (mem_Lset (T := [t0, t1, t2])).2 ⟨Y''.map (· - 1), by
      simpa using hY, by simp⟩, ?_⟩
    unfold qsets
    rw [List.mem_map]
    refine ⟨y0, ?_, ?_⟩
    · rw [List.mem_range]
      cases Y'' with
      | nil =>
        have := hYb y0 (by simp)
        simp only [List.map_nil, List.nil_append, List.headD_cons]
        omega
      | cons y1 Y1 =>
        have := hYi.1 y1 (by simp)
        simp only [List.map_cons, List.cons_append, List.headD_cons]
        omega
    · rw [List.map_append, hback]
      simp only [List.map_cons, List.map_nil, List.cons_append]
      simp only [Nat.add_assoc]

private theorem count_step {m c q : Nat} {T : List Nat} (hT : IsRSet m 3 T) (Z : List Nat) :
    ((Lset T c q).flatMap qsets).count Z = (Lset T (c + 1) (q + 1)).count Z := by
  rw [count_nodup (flat_qsets_nodup (Lset_nodup T c q)), count_nodup (Lset_nodup T (c + 1) (q + 1))]
  simp only [mem_flat_iff hT Z]

/-- Flipping the sets of `Lset T c q` once each turns `L s` into `L s^T` (Lemma 8.3(b)). -/
private theorem agree_of_count {m c q : Nat} (s : SignMap) {T : List Nat} (hT : IsRSet m 3 T)
    {Zs : List (List Nat)} (hc : ∀ Z, Zs.count Z = (Lset T c q).count Z) :
    AgreeR (c + m) (q + 3) (flipsR (lift c s) Zs) (lift c (flipR s T)) := by
  intro X hX
  rw [flipsR_apply, hc, count_nodup (Lset_nodup T c q)]
  have hd := lift_diff (q := q) s hT hX
  by_cases hm : X ∈ Lset T c q
  · have hne := hd.2 (mem_Lset.1 hm)
    simp only [hm, ↓reduceIte, Nat.one_mod, Nat.one_ne_zero]
    cases h1 : lift c s X <;> cases h2 : lift c (flipR s T) X <;> simp_all
  · have heq : lift c s X = lift c (flipR s T) X :=
      Classical.byContradiction fun hne => hm (mem_Lset.2 (hd.1 hne))
    simp only [hm, ↓reduceIte, Nat.zero_mod]
    exact heq

/-- Lemma 8.4, with the flipped sets: the walk flips exactly the sets `Y ++ (T + c)`, `Y ∈ binom([c + min T], q)`,
each once. -/
theorem liftflip_flips {m c q : Nat} (hc : q ≤ c) {s : SignMap} {T : List Nat} (hT : IsRSet m 3 T)
    (hs : IsSignotopeR m 3 s) (hsT : IsSignotopeR m 3 (flipR s T)) :
    ∃ Zs : List (List Nat), FlipWalkR (c + m) (q + 3) (IsSignotopeR (c + m) (q + 3)) (lift c s) Zs ∧
      AgreeR (c + m) (q + 3) (flipsR (lift c s) Zs) (lift c (flipR s T)) ∧
      ∀ Z, Zs.count Z = ((rsets (c + T.headD 0) q).map fun Y => Y ++ T.map (· + c)).count Z := by
  suffices h : ∃ Zs : List (List Nat), FlipWalkR (c + m) (q + 3) (IsSignotopeR (c + m) (q + 3)) (lift c s) Zs ∧
      ∀ Z, Zs.count Z = (Lset T c q).count Z by
    obtain ⟨Zs, hw, hcnt⟩ := h
    exact ⟨Zs, hw, agree_of_count s hT hcnt, hcnt⟩
  induction q generalizing c with
  | zero =>
    have hcnt : ∀ Z, [T.map (· + c)].count Z = (Lset T c 0).count Z := by
      intro Z
      rfl
    refine ⟨[T.map (· + c)], ⟨?_, ?_⟩, hcnt⟩
    · intro X hX
      rw [List.mem_singleton] at hX
      subst hX
      have := hT.map_add c
      rwa [Nat.add_comm m c] at this
    · intro i hi
      rcases i with _ | _ | i
      · simpa [flipsR_nil] using padding_signotope (c := c) hs
      · exact sig_agree (agree_of_count s hT hcnt).symm (padding_signotope hsT)
      · simp at hi
  | succ q ih =>
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨Ws, hWw, hWc⟩ := ih (c := c') (by omega)
    obtain ⟨Zs, hZw, -, hZc⟩ := expand_walk (M := c' + m) (k := q + 3) (by omega) Ws (lift c' s) hWw
    have hls := lift_succ m c' (q + 3) (by omega) s
    have e1 : c' + m + 1 = c' + 1 + m := by omega
    have e2 : q + 3 + 1 = q + 1 + 3 := by omega
    rw [e1, e2] at hZw
    rw [e2] at hls
    refine ⟨Zs, flipWalk_congr hZw hls.symm, fun Z => ?_⟩
    rw [hZc, (List.Perm.flatMap_right qsets (List.perm_iff_count.2 hWc)).count_eq, count_step hT]

/-- Lemma 8.4: a walk of length `binom(c + min T, q)` in `B(N ∪ S, r-1)` from `L s` to `L s^T`. -/
theorem liftflip {m c q : Nat} (hc : q ≤ c) {s : SignMap} {T : List Nat} (hT : IsRSet m 3 T)
    (hs : IsSignotopeR m 3 s) (hsT : IsSignotopeR m 3 (flipR s T)) :
    SigWalk (c + m) (q + 3) (lift c s) (lift c (flipR s T)) (binom (c + T.headD 0) q) := by
  obtain ⟨Zs, hw, hag, hcnt⟩ := liftflip_flips hc hT hs hsT
  have hlen : Zs.length = binom (c + T.headD 0) q := by
    rw [(List.perm_iff_count.2 hcnt).length_eq, List.length_map, length_rsets]
  rw [← hlen]
  exact flips_to_rwalk hw hag

end OMDistance
