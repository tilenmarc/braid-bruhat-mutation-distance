import OMDistance.OneStep

/-!
# Adding one element: lifting a flip (Lemma 8.1(b))

Let `v` and `v^X` be signotopes of rank `k ≥ 2` on `[M]`, `X = {t₁ < ⋯ < t_k}`.  After adding the new minimum
`ℓ = 0` (old `x` becomes `x + 1`), `Λ = {0, 1, …, t₁}` and `Q_x = {x} ∪ (X + 1)` (`qsets X`).  The maps `v'` and
`(v^X)'` differ exactly on the sets `Q_x`, and there is a walk in `B([M+1], k)` from `v'` to `(v^X)'` that flips each
`Q_x` exactly once.

Proof (paper): put `τ = v(X)`.  For `x < t₁` the packet of `{x} ∪ X` is `(α_k, …, α_1, τ)` under `v` and
`(α_k, …, α_1, -τ)` under `v^X`, `α_i = v(({x} ∪ X) ∖ t_i)`; both have at most one sign change, so the `α_i` have a
common value `α_x`.  Call `x` early if `α_x = τ` and late otherwise.  Order `Λ` by starting with `(ℓ)` and adding
`x = 0, 1, …, t₁ - 1` (old labels) in increasing order, early ones at the front and late ones at the back; then an
early `y` precedes and a late `y` follows every smaller element of `Λ` (8.1).  Flip the `Q_x` in this order.  A
`(k+2)`-set `P` containing at most one `Q_x` has at every moment the packet of `v'` or of `(v^X)'`; otherwise
`P = {x, y} ∪ X` with `x < y` in `Λ`, its packet is `(α_y, …, α_y, e_x, e_y)` with `e_x, e_y` the current values at
`Q_x, Q_y`, going from `(τ, τ)` to `(-τ, -τ)`, and it has two sign changes only in the state `(-α_y, α_y)`, which
(8.1) excludes.  (`check.py`, `drop_min_walk`, implements this order; it was also checked in Lean by evaluation on
all signotopes of ranks 2, 3 on `[4]`, `[5]`.)
-/

namespace OMDistance

open BraidDistance (StrictIncr signChanges oneChange)

private theorem signChanges_snoc2 (b c : Bool) : ∀ L : List Bool,
    signChanges (L ++ [b, c]) = signChanges (L ++ [b]) + (if b = c then 0 else 1)
  | [] => by simp [signChanges]
  | [x] => by simp [signChanges]
  | x :: y :: L => by
    have ih := signChanges_snoc2 b c (y :: L)
    simp only [List.cons_append] at ih ⊢
    simp only [signChanges, ih]
    omega

private theorem oneChange_dup (C : List Bool) (b : Bool) (h : oneChange (C ++ [b]) = true) :
    oneChange (C ++ [b, b]) = true := by
  simp only [oneChange, decide_eq_true_eq] at h ⊢
  rw [signChanges_snoc2]; simpa using h

private theorem oneChange_key (C₀ : List Bool) (a τ c d : Bool)
    (h1 : oneChange (C₀ ++ [a] ++ [τ]) = true) (h2 : oneChange (C₀ ++ [a] ++ [!τ]) = true)
    (hbad : ¬ (c = !a ∧ d = a)) : oneChange (C₀ ++ [a] ++ [c, d]) = true := by
  simp only [oneChange, decide_eq_true_eq, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  have e1 := signChanges_snoc2 a τ C₀
  have e2 := signChanges_snoc2 a (!τ) C₀
  have e3 := signChanges_snoc2 c d (C₀ ++ [a])
  have e4 := signChanges_snoc2 a c C₀
  simp only [List.append_assoc, List.cons_append, List.nil_append] at e3
  rw [e3, e4]
  rw [e1] at h1; rw [e2] at h2
  cases a <;> cases τ <;> cases c <;> cases d <;> simp_all <;> omega

private theorem range_succ_rev_map {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).reverse.map f = (List.range n).reverse.map (fun i => f (i + 1)) ++ [f 0] := by
  rw [List.range_succ_eq_map]
  simp [List.map_reverse]

private theorem rpacket_cons1 (u : SignMap) (q : Nat) (Q : List Nat) :
    rpacket u (q :: Q) = (List.range Q.length).reverse.map (fun i => u (q :: Q.eraseIdx i)) ++ [u Q] := by
  unfold rpacket
  rw [List.length_cons, range_succ_rev_map]
  simp

private theorem rpacket_cons2 (u : SignMap) (p r : Nat) (R : List Nat) :
    rpacket u (p :: r :: R) = (List.range R.length).reverse.map (fun i => u (p :: r :: R.eraseIdx i)) ++
      [u (p :: R), u (r :: R)] := by
  rw [rpacket_cons1, List.length_cons, range_succ_rev_map]
  simp


private def Qf (X : List Nat) (j : Nat) : List Nat := j :: X.map (· + 1)

private def gmap (v : SignMap) (X T : List Nat) (h : Nat) : SignMap := if h ∈ T then flipR v X else v

private theorem gmap_ne (v : SignMap) (X T : List Nat) (h : Nat) {Y : List Nat} (hY : Y ≠ X) :
    gmap v X T h Y = v Y := by
  unfold gmap; split
  · exact flipR_ne v hY
  · rfl

private theorem gmap_X (v : SignMap) (X T : List Nat) (h : Nat) :
    gmap v X T h X = if h ∈ T then !v X else v X := by
  unfold gmap; split
  · exact flipR_self v X
  · rfl

private theorem count_map_Qf (X : List Nat) (h : Nat) : ∀ T : List Nat,
    (T.map (Qf X)).count (Qf X h) = T.count h
  | [] => rfl
  | a :: T => by
    simp only [List.map_cons, List.count_cons, count_map_Qf X h T]
    congr 1
    simp [Qf]

private theorem map_pred_succ {Y : List Nat} (hY : ∀ y ∈ Y, 1 ≤ y) : (Y.map (· - 1)).map (· + 1) = Y := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id Y]
  apply List.map_congr_left
  intro y hy
  have := hY y hy
  simp; omega

/-- The value of an intermediate map of the walk: `g_h(Y - 1)` at `h :: Y`. -/
private theorem wval (v : SignMap) (X T : List Nat) (hT : T.Nodup) (h : Nat) (Y : List Nat)
    (hY : ∀ y ∈ Y, 1 ≤ y) :
    flipsR (expand v) (T.map (Qf X)) (h :: Y) = gmap v X T h (Y.map (· - 1)) := by
  rw [flipsR_apply]
  have hexp : expand v (h :: Y) = v (Y.map (· - 1)) := by simp [expand]
  rw [hexp]
  by_cases hYX : Y.map (· - 1) = X
  · have hY' : Y = X.map (· + 1) := by rw [← hYX, map_pred_succ hY]
    have hc : (T.map (Qf X)).count (h :: Y) = T.count h := by
      rw [hY']; exact count_map_Qf X h T
    rw [hc, hT.count, hYX, gmap_X]
    split <;> simp_all
  · have hc : (T.map (Qf X)).count (h :: Y) = 0 := by
      apply List.count_eq_zero_of_not_mem
      intro hm
      obtain ⟨j, _, hj⟩ := List.mem_map.1 hm
      simp only [Qf, List.cons.injEq] at hj
      apply hYX
      rw [← hj.2, List.map_map]
      conv => rhs; rw [← List.map_id X]
      apply List.map_congr_left
      intro y _; simp
    rw [hc, gmap_ne v X T h hYX]
    simp


private theorem map_eraseIdx'' (f : Nat → Nat) : ∀ (Q : List Nat) (i : Nat),
    (Q.eraseIdx i).map f = (Q.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | q :: Q, i + 1 => by simp [map_eraseIdx'' f Q i]

/-- `r` (new label, `1 ≤ r ≤ t₁`) is early: the common value `α` of the packet of `{r - 1} ∪ X` equals `v(X)`. -/
private def early (v : SignMap) (X : List Nat) (r : Nat) : Bool := v ((r - 1) :: X.eraseIdx 0) == v X

private theorem prefix_signotope {M k : Nat} (hk : 1 ≤ k) {v : SignMap} {X : List Nat} (hX : IsRSet M k X)
    (hv : IsSignotopeR M k v) (hvX : IsSignotopeR M k (flipR v X)) (T : List Nat) (hT : T.Nodup)
    (hord : ∀ p r, p < r → r ≤ X.headD 0 →
      (early v X r = true → p ∈ T → r ∈ T) ∧ (early v X r = false → r ∈ T → p ∈ T)) :
    IsSignotopeR (M + 1) (k + 1) (flipsR (expand v) (T.map (Qf X))) := by
  intro P hP
  obtain ⟨hlen, hinc, hlt⟩ := hP
  match P, hlen, hinc, hlt with
  | p :: r :: R, hlen, hinc, hlt =>
  simp only [List.length_cons] at hlen
  have hRlen : R.length = k := by omega
  simp only [StrictIncr, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hinc
  obtain ⟨⟨hpr, hpR⟩, hrR, hRinc⟩ := hinc
  have hR1 : ∀ x ∈ R, 1 ≤ x := fun x hx => by have := hpR x hx; omega
  have hr1 : 1 ≤ r := by omega
  -- the (k+1)-set `(r - 1) :: R'` of `[M]`
  have hRset : IsRSet M (k + 1) ((r - 1) :: R.map (· - 1)) := by
    refine ⟨by simp [hRlen], ?_, ?_⟩
    · simp only [StrictIncr, List.pairwise_cons, List.mem_map, List.pairwise_map]
      refine ⟨?_, hRinc.imp_of_mem (fun ha hb hab => by have := hR1 _ ha; have := hR1 _ hb; omega)⟩
      rintro _ ⟨x, hx, rfl⟩
      have := hrR x hx; omega
    · intro x hx
      simp only [List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · have := hlt r (by simp); omega
      · have := hlt y (by simp [hy]); have := hR1 y hy; omega
  rw [rpacket_cons2, wval v X T hT p R hR1, wval v X T hT r R hR1]
  have hC : ((List.range R.length).reverse.map fun i =>
      flipsR (expand v) (T.map (Qf X)) (p :: r :: R.eraseIdx i)) =
      (List.range R.length).reverse.map fun i => gmap v X T p ((r - 1) :: (R.map (· - 1)).eraseIdx i) := by
    apply List.map_congr_left
    intro i _
    rw [wval v X T hT p _ (fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hr1
      · exact hR1 x (List.mem_of_mem_eraseIdx hx))]
    simp [map_eraseIdx'']
  rw [hC]
  have hgp := (if hpT : p ∈ T then by have := hvX _ hRset; simpa [gmap, hpT] using this
    else by have := hv _ hRset; simpa [gmap, hpT] using this :
      oneChange (rpacket (gmap v X T p) ((r - 1) :: R.map (· - 1))) = true)
  rw [rpacket_cons1, List.length_map] at hgp
  by_cases hRX : R.map (· - 1) = X
  · rw [hRX] at hgp hRset ⊢
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hXlen : X.length = k' + 1 := by rw [← hRX, List.length_map, hRlen]
    obtain ⟨x0, Xs, rfl⟩ : ∃ x0 Xs, X = x0 :: Xs := by
      cases X with
      | nil => simp at hXlen
      | cons x0 Xs => exact ⟨x0, Xs, rfl⟩
    have hrx : r - 1 < x0 := by
      have := hRset.2.1
      simp only [StrictIncr, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at this
      exact this.1.1
    have hne : ∀ i, (r - 1) :: (x0 :: Xs).eraseIdx i ≠ x0 :: Xs := by
      intro i h
      simp only [List.cons.injEq] at h
      omega
    have hCv : ∀ (u : SignMap), (∀ i, u ((r - 1) :: (x0 :: Xs).eraseIdx i) = v ((r - 1) :: (x0 :: Xs).eraseIdx i)) →
        ((List.range (k' + 1)).reverse.map fun i => u ((r - 1) :: (x0 :: Xs).eraseIdx i)) =
        ((List.range k').reverse.map fun i => v ((r - 1) :: (x0 :: Xs).eraseIdx (i + 1))) ++
          [v ((r - 1) :: (x0 :: Xs).eraseIdx 0)] := by
      intro u hu
      rw [range_succ_rev_map]
      simp only [hu]
    have hv1 := hv _ hRset
    rw [rpacket_cons1, hXlen, hCv v (fun _ => rfl)] at hv1
    have hv2 := hvX _ hRset
    rw [rpacket_cons1, hXlen, hCv _ (fun i => flipR_ne v (hne i)), flipR_self] at hv2
    rw [hRlen, hCv _ (fun i => gmap_ne v _ T p (hne i))]
    refine oneChange_key _ _ (v (x0 :: Xs)) _ _ hv1 hv2 ?_
    rw [gmap_X, gmap_X]
    have hord' := hord p r hpr (by simp; omega)
    rintro ⟨hc, hd⟩
    cases he : early v (x0 :: Xs) r
    · have h1 := hord'.2 he
      simp only [early, beq_eq_false_iff_ne, ne_eq] at he
      by_cases hrT : r ∈ T
      · have hpT := h1 hrT
        simp only [hpT, hrT, ite_true] at hc hd
        cases ha : v ((r - 1) :: (x0 :: Xs).eraseIdx 0) <;> cases hτ : v (x0 :: Xs) <;> simp_all
      · simp only [hrT, ite_false] at hd
        exact he hd.symm
    · have h1 := hord'.1 he
      simp only [early, beq_iff_eq] at he
      by_cases hpT : p ∈ T
      · have hrT := h1 hpT
        simp only [hrT, ite_true] at hd
        cases ha : v ((r - 1) :: (x0 :: Xs).eraseIdx 0) <;> cases hτ : v (x0 :: Xs) <;> simp_all
      · simp only [hpT, ite_false] at hc
        cases ha : v ((r - 1) :: (x0 :: Xs).eraseIdx 0) <;> cases hτ : v (x0 :: Xs) <;> simp_all
  · rw [gmap_ne v X T p hRX, gmap_ne v X T r hRX]
    rw [gmap_ne v X T p hRX] at hgp
    exact oneChange_dup _ _ hgp


/-- The order of `Λ = {0, …, n}`: start with `[0]`, then put each `j = 1, …, n` at the front if `e j` (early) and
at the back otherwise. -/
private def ordL (e : Nat → Bool) : Nat → List Nat
  | 0 => [0]
  | n + 1 => if e (n + 1) then (n + 1) :: ordL e n else ordL e n ++ [n + 1]

private theorem mem_ordL (e : Nat → Bool) : ∀ n x, x ∈ ordL e n ↔ x ≤ n
  | 0, x => by simp [ordL]
  | n + 1, x => by
    have ih := mem_ordL e n x
    unfold ordL
    split <;> simp [ih] <;> omega

private theorem ordL_perm (e : Nat → Bool) : ∀ n, (ordL e n).Perm (List.range (n + 1))
  | 0 => by simp [ordL]
  | n + 1 => by
    have ih := ordL_perm e n
    rw [List.range_succ]
    unfold ordL
    split
    · exact (ih.cons (n + 1)).trans (List.perm_append_singleton _ _).symm
    · exact ih.append_right [n + 1]

private theorem ordL_nodup (e : Nat → Bool) (n : Nat) : (ordL e n).Nodup :=
  (ordL_perm e n).nodup_iff.2 List.nodup_range

/-- Equation (8.1): an early `r` precedes, and a late `r` follows, every smaller element. -/
private theorem ordL_prop (e : Nat → Bool) : ∀ n i p r, p < r → r ≤ n →
    (e r = true → p ∈ (ordL e n).take i → r ∈ (ordL e n).take i) ∧
    (e r = false → r ∈ (ordL e n).take i → p ∈ (ordL e n).take i)
  | 0, _, _, _, h1, h2 => by omega
  | n + 1, i, p, r, h1, h2 => by
    unfold ordL
    split
    · rename_i he
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.take_succ_cons, List.mem_cons]
        by_cases hr : r = n + 1
        · subst hr; simp [he]
        · have ih := ordL_prop e n j p r h1 (by omega)
          constructor
          · intro h3 h4; right; exact ih.1 h3 (h4.resolve_left (by omega))
          · intro h3 h4; right; exact ih.2 h3 (h4.resolve_left hr)
    · rename_i he
      simp only [List.take_append, List.mem_append]
      by_cases hr : r = n + 1
      · subst hr
        simp only [Bool.not_eq_true] at he
        refine ⟨fun h => by simp [he] at h, fun _ h4 => ?_⟩
        rcases h4 with h4 | h4
        · have := (mem_ordL e n _).1 (List.mem_of_mem_take h4); omega
        · have hi : (ordL e n).length < i := by
            false_or_by_contra
            rename_i hc
            have : i - (ordL e n).length = 0 := by omega
            rw [this] at h4; simp at h4
          left
          rw [List.take_of_length_le (by omega)]
          exact (mem_ordL e n p).2 (by omega)
      · have ih := ordL_prop e n i p r h1 (by omega)
        have hnot : ∀ x, x ≤ n → x ∉ List.take (i - (ordL e n).length) [n + 1] := by
          intro x hx hm
          have := List.mem_of_mem_take hm
          simp at this; omega
        constructor
        · intro h3 h4
          exact Or.inl (ih.1 h3 (h4.resolve_right (hnot p (by omega))))
        · intro h3 h4
          exact Or.inl (ih.2 h3 (h4.resolve_right (hnot r (by omega))))


private theorem qf_rset {M k : Nat} {X : List Nat} (hX : IsRSet M k X) (hk : 1 ≤ k) {j : Nat}
    (hj : j ≤ X.headD 0) : IsRSet (M + 1) (k + 1) (Qf X j) := by
  obtain ⟨x0, Xs, rfl⟩ : ∃ x0 Xs, X = x0 :: Xs := by
    cases X with
    | nil => have := hX.1; simp at this; omega
    | cons x0 Xs => exact ⟨x0, Xs, rfl⟩
  have hX' := hX.map_add 1
  have hinc := hX.2.1
  simp only [StrictIncr, List.pairwise_cons] at hinc
  have hx0 := hX.2.2 x0 (by simp)
  simp only [List.headD_cons] at hj
  refine ⟨by have := hX.1; simp only [List.length_cons] at this; simp [Qf, this], ?_, ?_⟩
  · unfold Qf StrictIncr
    refine List.Pairwise.cons ?_ hX'.2.1
    intro b hb
    simp only [List.map_cons, List.mem_cons, List.mem_map] at hb
    rcases hb with rfl | ⟨y, hy, rfl⟩
    · omega
    · have := hinc.1 y hy; omega
  · intro x hx
    simp only [Qf, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · exact hX'.2.2 x hx

/-- Lemma 8.1(b): a walk in `B([M+1], k)` from `v'` to `(v^X)'` flipping each `Q_x` exactly once and nothing
else. -/
theorem onestep_b {M k : Nat} (hk : 2 ≤ k) {v : SignMap} {X : List Nat} (hX : IsRSet M k X)
    (hv : IsSignotopeR M k v) (hvX : IsSignotopeR M k (flipR v X)) :
    ∃ Zs : List (List Nat), FlipWalkR (M + 1) (k + 1) (IsSignotopeR (M + 1) (k + 1)) (expand v) Zs ∧
      AgreeR (M + 1) (k + 1) (flipsR (expand v) Zs) (expand (flipR v X)) ∧
      ∀ Z, Zs.count Z = (qsets X).count Z := by
  have hk1 : 1 ≤ k := by omega
  refine ⟨(ordL (early v X) (X.headD 0)).map (Qf X), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hZ
    exact qf_rset hX hk1 ((mem_ordL _ _ _).1 hj)
  · intro i _
    rw [← List.map_take]
    exact prefix_signotope hk1 hX hv hvX _ ((List.take_sublist _ _).nodup (ordL_nodup _ _))
      (fun p r h1 h2 => ordL_prop _ _ i p r h1 h2)
  · intro Z hZ
    obtain ⟨hlen, hinc, hlt⟩ := hZ
    match Z, hlen, hinc with
    | h :: Y, hlen, hinc =>
    simp only [StrictIncr, List.pairwise_cons] at hinc
    have hY1 : ∀ y ∈ Y, 1 ≤ y := fun y hy => by have := hinc.1 y hy; omega
    rw [wval v X _ (ordL_nodup _ _) h Y hY1]
    have hexp : expand (flipR v X) (h :: Y) = flipR v X (Y.map (· - 1)) := by simp [expand]
    rw [hexp]
    by_cases hL : h ∈ ordL (early v X) (X.headD 0)
    · unfold gmap; simp only [hL, ↓reduceIte]
    · have hh : X.headD 0 < h := by
        exact Nat.lt_of_not_le fun h' => hL ((mem_ordL _ _ _).2 h')
      have hne : Y.map (· - 1) ≠ X := by
        intro heq
        cases Y with
        | nil =>
          have := hX.1; rw [← heq] at this; simp at this; omega
        | cons y Y =>
          have hy := hinc.1 y (by simp)
          rw [← heq] at hh
          simp at hh; omega
      rw [gmap_ne v X _ h hne, flipR_ne v hne]
  · intro Z
    exact ((ordL_perm _ _).map (Qf X)).count_eq Z

end OMDistance
