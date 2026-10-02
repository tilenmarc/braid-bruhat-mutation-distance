import BraidDistance.Blowup
import BraidDistance.FactorOverlap

/-!
# One step of the bead sweep, up to commutations (Lemma 4.5(a))

Passing from `W^ε_k` to `W^ε_{k+1}` moves the beads past the factor `φ_{k+1}` (0-based: the `k`-th factor).
The beads of the blocks not involved in the factor act on positions disjoint from (and not adjacent to) the window
of the factor, and keep their positions, so they commute with it; the beads of different blocks commute with each
other.  Hence, up to commutations, `W^ε_k = A ++ L ++ C` and `W^ε_{k+1} = A ++ L' ++ C`, where `L`, `L'` are the
local words of the case of the factor shifted to its window, and after `A` the wires `Z` of the factor occupy the
window in increasing order (they have not been swapped with each other yet, and the bead of a block lies in `L`).

`A` is `Φ̂` up to the factor followed by the beads of the other blocks, `C` is the rest of `Φ̂`.
-/

namespace BraidDistance

/-! ### Helpers -/

/-- Every letter of `U` commutes with every letter of `V`. -/
private def SD.Comm (U V : List Nat) : Prop := ∀ x ∈ U, ∀ y ∈ V, x + 2 ≤ y ∨ y + 2 ≤ x

/-- Pairwise commuting blocks, indexed by a duplicate-free list, can be permuted by commutations. -/
private theorem SD.blocks_perm (f : Nat → List Nat) {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) :
    l₁.Nodup → (∀ x ∈ l₁, ∀ y ∈ l₁, x ≠ y → SD.Comm (f x) (f y)) →
    Path (l₁.flatMap f) (l₂.flatMap f) 0 := by
  induction hp with
  | nil => intro _ _; exact Path.refl _
  | cons x p ih =>
    intro hnd hc
    have h := (ih (List.nodup_cons.mp hnd).2 (fun a ha b hb hab =>
      hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)).context (f x) []
    simpa [List.flatMap_cons] using h
  | swap x y l =>
    intro hnd hc
    have hxy : y ≠ x := by
      intro e; subst e; simp at hnd
    have h := Path.commute [] (f y) (f x) (l.flatMap f) (hc y (by simp) x (by simp) hxy)
    simpa [List.flatMap_cons] using h
  | trans p1 p2 ih1 ih2 =>
    intro hnd hc
    have h1 := ih1 hnd hc
    have h2 := ih2 (p1.nodup_iff.mp hnd)
      (fun a ha b hb hab => hc a (p1.mem_iff.mpr ha) b (p1.mem_iff.mpr hb) hab)
    exact (h1.trans h2).cast (by omega)

private theorem SD.wp_cons_self {a : Grp} {L : List Grp} : wirePos (a :: L) a = 0 := by
  simp [wirePos]

private theorem SD.wp_cons_ne {a g : Grp} {L : List Grp} (h : a ≠ g) :
    wirePos (a :: L) g = a.size + wirePos L g := by
  unfold wirePos
  rw [List.idxOf_cons]
  have hb : (a == g) = false := by simp [h]
  simp [hb]

private theorem SD.wp_append_mem {P R : List Grp} {g : Grp} (hg : g ∈ P) :
    wirePos (P ++ R) g = wirePos P g := by
  induction P with
  | nil => simp at hg
  | cons a P ih =>
    by_cases hag : a = g
    · subst hag; simp only [List.cons_append, SD.wp_cons_self]
    · have hgP : g ∈ P := by
        rcases List.mem_cons.mp hg with e | e
        · exact absurd e.symm hag
        · exact e
      rw [List.cons_append, SD.wp_cons_ne hag, SD.wp_cons_ne hag, ih hgP]

private theorem SD.wp_append_not_mem {P R : List Grp} {g : Grp} (hg : g ∉ P) :
    wirePos (P ++ R) g = (P.map Grp.size).sum + wirePos R g := by
  induction P with
  | nil => simp
  | cons a P ih =>
    have hag : a ≠ g := fun e => hg (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, SD.wp_cons_ne hag, ih (fun h => hg (List.mem_cons_of_mem _ h))]
    simp only [List.map_cons, List.sum_cons]; omega

private theorem SD.wp_add_size_le {L : List Grp} {g : Grp} (hg : g ∈ L) :
    wirePos L g + g.size ≤ (L.map Grp.size).sum := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    by_cases hag : a = g
    · subst hag
      simp [SD.wp_cons_self]
    · have hgL : g ∈ L := by
        rcases List.mem_cons.mp hg with h | h
        · exact absurd h.symm hag
        · exact h
      rw [SD.wp_cons_ne hag]
      have := ih hgL
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Two different groups of an arrangement occupy disjoint ranges of positions. -/
private theorem SD.wp_sep {L : List Grp} {g h : Grp} (hg : g ∈ L) (hh : h ∈ L) (hgh : g ≠ h) :
    wirePos L g + g.size ≤ wirePos L h ∨ wirePos L h + h.size ≤ wirePos L g := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    by_cases hag : a = g
    · subst hag; left; rw [SD.wp_cons_self, SD.wp_cons_ne hgh]; omega
    · by_cases hah : a = h
      · subst hah; right; rw [SD.wp_cons_self, SD.wp_cons_ne hag]; omega
      · have hgL : g ∈ L := by
          rcases List.mem_cons.mp hg with e | e
          · exact absurd e.symm hag
          · exact e
        have hhL : h ∈ L := by
          rcases List.mem_cons.mp hh with e | e
          · exact absurd e.symm hah
          · exact e
        rw [SD.wp_cons_ne hag, SD.wp_cons_ne hah]
        have := ih hgL hhL
        omega

private theorem SD.mem_bead {t : Bool} {r x : Nat} (h : x ∈ bead t r) : r ≤ x ∧ x ≤ r + 1 := by
  cases t <;> simp [bead] at h <;> omega

private theorem SD.shiftW_bead (t : Bool) (q r : Nat) : shiftW q (bead t r) = bead t (q + r) := by
  cases t <;> simp [bead, shiftW] <;> omega

/-- A bead acting outside the window `[q, q + wd)` leaves the wires in the window in place. -/
private theorem SD.window_bead (l : List Nat) (t : Bool) (r q wd : Nat) (hr : r + 3 ≤ l.length)
    (hd : r + 3 ≤ q ∨ q + wd ≤ r) :
    ((arrFrom l (bead t r)).drop q).take wd = (l.drop q).take wd := by
  have hv : ValidWord 3 (bead t 0) := by cases t <;> decide
  have e : bead t r = shiftW r (bead t 0) := by rw [SD.shiftW_bead, Nat.add_zero]
  rw [e, arrFrom_shift l (bead t 0) r 3 hv hr]
  have hlen : ((arrAfter 3 (bead t 0)).map (fun i => l.getD (r + i) 0)).length = 3 := by
    simp [arrAfter_length]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · rcases hd with hd | hd
    · rw [List.getElem?_append_right (by simp [arrAfter_length]; omega), List.getElem?_drop]
      congr 1; simp [arrAfter_length]; omega
    · rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take]
      simp; omega
  · rfl


/-- Beads acting outside the window `[q, q + wd)` leave the wires in the window in place. -/
private theorem SD.window_beads (e : Nat → Bool) (pos : Nat → Nat) (q wd : Nat) (R : List Nat) :
    ∀ l : List Nat, (∀ v ∈ R, pos v + 3 ≤ l.length ∧ (pos v + 3 ≤ q ∨ q + wd ≤ pos v)) →
    ((arrFrom l (R.flatMap fun v => bead (e v) (pos v))).drop q).take wd = (l.drop q).take wd := by
  induction R with
  | nil => intro l _; rfl
  | cons v R ih =>
    intro l h
    rw [List.flatMap_cons, arrFrom_append]
    have hv := h v (List.mem_cons_self ..)
    rw [ih _ (fun x hx => by rw [arrFrom_length]; exact h x (List.mem_cons_of_mem _ hx)),
      SD.window_bead l (e v) (pos v) q wd hv.1 hv.2]

private theorem SD.bead_comm {t t' : Bool} {r r' : Nat} (h : r + 3 ≤ r' ∨ r' + 3 ≤ r) :
    SD.Comm (bead t r) (bead t' r') := by
  intro x hx y hy
  have := SD.mem_bead hx
  have := SD.mem_bead hy
  omega

private theorem SD.map_swapNames {g h : Grp} {l : List Grp} (hl : ∀ x ∈ l, x ≠ g ∧ x ≠ h) :
    l.map (swapNames g h) = l := by
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  simp [swapNames, (hl x hx).1, (hl x hx).2]

private theorem SD.length_blowArr (G : Graph) (L : List Grp) :
    (blowArr G L).length = (L.map Grp.size).sum := by
  simp [blowArr, List.length_flatMap, wiresOf]

/-- The decomposition, given the arrangement of the groups around the factor: before the step the groups `M` of
the factor lie between `A'` and `B'`, after it the groups `M'`; `I`, `I'` are the vertices of the blocks of the factor
in the order of the beads in `L`, `L'`. -/
private theorem SD.core (G : Graph) (hG : G.Valid) (eps : Nat → Bool) {k : Nat} (hk : k < numFactors G)
    (A' M M' B' : List Grp) (I I' : List Nat)
    (harr : arrAt G k = A' ++ M ++ B') (harr' : arrAt G (k + 1) = A' ++ M' ++ B')
    (hMM' : ∀ x, x ∈ M' ↔ x ∈ M) (hsz : (M'.map Grp.size).sum = (M.map Grp.size).sum)
    (hI : ∀ v, v ∈ I ↔ v < G.n ∧ Grp.X v ∈ M) (hI' : ∀ v, v ∈ I' ↔ v ∈ I)
    (hInd : I.Nodup) (hI'nd : I'.Nodup)
    (hq : stepWindow G k = (A'.map Grp.size).sum)
    (hL : I.flatMap (fun v => bead (eps v) (wirePos (arrAt G k) (.X v))) ++
        shiftW (stepWindow G k) (evLocal (evAt G k)) = shiftW (stepWindow G k) (stepCase G k eps).L)
    (hL' : shiftW (stepWindow G k) (evLocal (evAt G k)) ++
        I'.flatMap (fun v => bead (eps v) (wirePos (arrAt G (k + 1)) (.X v))) =
        shiftW (stepWindow G k) (stepCase G k eps).L')
    (hwd : (stepCase G k eps).width = (M.map Grp.size).sum)
    (hZ : stepZ G k = M.flatMap (wiresOf G))
    (hφ : ∀ x ∈ evLocal (evAt G k), x + 2 ≤ (M.map Grp.size).sum) :
    ∃ A C : List Nat,
      Path (W G k eps) (A ++ shiftW (stepWindow G k) (stepCase G k eps).L ++ C) 0 ∧
      Path (W G (k + 1) eps) (A ++ shiftW (stepWindow G k) (stepCase G k eps).L' ++ C) 0 ∧
      ((arrAfter G.m A).drop (stepWindow G k)).take (stepCase G k eps).width = stepZ G k := by
  have hperm := arrAt_perm G hG (Nat.le_of_lt hk)
  have hperm' := arrAt_perm G hG (Nat.succ_le_of_lt hk)
  have hXmem : ∀ v, v < G.n → Grp.X v ∈ arrAt G k := fun v hv =>
    hperm.mem_iff.mpr ((mem_labelOrder G hG _).mpr (Or.inl ⟨v, hv, rfl⟩))
  have hXmem' : ∀ v, v < G.n → Grp.X v ∈ arrAt G (k + 1) := fun v hv =>
    hperm'.mem_iff.mpr ((mem_labelOrder G hG _).mpr (Or.inl ⟨v, hv, rfl⟩))
  have hblow : arrAfter G.m ((factors G).take k).flatten = blowArr G (arrAt G k) :=
    blowup_arr G hG (Nat.le_of_lt hk)
  have hszm : ((arrAt G k).map Grp.size).sum = G.m := by
    rw [← SD.length_blowArr, ← hblow, arrAfter_length]
  -- the beads
  let pos : Nat → Nat := fun v => wirePos (arrAt G k) (.X v)
  let pos' : Nat → Nat := fun v => wirePos (arrAt G (k + 1)) (.X v)
  let f : Nat → List Nat := fun v => bead (eps v) (pos v)
  let f' : Nat → List Nat := fun v => bead (eps v) (pos' v)
  let R : List Nat := (List.range G.n).filter (fun v => v ∉ I)
  have hRmem : ∀ v, v ∈ R ↔ v < G.n ∧ v ∉ I := by
    intro v; simp [R]
  have hRpos : ∀ v ∈ R, pos' v = pos v ∧
      (pos v + 3 ≤ stepWindow G k ∨ stepWindow G k + (M.map Grp.size).sum ≤ pos v) ∧
      pos v + 3 ≤ G.m := by
    intro v hv
    obtain ⟨hvn, hvI⟩ := (hRmem v).mp hv
    have hXM : Grp.X v ∉ M := fun h => hvI ((hI v).mpr ⟨hvn, h⟩)
    have hXM' : Grp.X v ∉ M' := fun h => hXM ((hMM' _).mp h)
    have hb := SD.wp_add_size_le (hXmem v hvn)
    rw [hszm] at hb
    refine ⟨?_, ?_, hb⟩
    · show wirePos (arrAt G (k + 1)) (.X v) = wirePos (arrAt G k) (.X v)
      rw [harr, harr']
      by_cases hA : Grp.X v ∈ A'
      · rw [List.append_assoc, List.append_assoc, SD.wp_append_mem hA, SD.wp_append_mem hA]
      · rw [List.append_assoc, List.append_assoc, SD.wp_append_not_mem hA, SD.wp_append_not_mem hA,
          SD.wp_append_not_mem hXM, SD.wp_append_not_mem hXM', hsz]
    · show wirePos (arrAt G k) (.X v) + 3 ≤ stepWindow G k ∨
        stepWindow G k + (M.map Grp.size).sum ≤ wirePos (arrAt G k) (.X v)
      rw [hq, harr]
      by_cases hA : Grp.X v ∈ A'
      · left
        rw [List.append_assoc, SD.wp_append_mem hA]
        exact SD.wp_add_size_le hA
      · right
        rw [List.append_assoc, SD.wp_append_not_mem hA, SD.wp_append_not_mem hXM]
        omega
  have hnI : ∀ v ∈ I, v < G.n := fun v hv => ((hI v).mp hv).1
  have hR_nd : R.Nodup := List.nodup_range.filter _
  have hpermI : ∀ J : List Nat, J.Nodup → (∀ v, v ∈ J ↔ v ∈ I) → (List.range G.n).Perm (R ++ J) := by
    intro J hJ hJI
    apply (List.perm_ext_iff_of_nodup List.nodup_range ?_).mpr
    · intro v
      simp only [List.mem_range, List.mem_append, hRmem, hJI]
      constructor
      · intro hv
        by_cases h : v ∈ I
        · exact Or.inr h
        · exact Or.inl ⟨hv, h⟩
      · rintro (h | h)
        · exact h.1
        · exact hnI v h
    · rw [List.nodup_append]
      exact ⟨hR_nd, hJ, fun a ha b hb e => ((hRmem a).mp ha).2 (by subst e; exact (hJI a).mp hb)⟩
  have hc : ∀ x ∈ List.range G.n, ∀ y ∈ List.range G.n, x ≠ y → SD.Comm (f x) (f y) := by
    intro x hx y hy hxy
    apply SD.bead_comm
    have := SD.wp_sep (hXmem x (List.mem_range.mp hx)) (hXmem y (List.mem_range.mp hy))
      (fun e => hxy (Grp.X.inj e))
    simpa [Grp.size] using this
  have hc' : ∀ x ∈ List.range G.n, ∀ y ∈ List.range G.n, x ≠ y → SD.Comm (f' x) (f' y) := by
    intro x hx y hy hxy
    apply SD.bead_comm
    have := SD.wp_sep (hXmem' x (List.mem_range.mp hx)) (hXmem' y (List.mem_range.mp hy))
      (fun e => hxy (Grp.X.inj e))
    simpa [Grp.size] using this
  have p1 : Path (beadsAt G k eps) (R.flatMap f ++ I.flatMap f) 0 := by
    have := SD.blocks_perm f (hpermI I hInd (fun _ => Iff.rfl)) List.nodup_range hc
    rw [List.flatMap_append] at this
    exact this
  have p2 : Path (beadsAt G (k + 1) eps) (R.flatMap f' ++ I'.flatMap f') 0 := by
    have := SD.blocks_perm f' (hpermI I' hI'nd hI') List.nodup_range hc'
    rw [List.flatMap_append] at this
    exact this
  have hRf : R.flatMap f' = R.flatMap f := by
    simp only [List.flatMap]
    congr 1
    apply List.map_congr_left
    intro v hv
    simp only [f, f', (hRpos v hv).1]
  refine ⟨((factors G).take k).flatten ++ R.flatMap f, ((factors G).drop (k + 1)).flatten, ?_, ?_, ?_⟩
  · show Path (((factors G).take k).flatten ++ beadsAt G k eps ++ ((factors G).drop k).flatten) _ 0
    rw [factors_split G hk, ← hL]
    have := p1.context (((factors G).take k).flatten)
      (shiftW (stepWindow G k) (evLocal (evAt G k)) ++ ((factors G).drop (k + 1)).flatten)
    simpa only [List.append_assoc] using this
  · show Path (((factors G).take (k + 1)).flatten ++ beadsAt G (k + 1) eps ++
      ((factors G).drop (k + 1)).flatten) _ 0
    rw [factors_take_succ G hk, ← hL']
    have h1 := p2.context (((factors G).take k).flatten ++ shiftW (stepWindow G k) (evLocal (evAt G k)))
      (((factors G).drop (k + 1)).flatten)
    rw [hRf] at h1
    have h2 := Path.commute (((factors G).take k).flatten) (shiftW (stepWindow G k) (evLocal (evAt G k)))
      (R.flatMap f) (I'.flatMap f' ++ ((factors G).drop (k + 1)).flatten) (by
        intro x hx y hy
        obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
        obtain ⟨v, hv, hyv⟩ := List.mem_flatMap.mp hy
        have h3 := SD.mem_bead hyv
        have h4 := (hRpos v hv).2.1
        have h5 := hφ x0 hx0
        omega)
    have := h1.trans (by simpa only [List.append_assoc] using h2)
    simpa only [List.append_assoc] using this
  · rw [hwd, hZ]
    have e1 : arrAfter G.m (((factors G).take k).flatten ++ R.flatMap f) =
        arrFrom (blowArr G (arrAt G k)) (R.flatMap fun v => bead (eps v) (pos v)) := by
      unfold arrAfter; rw [arrFrom_append]; rw [← hblow]; rfl
    rw [e1, SD.window_beads eps pos _ _ R _ (fun v hv => ⟨by rw [SD.length_blowArr, hszm]; exact (hRpos v hv).2.2,
      (hRpos v hv).2.1⟩), hq, harr]
    have hA : (A'.flatMap (wiresOf G)).length = (A'.map Grp.size).sum := SD.length_blowArr G A'
    have hM : (M.flatMap (wiresOf G)).length = (M.map Grp.size).sum := SD.length_blowArr G M
    unfold blowArr
    rw [List.flatMap_append, List.flatMap_append, ← hA, List.append_assoc, List.drop_left, ← hM,
      List.take_left]

private theorem SD.wp_after {A' R : List Grp} {x : Grp} (hx : x ∉ A') :
    wirePos (A' ++ R) x = (A'.map Grp.size).sum + wirePos R x := SD.wp_append_not_mem hx

/-- The arrangements before and after a move event. -/
private theorem SD.mv_setup (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) {g h : Grp}
    (hE : evAt G k = .mv g h) :
    ∃ A' B', arrAt G k = A' ++ [g, h] ++ B' ∧ arrAt G (k + 1) = A' ++ [h, g] ++ B' ∧ g ≠ h ∧
      g ∉ A' ∧ h ∉ A' ∧ stepWindow G k = (A'.map Grp.size).sum := by
  have hok := sweep_ok G hG hk
  have hsucc := arrAt_succ G hk
  have hnd : (arrAt G k).Nodup :=
    (arrAt_perm G hG (Nat.le_of_lt hk)).nodup_iff.mpr (labelOrder_nodup G)
  rw [hE] at hok hsucc
  obtain ⟨A', B', harr⟩ := hok
  rw [harr] at hnd
  have hn1 := List.nodup_append.mp hnd
  have hn2 := List.nodup_cons.mp hn1.2.1
  have hn3 := List.nodup_cons.mp hn2.2
  have hgA : g ∉ A' := fun hx => hn1.2.2 g hx g (List.mem_cons_self ..) rfl
  have hhA : h ∉ A' := fun hx => hn1.2.2 h hx h (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl
  have hgh : g ≠ h := fun e => hn2.1 (e ▸ List.mem_cons_self ..)
  have hgB : g ∉ B' := fun hx => hn2.1 (List.mem_cons_of_mem _ hx)
  have hhB : h ∉ B' := hn3.1
  refine ⟨A', B', by simp [harr], ?_, hgh, hgA, hhA, ?_⟩
  · rw [hsucc, harr]
    simp only [applyEv, List.map_append, List.map_cons]
    rw [SD.map_swapNames (fun x hx => ⟨fun e => hgA (by subst e; exact hx), fun e => hhA (by subst e; exact hx)⟩),
      SD.map_swapNames (fun x hx => ⟨fun e => hgB (by subst e; exact hx), fun e => hhB (by subst e; exact hx)⟩)]
    simp [swapNames, Ne.symm hgh]
  · unfold stepWindow
    rw [hE, harr]
    simp only [evTop]
    rw [SD.wp_after hgA, SD.wp_cons_self, Nat.add_zero]

/-- The arrangements before and after a cell event. -/
private theorem SD.cell_setup (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) {u w : Nat}
    (hE : evAt G k = .cell u w) :
    ∃ A' B', arrAt G k = A' ++ [.X u, .p u w, .X w] ++ B' ∧
      arrAt G (k + 1) = A' ++ [.X w, .p u w, .X u] ++ B' ∧ u ≠ w ∧
      Grp.X u ∉ A' ∧ Grp.X w ∉ A' ∧ stepWindow G k = (A'.map Grp.size).sum := by
  have hok := sweep_ok G hG hk
  have hsucc := arrAt_succ G hk
  have hnd : (arrAt G k).Nodup :=
    (arrAt_perm G hG (Nat.le_of_lt hk)).nodup_iff.mpr (labelOrder_nodup G)
  rw [hE] at hok hsucc
  obtain ⟨A', B', harr⟩ := hok
  rw [harr] at hnd
  have hn1 := List.nodup_append.mp hnd
  have hn2 := List.nodup_cons.mp hn1.2.1
  have hn3 := List.nodup_cons.mp hn2.2
  have hn4 := List.nodup_cons.mp hn3.2
  have hgA : Grp.X u ∉ A' := fun hx => hn1.2.2 _ hx _ (List.mem_cons_self ..) rfl
  have hhA : Grp.X w ∉ A' := fun hx => hn1.2.2 _ hx _ (by simp) rfl
  have hgh : u ≠ w := fun e => hn2.1 (by subst e; simp)
  have hgB : Grp.X u ∉ B' := fun hx => hn2.1 (by simp [hx])
  have hhB : Grp.X w ∉ B' := hn4.1
  refine ⟨A', B', by simp [harr], ?_, hgh, hgA, hhA, ?_⟩
  · rw [hsucc, harr]
    simp only [applyEv, List.map_append, List.map_cons]
    rw [SD.map_swapNames (fun x hx => ⟨fun e => hgA (by subst e; exact hx), fun e => hhA (by subst e; exact hx)⟩),
      SD.map_swapNames (fun x hx => ⟨fun e => hgB (by subst e; exact hx), fun e => hhB (by subst e; exact hx)⟩)]
    simp [swapNames, Ne.symm hgh]
  · unfold stepWindow
    rw [hE, harr]
    simp only [evTop]
    rw [SD.wp_after hgA, SD.wp_cons_self, Nat.add_zero]

private theorem SD.shiftW_append (q : Nat) (a b : List Nat) : shiftW q (a ++ b) = shiftW q a ++ shiftW q b :=
  List.map_append

/-- Lemma 4.5(a). -/
theorem step_decomp (G : Graph) (hG : G.Valid) (eps : Nat → Bool) {k : Nat} (hk : k < numFactors G) :
    ∃ A C : List Nat,
      Path (W G k eps) (A ++ shiftW (stepWindow G k) (stepCase G k eps).L ++ C) 0 ∧
      Path (W G (k + 1) eps) (A ++ shiftW (stepWindow G k) (stepCase G k eps).L' ++ C) 0 ∧
      ((arrAfter G.m A).drop (stepWindow G k)).take (stepCase G k eps).width = stepZ G k := by
  have hperm := arrAt_perm G hG (Nat.le_of_lt hk)
  have hXn : ∀ v, Grp.X v ∈ arrAt G k → v < G.n := by
    intro v hv
    rcases (mem_labelOrder G hG _).mp (hperm.mem_iff.mp hv) with ⟨u, hu, e⟩ | ⟨u, w, _, e⟩
    · cases e; exact hu
    · cases e
  cases hE : evAt G k with
  | cell u w =>
    obtain ⟨A', B', harr, harr', huw, huA, hwA, hq⟩ := SD.cell_setup G hG hk hE
    have hun : u < G.n := hXn u (by rw [harr]; simp)
    have hwn : w < G.n := hXn w (by rw [harr]; simp)
    have hpu : wirePos (arrAt G k) (.X u) = (A'.map Grp.size).sum := by
      rw [harr, List.append_assoc, SD.wp_after huA]; simp [SD.wp_cons_self]
    have hpw : wirePos (arrAt G k) (.X w) = (A'.map Grp.size).sum + 4 := by
      rw [harr, List.append_assoc, SD.wp_after hwA]; simp [SD.wp_cons_self, SD.wp_cons_ne, huw, Grp.size]
    have hpu' : wirePos (arrAt G (k + 1)) (.X u) = (A'.map Grp.size).sum + 4 := by
      rw [harr', List.append_assoc, SD.wp_after huA]
      simp [SD.wp_cons_self, SD.wp_cons_ne, Ne.symm huw, Grp.size]
    have hpw' : wirePos (arrAt G (k + 1)) (.X w) = (A'.map Grp.size).sum := by
      rw [harr', List.append_assoc, SD.wp_after hwA]; simp [SD.wp_cons_self]
    apply SD.core G hG eps hk A' [.X u, .p u w, .X w] [.X w, .p u w, .X u] B' [u, w] [w, u] harr harr'
    · intro x; simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor <;> rintro (h | h | h) <;> simp [h]
    · simp [Grp.size]
    · intro v; simp only [List.mem_cons, List.not_mem_nil, Grp.X.injEq, reduceCtorEq, false_or, or_false]
      constructor
      · rintro (rfl | rfl) <;> simp_all
      · rintro ⟨_, h⟩; exact h
    · intro v; simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor <;> rintro (h | h) <;> simp [h]
    · simp [huw]
    · simp [Ne.symm huw]
    · exact hq
    · rw [hq]; unfold stepCase; rw [hE]
      simp only [Case.L, caseOf, gadgetS, evLocal, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, hpu, hpw, List.append_assoc, Nat.add_zero]
    · rw [hq]; unfold stepCase; rw [hE]
      simp only [Case.L', caseOf, gadgetV, evLocal, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, hpu', hpw', List.append_assoc, Nat.add_zero]
    · unfold stepCase; rw [hE]; rfl
    · unfold stepZ; rw [hE]; simp [evZ, edgeWires]
    · rw [hE]; exact (by decide : ∀ x ∈ kappa, x + 2 ≤ 7)
  | mv g h =>
    obtain ⟨A', B', harr, harr', hgh, hgA, hhA, hq⟩ := SD.mv_setup G hG hk hE
    cases g with
    | X u =>
      cases h with
      | X w =>
        have huw : u ≠ w := fun e => hgh (by rw [e])
        have hun : u < G.n := hXn u (by rw [harr]; simp)
        have hwn : w < G.n := hXn w (by rw [harr]; simp)
        have hpu : wirePos (arrAt G k) (.X u) = (A'.map Grp.size).sum := by
          rw [harr, List.append_assoc, SD.wp_after hgA]; simp [SD.wp_cons_self]
        have hpw : wirePos (arrAt G k) (.X w) = (A'.map Grp.size).sum + 3 := by
          rw [harr, List.append_assoc, SD.wp_after hhA]; simp [SD.wp_cons_self, SD.wp_cons_ne, huw, Grp.size]
        have hpu' : wirePos (arrAt G (k + 1)) (.X u) = (A'.map Grp.size).sum + 3 := by
          rw [harr', List.append_assoc, SD.wp_after hgA]
          simp [SD.wp_cons_self, SD.wp_cons_ne, Ne.symm huw, Grp.size]
        have hpw' : wirePos (arrAt G (k + 1)) (.X w) = (A'.map Grp.size).sum := by
          rw [harr', List.append_assoc, SD.wp_after hhA]; simp [SD.wp_cons_self]
        apply SD.core G hG eps hk A' [.X u, .X w] [.X w, .X u] B' [u, w] [w, u] harr harr'
        · intro x; simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor <;> rintro (h | h) <;> simp [h]
        · simp [Grp.size]
        · intro v; simp only [List.mem_cons, List.not_mem_nil, Grp.X.injEq, or_false]
          constructor
          · rintro (rfl | rfl) <;> simp_all
          · rintro ⟨_, h⟩; exact h
        · intro v; simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor <;> rintro (h | h) <;> simp [h]
        · simp [huw]
        · simp [Ne.symm huw]
        · exact hq
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L, caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpu, hpw, List.append_assoc, Nat.add_zero]
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L', caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpu', hpw', List.append_assoc, Nat.add_zero]
        · unfold stepCase; rw [hE]; rfl
        · unfold stepZ; rw [hE]; simp [evZ]
        · rw [hE]; exact (by decide : ∀ x ∈ moveWord 3 3, x + 2 ≤ 6)
      | p a b =>
        have hun : u < G.n := hXn u (by rw [harr]; simp)
        have hpu : wirePos (arrAt G k) (.X u) = (A'.map Grp.size).sum := by
          rw [harr, List.append_assoc, SD.wp_after hgA]; simp [SD.wp_cons_self]
        have hpu' : wirePos (arrAt G (k + 1)) (.X u) = (A'.map Grp.size).sum + 1 := by
          rw [harr', List.append_assoc, SD.wp_after hgA]
          simp [SD.wp_cons_self, SD.wp_cons_ne, Grp.size]
        apply SD.core G hG eps hk A' [.X u, .p a b] [.p a b, .X u] B' [u] [u] harr harr'
        · intro x; simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor <;> rintro (h | h) <;> simp [h]
        · simp [Grp.size]
        · intro v; simp only [List.mem_cons, List.not_mem_nil, Grp.X.injEq, reduceCtorEq, or_false]
          constructor
          · rintro rfl; simp_all
          · rintro ⟨_, h⟩; exact h
        · intro v; exact Iff.rfl
        · simp
        · simp
        · exact hq
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L, caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpu, Nat.add_zero]
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L', caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpu']
        · unfold stepCase; rw [hE]; rfl
        · unfold stepZ; rw [hE]; simp [evZ]
        · rw [hE]; exact (by decide : ∀ x ∈ moveWord 3 1, x + 2 ≤ 4)
    | p a b =>
      cases h with
      | X w =>
        have hwn : w < G.n := hXn w (by rw [harr]; simp)
        have hpw : wirePos (arrAt G k) (.X w) = (A'.map Grp.size).sum + 1 := by
          rw [harr, List.append_assoc, SD.wp_after hhA]; simp [SD.wp_cons_self, SD.wp_cons_ne, Grp.size]
        have hpw' : wirePos (arrAt G (k + 1)) (.X w) = (A'.map Grp.size).sum := by
          rw [harr', List.append_assoc, SD.wp_after hhA]; simp [SD.wp_cons_self]
        apply SD.core G hG eps hk A' [.p a b, .X w] [.X w, .p a b] B' [w] [w] harr harr'
        · intro x; simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor <;> rintro (h | h) <;> simp [h]
        · simp [Grp.size]
        · intro v; simp only [List.mem_cons, List.not_mem_nil, Grp.X.injEq, reduceCtorEq, or_false,
            false_or]
          constructor
          · rintro rfl; simp_all
          · rintro ⟨_, h⟩; exact h
        · intro v; exact Iff.rfl
        · simp
        · simp
        · exact hq
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L, caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpw]
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L', caseOf, evLocal, Grp.size, SD.shiftW_append, SD.shiftW_bead, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, hpw', Nat.add_zero]
        · unfold stepCase; rw [hE]; rfl
        · unfold stepZ; rw [hE]; simp [evZ]
        · rw [hE]; exact (by decide : ∀ x ∈ moveWord 1 3, x + 2 ≤ 4)
      | p c d =>
        apply SD.core G hG eps hk A' [.p a b, .p c d] [.p c d, .p a b] B' [] [] harr harr'
        · intro x; simp only [List.mem_cons, List.not_mem_nil, or_false]
          constructor <;> rintro (h | h) <;> simp [h]
        · simp [Grp.size]
        · intro v; simp
        · intro v; exact Iff.rfl
        · simp
        · simp
        · exact hq
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L, caseOf, evLocal, Grp.size, List.flatMap_nil, List.nil_append]
        · rw [hq]; unfold stepCase; rw [hE]
          simp only [Case.L', caseOf, evLocal, Grp.size, List.flatMap_nil, List.append_nil]
        · unfold stepCase; rw [hE]; rfl
        · unfold stepZ; rw [hE]; simp [evZ]
        · rw [hE]; exact (by decide : ∀ x ∈ moveWord 1 1, x + 2 ≤ 2)

end BraidDistance
