import BraidDistance.SweepPairs
import BraidDistance.Arrangement
import BraidDistance.LocalCases

/-!
# The blow-up (Lemma 4.4)

Before and after every factor of `Φ̂` the wires are arranged as the groups of the current arrangement of `Φ`,
every group in label order (`blowup_arr`): a factor acts on the window of its groups, swaps every pair of wires of
two different ones of them once (for `κ` by (K1), (K2), see `kappa_K1K2`), and keeps their internal orders.
So `Φ̂` swaps every pair of wires from different groups exactly once and no pair inside a block, and the beads at
the end swap the pairs inside the blocks: `W^v_G` is reduced (`Wv_reduced`).
-/

namespace BraidDistance

/-- A word on the window `M` of `P ++ M ++ S` acts on `M` as the unshifted word acts on `[0, …, r-1]`. -/
private theorem blowup_window (P M S L : List Nat) (r : Nat) (hL : ValidWord r L) (hM : M.length = r) :
    (∀ i ∈ shiftW P.length L, i + 1 < (P ++ M ++ S).length) ∧
    arrFrom (P ++ M ++ S) (shiftW P.length L) = P ++ (arrAfter r L).map (fun i => M.getD i 0) ++ S := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [shiftW, List.mem_map] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    have := hL l hl
    simp; omega
  · rw [arrFrom_shift (P ++ M ++ S) L P.length r hL (by simp only [List.length_append]; omega)]
    have h1 : (P ++ M ++ S).take P.length = P := by simp
    have h2 : (P ++ M ++ S).drop (P.length + r) = S := by
      subst hM; simp [List.drop_append]
    rw [h1, h2]
    congr 2
    apply List.map_congr_left
    intro i hi
    have hi' : i < r := by
      have := (arrFrom_perm (List.range r) L).mem_iff.1 hi
      simpa using this
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]

private theorem blowArr_split (G : Graph) (A B : List Grp) (gs : List Grp) :
    blowArr G (A ++ gs ++ B) = blowArr G A ++ gs.flatMap (wiresOf G) ++ blowArr G B := by
  simp [blowArr, List.flatMap_append]

private theorem blowArr_length (G : Graph) (A : List Grp) :
    (blowArr G A).length = (A.map Grp.size).sum := by
  induction A with
  | nil => rfl
  | cons g A ih => simp [blowArr, wiresOf] at ih ⊢ <;> omega

private theorem wirePos_split (A B : List Grp) (g : Grp) (hg : g ∉ A) :
    wirePos (A ++ g :: B) g = (A.map Grp.size).sum := by
  simp [wirePos, List.idxOf_append, hg]

private theorem moveWord_valid (g h : Grp) : ValidWord (g.size + h.size) (moveWord g.size h.size) := by
  cases g <;> cases h <;> (simp only [Grp.size]; decide)

private theorem moveWord_arr (G : Graph) (g h : Grp) :
    (arrAfter (g.size + h.size) (moveWord g.size h.size)).map
      (fun i => (wiresOf G g ++ wiresOf G h).getD i 0) = wiresOf G h ++ wiresOf G g := by
  cases g <;> cases h <;>
  · simp only [Grp.size]
    first
    | rw [show arrAfter (3 + 3) (moveWord 3 3) = [3, 4, 5, 0, 1, 2] by decide]
    | rw [show arrAfter (3 + 1) (moveWord 3 1) = [3, 0, 1, 2] by decide]
    | rw [show arrAfter (1 + 3) (moveWord 1 3) = [1, 2, 3, 0] by decide]
    | rw [show arrAfter (1 + 1) (moveWord 1 1) = [1, 0] by decide]
    simp [wiresOf, Grp.size, List.range']

private theorem kappa_arr (x y z : List Nat) (hx : x.length = 3) (hy : y.length = 1) (hz : z.length = 3) :
    (arrAfter 7 kappa).map (fun i => (x ++ y ++ z).getD i 0) = z ++ y ++ x := by
  rw [kappa_K1K2.2]
  match x, y, z, hx, hy, hz with
  | [a, b, c], [d], [e, f, g], _, _, _ => rfl

/-- One event: the factor acts on the window of its groups and exchanges them in the blown-up arrangement. -/
private theorem ev_step (G : Graph) (arr : List Grp) (ev : Ev) (hnd : arr.Nodup) (hok : EvOK arr ev) :
    (∀ i ∈ shiftW (wirePos arr (evTop ev)) (evLocal ev), i + 1 < (blowArr G arr).length) ∧
    arrFrom (blowArr G arr) (shiftW (wirePos arr (evTop ev)) (evLocal ev)) =
      blowArr G (applyEv arr ev) := by
  cases ev with
  | mv g h =>
    obtain ⟨A, B, rfl⟩ := hok
    obtain ⟨_, hr, hA⟩ := List.nodup_append.1 hnd
    obtain ⟨hg1, hr⟩ := List.nodup_cons.1 hr
    obtain ⟨hhB, _⟩ := List.nodup_cons.1 hr
    have hgA : g ∉ A := fun hm => hA g hm g (List.mem_cons_self ..) rfl
    have hhA : h ∉ A := fun hm => hA h hm h (by simp) rfl
    have hgh' : g ≠ h := fun e => hg1 (by simp [e])
    have hgB' : g ∉ B := fun hm => hg1 (by simp [hm])
    have happ : applyEv (A ++ g :: h :: B) (Ev.mv g h) = A ++ [h, g] ++ B := by
      simp only [applyEv, List.map_append, List.map_cons]
      have eA : A.map (swapNames g h) = A := by
        conv => rhs; rw [← List.map_id A]
        apply List.map_congr_left
        intro x hx
        have : x ≠ g := fun e => hgA (e ▸ hx)
        have : x ≠ h := fun e => hhA (e ▸ hx)
        simp [swapNames, *]
      have eB : B.map (swapNames g h) = B := by
        conv => rhs; rw [← List.map_id B]
        apply List.map_congr_left
        intro x hx
        have : x ≠ g := fun e => hgB' (e ▸ hx)
        have : x ≠ h := fun e => hhB (e ▸ hx)
        simp [swapNames, *]
      rw [eA, eB]
      simp [swapNames]
    have harr : A ++ g :: h :: B = A ++ [g, h] ++ B := by simp
    rw [happ, show evTop (Ev.mv g h) = g from rfl, wirePos_split A (h :: B) g hgA,
      show evLocal (Ev.mv g h) = moveWord g.size h.size from rfl, harr, blowArr_split, blowArr_split,
      ← blowArr_length]
    have hw := blowup_window (blowArr G A) ([g, h].flatMap (wiresOf G)) (blowArr G B)
      (moveWord g.size h.size) (g.size + h.size) (moveWord_valid g h) (by simp [wiresOf])
    refine ⟨hw.1, ?_⟩
    rw [hw.2]
    have := moveWord_arr G g h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this ⊢
    rw [this]
  | cell u w =>
    obtain ⟨A, B, rfl⟩ := hok
    obtain ⟨_, hr, hA⟩ := List.nodup_append.1 hnd
    obtain ⟨hu, hr⟩ := List.nodup_cons.1 hr
    obtain ⟨_, hr⟩ := List.nodup_cons.1 hr
    obtain ⟨hwB, _⟩ := List.nodup_cons.1 hr
    have huA : Grp.X u ∉ A := fun hm => hA _ hm _ (List.mem_cons_self ..) rfl
    have hwA : Grp.X w ∉ A := fun hm => hA _ hm (Grp.X w) (by simp) rfl
    have huw : Grp.X u ≠ Grp.X w := fun e => hu (by simp [e])
    have huB : Grp.X u ∉ B := fun hm => hu (by simp [hm])
    have happ : applyEv (A ++ Grp.X u :: Grp.p u w :: Grp.X w :: B) (Ev.cell u w) =
        A ++ [Grp.X w, Grp.p u w, Grp.X u] ++ B := by
      simp only [applyEv, List.map_append, List.map_cons]
      have eA : A.map (swapNames (Grp.X u) (Grp.X w)) = A := by
        conv => rhs; rw [← List.map_id A]
        apply List.map_congr_left
        intro x hx
        have : x ≠ Grp.X u := fun e => huA (e ▸ hx)
        have : x ≠ Grp.X w := fun e => hwA (e ▸ hx)
        simp [swapNames, *]
      have eB : B.map (swapNames (Grp.X u) (Grp.X w)) = B := by
        conv => rhs; rw [← List.map_id B]
        apply List.map_congr_left
        intro x hx
        have : x ≠ Grp.X u := fun e => huB (e ▸ hx)
        have : x ≠ Grp.X w := fun e => hwB (e ▸ hx)
        simp [swapNames, *]
      rw [eA, eB]
      simp [swapNames]
    have harr : A ++ Grp.X u :: Grp.p u w :: Grp.X w :: B = A ++ [Grp.X u, Grp.p u w, Grp.X w] ++ B := by
      simp
    rw [happ, show evTop (Ev.cell u w) = Grp.X u from rfl, wirePos_split A _ _ huA,
      show evLocal (Ev.cell u w) = kappa from rfl, harr, blowArr_split, blowArr_split,
      ← blowArr_length]
    have hw := blowup_window (blowArr G A) ([Grp.X u, Grp.p u w, Grp.X w].flatMap (wiresOf G))
      (blowArr G B) kappa 7 (by decide) (by simp [wiresOf, Grp.size])
    refine ⟨hw.1, ?_⟩
    rw [hw.2]
    have := kappa_arr (wiresOf G (.X u)) (wiresOf G (.p u w)) (wiresOf G (.X w))
      (by simp [wiresOf, Grp.size]) (by simp [wiresOf, Grp.size]) (by simp [wiresOf, Grp.size])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] at this ⊢
    rw [this]; simp


/-! ### The arrangement after the factors -/

/-- Lemma 4.4: after the first `k` factors the wires are arranged as the blow-up of `arrAt G k`. -/
theorem blowup_arr (G : Graph) (hG : G.Valid) {k : Nat} (hk : k ≤ numFactors G) :
    arrAfter G.m ((factors G).take k).flatten = blowArr G (arrAt G k) := by
  induction k with
  | zero =>
    rw [arrAt_zero, blowArr_labelOrder G hG]; rfl
  | succ k ih =>
    have hk' : k < numFactors G := by omega
    rw [factors_take_succ G hk', arrAfter, arrFrom_append, ← arrAfter, ih (by omega),
      arrAt_succ G hk']
    have hnd : (arrAt G k).Nodup := (arrAt_perm G hG (by omega)).nodup_iff.2 (labelOrder_nodup G)
    exact (ev_step G _ _ hnd (sweep_ok G hG hk')).2

private theorem blowArr_arrAt_length (G : Graph) (hG : G.Valid) {k : Nat} (hk : k ≤ numFactors G) :
    (blowArr G (arrAt G k)).length = G.m := by
  rw [← blowup_arr G hG hk, arrAfter_length]

private theorem phi_valid (G : Graph) (hG : G.Valid) {k : Nat} (hk : k ≤ numFactors G) :
    ∀ i ∈ ((factors G).take k).flatten, i + 1 < G.m := by
  induction k with
  | zero => intro i hi; simp at hi
  | succ k ih =>
    have hk' : k < numFactors G := by omega
    rw [factors_take_succ G hk']
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact ih (by omega) i hi
    · have hnd : (arrAt G k).Nodup :=
        (arrAt_perm G hG (by omega)).nodup_iff.2 (labelOrder_nodup G)
      have := (ev_step G _ _ hnd (sweep_ok G hG hk')).1 i hi
      rwa [blowArr_arrAt_length G hG (by omega)] at this

/-! ### The beads at the end -/

private theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem flatMap_length_sizes (A : List Grp) (F : Grp → List Nat) (hF : ∀ g, (F g).length = g.size) :
    (A.flatMap F).length = (A.map Grp.size).sum := by
  induction A with
  | nil => rfl
  | cons g A ih => simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih, hF]

private theorem bead_shift (q : Nat) : bead false q = shiftW q [0, 1, 0] := by
  simp [bead, shiftW, Nat.add_comm]

private theorem bead_step (arr : List Grp) (hnd : arr.Nodup) (F : Grp → List Nat)
    (hF : ∀ g, (F g).length = g.size) (u : Nat) (hu : Grp.X u ∈ arr) :
    (∀ i ∈ bead false (wirePos arr (.X u)), i + 1 < (arr.flatMap F).length) ∧
    arrFrom (arr.flatMap F) (bead false (wirePos arr (.X u))) =
      arr.flatMap (fun g => if g = .X u then (F g).reverse else F g) := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hu
  obtain ⟨_, hr, hA⟩ := List.nodup_append.1 hnd
  have huB := (List.nodup_cons.1 hr).1
  have huA : Grp.X u ∉ A := fun hm => hA _ hm _ (List.mem_cons_self ..) rfl
  rw [wirePos_split A B _ huA, ← flatMap_length_sizes A F hF, bead_shift]
  have hsplit : (A ++ Grp.X u :: B).flatMap F = A.flatMap F ++ F (.X u) ++ B.flatMap F := by
    simp [List.flatMap_append]
  rw [hsplit]
  have hw := blowup_window (A.flatMap F) (F (.X u)) (B.flatMap F) [0, 1, 0] 3 (by decide)
    (by rw [hF]; rfl)
  refine ⟨hw.1, ?_⟩
  rw [hw.2, show arrAfter 3 [0, 1, 0] = [2, 1, 0] by decide]
  have e3 : (List.map (fun i => (F (Grp.X u)).getD i 0) [2, 1, 0]) = (F (.X u)).reverse := by
    have h3 : (F (Grp.X u)).length = 3 := by rw [hF]; rfl
    match F (Grp.X u), h3 with
    | [a, b, c], _ => rfl
  rw [e3]
  have eA : A.flatMap (fun g => if g = .X u then (F g).reverse else F g) = A.flatMap F :=
    flatMap_congr' (fun x hx => by
      have : x ≠ Grp.X u := fun e => huA (e ▸ hx)
      simp [this])
  have eB : B.flatMap (fun g => if g = .X u then (F g).reverse else F g) = B.flatMap F :=
    flatMap_congr' (fun x hx => by
      have : x ≠ Grp.X u := fun e => huB (e ▸ hx)
      simp [this])
  simp [List.flatMap_append, eA, eB]

/-- The wires of the groups after the beads of the vertices `< u`: those blocks are reversed. -/
private def beadF (G : Graph) (u : Nat) : Grp → List Nat
  | .X v => if v < u then (wiresOf G (.X v)).reverse else wiresOf G (.X v)
  | .p a b => wiresOf G (.p a b)

private theorem beadF_length (G : Graph) (u : Nat) (g : Grp) : (beadF G u g).length = g.size := by
  cases g with
  | X v => simp only [beadF]; split <;> simp [wiresOf, Grp.size]
  | p a b => simp [beadF, wiresOf]

private theorem X_mem_labelOrder (G : Graph) {u : Nat} (hu : u < G.n) : Grp.X u ∈ labelOrder G :=
  List.mem_flatMap.2 ⟨u, List.mem_range.2 hu, List.mem_cons_self ..⟩

private theorem beads_iter (G : Graph) {u : Nat} (hu : u ≤ G.n) :
    (∀ i ∈ (List.range u).flatMap (fun v => bead false (wirePos (labelOrder G).reverse (.X v))),
      i + 1 < (blowArr G (labelOrder G).reverse).length) ∧
    arrFrom (blowArr G (labelOrder G).reverse)
        ((List.range u).flatMap (fun v => bead false (wirePos (labelOrder G).reverse (.X v)))) =
      (labelOrder G).reverse.flatMap (beadF G u) := by
  have hnd : (labelOrder G).reverse.Nodup := (List.reverse_perm _).nodup_iff.2 (labelOrder_nodup G)
  have hlen : ∀ v, ((labelOrder G).reverse.flatMap (beadF G v)).length =
      (blowArr G (labelOrder G).reverse).length := by
    intro v
    rw [flatMap_length_sizes _ _ (beadF_length G v), blowArr,
      flatMap_length_sizes _ _ (fun g => by simp [wiresOf])]
  induction u with
  | zero =>
    refine ⟨fun i hi => by simp at hi, ?_⟩
    simp only [List.range_zero, List.flatMap_nil]
    exact flatMap_congr' (fun g _ => by cases g <;> simp [beadF])
  | succ u ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hs := bead_step _ hnd (beadF G u) (beadF_length G u) u
      (List.mem_reverse.2 (X_mem_labelOrder G (by omega)))
    rw [List.range_succ, List.flatMap_append, arrFrom_append, ih2]
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases List.mem_append.1 hi with hi | hi
      · exact ih1 i hi
      · have := hs.1 i (by simpa using hi)
        rwa [hlen] at this
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [hs.2]
      congr 1
      funext g
      cases g with
      | X v =>
        by_cases hv : v = u
        · subst hv; simp [beadF]
        · have : Grp.X v ≠ Grp.X u := fun e => hv (by injection e)
          simp only [this, ite_false, beadF]
          by_cases h1 : v < u
          · simp [h1, show v < u + 1 by omega]
          · simp [h1, show ¬ v < u + 1 by omega]
      | p a b => simp [beadF]

private theorem beads_final (G : Graph) (hG : G.Valid) :
    (labelOrder G).reverse.flatMap (beadF G G.n) = (List.range G.m).reverse := by
  rw [List.flatMap_reverse, ← blowArr_labelOrder G hG, blowArr]
  congr 1
  apply flatMap_congr'
  intro g hg
  obtain ⟨v, hv, hgv⟩ := List.mem_flatMap.1 hg
  have hv' := List.mem_range.1 hv
  simp only [bundle, List.mem_cons, List.mem_map] at hgv
  rcases hgv with rfl | ⟨w, _, rfl⟩
  · simp [beadF, hv']
  · simp [beadF, wiresOf, Grp.size]


/-! ### The length of `W^v_G` -/

private def pprod (x : Grp × Grp) : Nat := x.1.size * x.2.size

private theorem factorsFrom_length (arr : List Grp) (evs : List Ev) :
    (factorsFrom arr evs).map List.length = evs.map (fun e => (evLocal e).length) := by
  induction evs generalizing arr with
  | nil => rfl
  | cons e evs ih => simp [factorsFrom, shiftW, ih]

private theorem evLocal_length (e : Ev) : (evLocal e).length = ((evPairs e).map pprod).sum := by
  cases e with
  | mv g h => cases g <;> cases h <;> rfl
  | cell u w => rfl

private theorem sum_map_flatMap' {α β : Type} (l : List α) (f : α → List β) (h : β → Nat) :
    ((l.flatMap f).map h).sum = (l.map (fun x => ((f x).map h).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_pairs_cons (x : Grp) (xs : List Grp) :
    ((xs.map (fun y => (x, y))).map pprod).sum = x.size * (xs.map Grp.size).sum := by
  induction xs with
  | nil => simp
  | cons y xs ih => simp only [List.map_cons, List.sum_cons, ih, pprod, Nat.mul_add]

private theorem orderedPairs_sum (l : List Grp) :
    2 * ((orderedPairs l).map pprod).sum + (l.map (fun g => g.size * g.size)).sum =
      (l.map Grp.size).sum * (l.map Grp.size).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [orderedPairs, List.map_append, List.sum_append, sum_pairs_cons, List.map_cons,
      List.sum_cons]
    generalize (List.map Grp.size xs).sum = S at *
    generalize x.size = a
    have : (a + S) * (a + S) = a * a + 2 * (a * S) + S * S := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm S a]; omega
    rw [this]
    omega

private theorem sq_sum (G : Graph) (us : List Nat) :
    ((us.flatMap (bundle G)).map (fun g => g.size * g.size)).sum =
      ((us.flatMap (bundle G)).map Grp.size).sum + 6 * us.length := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, bundle, List.map_cons,
      List.sum_cons, List.map_map, List.length_cons]
    have : ((G.up u).map ((fun g => g.size * g.size) ∘ Grp.p u)).sum =
        ((G.up u).map (Grp.size ∘ Grp.p u)).sum := by
      congr 1
    rw [this]
    simp only [Grp.size]
    omega

private theorem sum_const3 (l : List Nat) : (l.map (fun _ => 3)).sum = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

/-- All pairs `(a, b)` with `a < b < m`. -/
private def allPairs : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => allPairs m ++ (List.range m).map (fun a => (a, m))

private theorem mem_allPairs (m : Nat) (p : Nat × Nat) : p ∈ allPairs m ↔ p.1 < p.2 ∧ p.2 < m := by
  induction m with
  | zero => simp [allPairs]
  | succ m ih =>
    simp only [allPairs, List.mem_append, ih, List.mem_map, List.mem_range]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · omega
      · simp; omega
    · intro h
      by_cases hm : p.2 < m
      · exact Or.inl ⟨h.1, hm⟩
      · refine Or.inr ⟨p.1, by omega, ?_⟩
        obtain ⟨p1, p2⟩ := p
        simp only at h hm ⊢
        rw [show p2 = m by omega]

private theorem allPairs_nodup (m : Nat) : (allPairs m).Nodup := by
  induction m with
  | zero => exact List.nodup_nil
  | succ m ih =>
    simp only [allPairs]
    refine List.nodup_append.2 ⟨ih, ?_, ?_⟩
    · exact List.Pairwise.map _ (fun a b h e => h (by injection e)) List.nodup_range
    · intro a ha b hb e
      subst e
      have := ((mem_allPairs m a).1 ha).2
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hb
      simp at this

private theorem allPairs_length (m : Nat) : 2 * (allPairs m).length + m = m * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [allPairs, List.length_append, List.length_map, List.length_range]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_succ]
    omega

/-! ### Reducedness from the final arrangement and the length -/

private theorem perm_of_subset {P l : List (Nat × Nat)} (hP : P.Nodup) (hsub : ∀ p ∈ P, p ∈ l)
    (hlen : l.length ≤ P.length) : l.Perm P := by
  induction P generalizing l with
  | nil =>
    cases l with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp at hlen
  | cons x P ih =>
    have hx : x ∈ l := hsub x (List.mem_cons_self ..)
    obtain ⟨hxP, hP'⟩ := List.nodup_cons.1 hP
    have h1 := List.perm_cons_erase hx
    have h2 : (l.erase x).Perm P := by
      apply ih hP'
      · intro p hp
        have hne : p ≠ x := fun e => hxP (e ▸ hp)
        exact (List.mem_erase_of_ne hne).2 (hsub p (List.mem_cons_of_mem _ hp))
      · rw [List.length_erase_of_mem hx]; simp at hlen; omega
    exact h1.trans (h2.cons x)

private theorem idxOf_rev {m a b : Nat} (hab : a < b) (hb : b < m) :
    (List.range m).reverse.idxOf b < (List.range m).reverse.idxOf a := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.idxOf_cons]
    by_cases hbm : b = m
    · subst hbm
      have : (b == a) = false := by simp; omega
      simp [this]
    · have h1 : (m == a) = false := by simp; omega
      have h2 : (m == b) = false := by simp; omega
      simp only [h1, h2]
      have := ih (by omega)
      simp only [Bool.false_eq_true, ite_false]
      omega

private theorem reduced_of (m : Nat) (w : List Nat) (hv : ValidWord m w)
    (hrev : arrAfter m w = (List.range m).reverse) (hlen : w.length ≤ (allPairs m).length) :
    Reduced m w := by
  have hperm : (swaps m w).Perm (allPairs m) := by
    apply perm_of_subset (allPairs_nodup m)
    · intro p hp
      obtain ⟨hab, hb⟩ := (mem_allPairs m p).1 hp
      have ho := arrAfter_order hv hab hb
      rw [hrev] at ho
      have hlt := idxOf_rev hab hb
      have hc : (swaps m w).count (p.1, p.2) % 2 ≠ 0 := fun h => by
        have := ho.2 h; omega
      have hpos : 0 < (swaps m w).count (p.1, p.2) := by omega
      exact List.count_pos_iff.1 hpos
    · rw [swaps, swapsFrom_length]; exact hlen
  refine ⟨hv, fun b hb a hab => ?_⟩
  rw [hperm.count_eq, List.Nodup.count (allPairs_nodup m)]
  simp [mem_allPairs, hab, hb]

/-- Lemma 4.4: `W^v_G` is a reduced word. -/
theorem Wv_reduced (G : Graph) (hG : G.Valid) : Reduced G.m (Wv G) := by
  have hJ := factors_length G
  have hbeads : beadsAt G (numFactors G) zeroEps =
      (List.range G.n).flatMap (fun v => bead false (wirePos (labelOrder G).reverse (.X v))) := by
    rw [beadsAt, sweep_final G hG]; rfl
  have hWv : Wv G = (factors G).flatten ++ beadsAt G (numFactors G) zeroEps := by
    simp [Wv, W, List.take_of_length_le, List.drop_of_length_le, hJ]
  have hphi : arrAfter G.m (factors G).flatten = blowArr G (labelOrder G).reverse := by
    have := blowup_arr G hG (Nat.le_refl (numFactors G))
    rwa [List.take_of_length_le (by omega), sweep_final G hG] at this
  have hvphi : ∀ i ∈ (factors G).flatten, i + 1 < G.m := by
    have := phi_valid G hG (Nat.le_refl (numFactors G))
    rwa [List.take_of_length_le (by omega)] at this
  have hbl : (blowArr G (labelOrder G).reverse).length = G.m := by
    rw [← hphi, arrAfter_length]
  have hit := beads_iter G (Nat.le_refl G.n)
  rw [hbl] at hit
  rw [hWv, hbeads]
  apply reduced_of
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact hvphi i hi
    · exact hit.1 i hi
  · rw [arrAfter, arrFrom_append, ← arrAfter, hphi, hit.2, beads_final G hG]
  · have hlphi : (factors G).flatten.length = ((orderedPairs (labelOrder G)).map pprod).sum := by
      rw [List.length_flatten, factors, factorsFrom_length]
      rw [List.map_congr_left (fun e _ => evLocal_length e), ← sum_map_flatMap']
      exact List.Perm.sum_nat ((sweep_pairs G hG).map pprod)
    have hlb : ((List.range G.n).flatMap
        (fun v => bead false (wirePos (labelOrder G).reverse (.X v)))).length = 3 * G.n := by
      rw [List.length_flatMap]
      have : (List.range G.n).map
          (fun v => (bead false (wirePos (labelOrder G).reverse (.X v))).length) =
          (List.range G.n).map (fun _ => 3) := by
        apply List.map_congr_left; intro v _; simp [bead]
      rw [this, sum_const3, List.length_range]
    have h1 := orderedPairs_sum (labelOrder G)
    have h2 := sq_sum G (List.range G.n)
    have h3 := sum_sizes G hG
    have h4 := allPairs_length G.m
    simp only [labelOrder, List.length_range] at h1 h2 h3
    simp only [labelOrder] at hlphi
    rw [List.length_append, hlphi, hlb]
    rw [h3] at h1 h2
    omega

end BraidDistance
