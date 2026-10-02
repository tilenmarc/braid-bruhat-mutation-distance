import BraidDistance.Construction
import BraidDistance.Restrict

/-!
# Wire labels of groups, blocks and gadgets (Section 4.1)

The groups occupy consecutive ranges of labels in label order: `X u` the three labels
`firstWire G (X u), +1, +2`, a private wire one label.  Different groups have disjoint label ranges, and a group
earlier in label order has smaller labels.  For an edge `e = uw` the seven wires
`A_e = edgeWires G u w` are increasing, and two different gadgets share at most one block, so a triple inside
two of them is the bead triple of a common endpoint ("Overlaps" in the proof of Proposition 5.1).
-/

namespace BraidDistance

/-! ### Prefix sums over a list of groups -/

private theorem Wi.wirePos_cons_self {a : Grp} {L : List Grp} : wirePos (a :: L) a = 0 := by
  simp [wirePos]

private theorem Wi.wirePos_cons_ne {a g : Grp} {L : List Grp} (h : a ≠ g) :
    wirePos (a :: L) g = a.size + wirePos L g := by
  unfold wirePos
  rw [List.idxOf_cons]
  have hb : (a == g) = false := by simp [h]
  simp [hb]

private theorem Wi.idxOf_cons_ne {a g : Grp} {L : List Grp} (h : a ≠ g) :
    (a :: L).idxOf g = L.idxOf g + 1 := by
  rw [List.idxOf_cons]
  have hb : (a == g) = false := by simp [h]
  simp [hb]

private theorem Wi.wirePos_add_size_le {L : List Grp} {g : Grp} (hg : g ∈ L) :
    wirePos L g + g.size ≤ (L.map Grp.size).sum := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    by_cases hag : a = g
    · subst hag
      simp [Wi.wirePos_cons_self]
    · have hgL : g ∈ L := by
        rcases List.mem_cons.mp hg with h | h
        · exact absurd h.symm hag
        · exact h
      rw [Wi.wirePos_cons_ne hag]
      have := ih hgL
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem Wi.wirePos_before {L : List Grp} {g h : Grp} (hg : g ∈ L) (hh : h ∈ L)
    (hgh : L.idxOf g < L.idxOf h) : wirePos L g + g.size ≤ wirePos L h := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    by_cases hag : a = g
    · subst hag
      have hah : a ≠ h := by
        intro e; subst e; simp at hgh
      rw [Wi.wirePos_cons_self, Wi.wirePos_cons_ne hah]
      omega
    · have hah : a ≠ h := by
        intro e; subst e; simp at hgh
      have hgL : g ∈ L := by
        rcases List.mem_cons.mp hg with e | e
        · exact absurd e.symm hag
        · exact e
      have hhL : h ∈ L := by
        rcases List.mem_cons.mp hh with e | e
        · exact absurd e.symm hah
        · exact e
      rw [Wi.idxOf_cons_ne hag, Wi.idxOf_cons_ne hah] at hgh
      rw [Wi.wirePos_cons_ne hag, Wi.wirePos_cons_ne hah]
      have := ih hgL hhL (by omega)
      omega

private theorem Wi.flatMap_range' {L : List Grp} (hL : L.Nodup) :
    ∀ (s : Nat) (f : Grp → Nat), (∀ g ∈ L, f g = s + wirePos L g) →
      L.flatMap (fun g => List.range' (f g) g.size) = List.range' s (L.map Grp.size).sum := by
  induction L with
  | nil => intro s f _; simp
  | cons a L ih =>
    intro s f hf
    have ha : a ∉ L := (List.nodup_cons.mp hL).1
    have hL' : L.Nodup := (List.nodup_cons.mp hL).2
    have hfa : f a = s := by
      have := hf a (List.mem_cons_self ..)
      rw [Wi.wirePos_cons_self] at this
      omega
    have hrest : ∀ g ∈ L, f g = (s + a.size) + wirePos L g := by
      intro g hg
      have hag : a ≠ g := by intro e; subst e; exact ha hg
      have := hf g (List.mem_cons_of_mem _ hg)
      rw [Wi.wirePos_cons_ne hag] at this
      omega
    rw [List.flatMap_cons, ih hL' (s + a.size) f hrest, hfa]
    simp only [List.map_cons, List.sum_cons]
    rw [List.range'_append_1]

/-! ### The label order is sorted by a lexicographic key -/

private def Wi.key : Grp → Nat × Nat
  | .X u => (u, 0)
  | .p u w => (u, w + 1)

private def Wi.lt (g h : Grp) : Prop :=
  (Wi.key g).1 < (Wi.key h).1 ∨ ((Wi.key g).1 = (Wi.key h).1 ∧ (Wi.key g).2 < (Wi.key h).2)

private theorem Wi.lt_irrefl (g : Grp) : ¬ Wi.lt g g := by
  cases g <;> simp [Wi.lt, Wi.key]

private theorem Wi.lt_asymm {g h : Grp} (h1 : Wi.lt g h) (h2 : Wi.lt h g) : False := by
  cases g <;> cases h <;> simp [Wi.lt, Wi.key] at h1 h2 <;> omega

private theorem Wi.mem_up {G : Graph} {u w : Nat} :
    w ∈ G.up u ↔ w < G.n ∧ u < w ∧ (u, w) ∈ G.edges := by
  simp [Graph.up, Graph.isEdge]

private theorem Wi.key_of_mem_bundle {G : Graph} {u : Nat} {x : Grp} (hx : x ∈ bundle G u) :
    (Wi.key x).1 = u := by
  simp only [bundle, List.mem_cons, List.mem_map] at hx
  rcases hx with h | ⟨w, _, h⟩
  · subst h; rfl
  · subst h; rfl

private theorem Wi.pairwise_labelOrder (G : Graph) : (labelOrder G).Pairwise Wi.lt := by
  unfold labelOrder
  rw [List.pairwise_flatMap]
  constructor
  · intro u _
    simp only [bundle, List.pairwise_cons, List.mem_map]
    constructor
    · rintro _ ⟨w, _, rfl⟩
      simp [Wi.lt, Wi.key]
    · rw [List.pairwise_map]
      have hup : (G.up u).Pairwise (· < ·) := by
        unfold Graph.up
        exact List.pairwise_lt_range.filter _
      exact hup.imp (fun h => by simp [Wi.lt, Wi.key]; omega)
  · refine List.pairwise_lt_range.imp ?_
    intro a b hab x hx y hy
    left
    rw [Wi.key_of_mem_bundle hx, Wi.key_of_mem_bundle hy]
    exact hab

private theorem Wi.idxOf_lt_of_lt {L : List Grp} (hL : L.Pairwise Wi.lt) {g h : Grp} (hg : g ∈ L)
    (hh : h ∈ L) (hgh : Wi.lt g h) : L.idxOf g < L.idxOf h := by
  induction L with
  | nil => simp at hg
  | cons a L ih =>
    have hpa := (List.pairwise_cons.mp hL).1
    have hL' := (List.pairwise_cons.mp hL).2
    by_cases hag : a = g
    · subst hag
      have hah : a ≠ h := by intro e; subst e; exact Wi.lt_irrefl _ hgh
      rw [Wi.idxOf_cons_ne hah]
      simp
    · have hgL : g ∈ L := by
        rcases List.mem_cons.mp hg with e | e
        · exact absurd e.symm hag
        · exact e
      have hah : a ≠ h := by
        intro e; subst e; exact Wi.lt_asymm hgh (hpa g hgL)
      have hhL : h ∈ L := by
        rcases List.mem_cons.mp hh with e | e
        · exact absurd e.symm hah
        · exact e
      rw [Wi.idxOf_cons_ne hag, Wi.idxOf_cons_ne hah]
      have := ih hL' hgL hhL
      omega

/-! ### Basic facts on wires -/

private theorem Wi.X_mem (G : Graph) {u : Nat} (hu : u < G.n) : Grp.X u ∈ labelOrder G := by
  unfold labelOrder
  simp only [List.mem_flatMap, List.mem_range]
  exact ⟨u, hu, by simp [bundle]⟩

private theorem Wi.p_mem (G : Graph) (hG : G.Valid) {u w : Nat} (he : (u, w) ∈ G.edges) :
    Grp.p u w ∈ labelOrder G := by
  have hv := hG.2 _ he
  simp only at hv
  unfold labelOrder
  simp only [List.mem_flatMap, List.mem_range]
  refine ⟨u, by omega, ?_⟩
  simp only [bundle, List.mem_cons, List.mem_map]
  right
  exact ⟨w, Wi.mem_up.mpr ⟨hv.2, hv.1, he⟩, rfl⟩

private theorem Wi.fw_before (G : Graph) {g h : Grp} (hg : g ∈ labelOrder G) (hh : h ∈ labelOrder G)
    (hgh : Wi.lt g h) : firstWire G g + g.size ≤ firstWire G h :=
  Wi.wirePos_before hg hh (Wi.idxOf_lt_of_lt (Wi.pairwise_labelOrder G) hg hh hgh)

private theorem Wi.wiresOf_X (G : Graph) (u : Nat) :
    wiresOf G (.X u) = [firstWire G (.X u), firstWire G (.X u) + 1, firstWire G (.X u) + 2] := rfl

private theorem Wi.wiresOf_p (G : Graph) (u w : Nat) :
    wiresOf G (.p u w) = [firstWire G (.p u w)] := rfl

private theorem Wi.edge_mem (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    Grp.X e.1 ∈ labelOrder G ∧ Grp.p e.1 e.2 ∈ labelOrder G ∧ Grp.X e.2 ∈ labelOrder G := by
  have hv := hG.2 _ he
  exact ⟨Wi.X_mem G (by omega), Wi.p_mem G hG he, Wi.X_mem G hv.2⟩

theorem labelOrder_nodup (G : Graph) : (labelOrder G).Nodup := by
  exact (Wi.pairwise_labelOrder G).imp (fun h e => by subst e; exact Wi.lt_irrefl _ h)

theorem mem_labelOrder (G : Graph) (hG : G.Valid) (g : Grp) :
    g ∈ labelOrder G ↔ (∃ u, u < G.n ∧ g = .X u) ∨ (∃ u w, (u, w) ∈ G.edges ∧ g = .p u w) := by
  constructor
  · intro hg
    unfold labelOrder at hg
    simp only [List.mem_flatMap, List.mem_range, bundle, List.mem_cons, List.mem_map] at hg
    obtain ⟨u, hu, h | ⟨w, hw, h⟩⟩ := hg
    · exact Or.inl ⟨u, hu, h⟩
    · exact Or.inr ⟨u, w, (Wi.mem_up.mp hw).2.2, h.symm⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, w, he, rfl⟩)
    · exact Wi.X_mem G hu
    · exact Wi.p_mem G hG he

/-- The total number of wires is `m = 3n + |E|`. -/
theorem sum_sizes (G : Graph) (hG : G.Valid) : ((labelOrder G).map Grp.size).sum = G.m := by
  have hsz : ∀ (l : List Nat), ((l.flatMap (bundle G)).map Grp.size).sum =
      3 * l.length + (l.map (fun u => (G.up u).length)).sum := by
    have hp : ∀ (u : Nat) (l : List Nat), ((l.map (Grp.p u)).map Grp.size).sum = l.length := by
      intro u l
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Grp.size]; omega
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append_nat, ih, bundle, List.map_cons,
        List.sum_cons, hp, Grp.size, List.length_cons]
      omega
  unfold labelOrder
  rw [hsz]
  let P : List (Nat × Nat) := (List.range G.n).flatMap (fun u => (G.up u).map (fun w => (u, w)))
  have hPlen : P.length = ((List.range G.n).map (fun u => (G.up u).length)).sum := by
    simp [P, List.length_flatMap]
  have hPnodup : P.Nodup := by
    have hpw : P.Pairwise (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := by
      simp only [P]
      rw [List.pairwise_flatMap]
      constructor
      · intro u _
        rw [List.pairwise_map]
        have hup : (G.up u).Pairwise (· < ·) := by
          unfold Graph.up
          exact List.pairwise_lt_range.filter _
        exact hup.imp (fun h => Or.inr ⟨rfl, h⟩)
      · refine List.pairwise_lt_range.imp ?_
        intro a b hab x hx y hy
        simp only [List.mem_map] at hx hy
        obtain ⟨_, _, rfl⟩ := hx
        obtain ⟨_, _, rfl⟩ := hy
        exact Or.inl hab
    exact hpw.imp (fun h e => by subst e; omega)
  have hmem : ∀ a, a ∈ P ↔ a ∈ G.edges := by
    intro ⟨u, w⟩
    simp only [P, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨u', _, w', hw', rfl, rfl⟩
      exact (Wi.mem_up.mp hw').2.2
    · intro he
      have hv := hG.2 _ he
      simp only at hv
      exact ⟨u, by omega, w, Wi.mem_up.mpr ⟨hv.2, hv.1, he⟩, rfl, rfl⟩
  have hperm := (List.perm_ext_iff_of_nodup hPnodup hG.1).mpr hmem
  rw [← hPlen, hperm.length_eq, List.length_range]
  rfl

/-- Blowing up the label order gives the initial arrangement of wires. -/
theorem blowArr_labelOrder (G : Graph) (hG : G.Valid) : blowArr G (labelOrder G) = List.range G.m := by
  unfold blowArr
  have := Wi.flatMap_range' (labelOrder_nodup G) 0 (firstWire G) (fun g _ => by simp [firstWire])
  rw [sum_sizes G hG] at this
  rw [List.range_eq_range']
  exact this

theorem wiresOf_lt (G : Graph) (hG : G.Valid) {g : Grp} (hg : g ∈ labelOrder G) :
    ∀ x ∈ wiresOf G g, x < G.m := by
  intro x hx
  have h1 := Wi.wirePos_add_size_le hg
  rw [sum_sizes G hG] at h1
  simp only [wiresOf, List.mem_range'_1, firstWire] at hx
  omega

/-- Groups earlier in label order have smaller wires. -/
theorem wiresOf_lt_of_before (G : Graph) {g h : Grp} (hg : g ∈ labelOrder G) (hh : h ∈ labelOrder G)
    (hgh : (labelOrder G).idxOf g < (labelOrder G).idxOf h) :
    ∀ x ∈ wiresOf G g, ∀ y ∈ wiresOf G h, x < y := by
  intro x hx y hy
  have h1 := Wi.wirePos_before hg hh hgh
  simp only [wiresOf, List.mem_range'_1, firstWire] at hx hy
  omega

theorem wiresOf_disjoint (G : Graph) {g h : Grp} (hg : g ∈ labelOrder G) (hh : h ∈ labelOrder G)
    (hgh : g ≠ h) : ∀ x ∈ wiresOf G g, x ∉ wiresOf G h := by
  intro x hx hxh
  have hne : (labelOrder G).idxOf g ≠ (labelOrder G).idxOf h := by
    intro e
    apply hgh
    have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hg)
    have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hh)
    rw [← h1, ← h2]
    simp only [e]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := wiresOf_lt_of_before G hg hh hlt x hx x hxh
    omega
  · have := wiresOf_lt_of_before G hh hg hlt x hxh x hx
    omega

private theorem Wi.fw_bound (G : Graph) (hG : G.Valid) {g : Grp} (hg : g ∈ labelOrder G) :
    firstWire G g + g.size ≤ G.m := by
  have h1 := Wi.wirePos_add_size_le hg
  rw [sum_sizes G hG] at h1
  exact h1

/-- A wire lies in the wires of at most one group. -/
private theorem Wi.owner (G : Graph) {g h : Grp} (hg : g ∈ labelOrder G) (hh : h ∈ labelOrder G) {x : Nat}
    (hxg : x ∈ wiresOf G g) (hxh : x ∈ wiresOf G h) : g = h := by
  by_cases e : g = h
  · exact e
  · exact absurd hxh (wiresOf_disjoint G hg hh e x hxg)

/-- The explicit form of `A_e` with the order of its three groups. -/
private theorem Wi.edge_explicit (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    edgeWires G e.1 e.2 = [firstWire G (.X e.1), firstWire G (.X e.1) + 1, firstWire G (.X e.1) + 2,
      firstWire G (.p e.1 e.2), firstWire G (.X e.2), firstWire G (.X e.2) + 1, firstWire G (.X e.2) + 2] ∧
    firstWire G (.X e.1) + 3 ≤ firstWire G (.p e.1 e.2) ∧
    firstWire G (.p e.1 e.2) + 1 ≤ firstWire G (.X e.2) ∧ firstWire G (.X e.2) + 3 ≤ G.m := by
  have hv := hG.2 _ he
  obtain ⟨h1, h2, h3⟩ := Wi.edge_mem G hG he
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Wi.fw_before G h1 h2 (by simp [Wi.lt, Wi.key])
  · exact Wi.fw_before G h2 h3 (by simp [Wi.lt, Wi.key]; omega)
  · exact Wi.fw_bound G hG h3

theorem edgeWires_spec (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    StrictIncr (edgeWires G e.1 e.2) ∧ (edgeWires G e.1 e.2).length = 7 ∧
      ∀ x ∈ edgeWires G e.1 e.2, x < G.m := by
  obtain ⟨hE, h1, h2, h3⟩ := Wi.edge_explicit G hG he
  rw [hE]
  refine ⟨?_, rfl, ?_⟩
  · simp only [StrictIncr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.Pairwise.nil, forall_eq_or_imp, forall_eq, and_true]
    and_intros <;> first | omega | (intro _ h; exact h.elim)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

theorem beadTriple_valid (G : Graph) (hG : G.Valid) {u : Nat} (hu : u < G.n) :
    ValidTriple G.m (beadTriple G u) := by
  have := Wi.fw_bound G hG (Wi.X_mem G hu)
  simp only [ValidTriple, beadTriple, Grp.size] at this ⊢
  omega

theorem beadTriple_inj (G : Graph) (_hG : G.Valid) {u v : Nat} (hu : u < G.n) (hv : v < G.n)
    (h : beadTriple G u = beadTriple G v) : u = v := by
  simp only [beadTriple, Prod.mk.injEq] at h
  have hu' := Wi.X_mem G hu
  have hv' := Wi.X_mem G hv
  by_cases e : u = v
  · exact e
  · rcases Nat.lt_or_gt_of_ne e with hlt | hlt
    · have := Wi.fw_before G hu' hv' (by simp [Wi.lt, Wi.key]; omega)
      simp only [Grp.size] at this
      omega
    · have := Wi.fw_before G hv' hu' (by simp [Wi.lt, Wi.key]; omega)
      simp only [Grp.size] at this
      omega

/-- The bead triples of a gadget are those of its two blocks, at the local positions `012` and `456`. -/
theorem edgeWires_beads (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    embT (edgeWires G e.1 e.2) (0, 1, 2) = beadTriple G e.1 ∧
      embT (edgeWires G e.1 e.2) (4, 5, 6) = beadTriple G e.2 := by
  rw [(Wi.edge_explicit G hG he).1]
  exact ⟨rfl, rfl⟩

/-- The bead triple of `u` lies inside `A_e` iff `u` is an endpoint of `e`. -/
theorem beadTriple_inside_edge (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) {u : Nat}
    (hu : u < G.n) : Inside (edgeWires G e.1 e.2) (beadTriple G u) ↔ (u = e.1 ∨ u = e.2) := by
  obtain ⟨m1, m2, m3⟩ := Wi.edge_mem G hG he
  have hxu := Wi.X_mem G hu
  constructor
  · intro hin
    have h0 : firstWire G (.X u) ∈ wiresOf G (.X u) := by simp [Wi.wiresOf_X]
    have ha := hin.1
    simp only [beadTriple, edgeWires, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · have := Wi.owner G hxu m1 h0 ha
      injection this with e
      exact Or.inl e
    · have := Wi.owner G hxu m2 h0 ha
      cases this
    · have := Wi.owner G hxu m3 h0 ha
      injection this with e
      exact Or.inr e
  · intro h
    rw [(Wi.edge_explicit G hG he).1]
    rcases h with rfl | rfl <;> simp [Inside, beadTriple]

/-- Overlaps: a triple inside two different gadgets is the bead triple of a common endpoint. -/
theorem edgeWires_overlap (G : Graph) (hG : G.Valid) {e f : Nat × Nat} (he : e ∈ G.edges)
    (hf : f ∈ G.edges) (hef : e ≠ f) {t : Triple} (ht : ValidTriple G.m t)
    (hte : Inside (edgeWires G e.1 e.2) t) (htf : Inside (edgeWires G f.1 f.2) t) :
    ∃ u, (u = e.1 ∨ u = e.2) ∧ (u = f.1 ∨ u = f.2) ∧ t = beadTriple G u := by
  have hve := hG.2 _ he
  have hvf := hG.2 _ hf
  obtain ⟨e1, e2, e3⟩ := Wi.edge_mem G hG he
  obtain ⟨f1, f2, f3⟩ := Wi.edge_mem G hG hf
  -- every wire common to `A_e` and `A_f` is a wire of the block of a common endpoint
  have common : ∀ x, x ∈ edgeWires G e.1 e.2 → x ∈ edgeWires G f.1 f.2 →
      ∃ c, (c = e.1 ∨ c = e.2) ∧ (c = f.1 ∨ c = f.2) ∧ x ∈ wiresOf G (.X c) := by
    intro x hxe hxf
    simp only [edgeWires, List.mem_append] at hxe hxf
    rcases hxe with (hxe | hxe) | hxe <;> rcases hxf with (hxf | hxf) | hxf
    · have := Wi.owner G e1 f1 hxe hxf; injection this with q
      exact ⟨e.1, Or.inl rfl, Or.inl q, hxe⟩
    · have := Wi.owner G e1 f2 hxe hxf; cases this
    · have := Wi.owner G e1 f3 hxe hxf; injection this with q
      exact ⟨e.1, Or.inl rfl, Or.inr q, hxe⟩
    · have := Wi.owner G e2 f1 hxe hxf; cases this
    · have := Wi.owner G e2 f2 hxe hxf
      injection this with q1 q2
      exact absurd (Prod.ext q1 q2) hef
    · have := Wi.owner G e2 f3 hxe hxf; cases this
    · have := Wi.owner G e3 f1 hxe hxf; injection this with q
      exact ⟨e.2, Or.inr rfl, Or.inl q, hxe⟩
    · have := Wi.owner G e3 f2 hxe hxf; cases this
    · have := Wi.owner G e3 f3 hxe hxf; injection this with q
      exact ⟨e.2, Or.inr rfl, Or.inr q, hxe⟩
  -- at most one common endpoint
  have uniq : ∀ c d, (c = e.1 ∨ c = e.2) → (c = f.1 ∨ c = f.2) → (d = e.1 ∨ d = e.2) →
      (d = f.1 ∨ d = f.2) → c = d := by
    intro c d hc1 hc2 hd1 hd2
    by_cases hcd : c = d
    · exact hcd
    · exfalso
      apply hef
      have q1 : e.1 = f.1 := by omega
      have q2 : e.2 = f.2 := by omega
      exact Prod.ext q1 q2
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ca, ha1, ha2, ha⟩ := common a hte.1 htf.1
  obtain ⟨cb, hb1, hb2, hb⟩ := common b hte.2.1 htf.2.1
  obtain ⟨cc, hc1, hc2, hc⟩ := common c hte.2.2 htf.2.2
  have qab := uniq ca cb ha1 ha2 hb1 hb2
  have qac := uniq ca cc ha1 ha2 hc1 hc2
  subst qab qac
  refine ⟨ca, ha1, ha2, ?_⟩
  simp only [Wi.wiresOf_X, List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
  simp only [ValidTriple] at ht
  simp only [beadTriple, Prod.mk.injEq]
  omega

end BraidDistance
