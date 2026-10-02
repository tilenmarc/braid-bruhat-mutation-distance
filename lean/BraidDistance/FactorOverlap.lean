import BraidDistance.SweepPairs

/-!
# The wires of a factor (Lemma 4.5, Corollary 4.6)

For the `k`-th factor, `stepZ G k` lists the wires of its groups in increasing order; it has `width` elements.
Two different factors share at most one group (a pair of groups is exchanged only once, `sweep_pairs`), so a
triple inside the wires of two different factors lies in one block: it is a bead triple.  A bead triple inside
the wires of a factor sits at a local bead position of its case.  The cell of each edge is one of the factors.
-/

namespace BraidDistance


private theorem FO.flatMap_nodup_idx {α β : Type} (f : α → List β) :
    ∀ (l : List α), (l.flatMap f).Nodup → ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i < j →
      ∀ q, q ∈ f l[i] → q ∈ f l[j] → False := by
  intro l
  induction l with
  | nil => intro _ i j hi; simp at hi
  | cons a as ih =>
    intro hnd i j hi hj hij q hqi hqj
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨_, hnd2, hdis⟩ := hnd
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hqi hqj
        have hj' : j < as.length := by simp at hj; omega
        exact hdis q hqi q (List.mem_flatMap.mpr ⟨as[j], List.getElem_mem hj', hqj⟩) rfl
      | succ i =>
        simp only [List.getElem_cons_succ] at hqi hqj
        exact ih hnd2 i j (by simp at hi; omega) (by simp at hj; omega) (by omega) q hqi hqj

private theorem FO.mem_orderedPairs {α : Type} [DecidableEq α] :
    ∀ (l : List α), l.Nodup → ∀ x y, (x, y) ∈ orderedPairs l → x ∈ l ∧ y ∈ l ∧ l.idxOf x < l.idxOf y := by
  intro l
  induction l with
  | nil => intro _ x y h; simp [orderedPairs] at h
  | cons a as ih =>
    intro hnd x y h
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    simp only [orderedPairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨z, hz, hzeq⟩ | h
    · cases hzeq
      have hya : y ≠ a := fun e => ha (e ▸ hz)
      refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ hz, ?_⟩
      rw [List.idxOf_cons_self, List.idxOf_cons]
      have : (a == y) = false := by simp; exact fun e => hya e.symm
      simp [this]
    · obtain ⟨hx, hy, hlt⟩ := ih hnd' x y h
      have hxa : (a == x) = false := by simp; exact fun e => ha (e ▸ hx)
      have hya : (a == y) = false := by simp; exact fun e => ha (e ▸ hy)
      refine ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy, ?_⟩
      rw [List.idxOf_cons, List.idxOf_cons]
      simp [hxa, hya]; omega

private theorem FO.orderedPairs_nodup {α : Type} [DecidableEq α] :
    ∀ (l : List α), l.Nodup → (orderedPairs l).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp [orderedPairs]
  | cons a as ih =>
    intro hnd
    have ha : a ∉ as := (List.nodup_cons.mp hnd).1
    have hnd' : as.Nodup := (List.nodup_cons.mp hnd).2
    simp only [orderedPairs]
    rw [List.nodup_append]
    refine ⟨?_, ih hnd', ?_⟩
    · exact List.Pairwise.map _ (fun y y' h e => h (by cases e; rfl)) hnd'
    · intro p hp q hq hpq
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
      subst hpq
      exact ha (FO.mem_orderedPairs as hnd' a z hq).1

/-- The groups of an event, top to bottom. -/
private def FO.evGrps : Ev → List Grp
  | .mv g h => [g, h]
  | .cell u w => [.X u, .p u w, .X w]

private theorem FO.wiresOf_X (G : Graph) (u : Nat) :
    wiresOf G (.X u) = [firstWire G (.X u), firstWire G (.X u) + 1, firstWire G (.X u) + 2] := rfl

private theorem FO.wiresOf_p (G : Graph) (u w : Nat) :
    wiresOf G (.p u w) = [firstWire G (.p u w)] := rfl

private theorem FO.mem_evZ (G : Graph) (ev : Ev) (x : Nat) :
    x ∈ evZ G ev ↔ ∃ g ∈ FO.evGrps ev, x ∈ wiresOf G g := by
  cases ev with
  | mv g h => simp [evZ, FO.evGrps]
  | cell u w =>
    simp only [evZ, edgeWires, FO.evGrps, List.mem_append, List.mem_cons, List.not_mem_nil]
    constructor
    · rintro ((h | h) | h)
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr (Or.inl rfl), h⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · rintro ⟨g, hg, hx⟩
      rcases hg with rfl | rfl | rfl | hf
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
      · exact hf.elim

private theorem FO.flat_nodup (G : Graph) (hG : G.Valid) : ((sweepEvents G).flatMap evPairs).Nodup :=
  (sweep_pairs G hG).nodup_iff.mpr (FO.orderedPairs_nodup _ (labelOrder_nodup G))

private theorem FO.pair_mem (G : Graph) (hG : G.Valid) {ev : Ev} (hev : ev ∈ sweepEvents G) {x y : Grp}
    (h : (x, y) ∈ evPairs ev) :
    x ∈ labelOrder G ∧ y ∈ labelOrder G ∧ (labelOrder G).idxOf x < (labelOrder G).idxOf y := by
  have hm : (x, y) ∈ (sweepEvents G).flatMap evPairs := List.mem_flatMap.mpr ⟨ev, hev, h⟩
  exact FO.mem_orderedPairs _ (labelOrder_nodup G) x y ((sweep_pairs G hG).mem_iff.mp hm)

private theorem FO.grp_mem (G : Graph) (hG : G.Valid) {ev : Ev} (hev : ev ∈ sweepEvents G) {g : Grp}
    (hg : g ∈ FO.evGrps ev) : g ∈ labelOrder G := by
  cases ev with
  | mv a b =>
    have := FO.pair_mem G hG hev (x := a) (y := b) (by simp [evPairs])
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil] at hg
    rcases hg with rfl | rfl | hf
    · exact this.1
    · exact this.2.1
    · exact hf.elim
  | cell u w =>
    have h1 := FO.pair_mem G hG hev (x := .X u) (y := .p u w) (by simp [evPairs])
    have h2 := FO.pair_mem G hG hev (x := .X u) (y := .X w) (by simp [evPairs])
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil] at hg
    rcases hg with rfl | rfl | rfl | hf
    · exact h1.1
    · exact h1.2.1
    · exact h2.2.1
    · exact hf.elim

private theorem FO.pair_of_grps {ev : Ev} {g₁ g₂ : Grp} (h₁ : g₁ ∈ FO.evGrps ev) (h₂ : g₂ ∈ FO.evGrps ev)
    (hne : g₁ ≠ g₂) : (g₁, g₂) ∈ evPairs ev ∨ (g₂, g₁) ∈ evPairs ev := by
  cases ev with
  | mv a b =>
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp_all [evPairs]
  | cell u w =>
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;> simp_all [evPairs]

private theorem FO.evAt_eq (G : Graph) {k : Nat} (hk : k < numFactors G) :
    evAt G k = (sweepEvents G)[k]'hk := by
  simp [evAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

/-- Two different events do not share two different groups. -/
private theorem FO.shared (G : Graph) (hG : G.Valid) {k k' : Nat} (hk : k < numFactors G)
    (hk' : k' < numFactors G) (hne : k ≠ k') {g₁ g₂ : Grp} (hg : g₁ ≠ g₂)
    (h₁ : g₁ ∈ FO.evGrps (evAt G k)) (h₂ : g₂ ∈ FO.evGrps (evAt G k))
    (h₁' : g₁ ∈ FO.evGrps (evAt G k')) (h₂' : g₂ ∈ FO.evGrps (evAt G k')) : False := by
  have hm := evAt_mem G hk
  have hm' := evAt_mem G hk'
  -- a common ordered pair
  have hq : ∃ q, q ∈ evPairs (evAt G k) ∧ q ∈ evPairs (evAt G k') := by
    rcases FO.pair_of_grps h₁ h₂ hg with p | p <;>
      rcases FO.pair_of_grps h₁' h₂' hg with p' | p'
    · exact ⟨_, p, p'⟩
    · have a := FO.pair_mem G hG hm p
      have b := FO.pair_mem G hG hm' p'
      omega
    · have a := FO.pair_mem G hG hm p
      have b := FO.pair_mem G hG hm' p'
      omega
    · exact ⟨_, p, p'⟩
  obtain ⟨q, hq, hq'⟩ := hq
  rw [FO.evAt_eq G hk] at hq
  rw [FO.evAt_eq G hk'] at hq'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact FO.flatMap_nodup_idx evPairs _ (FO.flat_nodup G hG) k k' hk hk' hlt q hq hq'
  · exact FO.flatMap_nodup_idx evPairs _ (FO.flat_nodup G hG) k' k hk' hk hlt q hq' hq

/-- A wire of the `k`-th factor lies in a group of the event, and that group is unique. -/
private theorem FO.grp_unique (G : Graph) {g g' : Grp} (hg : g ∈ labelOrder G) (hg' : g' ∈ labelOrder G)
    {x : Nat} (hx : x ∈ wiresOf G g) (hx' : x ∈ wiresOf G g') : g = g' :=
  Classical.byContradiction fun hne => wiresOf_disjoint G hg hg' hne x hx hx'

theorem stepZ_spec (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) (eps : Nat → Bool) :
    StrictIncr (stepZ G k) ∧ (stepZ G k).length = (stepCase G k eps).width ∧
      ∀ x ∈ stepZ G k, x < G.m := by
  have hm := evAt_mem G hk
  unfold stepZ stepCase
  generalize evAt G k = ev at hm ⊢
  cases ev with
  | mv g h =>
    obtain ⟨hg, hh, hlt⟩ := FO.pair_mem G hG hm (x := g) (y := h) (by simp [evPairs])
    refine ⟨?_, ?_, ?_⟩
    · unfold StrictIncr
      simp only [evZ]
      rw [List.pairwise_append]
      exact ⟨List.pairwise_lt_range' _, List.pairwise_lt_range' _, wiresOf_lt_of_before G hg hh hlt⟩
    · cases g <;> cases h <;> rfl
    · intro x hx
      simp only [evZ, List.mem_append] at hx
      rcases hx with hx | hx
      · exact wiresOf_lt G hG hg x hx
      · exact wiresOf_lt G hG hh x hx
  | cell u w =>
    have he : (u, w) ∈ G.edges := (sweep_cell_iff G hG u w).mp hm
    obtain ⟨h1, h2, h3⟩ := edgeWires_spec G hG he
    exact ⟨h1, h2, h3⟩

/-- A triple inside the wires of two different factors is a bead triple. -/
theorem factor_overlap (G : Graph) (hG : G.Valid) {k k' : Nat} (hk : k < numFactors G)
    (hk' : k' < numFactors G) (hne : k ≠ k') {t : Triple} (ht : ValidTriple G.m t)
    (h₁ : Inside (stepZ G k) t) (h₂ : Inside (stepZ G k') t) : ∃ u, u < G.n ∧ t = beadTriple G u := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨hab, hbc, _⟩ := ht
  change a < b at hab
  change b < c at hbc
  obtain ⟨ha, _, hc⟩ := h₁
  obtain ⟨ha', _, hc'⟩ := h₂
  have hm := evAt_mem G hk
  have hm' := evAt_mem G hk'
  simp only [stepZ] at ha hc ha' hc'
  obtain ⟨ga, hga, hag⟩ := (FO.mem_evZ G _ a).mp ha
  obtain ⟨gc, hgc, hcg⟩ := (FO.mem_evZ G _ c).mp hc
  obtain ⟨ga', hga', hag'⟩ := (FO.mem_evZ G _ a).mp ha'
  obtain ⟨gc', hgc', hcg'⟩ := (FO.mem_evZ G _ c).mp hc'
  have ea : ga = ga' :=
    FO.grp_unique G (FO.grp_mem G hG hm hga) (FO.grp_mem G hG hm' hga') hag hag'
  have ec : gc = gc' :=
    FO.grp_unique G (FO.grp_mem G hG hm hgc) (FO.grp_mem G hG hm' hgc') hcg hcg'
  subst ea ec
  have hac : ga = gc := Classical.byContradiction fun hne' =>
    FO.shared G hG hk hk' hne hne' hga hgc hga' hgc'
  subst hac
  have hgl := FO.grp_mem G hG hm hga
  cases ga with
  | p u w =>
    rw [FO.wiresOf_p] at hag hcg
    simp at hag hcg
    omega
  | X u =>
    rw [FO.wiresOf_X] at hag hcg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hag hcg
    have hu : u < G.n := by
      rcases (mem_labelOrder G hG _).mp hgl with ⟨v, hv, e⟩ | ⟨v, w, _, e⟩
      · cases e; exact hv
      · cases e
    refine ⟨u, hu, ?_⟩
    simp only [beadTriple]
    have : a = firstWire G (.X u) ∧ b = firstWire G (.X u) + 1 ∧ c = firstWire G (.X u) + 2 := by
      omega
    obtain ⟨r1, r2, r3⟩ := this
    subst r1 r2 r3
    rfl

/-- A bead triple inside the wires of a factor is at a local bead position. -/
theorem bead_in_factor (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) (eps : Nat → Bool)
    {u : Nat} (hu : u < G.n) (h : Inside (stepZ G k) (beadTriple G u)) :
    ∃ t ∈ (stepCase G k eps).beadTriples, embT (stepZ G k) t = beadTriple G u := by
  have hm := evAt_mem G hk
  have hXu : Grp.X u ∈ labelOrder G := (mem_labelOrder G hG _).mpr (Or.inl ⟨u, hu, rfl⟩)
  have h1 := h.1
  simp only [stepZ, beadTriple] at h1
  obtain ⟨g, hg, hfg⟩ := (FO.mem_evZ G _ _).mp h1
  have hgX : g = .X u :=
    FO.grp_unique G (FO.grp_mem G hG hm hg) hXu hfg (by rw [FO.wiresOf_X]; simp)
  subst hgX
  unfold stepZ stepCase
  generalize evAt G k = ev at hg ⊢
  cases ev with
  | mv a b =>
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · cases b with
      | X w =>
        refine ⟨(0, 1, 2), by simp [caseOf, Case.beadTriples], ?_⟩
        simp [embT, evZ, FO.wiresOf_X, beadTriple]
      | p v w =>
        refine ⟨(0, 1, 2), by simp [caseOf, Case.beadTriples], ?_⟩
        simp [embT, evZ, FO.wiresOf_X, FO.wiresOf_p, beadTriple]
    · cases a with
      | X w =>
        refine ⟨(3, 4, 5), by simp [caseOf, Case.beadTriples], ?_⟩
        simp [embT, evZ, FO.wiresOf_X, beadTriple]
      | p v w =>
        refine ⟨(1, 2, 3), by simp [caseOf, Case.beadTriples], ?_⟩
        simp [embT, evZ, FO.wiresOf_X, FO.wiresOf_p, beadTriple]
  | cell a b =>
    simp only [FO.evGrps, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with e | e | e
    · cases e
      refine ⟨(0, 1, 2), by simp [caseOf, Case.beadTriples], ?_⟩
      simp [embT, evZ, edgeWires, FO.wiresOf_X, FO.wiresOf_p, beadTriple]
    · cases e
    · cases e
      refine ⟨(4, 5, 6), by simp [caseOf, Case.beadTriples], ?_⟩
      simp [embT, evZ, edgeWires, FO.wiresOf_X, FO.wiresOf_p, beadTriple]

/-- The cell of an edge is a factor. -/
theorem cell_step (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    ∃ k, k < numFactors G ∧ evAt G k = .cell e.1 e.2 :=
  exists_evAt G ((sweep_cell_iff G hG e.1 e.2).mpr he)

/-- Every cell is the cell of an edge. -/
theorem step_cell_edge (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) {u w : Nat}
    (h : evAt G k = .cell u w) : (u, w) ∈ G.edges := by
  have hm := evAt_mem G hk
  rw [h] at hm
  exact (sweep_cell_iff G hG u w).mp hm

end BraidDistance
