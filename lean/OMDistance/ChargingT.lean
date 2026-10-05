import OMDistance.Basic
import BraidDistance.Graph

/-!
# The vertex-cover charging argument, abstractly (Proposition 7.1, last step)

Let `Y` be a set of bases (`inY`).  Suppose that every gadget (`gad e`, for an edge `e`) contains a valid basis of
`Y`, and that there are pairwise disjoint finite sets `T u` of valid bases, one per vertex, such that a basis of
`T x` inside the gadget of `e` forces `x ∈ e`, and a basis inside two different gadgets lies in some `T u`.  Then
there are a vertex cover `C` and a duplicate-free list `Ys` of valid bases of `Y` with `|C| ≤ |Ys|`.

Proof (as in Proposition 5.1, with `𝒯_u` in place of the bead triple): call an edge `uw` *charged* if `Y` meets
`T u` or `T w`.  `C` consists of the vertices `u` with `Y ∩ T u ≠ ∅` and one chosen endpoint of each edge that is
not charged.  `Ys` consists of one element of `Y ∩ T u` for each vertex of the first kind, and, for each edge `e`
that is not charged and whose chosen endpoint is not yet in `C`, a basis of `Y` in the gadget of `e`.  Such a basis
lies in no `T x` (it would force `x ∈ e`, but `e` is not charged), hence in no other gadget, so all chosen bases
are different.

Part I's `BraidDistance.charging` is the special case with triples and bead triples.
-/

namespace OMDistance

open BraidDistance (Graph IsVertexCover)

/-- The invariant of the charging recursion after processing the edges of `L`. -/
private def ChargingT.Inv (G : Graph) (valid : List Nat → Prop) (inY : List Nat → Bool)
    (gad : Nat × Nat → List Nat → Prop) (T : Nat → List (List Nat)) (L : List (Nat × Nat)) (C : List Nat)
    (Ys : List (List Nat)) : Prop :=
  C.Nodup ∧ (∀ v ∈ C, v < G.n) ∧ (∀ v, v < G.n → ∀ B ∈ T v, inY B = true → v ∈ C) ∧
    (∀ e ∈ L, e.1 ∈ C ∨ e.2 ∈ C) ∧ Ys.Nodup ∧ C.length ≤ Ys.length ∧
    ∀ B ∈ Ys, valid B ∧ inY B = true ∧
      ((∃ v, v < G.n ∧ B ∈ T v) ∨ (∃ e ∈ L, gad e B ∧ ∀ v, v < G.n → B ∉ T v))

open Classical in
/-- A chosen element of `Y ∩ T u`, when one exists. -/
private noncomputable def ChargingT.rep (inY : List Nat → Bool) (T : Nat → List (List Nat)) (u : Nat) :
    List Nat :=
  if h : ∃ B, B ∈ T u ∧ inY B = true then Classical.choose h else []

private theorem ChargingT.rep_spec (inY : List Nat → Bool) (T : Nat → List (List Nat)) (u : Nat)
    (h : ∃ B, B ∈ T u ∧ inY B = true) : ChargingT.rep inY T u ∈ T u ∧ inY (ChargingT.rep inY T u) = true := by
  unfold ChargingT.rep
  simp only [h, dite_true]
  exact Classical.choose_spec h

open Classical in
private theorem ChargingT.build (G : Graph) (hG : G.Valid) (valid : List Nat → Prop) (inY : List Nat → Bool)
    (gad : Nat × Nat → List Nat → Prop) (T : Nat → List (List Nat))
    (hgad : ∀ e ∈ G.edges, ∃ B, valid B ∧ gad e B ∧ inY B = true)
    (hTvalid : ∀ u, u < G.n → ∀ B ∈ T u, valid B)
    (hTdisj : ∀ u w, u < G.n → w < G.n → ∀ B, B ∈ T u → B ∈ T w → u = w)
    (hTgad : ∀ e ∈ G.edges, ∀ B, gad e B → ∀ x, x < G.n → B ∈ T x → x = e.1 ∨ x = e.2)
    (hover : ∀ e ∈ G.edges, ∀ f ∈ G.edges, e ≠ f → ∀ B, valid B → gad e B → gad f B →
      ∃ u, u < G.n ∧ B ∈ T u) :
    ∀ L : List (Nat × Nat), L.Nodup → (∀ e ∈ L, e ∈ G.edges) →
      ∃ C : List Nat, ∃ Ys : List (List Nat), ChargingT.Inv G valid inY gad T L C Ys := by
  intro L
  induction L with
  | nil =>
    intro _ _
    let C := (List.range G.n).filter (fun v => decide (∃ B, B ∈ T v ∧ inY B = true))
    have hCmem : ∀ v, v ∈ C ↔ v < G.n ∧ ∃ B, B ∈ T v ∧ inY B = true := by
      intro v
      simp only [C, List.mem_filter, List.mem_range, decide_eq_true_eq]
    have hCnd : C.Nodup := List.nodup_range.filter _
    refine ⟨C, C.map (ChargingT.rep inY T), hCnd, fun v hv => ((hCmem v).mp hv).1, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv B hB hy
      exact (hCmem v).mpr ⟨hv, B, hB, hy⟩
    · intro e he; simp at he
    · unfold List.Nodup
      rw [List.pairwise_map]
      refine hCnd.imp_of_mem ?_
      intro a b ha hb hab heq
      obtain ⟨han, hae⟩ := (hCmem a).mp ha
      obtain ⟨hbn, hbe⟩ := (hCmem b).mp hb
      have h1 := (ChargingT.rep_spec inY T a hae).1
      have h2 := (ChargingT.rep_spec inY T b hbe).1
      rw [heq] at h1
      exact hab (hTdisj a b han hbn _ h1 h2)
    · simp
    · intro B hB
      simp only [List.mem_map] at hB
      obtain ⟨v, hv, rfl⟩ := hB
      obtain ⟨hvn, hve⟩ := (hCmem v).mp hv
      obtain ⟨h1, h2⟩ := ChargingT.rep_spec inY T v hve
      exact ⟨hTvalid v hvn _ h1, h2, Or.inl ⟨v, hvn, h1⟩⟩
  | cons f L ih =>
    intro hnd hsub
    have hfL : f ∉ L := (List.nodup_cons.mp hnd).1
    have hf : f ∈ G.edges := hsub f (List.mem_cons_self ..)
    obtain ⟨C, Ys, hCnd, hCn, hB, hcov, hYnd, hlen, hYs⟩ :=
      ih (List.nodup_cons.mp hnd).2 (fun e he => hsub e (List.mem_cons_of_mem _ he))
    have hYs' : ∀ B ∈ Ys, valid B ∧ inY B = true ∧
        ((∃ v, v < G.n ∧ B ∈ T v) ∨ (∃ e ∈ f :: L, gad e B ∧ ∀ v, v < G.n → B ∉ T v)) := by
      intro B hB'
      obtain ⟨h1, h2, h3 | ⟨e, he, h4⟩⟩ := hYs B hB'
      · exact ⟨h1, h2, Or.inl h3⟩
      · exact ⟨h1, h2, Or.inr ⟨e, List.mem_cons_of_mem _ he, h4⟩⟩
    by_cases hc : f.1 ∈ C ∨ f.2 ∈ C
    · refine ⟨C, Ys, hCnd, hCn, hB, ?_, hYnd, hlen, hYs'⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc
      · exact hcov e he
    · have hv := hG.2 f hf
      obtain ⟨X, hXv, hXin, hXy⟩ := hgad f hf
      have h1C : f.1 ∉ C := fun h => hc (Or.inl h)
      have h2C : f.2 ∉ C := fun h => hc (Or.inr h)
      have hXnT : ∀ v, v < G.n → X ∉ T v := by
        intro v hvn hXT
        have := hB v hvn X hXT hXy
        rcases hTgad f hf X hXin v hvn hXT with rfl | rfl
        · exact h1C this
        · exact h2C this
      have hXY : X ∉ Ys := by
        intro hX
        obtain ⟨_, _, ⟨v, hvn, hXT⟩ | ⟨e, he, hein, _⟩⟩ := hYs X hX
        · exact hXnT v hvn hXT
        · have hef : e ≠ f := by intro h; subst h; exact hfL he
          have he' : e ∈ G.edges := hsub e (List.mem_cons_of_mem _ he)
          obtain ⟨u, hun, hXT⟩ := hover e he' f hf hef X hXv hein hXin
          exact hXnT u hun hXT
      refine ⟨f.1 :: C, X :: Ys, List.nodup_cons.mpr ⟨h1C, hCnd⟩, ?_, ?_, ?_,
        List.nodup_cons.mpr ⟨hXY, hYnd⟩, by simp only [List.length_cons]; omega, ?_⟩
      · intro v hvC
        rcases List.mem_cons.mp hvC with rfl | hvC
        · omega
        · exact hCn v hvC
      · intro v hvn B hBT hy
        exact List.mem_cons_of_mem _ (hB v hvn B hBT hy)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inl (List.mem_cons_self ..)
        · rcases hcov e he with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro B hB'
        rcases List.mem_cons.mp hB' with rfl | hB'
        · exact ⟨hXv, hXy, Or.inr ⟨f, List.mem_cons_self .., hXin, hXnT⟩⟩
        · exact hYs' B hB'

theorem charging_abstract (G : Graph) (hG : G.Valid) (valid : List Nat → Prop) (inY : List Nat → Bool)
    (gad : Nat × Nat → List Nat → Prop) (T : Nat → List (List Nat))
    (hgad : ∀ e ∈ G.edges, ∃ B, valid B ∧ gad e B ∧ inY B = true)
    (hTvalid : ∀ u, u < G.n → ∀ B ∈ T u, valid B)
    (hTdisj : ∀ u w, u < G.n → w < G.n → ∀ B, B ∈ T u → B ∈ T w → u = w)
    (hTgad : ∀ e ∈ G.edges, ∀ B, gad e B → ∀ x, x < G.n → B ∈ T x → x = e.1 ∨ x = e.2)
    (hover : ∀ e ∈ G.edges, ∀ f ∈ G.edges, e ≠ f → ∀ B, valid B → gad e B → gad f B →
      ∃ u, u < G.n ∧ B ∈ T u) :
    ∃ C : List Nat, ∃ Ys : List (List Nat), IsVertexCover G C ∧ Ys.Nodup ∧
      (∀ B ∈ Ys, valid B ∧ inY B = true) ∧ C.length ≤ Ys.length := by
  obtain ⟨C, Ys, hCnd, hCn, _, hcov, hYnd, hlen, hYs⟩ :=
    ChargingT.build G hG valid inY gad T hgad hTvalid hTdisj hTgad hover G.edges hG.1 (fun e he => he)
  exact ⟨C, Ys, ⟨hCnd, hCn, hcov⟩, hYnd, fun B hB => ⟨(hYs B hB).1, (hYs B hB).2.1⟩, hlen⟩

end OMDistance
