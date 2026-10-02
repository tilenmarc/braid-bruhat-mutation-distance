import BraidDistance.Wires

/-!
# The vertex-cover charging argument (Proposition 5.1, combinatorial part)

Let `Y` be any set of triples (here given by a Boolean predicate `inY`) such that every gadget `A_e` contains a
valid triple of `Y`.  Then there are a vertex cover `C` and a duplicate-free list `Ys` of triples of `Y` with
`|C| ≤ |Ys|`:

* call an edge *charged* if the bead triple of one of its endpoints lies in `Y`;
* `C` = the vertices whose bead triple lies in `Y`, together with one chosen endpoint of every edge that is not
  charged (duplicates removed);
* `Ys` = the bead triples of the first kind of vertices, together with, for each edge `e` that is not charged and
  whose chosen endpoint is not already in `C`, a triple `T_e ∈ Y` inside `A_e`.  Such a `T_e` is not a bead
  triple of `e`'s endpoints, hence (by `edgeWires_overlap`) lies in no other gadget, so the `T_e` of different
  edges are different and differ from all bead triples.
-/

namespace BraidDistance

/-- The invariant of the charging recursion after processing the edges of `L`. -/
private def Charging.Inv (G : Graph) (inY : Triple → Bool) (L : List (Nat × Nat)) (C : List Nat)
    (Ys : List Triple) : Prop :=
  C.Nodup ∧ (∀ v ∈ C, v < G.n) ∧ (∀ v, v < G.n → inY (beadTriple G v) = true → v ∈ C) ∧
    (∀ e ∈ L, e.1 ∈ C ∨ e.2 ∈ C) ∧ Ys.Nodup ∧ C.length ≤ Ys.length ∧
    ∀ t ∈ Ys, ValidTriple G.m t ∧ inY t = true ∧
      ((∃ v, v < G.n ∧ t = beadTriple G v) ∨
        (∃ e ∈ L, Inside (edgeWires G e.1 e.2) t ∧ ∀ v, v < G.n → t ≠ beadTriple G v))

private theorem Charging.build (G : Graph) (hG : G.Valid) (inY : Triple → Bool)
    (hgad : ∀ e ∈ G.edges, ∃ t : Triple, ValidTriple G.m t ∧ Inside (edgeWires G e.1 e.2) t ∧ inY t = true) :
    ∀ L : List (Nat × Nat), L.Nodup → (∀ e ∈ L, e ∈ G.edges) →
      ∃ C : List Nat, ∃ Ys : List Triple, Charging.Inv G inY L C Ys := by
  intro L
  induction L with
  | nil =>
    intro _ _
    let C := (List.range G.n).filter (fun v => inY (beadTriple G v))
    have hCn : ∀ v ∈ C, v < G.n := by
      intro v hv
      simp only [C, List.mem_filter, List.mem_range] at hv
      exact hv.1
    refine ⟨C, C.map (beadTriple G), List.nodup_range.filter _, hCn, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv hy
      simp only [C, List.mem_filter, List.mem_range]
      exact ⟨hv, hy⟩
    · intro e he; simp at he
    · have hCnd : C.Nodup := List.nodup_range.filter _
      unfold List.Nodup
      rw [List.pairwise_map]
      refine hCnd.imp_of_mem ?_
      intro a b ha hb hab heq
      exact hab (beadTriple_inj G hG (hCn a ha) (hCn b hb) heq)
    · simp
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨v, hv, rfl⟩ := ht
      have hv' := hv
      simp only [C, List.mem_filter, List.mem_range] at hv'
      exact ⟨beadTriple_valid G hG hv'.1, hv'.2, Or.inl ⟨v, hv'.1, rfl⟩⟩
  | cons f L ih =>
    intro hnd hsub
    have hfL : f ∉ L := (List.nodup_cons.mp hnd).1
    have hf : f ∈ G.edges := hsub f (List.mem_cons_self ..)
    obtain ⟨C, Ys, hCnd, hCn, hB, hcov, hYnd, hlen, hYs⟩ :=
      ih (List.nodup_cons.mp hnd).2 (fun e he => hsub e (List.mem_cons_of_mem _ he))
    have hYs' : ∀ t ∈ Ys, ValidTriple G.m t ∧ inY t = true ∧
        ((∃ v, v < G.n ∧ t = beadTriple G v) ∨
          (∃ e ∈ f :: L, Inside (edgeWires G e.1 e.2) t ∧ ∀ v, v < G.n → t ≠ beadTriple G v)) := by
      intro t ht
      obtain ⟨h1, h2, h3 | ⟨e, he, h4⟩⟩ := hYs t ht
      · exact ⟨h1, h2, Or.inl h3⟩
      · exact ⟨h1, h2, Or.inr ⟨e, List.mem_cons_of_mem _ he, h4⟩⟩
    by_cases hc : f.1 ∈ C ∨ f.2 ∈ C
    · refine ⟨C, Ys, hCnd, hCn, hB, ?_, hYnd, hlen, hYs'⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc
      · exact hcov e he
    · have hv := hG.2 f hf
      obtain ⟨T, hTv, hTin, hTy⟩ := hgad f hf
      have h1C : f.1 ∉ C := fun h => hc (Or.inl h)
      have h2C : f.2 ∉ C := fun h => hc (Or.inr h)
      have hTnb : ∀ v, v < G.n → T ≠ beadTriple G v := by
        intro v hvn heq
        rw [heq] at hTin hTy
        have := hB v hvn hTy
        rcases (beadTriple_inside_edge G hG hf hvn).mp hTin with rfl | rfl
        · exact h1C this
        · exact h2C this
      have hTY : T ∉ Ys := by
        intro hT
        obtain ⟨_, _, ⟨v, hvn, heq⟩ | ⟨e, he, hein, _⟩⟩ := hYs T hT
        · exact hTnb v hvn heq
        · have hef : e ≠ f := by intro h; subst h; exact hfL he
          have he' : e ∈ G.edges := hsub e (List.mem_cons_of_mem _ he)
          obtain ⟨u, hu, _, rfl⟩ := edgeWires_overlap G hG he' hf hef hTv hein hTin
          have hve := hG.2 e he'
          have hun : u < G.n := by omega
          exact hTnb u hun rfl
      refine ⟨f.1 :: C, T :: Ys, List.nodup_cons.mpr ⟨h1C, hCnd⟩, ?_, ?_, ?_,
        List.nodup_cons.mpr ⟨hTY, hYnd⟩, by simp only [List.length_cons]; omega, ?_⟩
      · intro v hvC
        rcases List.mem_cons.mp hvC with rfl | hvC
        · omega
        · exact hCn v hvC
      · intro v hvn hy
        exact List.mem_cons_of_mem _ (hB v hvn hy)
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inl (List.mem_cons_self ..)
        · rcases hcov e he with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hTv, hTy, Or.inr ⟨f, List.mem_cons_self .., hTin, hTnb⟩⟩
        · exact hYs' t ht

/-- Proposition 5.1, the charging argument. -/
theorem charging (G : Graph) (hG : G.Valid) (inY : Triple → Bool)
    (hgad : ∀ e ∈ G.edges, ∃ t : Triple, ValidTriple G.m t ∧ Inside (edgeWires G e.1 e.2) t ∧ inY t = true) :
    ∃ C : List Nat, ∃ Ys : List Triple, IsVertexCover G C ∧ Ys.Nodup ∧
      (∀ t ∈ Ys, ValidTriple G.m t ∧ inY t = true) ∧ C.length ≤ Ys.length := by
  obtain ⟨C, Ys, hCnd, hCn, _, hcov, hYnd, hlen, hYs⟩ :=
    Charging.build G hG inY hgad G.edges hG.1 (fun e he => he)
  exact ⟨C, Ys, ⟨hCnd, hCn, hcov⟩, hYnd, fun t ht => ⟨(hYs t ht).1, (hYs t ht).2.1⟩, hlen⟩

end BraidDistance
