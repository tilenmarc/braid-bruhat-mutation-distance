import BraidDistance.ConstructionBasic

/-!
# Turning beads over (phases 1 and 3 of Proposition 5.3)

At any stage `k`, turning over the bead of one block `X_u` is a single braid move (property (B)), so turning over
the beads of a vertex cover `C` costs `|C|` braid moves.
-/

namespace BraidDistance

/-- Set the bead type of `u` to `true`. -/
def turnOver (eps : Nat → Bool) (u : Nat) : Nat → Bool := fun x => if x = u then true else eps x

/-- Turning over one bead is one braid move. -/
theorem beads_flip (G : Graph) (k : Nat) (eps : Nat → Bool) {u : Nat} (hu : u < G.n)
    (he : eps u = false) : Path (W G k eps) (W G k (turnOver eps u)) 1 := by
  have hmem : u ∈ List.range G.n := List.mem_range.mpr hu
  obtain ⟨s, t, hst⟩ := List.append_of_mem hmem
  have hnd : (s ++ u :: t).Nodup := hst ▸ List.nodup_range
  have hns : u ∉ s := by
    intro h
    have := (List.nodup_append.mp hnd).2.2 u h u (List.mem_cons_self)
    exact this rfl
  have hnt : u ∉ t := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have hs : s.flatMap (fun x => bead (turnOver eps u x) (wirePos (arrAt G k) (.X x))) =
      s.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) := by
    simp only [List.flatMap]; congr 1; apply List.map_congr_left
    intro x hx
    have : x ≠ u := fun h => hns (h ▸ hx)
    simp [turnOver, this]
  have ht : t.flatMap (fun x => bead (turnOver eps u x) (wirePos (arrAt G k) (.X x))) =
      t.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) := by
    simp only [List.flatMap]; congr 1; apply List.map_congr_left
    intro x hx
    have : x ≠ u := fun h => hnt (h ▸ hx)
    simp [turnOver, this]
  have h := Path.bead_flip
    (((factors G).take k).flatten ++ s.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))))
    (t.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) ++ ((factors G).drop k).flatten)
    (wirePos (arrAt G k) (.X u))
  have e1 : W G k eps = ((factors G).take k).flatten ++
      s.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) ++
      bead false (wirePos (arrAt G k) (.X u)) ++
      (t.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) ++ ((factors G).drop k).flatten) := by
    unfold W beadsAt
    rw [hst, List.flatMap_append, List.flatMap_cons, he]
    simp only [List.append_assoc]
  have e2 : W G k (turnOver eps u) = ((factors G).take k).flatten ++
      s.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) ++
      bead true (wirePos (arrAt G k) (.X u)) ++
      (t.flatMap (fun x => bead (eps x) (wirePos (arrAt G k) (.X x))) ++ ((factors G).drop k).flatten) := by
    unfold W beadsAt
    rw [hst, List.flatMap_append, List.flatMap_cons, hs, ht]
    simp only [turnOver, ite_true, List.append_assoc]
  rw [e1, e2]
  exact h

/-- Turning over the beads of a vertex cover. -/
theorem beads_cover (G : Graph) (k : Nat) (C : List Nat) (hC : C.Nodup) (hCn : ∀ v ∈ C, v < G.n) :
    Path (W G k zeroEps) (W G k (coverEps C)) C.length := by
  induction C with
  | nil =>
    have : W G k (coverEps []) = W G k zeroEps := by
      apply W_congr; intro u _; simp [coverEps, zeroEps]
    rw [this]; exact Path.refl _
  | cons a C ih =>
    have hnd := List.nodup_cons.mp hC
    have h1 := ih hnd.2 (fun v hv => hCn v (List.mem_cons_of_mem a hv))
    have ha : coverEps C a = false := by
      simp [coverEps, hnd.1]
    have h2 := beads_flip G k (coverEps C) (hCn a (List.mem_cons_self)) ha
    have h3 : W G k (turnOver (coverEps C) a) = W G k (coverEps (a :: C)) := by
      apply W_congr; intro u _
      by_cases h : u = a
      · subst h; simp [turnOver, coverEps]
      · simp [turnOver, coverEps, h]
    rw [h3] at h2
    exact (h1.trans h2).cast (by simp)

end BraidDistance
