/-!
# Graphs and vertex covers

A graph has the vertices `0, …, n-1` and a list of edges `(u, w)`.  A graph is *valid* if every edge satisfies
`u < w < n` and no edge is listed twice; the construction and the main theorem assume validity.  A vertex cover
is a duplicate-free list of vertices meeting every edge; its size is its length, and `VC(G)` is the least size
of a vertex cover.  The number of wires of the construction is `m = 3n + |E|`.
-/

namespace BraidDistance

/-- A graph on the vertices `0, …, n-1`, given by its list of edges `(u, w)` with `u < w`. -/
structure Graph where
  n : Nat
  edges : List (Nat × Nat)
deriving Repr

namespace Graph

/-- Validity: edges are listed once and satisfy `u < w < n`. -/
def Valid (G : Graph) : Prop := G.edges.Nodup ∧ ∀ e ∈ G.edges, e.1 < e.2 ∧ e.2 < G.n

instance (G : Graph) : Decidable G.Valid := by
  unfold Valid; infer_instance

/-- The number of wires `m = 3n + |E|`. -/
def m (G : Graph) : Nat := 3 * G.n + G.edges.length

/-- Whether `(u, w)` is a listed edge (for `u < w`). -/
def isEdge (G : Graph) (u w : Nat) : Bool := G.edges.contains (u, w)

/-- The neighbours of `u` larger than `u`, in increasing order (`w₁ < ⋯ < w_{k_u}` in Section 4.1). -/
def up (G : Graph) (u : Nat) : List Nat :=
  (List.range G.n).filter fun w => u < w && G.isEdge u w

end Graph

/-- A vertex cover: a duplicate-free list of vertices of `G` containing an endpoint of every edge. -/
def IsVertexCover (G : Graph) (C : List Nat) : Prop :=
  C.Nodup ∧ (∀ v ∈ C, v < G.n) ∧ ∀ e ∈ G.edges, e.1 ∈ C ∨ e.2 ∈ C

instance (G : Graph) (C : List Nat) : Decidable (IsVertexCover G C) := by
  unfold IsVertexCover; infer_instance

end BraidDistance
