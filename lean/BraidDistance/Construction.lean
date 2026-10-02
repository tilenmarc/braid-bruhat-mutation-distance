import BraidDistance.Graph
import BraidDistance.Cases

/-!
# The construction (Section 4)

Everything is 0-based: vertices `0, …, n-1`, wires `0, …, m-1`, positions `0, …, m-1` (position `0` on top).

## Groups and bundles (Section 4.1)
Every vertex `u` has a *block* `Grp.X u` of three wires and every edge `uw` (`u < w`) a *private wire*
`Grp.p u w`.  The *bundle* of `u` is `X u` followed by the private wires `p u w₁, …, p u w_k` of the edges to
the larger neighbours `w₁ < ⋯ < w_k` of `u` (`G.up u`).  The *label order* lists the bundles `B_0, …, B_{n-1}`;
the wires are labelled `0, …, m-1` in this order (`firstWire`, `wiresOf`).

## The shadow sweep (Section 4.2)
The shadow sweep `Φ` is the list `sweepEvents G` of *events* on groups:
* `Ev.mv g h`: the group `h`, lying directly below `g`, passes up through `g` (one move);
* `Ev.cell u w`: the cell of the edge `uw`: the groups `X u, p u w, X w`, lying consecutively in this order,
  become `X w, p u w, X u` (three moves).

It consists of the rounds `u = 0, …, n-1` (`roundEvents`), in which the bundles `B_w`, `w = u+1, …, n-1`, pass up
through `B_u` one after another (`passEvents`), followed by the completion (`completionEvents`), which reverses
the private wires of every bundle (for `j = 1, …, k-1`, `p u w_j` passes up through the private wires above it).
The event lists follow the description of Section 4.2; the arrangement of the groups of `B_u` when `B_w` passes
through it is `(Π_u^{<w}, X_u, Π_u^{≥w})` by Lemma 4.1(b), which is used to write the events down explicitly.
The completion is the one fixed "for definiteness" in the paper (and in `check.py`).

The arrangement of the groups before the `k`-th event is `arrAt G k`; an event acts on an arrangement by
exchanging the names of the two groups (`applyEv`), which is the exchange of two adjacent groups whenever the
event can be applied (Lemma 4.1).

## The blow-up and the words (Sections 4.3, 4.4)
The factor of an event is its local word (`moveWord` for a move, `kappa` for a cell) shifted to the wire position
`wirePos` of its top group in the current arrangement (`factors`).  The word `Φ̂` is the concatenation of the
factors.  `W G k ε` is `Φ̂` with the beads of all blocks inserted after the `k`-th factor, the bead of `u` of type
`ε u` at the current position of `X u`; the beads are listed by increasing vertex (the paper notes that their
order is irrelevant up to commutations; `check.py` lists them by position).  Finally
`W^s_G = W G 0 0`, `W^v_G = W G J 0` with `J = numFactors G`, and `s_G`, `v_G` are their sign vectors.

The values agree with `check.py` (`construct`, `word_with_beads`, `sG_vG`), see `Sanity.lean`.
-/

namespace BraidDistance

/-- A group: the block `X u` of the vertex `u`, or the private wire `p u w` of the edge `uw`. -/
inductive Grp where
  | X (u : Nat)
  | p (u w : Nat)
deriving DecidableEq, Repr

/-- The number of wires of a group. -/
def Grp.size : Grp → Nat
  | .X _ => 3
  | .p _ _ => 1

/-- The bundle `B_u = (X_u, p_{uw₁}, …, p_{uw_k})`. -/
def bundle (G : Graph) (u : Nat) : List Grp := .X u :: (G.up u).map (Grp.p u)

/-- The label order of the groups: `B_0, B_1, …, B_{n-1}`. -/
def labelOrder (G : Graph) : List Grp := (List.range G.n).flatMap (bundle G)

/-- The wire position of the top wire of `g` in the arrangement of groups `arr`: the number of wires of the
groups above `g`. -/
def wirePos (arr : List Grp) (g : Grp) : Nat := ((arr.take (arr.idxOf g)).map Grp.size).sum

/-- The smallest wire label of the group `g`. -/
def firstWire (G : Graph) (g : Grp) : Nat := wirePos (labelOrder G) g

/-- The wire labels of the group `g`, increasing. -/
def wiresOf (G : Graph) (g : Grp) : List Nat := List.range' (firstWire G g) g.size

/-- The arrangement of wires of an arrangement of groups, every group in label order. -/
def blowArr (G : Graph) (arr : List Grp) : List Nat := arr.flatMap (wiresOf G)

/-- An event of the shadow sweep. -/
inductive Ev where
  /-- `h`, lying directly below `g`, passes up through `g`. -/
  | mv (g h : Grp)
  /-- The cell of the edge `uw`: `X u, p u w, X w` become `X w, p u w, X u`. -/
  | cell (u w : Nat)
deriving DecidableEq, Repr

/-- The events of `B_w` passing up through `B_u` in round `u` (Section 4.2, "One bundle passing up through
another"), with `B_u` in the order `(Π_u^{<w}, X_u, Π_u^{≥w})`.  First `X_w` passes up through the groups of
`B_u` from the bottom (through a cell if `uw` is an edge), then each private wire of `B_w` passes up through all
groups of `B_u`. -/
def passEvents (G : Graph) (u w : Nat) : List Ev :=
  let below := ((G.up u).filter (· < w)).map (Grp.p u)
  if G.isEdge u w then
    let above := ((G.up u).filter (w < ·)).map (Grp.p u)
    (above.reverse.map fun g => Ev.mv g (.X w)) ++ [Ev.cell u w] ++
      (below.reverse.map fun g => Ev.mv g (.X w)) ++
      ((G.up w).map (Grp.p w)).flatMap fun h =>
        (below ++ [Grp.p u w, Grp.X u] ++ above).reverse.map fun g => Ev.mv g h
  else
    let above := ((G.up u).filter (w ≤ ·)).map (Grp.p u)
    (above.reverse.map fun g => Ev.mv g (.X w)) ++ [Ev.mv (.X u) (.X w)] ++
      (below.reverse.map fun g => Ev.mv g (.X w)) ++
      ((G.up w).map (Grp.p w)).flatMap fun h =>
        (below ++ [Grp.X u] ++ above).reverse.map fun g => Ev.mv g h

/-- Round `u`: for `w = u+1, …, n-1`, the bundle `B_w` passes up through `B_u`. -/
def roundEvents (G : Graph) (u : Nat) : List Ev :=
  (List.range' (u + 1) (G.n - (u + 1))).flatMap (passEvents G u)

/-- The completion for the vertex `u`: for `j = 1, …, k-1`, the private wire `p u w_j` passes up through the
private wires `p u w_0, …, p u w_{j-1}` (which lie above it, `p u w_0` nearest). -/
def completionEvents (G : Graph) (u : Nat) : List Ev :=
  let ps := (G.up u).map (Grp.p u)
  (List.range ps.length).flatMap fun j => (ps.take j).map fun g => Ev.mv g (ps.getD j (.X 0))

/-- The shadow sweep `Φ`: the rounds `0, …, n-1`, then the completion. -/
def sweepEvents (G : Graph) : List Ev :=
  (List.range G.n).flatMap (roundEvents G) ++ (List.range G.n).flatMap (completionEvents G)

/-- Exchange the names `g` and `h`. -/
def swapNames (g h x : Grp) : Grp := if x = g then h else if x = h then g else x

/-- The arrangement after an event: the two groups exchanged by the event trade places. -/
def applyEv (arr : List Grp) : Ev → List Grp
  | .mv g h => arr.map (swapNames g h)
  | .cell u w => arr.map (swapNames (.X u) (.X w))

/-- The number of events (= number of factors) `J`. -/
def numFactors (G : Graph) : Nat := (sweepEvents G).length

/-- The `k`-th event (0-based). -/
def evAt (G : Graph) (k : Nat) : Ev := (sweepEvents G).getD k (.cell 0 0)

/-- The arrangement of the groups after the first `k` events. -/
def arrAt (G : Graph) (k : Nat) : List Grp := ((sweepEvents G).take k).foldl applyEv (labelOrder G)

/-- The top group of an event. -/
def evTop : Ev → Grp
  | .mv g _ => g
  | .cell u _ => .X u

/-- The local word of an event, on the positions `0, 1, …` of its groups. -/
def evLocal : Ev → List Nat
  | .mv g h => moveWord g.size h.size
  | .cell _ _ => kappa

/-- The factors of the events, each shifted to the position of its top group. -/
def factorsFrom : List Grp → List Ev → List (List Nat)
  | _, [] => []
  | arr, e :: es => shiftW (wirePos arr (evTop e)) (evLocal e) :: factorsFrom (applyEv arr e) es

/-- The factors `φ_1, …, φ_J` of `Φ̂` (0-based list). -/
def factors (G : Graph) : List (List Nat) := factorsFrom (labelOrder G) (sweepEvents G)

/-- The beads of all blocks at their positions after the first `k` factors, the bead of `u` of type `eps u`,
listed by increasing vertex. -/
def beadsAt (G : Graph) (k : Nat) (eps : Nat → Bool) : List Nat :=
  (List.range G.n).flatMap fun u => bead (eps u) (wirePos (arrAt G k) (.X u))

/-- `W^ε_k`: the word `Φ̂` with all beads inserted after its `k`-th factor. -/
def W (G : Graph) (k : Nat) (eps : Nat → Bool) : List Nat :=
  ((factors G).take k).flatten ++ beadsAt G k eps ++ ((factors G).drop k).flatten

/-- All beads of type `β`. -/
def zeroEps : Nat → Bool := fun _ => false

/-- The bead types of a vertex cover: turned over exactly at the vertices of `C`. -/
def coverEps (C : List Nat) : Nat → Bool := fun u => C.contains u

/-- `W^s_G = W^0_0`. -/
def Ws (G : Graph) : List Nat := W G 0 zeroEps

/-- `W^v_G = W^0_J`. -/
def Wv (G : Graph) : List Nat := W G (numFactors G) zeroEps

/-- `s_G`. -/
def sG (G : Graph) : SMap := signVec G.m (Ws G)

/-- `v_G`. -/
def vG (G : Graph) : SMap := signVec G.m (Wv G)

/-- The local case of an event for the bead types `eps`. -/
def caseOf (eps : Nat → Bool) : Ev → Case
  | .mv (.p _ _) (.p _ _) => .pp
  | .mv (.X u) (.p _ _) => .Xp (eps u)
  | .mv (.p _ _) (.X w) => .pX (eps w)
  | .mv (.X u) (.X w) => .XX (eps u) (eps w)
  | .cell u w => .cell (eps u) (eps w)

/-- The local case of the `k`-th step. -/
def stepCase (G : Graph) (k : Nat) (eps : Nat → Bool) : Case := caseOf eps (evAt G k)

/-- The wire position of the top wire of the `k`-th factor. -/
def stepWindow (G : Graph) (k : Nat) : Nat := wirePos (arrAt G k) (evTop (evAt G k))

/-- The seven wires `A_e = X_u ∪ {p_e} ∪ X_w` of the edge `e = uw`, increasing. -/
def edgeWires (G : Graph) (u w : Nat) : List Nat :=
  wiresOf G (.X u) ++ wiresOf G (.p u w) ++ wiresOf G (.X w)

/-- The wires `Z` of the groups of an event, increasing. -/
def evZ (G : Graph) : Ev → List Nat
  | .mv g h => wiresOf G g ++ wiresOf G h
  | .cell u w => edgeWires G u w

/-- The wires `Z` of the groups of the `k`-th factor, increasing. -/
def stepZ (G : Graph) (k : Nat) : List Nat := evZ G (evAt G k)

/-- The bead triple of the block `X_u`. -/
def beadTriple (G : Graph) (u : Nat) : Triple :=
  (firstWire G (.X u), firstWire G (.X u) + 1, firstWire G (.X u) + 2)

/-- `|D_k|` of an event (it does not depend on the bead types). -/
def evHam (ev : Ev) : Nat := (caseOf zeroEps ev).ham

theorem caseOf_ham (eps : Nat → Bool) (ev : Ev) : (caseOf eps ev).ham = evHam ev := by
  cases ev with
  | mv g h => cases g <;> cases h <;> rfl
  | cell u w => rfl

end BraidDistance
