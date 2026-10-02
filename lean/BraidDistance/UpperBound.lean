import BraidDistance.Chain

/-!
# The upper bound (Proposition 5.3)

For a vertex cover `C`, with `ε` the indicator of `C`:
`W^s_G = W^0_0 → W^ε_0` (turn over the beads of `C`, `|C|` braid moves),
`W^ε_0 → W^ε_J` (move the beads through `Φ̂` one factor at a time; every cell has a turned bead, so step `k`
costs `|D_k|` braid moves, `|D|` in total), and `W^ε_J → W^0_J = W^v_G` (turn the beads back, `|C|`).

This file is complete given the lemmas it imports.
-/

namespace BraidDistance

/-- With a turned bead in every cell, a step costs exactly `|D_k|`. -/
theorem step_cost (G : Graph) (hG : G.Valid) (eps : Nat → Bool)
    (hcov : ∀ e ∈ G.edges, eps e.1 = true ∨ eps e.2 = true) {k : Nat} (hk : k < numFactors G) :
    (stepCase G k eps).cost = evHam (evAt G k) := by
  unfold stepCase
  rw [← caseOf_ham eps]
  cases hev : evAt G k with
  | mv g h => cases g <;> cases h <;> rfl
  | cell u w =>
    have hedge := step_cell_edge G hG hk hev
    have hc := hcov (u, w) hedge
    simp only [caseOf, Case.cost, Case.ham]
    rcases hc with hc | hc <;> simp [hc]

/-- Phase 2: moving all beads through `Φ̂` with `|D|` braid moves. -/
theorem phase2 (G : Graph) (hG : G.Valid) (eps : Nat → Bool)
    (hcov : ∀ e ∈ G.edges, eps e.1 = true ∨ eps e.2 = true) :
    Path (W G 0 eps) (W G (numFactors G) eps) ((sweepEvents G).map evHam).sum := by
  have key : ∀ j, j ≤ numFactors G →
      Path (W G 0 eps) (W G j eps) ((List.range j).map fun k => evHam (evAt G k)).sum := by
    intro j
    induction j with
    | zero => intro _; exact Path.refl _
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := step_path G hG eps (k := j) (by omega)
      rw [step_cost G hG eps hcov (by omega)] at h2
      refine (h1.trans h2).cast ?_
      rw [List.range_succ, List.map_append, List.sum_append]
      simp
  have := key (numFactors G) (Nat.le_refl _)
  rwa [sum_range_evAt] at this

/-- Proposition 5.3: a path from `W^s_G` to `W^v_G` with `|D| + 2|C|` braid moves. -/
theorem upper_path (G : Graph) (hG : G.Valid) {C : List Nat} (hC : IsVertexCover G C) :
    Path (Ws G) (Wv G) (hamming G.m (sG G) (vG G) + 2 * C.length) := by
  have hcov : ∀ e ∈ G.edges, coverEps C e.1 = true ∨ coverEps C e.2 = true := by
    intro e he
    rcases hC.2.2 e he with h | h
    · left; simp [coverEps, h]
    · right; simp [coverEps, h]
  have h1 := beads_cover G 0 C hC.1 hC.2.1
  have h2 := phase2 G hG (coverEps C) hcov
  have h3 := (beads_cover G (numFactors G) C hC.1 hC.2.1).symm
  rw [count_D G hG]
  exact ((h1.trans h2).trans h3).cast (by omega)

end BraidDistance
