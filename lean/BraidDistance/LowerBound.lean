import BraidDistance.Chain
import BraidDistance.Charging
import BraidDistance.GadgetLower
import BraidDistance.Restrict

/-!
# The lower bound (Proposition 5.1)

For every walk of signotopes from `s_G` to `v_G` of length `k` there is a vertex cover `C` with
`|D| + 2|C| ≤ k`; with `d_B ≤ d_br` (`path_to_walk`) the same holds for every sequence of commutations and braid
moves from `W^s_G` to `W^v_G` with `k` braid moves.

Proof: let `Y` be the set of triples flipped more often than necessary.  Restricting the walk to a gadget `A_e`
gives a walk from `g^s` to `g^v` (Corollary 4.6(a)), which flips some triple more often than necessary
(Lemma 3.3); its image lies in `Y` and inside `A_e`.  The charging argument gives `C` and `Ys ⊆ Y` with
`|C| ≤ |Ys|`, and Lemma 2.5 gives `|D| + 2|Ys| ≤ k`.

This file is complete given the lemmas it imports.
-/

namespace BraidDistance

/-- Proposition 5.1 for walks of signotopes. -/
theorem lower_walk (G : Graph) (hG : G.Valid) {k : Nat} (hw : Walk G.m (sG G) (vG G) k) :
    ∃ C, IsVertexCover G C ∧ hamming G.m (sG G) (vG G) + 2 * C.length ≤ k := by
  obtain ⟨ts, hlen, hfw, hend⟩ := walk_to_flips hw
  let inY : Triple → Bool := fun t =>
    decide ((if t ∈ diffList G.m (sG G) (vG G) then 1 else 0) < ts.count t)
  have hgad : ∀ e ∈ G.edges, ∃ t : Triple, ValidTriple G.m t ∧ Inside (edgeWires G e.1 e.2) t ∧
      inY t = true := by
    intro e he
    obtain ⟨hzinc, hzlen, hzm⟩ := edgeWires_spec G hG he
    obtain ⟨hs, hv⟩ := edge_restrict G hG he
    have hfw' := flipWalk_restrict hzinc hzm hfw
    rw [hzlen] at hfw'
    have hfw'' : FlipWalk 7 gs (localize (edgeWires G e.1 e.2) ts) := FlipWalk.congr hs hfw'
    have hend' : Agree 7 (flipList gs (localize (edgeWires G e.1 e.2) ts)) gv := by
      have a1 := flipList_congr hs.symm (localize (edgeWires G e.1 e.2) ts)
      have a2 := pull_flipList hzinc hzm (sG G) hfw.1
      rw [hzlen] at a2
      have a3 := pull_agree hzinc hzm hend
      rw [hzlen] at a3
      exact a1.trans (a2.symm.trans (a3.trans hv))
    obtain ⟨t', ht', hc⟩ := gadget_lower hfw'' hend'
    have ht'z : ValidTriple (edgeWires G e.1 e.2).length t' := by rw [hzlen]; exact ht'
    obtain ⟨hvalid, hins⟩ := embT_valid hzinc hzm ht'z
    refine ⟨embT (edgeWires G e.1 e.2) t', hvalid, hins, ?_⟩
    have hcount := count_localize hzinc hzm hfw.1 ht'z
    have hmem : t' ∈ Dkappa ↔ embT (edgeWires G e.1 e.2) t' ∈ diffList G.m (sG G) (vG G) := by
      have e1 := hs.at ht'
      have e2 := hv.at ht'
      rw [pull_at] at e1 e2
      unfold Dkappa
      rw [mem_diffList, mem_diffList, ← e1, ← e2]
      exact ⟨fun h => ⟨hvalid, h.2⟩, fun h => ⟨ht', h.2⟩⟩
    simp only [inY, decide_eq_true_eq]
    rw [← hcount]
    by_cases h : t' ∈ Dkappa
    · have h' := hmem.mp h
      simp only [h, h', ite_true] at hc ⊢
      exact hc
    · have h' : embT (edgeWires G e.1 e.2) t' ∉ diffList G.m (sG G) (vG G) := fun h' => h (hmem.mpr h')
      simp only [h, h', ite_false] at hc ⊢
      exact hc
  obtain ⟨C, Ys, hC, hYnd, hYs, hle⟩ := charging G hG inY hgad
  refine ⟨C, hC, ?_⟩
  have hb := parity_bound hfw.1 hend Ys hYnd (fun t ht => (hYs t ht).1) (fun t ht => by
    have := (hYs t ht).2
    simpa [inY] using this)
  omega

/-- Proposition 5.1 for sequences of commutations and braid moves. -/
theorem lower_path (G : Graph) (hG : G.Valid) {k : Nat} (hp : Path (Ws G) (Wv G) k) :
    ∃ C, IsVertexCover G C ∧ hamming G.m (sG G) (vG G) + 2 * C.length ≤ k :=
  lower_walk G hG (path_to_walk (Ws_reduced G hG) hp)

end BraidDistance
