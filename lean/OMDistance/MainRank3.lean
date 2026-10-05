import OMDistance.LowerRank3
import OMDistance.ObsCover
import OMDistance.ArithRank3
import BraidDistance.Main

/-!
# Theorem 7.2 (`\label{thm:rank3}`)

Let `G` be a valid graph (Part I's `Graph.Valid`) with `n ≥ 1` vertices, `m = 3n + |E|`, and let `s_G`, `v_G` be the
sign vectors of the words `W^s_G`, `W^v_G` of Section 4 (Part I's `sG G`, `vG G`), and
`|D| = hamming m s_G v_G = |D(s_G, v_G)|`.  The ground set of the positive fibres is `[m] ∪ {∞} = [m+1]`, `∞ = m`.
`rank3_theorem` states:

1. `Pos₃(s_G)` and `Pos₃(v_G)` are uniform chirotopes of rank 3 on `[m+1]`;
2. (upper bound, chirotopes) for every vertex cover `C` there is a walk of chirotopes of length `|D| + 2|C|` from
   `Pos₃(s_G)` to `Pos₃(v_G)`;
3. (lower bound, chirotopes) every walk of chirotopes of length `k` between them yields a vertex cover `C` with
   `|D| + 2|C| ≤ k`;
4. (upper bound, mutation graph) for every vertex cover `C` there is a walk of length `|D| + 2|C|` in the mutation
   graph `G_{m+1,3}` from `[Pos₃(s_G)]` to `[Pos₃(v_G)]`;
5. (lower bound, mutation graph) if `n ≥ 3`, every walk of length `k` in the mutation graph from `[Pos₃(s_G)]` to
   `[Pos₃(v_G)]` yields a vertex cover `C` with `|D| + 2|C| ≤ k`;
6. `|D| = 3n(m-3) + 6|E|`.

## How this is Theorem 7.2
`d_t(Pos₃ s_G, Pos₃ v_G)` is the least `k` with a walk of chirotopes of length `k`, and the mutation distance
`d([Pos₃ s_G], [Pos₃ v_G])` the least `k` with `OMWalk (m+1) 3 (Pos₃ s_G) (Pos₃ v_G) k`.  For a minimum vertex
cover `C` (size `VC(G)`, `BraidDistance.exists_min_cover`), (2) and (4) give the upper bound `|D| + 2VC(G)` and (3),
(5) the lower bound, so `d_t = |D| + 2VC(G)` for every `G`, and `d = |D| + 2VC(G)` for `n ≥ 3`; Part I
(`BraidDistance.main_theorem`) gives `d_B(s_G, v_G) = d_br([W^s_G], [W^v_G]) = |D| + 2VC(G)`.  The paper states the
theorem for graphs with vertex set `[n]`; the hypothesis `n ≥ 1` only excludes the empty graph, for which the ground
set `[1]` has no bases.
-/

namespace OMDistance

open BraidDistance (Graph IsVertexCover hamming sG vG Ws Wv main_theorem)

/-- The vertices `0, …, n-2` form a vertex cover (every edge `uw`, `u < w < n`, has `u ≤ n - 2`). -/
theorem range_cover (G : Graph) (hG : G.Valid) : IsVertexCover G (List.range (G.n - 1)) := by
  refine ⟨List.nodup_range, fun v hv => by have := List.mem_range.1 hv; omega, fun e he => ?_⟩
  have := hG.2 e he
  exact Or.inl (List.mem_range.2 (by omega))

theorem sG_signotope (G : Graph) (hG : G.Valid) : IsSignotopeR G.m 3 (sMap G) :=
  isSignotopeR_ofSMap.2 (BraidDistance.Reduced.signotope (main_theorem G hG).1)

theorem vG_signotope (G : Graph) (hG : G.Valid) : IsSignotopeR G.m 3 (vMap G) :=
  isSignotopeR_ofSMap.2 (BraidDistance.Reduced.signotope (main_theorem G hG).2.1)

/-- Theorem 7.2, stated without minima (see the module docstring). -/
theorem rank3_theorem (G : Graph) (hG : G.Valid) (hn : 1 ≤ G.n) :
    IsChirotope (G.m + 1) 3 (posF G.m (sMap G)) ∧
    IsChirotope (G.m + 1) 3 (posF G.m (vMap G)) ∧
    (∀ C, IsVertexCover G C →
      ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G))
        (hamming G.m (sG G) (vG G) + 2 * C.length)) ∧
    (∀ k, ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) k →
      ∃ C, IsVertexCover G C ∧ hamming G.m (sG G) (vG G) + 2 * C.length ≤ k) ∧
    (∀ C, IsVertexCover G C →
      OMWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G))
        (hamming G.m (sG G) (vG G) + 2 * C.length)) ∧
    (3 ≤ G.n → ∀ k, OMWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) k →
      ∃ C, IsVertexCover G C ∧ hamming G.m (sG G) (vG G) + 2 * C.length ≤ k) ∧
    hamming G.m (sG G) (vG G) = 3 * G.n * (G.m - 3) + 6 * G.edges.length := by
  obtain ⟨_, _, _, hupw, _, _, hD⟩ := main_theorem G hG
  have hm : 3 ≤ G.m := by unfold Graph.m; omega
  have hup : ∀ C, IsVertexCover G C →
      ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G))
        (hamming G.m (sG G) (vG G) + 2 * C.length) :=
    fun C hC => sheet_b (by decide) hm (walk_to_sigWalk (hupw C hC))
  refine ⟨fibre_backward (by decide) hm (sG_signotope G hG), fibre_backward (by decide) hm (vG_signotope G hG),
    hup, fun k hw => prop_lower G hG hw, fun C hC => (hup C hC).toOM, ?_, hD⟩
  intro hn3 k hw
  rcases hw.toChiro with hw | hw
  · exact prop_lower G hG hw
  · refine ⟨List.range (G.n - 1), range_cover G hG, ?_⟩
    have h1 := hw.length_negR
    have h2 : hamR (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) = hamming G.m (sG G) (vG G) := by
      rw [hamR_posF, sMap, vMap, hamR_ofSMap]
    have h3 := rank3_far (rfl : G.m = 3 * G.n + G.edges.length) hn3
    have hD' : hamming G.m (sG G) (vG G) = 3 * G.n * (G.m - 3) + 6 * G.edges.length := hD
    rw [List.length_range]
    omega

/-- Theorem 7.2 with the vertex cover number: if `C₀` is a minimum vertex cover, then `|D| + 2|C₀|` is the least
length of a walk of chirotopes from `Pos₃(s_G)` to `Pos₃(v_G)` (that is, `d_t`), and, if `n ≥ 3`, the least length
of a walk in the mutation graph from `[Pos₃(s_G)]` to `[Pos₃(v_G)]` (that is, the mutation distance `d`). -/
theorem rank3_distance_eq (G : Graph) (hG : G.Valid) (hn : 1 ≤ G.n) {C₀ : List Nat} (hC₀ : IsVertexCover G C₀)
    (hmin : ∀ C, IsVertexCover G C → C₀.length ≤ C.length) :
    (ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) (hamming G.m (sG G) (vG G) + 2 * C₀.length) ∧
      ∀ k, ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) k →
        hamming G.m (sG G) (vG G) + 2 * C₀.length ≤ k) ∧
    (3 ≤ G.n →
      OMWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) (hamming G.m (sG G) (vG G) + 2 * C₀.length) ∧
      ∀ k, OMWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) k →
        hamming G.m (sG G) (vG G) + 2 * C₀.length ≤ k) := by
  obtain ⟨_, _, hup, hlo, hupO, hloO, _⟩ := rank3_theorem G hG hn
  refine ⟨⟨hup C₀ hC₀, fun k hw => ?_⟩, fun hn3 => ⟨hupO C₀ hC₀, fun k hw => ?_⟩⟩
  · obtain ⟨C, hC, hle⟩ := hlo k hw
    have := hmin C hC
    omega
  · obtain ⟨C, hC, hle⟩ := hloO hn3 k hw
    have := hmin C hC
    omega

end OMDistance
