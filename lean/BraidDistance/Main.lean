import BraidDistance.UpperBound
import BraidDistance.LowerBound

/-!
# Theorem 5.4 (`\label{thm:wiring}`)

Let `G` be a valid graph on the vertices `0, …, n-1` (edges `(u, w)` with `u < w < n`, listed once), and let
`m = 3n + |E|`.  The construction of Section 4 gives two words `W^s_G = Ws G` and `W^v_G = Wv G` on `m` wires,
with sign vectors `s_G = signVec m (Ws G)` and `v_G = signVec m (Wv G)`; let `|D| = hamming m s_G v_G` be the
number of triples on which they differ.  `main_theorem` states, for every valid `G`:

1. `W^s_G` and `W^v_G` are reduced words of `w₀ ∈ S_m`;
2. (upper bound, words) for every vertex cover `C` there is a sequence of commutations and braid moves from
   `W^s_G` to `W^v_G` with exactly `|D| + 2|C|` braid moves;
3. (upper bound, signotopes) for every vertex cover `C` there is a walk in `B(m,2)` from `s_G` to `v_G` of length
   exactly `|D| + 2|C|`;
4. (lower bound, words) every sequence of commutations and braid moves from `W^s_G` to `W^v_G` with `k` braid
   moves admits a vertex cover `C` with `|D| + 2|C| ≤ k`;
5. (lower bound, signotopes) every walk of signotopes from `s_G` to `v_G` of length `k` admits a vertex cover `C`
   with `|D| + 2|C| ≤ k`;
6. (count) `|D| = 3n(m-3) + 6|E|`.

## How this is Theorem 5.4
The braid-move distance `d_br([W^s_G], [W^v_G])` is the least `k` with `Path (Ws G) (Wv G) k`, and
`d_B(s_G, v_G)` is the least `k` with `Walk m s_G v_G k`.  Taking for `C` a minimum vertex cover (size `VC(G)`),
(2) and (3) give `d_br, d_B ≤ |D| + 2 VC(G)`; (4) and (5) give, for every path or walk of length `k`, a cover `C`
with `|D| + 2 VC(G) ≤ |D| + 2|C| ≤ k`, so `d_br, d_B ≥ |D| + 2 VC(G)`.  Hence
`d_br([W^s_G],[W^v_G]) = d_B(s_G, v_G) = |D| + 2 VC(G)` with `|D| = 3n(m-3) + 6|E|` by (6).
`braid_distance_eq` states this for a minimum vertex cover, and `exists_min_cover` provides one.

The proof does not use the classical correspondence between commutation classes and signotopes
(Theorem 2.8): the upper bounds are explicit sequences of moves (local certificates checked by `decide`, lifted
into the words), and the lower bound for words goes through `d_B ≤ d_br` (`path_to_walk`).
-/

namespace BraidDistance

/-- Theorem 5.4, stated without minima: upper bounds for every vertex cover, lower bounds for every path and
every walk, and the size of `D`. -/
theorem main_theorem (G : Graph) (hG : G.Valid) :
    Reduced G.m (Ws G) ∧ Reduced G.m (Wv G) ∧
    (∀ C : List Nat, IsVertexCover G C →
      Path (Ws G) (Wv G)
        (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length)) ∧
    (∀ C : List Nat, IsVertexCover G C →
      Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G))
        (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length)) ∧
    (∀ k : Nat, Path (Ws G) (Wv G) k → ∃ C : List Nat, IsVertexCover G C ∧
      hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length ≤ k) ∧
    (∀ k : Nat, Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) k → ∃ C : List Nat,
      IsVertexCover G C ∧ hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C.length ≤ k) ∧
    hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) = 3 * G.n * (G.m - 3) + 6 * G.edges.length := by
  have hWs := Ws_reduced G hG
  have hWv : Reduced G.m (Wv G) := W_reduced G hG (Nat.le_refl _) zeroEps
  refine ⟨hWs, hWv, ?_, ?_, ?_, ?_, D_formula G hG⟩
  · intro C hC
    exact upper_path G hG hC
  · intro C hC
    exact path_to_walk hWs (upper_path G hG hC)
  · intro k hp
    exact lower_path G hG hp
  · intro k hw
    exact lower_walk G hG hw

/-- Every valid graph has a vertex cover of minimum size. -/
theorem exists_min_cover (G : Graph) (hG : G.Valid) :
    ∃ C₀, IsVertexCover G C₀ ∧ ∀ C, IsVertexCover G C → C₀.length ≤ C.length := by
  have hfull : IsVertexCover G (List.range G.n) :=
    ⟨List.nodup_range, fun v hv => List.mem_range.mp hv,
      fun e he => Or.inl (List.mem_range.mpr (by have := hG.2 e he; omega))⟩
  have key : ∀ k, (∃ C, IsVertexCover G C ∧ C.length ≤ k) →
      ∃ C₀, IsVertexCover G C₀ ∧ ∀ C, IsVertexCover G C → C₀.length ≤ C.length := by
    intro k
    induction k with
    | zero =>
      intro ⟨C, hC, hlen⟩
      exact ⟨C, hC, fun _ _ => by omega⟩
    | succ k ih =>
      intro ⟨C, hC, hlen⟩
      by_cases h : ∃ C', IsVertexCover G C' ∧ C'.length ≤ k
      · exact ih h
      · refine ⟨C, hC, fun C' hC' => ?_⟩
        have : ¬ C'.length ≤ k := fun h' => h ⟨C', hC', h'⟩
        omega
  exact key _ ⟨_, hfull, Nat.le_refl _⟩

/-- Theorem 5.4 with the vertex cover number: if `C₀` is a minimum vertex cover, then `|D| + 2|C₀|` is the
least number of braid moves of a sequence from `W^s_G` to `W^v_G` (that is, `d_br`), and the least length of a
walk of signotopes from `s_G` to `v_G` (that is, `d_B`). -/
theorem braid_distance_eq (G : Graph) (hG : G.Valid) {C₀ : List Nat} (hC₀ : IsVertexCover G C₀)
    (hmin : ∀ C, IsVertexCover G C → C₀.length ≤ C.length) :
    (Path (Ws G) (Wv G) (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C₀.length) ∧
      ∀ k, Path (Ws G) (Wv G) k →
        hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C₀.length ≤ k) ∧
    (Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G))
        (hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C₀.length) ∧
      ∀ k, Walk G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) k →
        hamming G.m (signVec G.m (Ws G)) (signVec G.m (Wv G)) + 2 * C₀.length ≤ k) := by
  obtain ⟨_, _, hup, hupw, hlo, hlow, _⟩ := main_theorem G hG
  refine ⟨⟨hup C₀ hC₀, fun k hp => ?_⟩, ⟨hupw C₀ hC₀, fun k hw => ?_⟩⟩
  · obtain ⟨C, hC, hle⟩ := hlo k hp
    have := hmin C hC
    omega
  · obtain ⟨C, hC, hle⟩ := hlow k hw
    have := hmin C hC
    omega

end BraidDistance
