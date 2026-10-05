import OMDistance.Excess
import OMDistance.MainRank3
import OMDistance.ArithRatio
import OMDistance.ArithFar

/-!
# Theorem 8.6 and Corollary 8.7 (`\label{thm:allranks}`, `\label{cor:hbo}`), without the complexity statements

Let `G` be a valid graph with `n ≥ 1` vertices and `m = 3n + |E|` wires, `s = s_G`, `v = v_G` (Part I), `r ≥ 4`,
`q = r - 3`, and let `c ≥ q` new elements `N = [c]` be placed below `S = {c, …, c+m-1}` (the element `i` of `[m]` is
`c + i`), with `∞ = c + m`.  Write `L s = lift c (sMap G)`, `L v = lift c (vMap G)` (rank `r` on `[c+m]`),
`Pos_r(L s) = posF (c+m) (L s)` (on `[c+m+1]`), `H = |D(L s, L v)|`, `λ = binom(c, q)`, `μ = binom(c+m-3, q)`.

`higher_rank_theorem` is the chain `H + 2λ VC(G) ≤ d_t(Pos_r L s, Pos_r L v) ≤ d_B(L s, L v) ≤ H + 2μ VC(G)` of the
proofs of Theorem 8.6 and Corollary 8.7, without minima:
1. `L s`, `L v` are signotopes of rank `r`, and `Pos_r(L s)`, `Pos_r(L v)` are uniform chirotopes of rank `r`;
2. (upper bounds) for every vertex cover `C` there is a walk in `B(N ∪ S, r-1)` from `L s` to `L v`, which is also a
   walk of chirotopes between the positive fibres, of length `≤ H + 2μ|C|`;
3. (lower bounds) every walk in `B(N ∪ S, r-1)` and every walk of chirotopes between them, of length `ℓ`, yields a
   vertex cover `C` with `H + 2λ|C| ≤ ℓ`.

The reductions (`hbo_reduction`, `chiro_reduction`, `allranks_reduction`) are the equivalences in the proofs of
Corollary 8.7 and Theorem 8.6: for `n ≥ 2`, `k ≥ 1`, `c = q m (k+1) + q` and `K = H + 2μk`, a walk of length
`≤ K` exists — in `B(N ∪ S, r-1)` between the lifts, of chirotopes between their positive fibres, or in the mutation
graph `G_{c+m+1, r}` between `[Pos_r L s]` and `[Pos_r L v]` — if and only if `G` has a vertex cover with at most `k`
vertices.  Only the reduction for the mutation graph assumes `k ≤ n`, as in the paper; the other two do not need
it.  The polynomial-time computability of the instances (the NP-hardness itself) is not formalized.

## How this is Theorem 8.6 / Corollary 8.7
Taking for `C` a minimum vertex cover in (2) and (3) gives the chain above.  The equivalences say that the distance
(`d_B`, `d_t`, or the mutation distance `d`) is at most `K` iff `VC(G) ≤ k`, which is the reduction from
`VERTEX COVER` used for NP-hardness.
-/

namespace OMDistance

open BraidDistance (Graph IsVertexCover hamming sG vG main_theorem)

/-- Theorem 8.6 / Corollary 8.7: the chain of bounds, stated without minima. -/
theorem higher_rank_theorem (G : Graph) (hG : G.Valid) (hn : 1 ≤ G.n) {r c : Nat} (hr : 4 ≤ r)
    (hc : r - 3 ≤ c) :
    IsSignotopeR (c + G.m) r (lift c (sMap G)) ∧ IsSignotopeR (c + G.m) r (lift c (vMap G)) ∧
    IsChirotope (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) ∧
    IsChirotope (c + G.m + 1) r (posF (c + G.m) (lift c (vMap G))) ∧
    (∀ C, IsVertexCover G C → ∃ ℓ,
      ℓ ≤ hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) +
        2 * binom (c + G.m - 3) (r - 3) * C.length ∧
      SigWalk (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) ℓ ∧
      ChiroWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) (posF (c + G.m) (lift c (vMap G))) ℓ) ∧
    (∀ ℓ, SigWalk (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) ℓ → ∃ C, IsVertexCover G C ∧
      hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom c (r - 3) * C.length ≤ ℓ) ∧
    (∀ ℓ, ChiroWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) (posF (c + G.m) (lift c (vMap G))) ℓ →
      ∃ C, IsVertexCover G C ∧
        hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom c (r - 3) * C.length ≤ ℓ) := by
  have hm : 3 ≤ G.m := by unfold Graph.m; omega
  obtain ⟨hLs, hLv, hlow, hmid, hupp⟩ := prop_excess hm hr hc (sG_signotope G hG) (vG_signotope G hG)
  have hh : hamR G.m 3 (sMap G) (vMap G) = hamming G.m (sG G) (vG G) := hamR_ofSMap _ _ _
  have hchiro : ∀ ℓ, ChiroWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G)))
      (posF (c + G.m) (lift c (vMap G))) ℓ → ∃ C, IsVertexCover G C ∧
        hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom c (r - 3) * C.length ≤ ℓ := by
    intro ℓ hw
    obtain ⟨k, hk, hineq⟩ := hlow ℓ hw
    obtain ⟨C, hC, hCk⟩ := prop_lower G hG hk
    refine ⟨C, hC, ?_⟩
    have h1 := Nat.mul_le_mul_left (binom c (r - 3)) hCk
    have h2 : binom c (r - 3) * (2 * C.length) = 2 * binom c (r - 3) * C.length := by
      rw [← Nat.mul_assoc, Nat.mul_comm (binom c (r - 3)) 2]
    rw [Nat.mul_add] at h1
    rw [hh] at hineq
    omega
  refine ⟨hLs, hLv, fibre_backward (by omega) (by omega) hLs, fibre_backward (by omega) (by omega) hLv, ?_,
    fun ℓ hw => hchiro ℓ (hmid ℓ hw), hchiro⟩
  intro C hC
  have hw3 : SigWalk G.m 3 (sMap G) (vMap G) (hamming G.m (sG G) (vG G) + 2 * C.length) :=
    walk_to_sigWalk ((main_theorem G hG).2.2.2.1 C hC)
  obtain ⟨ℓ, hℓ, hineq⟩ := hupp _ hw3
  refine ⟨ℓ, ?_, hℓ, hmid ℓ hℓ⟩
  have h2 : binom (c + G.m - 3) (r - 3) * (2 * C.length) = 2 * binom (c + G.m - 3) (r - 3) * C.length := by
    rw [← Nat.mul_assoc, Nat.mul_comm (binom (c + G.m - 3) (r - 3)) 2]
  rw [Nat.mul_add, hh] at hineq
  omega

/-- The number `K = H + 2μk` of the reductions. -/
private theorem K_mono {μ a b : Nat} (h : a ≤ b) : 2 * μ * a ≤ 2 * μ * b := Nat.mul_le_mul_left _ h

/-- The separation: a vertex cover `C` with `H + 2λ|C| ≤ H + 2μk` has at most `k` vertices, by
`μ k < λ (k+1)` for `c = q m (k+1) + q`. -/
private theorem cover_small {m k q H : Nat} (hq : 1 ≤ q) (hk : 1 ≤ k) {C : List Nat}
    (h : H + 2 * binom (q * m * (k + 1) + q) q * C.length ≤
      H + 2 * binom (q * m * (k + 1) + q + m - 3) q * k) : C.length ≤ k := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h1 := ratio_bound (m := m) hq hk
  have h2 := Nat.mul_le_mul_left (binom (q * m * (k + 1) + q) q) (show k + 1 ≤ C.length from hlt)
  have e1 : 2 * binom (q * m * (k + 1) + q) q * C.length = 2 * (binom (q * m * (k + 1) + q) q * C.length) :=
    Nat.mul_assoc _ _ _
  have e2 : 2 * binom (q * m * (k + 1) + q + m - 3) q * k = 2 * (binom (q * m * (k + 1) + q + m - 3) q * k) :=
    Nat.mul_assoc _ _ _
  omega

/-- Corollary 8.7, the reduction: for `n ≥ 2`, `k ≥ 1` and `c = q m (k+1) + q`, there is a walk of length at most
`K = H + 2μk` in `B(N ∪ S, r-1)` from `L s_G` to `L v_G` iff `G` has a vertex cover with at most `k` vertices. -/
theorem hbo_reduction (G : Graph) (hG : G.Valid) (hn : 2 ≤ G.n) {r k c : Nat} (hr : 4 ≤ r) (hk : 1 ≤ k)
    (hcdef : c = (r - 3) * G.m * (k + 1) + (r - 3)) :
    (∃ ℓ, ℓ ≤ hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom (c + G.m - 3) (r - 3) * k ∧
        SigWalk (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) ℓ) ↔
      ∃ C, IsVertexCover G C ∧ C.length ≤ k := by
  have hc : r - 3 ≤ c := by subst hcdef; omega
  obtain ⟨_, _, _, _, hup, hlowB, _⟩ := higher_rank_theorem G hG (by omega) hr hc
  constructor
  · rintro ⟨ℓ, hℓ, hw⟩
    obtain ⟨C, hC, hCℓ⟩ := hlowB ℓ hw
    refine ⟨C, hC, ?_⟩
    subst hcdef
    exact cover_small (by omega) hk (Nat.le_trans hCℓ hℓ)
  · rintro ⟨C, hC, hCk⟩
    obtain ⟨ℓ, hℓ, hw, _⟩ := hup C hC
    exact ⟨ℓ, Nat.le_trans hℓ (Nat.add_le_add_left (K_mono hCk) _), hw⟩

/-- The same reduction for walks of chirotopes between `Pos_r(L s_G)` and `Pos_r(L v_G)`. -/
theorem chiro_reduction (G : Graph) (hG : G.Valid) (hn : 2 ≤ G.n) {r k c : Nat} (hr : 4 ≤ r) (hk : 1 ≤ k)
    (hcdef : c = (r - 3) * G.m * (k + 1) + (r - 3)) :
    (∃ ℓ, ℓ ≤ hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom (c + G.m - 3) (r - 3) * k ∧
        ChiroWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) (posF (c + G.m) (lift c (vMap G))) ℓ) ↔
      ∃ C, IsVertexCover G C ∧ C.length ≤ k := by
  have hc : r - 3 ≤ c := by subst hcdef; omega
  obtain ⟨_, _, _, _, hup, _, hlowC⟩ := higher_rank_theorem G hG (by omega) hr hc
  constructor
  · rintro ⟨ℓ, hℓ, hw⟩
    obtain ⟨C, hC, hCℓ⟩ := hlowC ℓ hw
    refine ⟨C, hC, ?_⟩
    subst hcdef
    exact cover_small (by omega) hk (Nat.le_trans hCℓ hℓ)
  · rintro ⟨C, hC, hCk⟩
    obtain ⟨ℓ, hℓ, _, hw⟩ := hup C hC
    exact ⟨ℓ, Nat.le_trans hℓ (Nat.add_le_add_left (K_mono hCk) _), hw⟩

/-- Theorem 8.6, the reduction: for `n ≥ 2`, `1 ≤ k ≤ n` and `c = q m (k+1) + q`, there is a walk of length at most
`K = H + 2μk` in the mutation graph `G_{c+m+1, r}` from `[Pos_r(L s_G)]` to `[Pos_r(L v_G)]` iff `G` has a vertex
cover with at most `k` vertices.  A walk ending at `-Pos_r(L v_G)` is too long, since `-Pos_r(L v_G)` differs from
`Pos_r(L s_G)` on all but `H` of the `binom(c+m+1, r)` bases and `binom(c+m+1, r) - H > K`. -/
theorem allranks_reduction (G : Graph) (hG : G.Valid) (hn : 2 ≤ G.n) {r k c : Nat} (hr : 4 ≤ r) (hk : 1 ≤ k)
    (hkn : k ≤ G.n) (hcdef : c = (r - 3) * G.m * (k + 1) + (r - 3)) :
    (∃ ℓ, ℓ ≤ hamR (c + G.m) r (lift c (sMap G)) (lift c (vMap G)) + 2 * binom (c + G.m - 3) (r - 3) * k ∧
        OMWalk (c + G.m + 1) r (posF (c + G.m) (lift c (sMap G))) (posF (c + G.m) (lift c (vMap G))) ℓ) ↔
      ∃ C, IsVertexCover G C ∧ C.length ≤ k := by
  rw [← chiro_reduction G hG hn hr hk hcdef]
  constructor
  · rintro ⟨ℓ, hℓ, hw⟩
    rcases hw.toChiro with hw | hw
    · exact ⟨ℓ, hℓ, hw⟩
    · exfalso
      have hm : 6 ≤ G.m := by unfold Graph.m; omega
      obtain ⟨q, rfl⟩ : ∃ q, r = q + 3 := ⟨r - 3, by omega⟩
      have hq : q + 3 - 3 = q := by omega
      rw [hq] at hcdef hℓ
      subst hcdef
      have h1 := hw.length_negR
      rw [hamR_posF] at h1
      have h2 := far_bound (m := G.m) (by omega : 1 ≤ q) (by omega) hk
      have h3 := binom_mono (q + 3) (Nat.le_add_right (q * G.m * (k + 1) + q + G.m) 1)
      have h4 := hamR_lift_le G.m (q * G.m * (k + 1) + q) q (sMap G) (vMap G)
      have h5 := Nat.mul_le_mul_left (binom (q * G.m * (k + 1) + q + G.m - 3) q)
        (hamR_le_binom G.m 3 (sMap G) (vMap G))
      have h6 := Nat.mul_le_mul_left (binom (q * G.m * (k + 1) + q + G.m - 3) q)
        (Nat.le_trans hkn (Nat.le_trans (by unfold Graph.m; omega : G.n ≤ G.m) (le_binom_three (by omega))))
      have e1 : 4 * binom (q * G.m * (k + 1) + q + G.m - 3) q * binom G.m 3 =
          4 * (binom (q * G.m * (k + 1) + q + G.m - 3) q * binom G.m 3) := Nat.mul_assoc _ _ _
      have e2 : 2 * binom (q * G.m * (k + 1) + q + G.m - 3) q * k =
          2 * (binom (q * G.m * (k + 1) + q + G.m - 3) q * k) := Nat.mul_assoc _ _ _
      omega
  · rintro ⟨ℓ, hℓ, hw⟩
    exact ⟨ℓ, hℓ, hw.toOM⟩

end OMDistance
