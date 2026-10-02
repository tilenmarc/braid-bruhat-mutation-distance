import BraidDistance.StepLemma
import BraidDistance.SweepCount
import BraidDistance.HammingParity

/-!
# The difference set of `s_G` and `v_G` (Corollary 4.6)

Along the chain `W^0_0, W^0_1, …, W^0_J` (all beads of type `β`), a triple changes sign at the step `k` only if
it lies inside the wires `Z_k` of the `k`-th factor and is not a bead triple (`step_sign`, `case_bead`).  Two
different factors share no such triple (`factor_overlap`), so every triple changes at most once, and
`|D| = ∑_k |D_k| = ∑_k evHam = 3n(m-3) + 6|E|` (Corollary 4.6(b)).  The triples inside a gadget `A_e` change
only at the cell of `e`, where the restrictions are `g^s` and `g^v` (Corollary 4.6(a)).

This file is complete given the lemmas it imports.
-/

namespace BraidDistance

/-- The sign vector after the first `k` factors, all beads of type `β`. -/
def chainSig (G : Graph) (k : Nat) : SMap := signVec G.m (W G k zeroEps)

/-- A triple that changes at step `k` lies inside `Z_k` and is not a bead triple. -/
theorem step_changes (G : Graph) (hG : G.Valid) {k : Nat} (hk : k < numFactors G) {t : Triple}
    (ht : ValidTriple G.m t) (hch : (chainSig G k).at t ≠ (chainSig G (k + 1)).at t) :
    Inside (stepZ G k) t ∧ ∀ u, u < G.n → t ≠ beadTriple G u := by
  obtain ⟨hout, hin, hin'⟩ := step_sign G hG zeroEps hk
  have hinside : Inside (stepZ G k) t := by
    apply Classical.byContradiction
    intro hnot
    exact hch (hout t ht hnot).symm
  refine ⟨hinside, ?_⟩
  intro u hu hbt
  subst hbt
  obtain ⟨t', ht'mem, hemb⟩ := bead_in_factor G hG hk zeroEps hu hinside
  have hv' := case_beadTriples_valid _ t' ht'mem
  have hb := case_bead _ t' ht'mem
  have e1 := hin.at hv'
  have e2 := hin'.at hv'
  simp only [pull_at, hemb] at e1 e2
  exact hch (by unfold chainSig; rw [e1, e2, hb])

/-- A triple inside `Z_{k₀}` does not change at any other step. -/
theorem no_change_other (G : Graph) (hG : G.Valid) {k₀ j : Nat} (hk₀ : k₀ < numFactors G)
    (hj : j < numFactors G) (hne : j ≠ k₀) {t : Triple} (ht : ValidTriple G.m t)
    (hin : Inside (stepZ G k₀) t) : (chainSig G j).at t = (chainSig G (j + 1)).at t := by
  apply Classical.byContradiction
  intro hch
  obtain ⟨hinj, hnb⟩ := step_changes G hG hj ht hch
  obtain ⟨u, hu, rfl⟩ := factor_overlap G hG hj hk₀ hne ht hinj hin
  exact hnb u hu rfl

/-- Constancy over a range of steps. -/
theorem chain_const (us : Nat → SMap) (t : Triple) {i j : Nat} (hij : i ≤ j)
    (h : ∀ l, i ≤ l → l < j → (us l).at t = (us (l + 1)).at t) : (us i).at t = (us j).at t := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; rfl
  | succ j ih =>
    by_cases hij' : i ≤ j
    · rw [ih hij' (fun l h1 h2 => h l h1 (by omega))]
      exact h j hij' (by omega)
    · have : i = j + 1 := by omega
      subst this; rfl

/-- A list without two different elements has at most one element. -/
theorem length_le_one_of_eq {l : List Nat} (hnd : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a = b) :
    l.length ≤ 1 := by
  match l, hnd, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: rest, hnd, h =>
    have hab : a = b := h a (by simp) b (by simp)
    have : a ∉ b :: rest := (List.nodup_cons.mp hnd).1
    exact absurd (hab ▸ List.mem_cons_self) this

/-- Corollary 4.6(b): `|D| = ∑_k |D_k|`. -/
theorem count_D (G : Graph) (hG : G.Valid) :
    hamming G.m (sG G) (vG G) = ((sweepEvents G).map evHam).sum := by
  have hchain := hamming_chain G.m (numFactors G) (chainSig G) (by
    intro t ht
    apply length_le_one_of_eq (List.Sublist.nodup List.filter_sublist List.nodup_range)
    intro a ha b hb
    simp only [List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at ha hb
    apply Classical.byContradiction
    intro hab
    obtain ⟨hina, _⟩ := step_changes G hG ha.1 ht ha.2
    exact hb.2 (no_change_other G hG ha.1 hb.1 (fun h => hab h.symm) ht hina))
  have hterm : ∀ k ∈ List.range (numFactors G),
      hamming G.m (chainSig G k) (chainSig G (k + 1)) = evHam (evAt G k) := by
    intro k hk
    rw [List.mem_range] at hk
    unfold chainSig
    obtain ⟨hout, hin, hin'⟩ := step_sign G hG zeroEps hk
    obtain ⟨hzinc, hzlen, hzm⟩ := stepZ_spec G hG hk zeroEps
    rw [hamming_pull hzinc hzm (fun t ht hnot => (hout t ht hnot).symm), hzlen,
      hamming_congr hin hin', case_ham, stepCase, caseOf_ham]
  have hsum := congrArg List.sum (List.map_congr_left hterm)
  rw [sum_range_evAt] at hsum
  show hamming G.m (chainSig G 0) (chainSig G (numFactors G)) = _
  rw [hchain, hsum]

/-- Corollary 4.6(b): `|D| = 3n(m-3) + 6|E|`. -/
theorem D_formula (G : Graph) (hG : G.Valid) :
    hamming G.m (sG G) (vG G) = 3 * G.n * (G.m - 3) + 6 * G.edges.length := by
  rw [count_D G hG, sweep_ham_sum G hG]

/-- Corollary 4.6(a): the restrictions of `s_G` and `v_G` to a gadget are `g^s` and `g^v`. -/
theorem edge_restrict (G : Graph) (hG : G.Valid) {e : Nat × Nat} (he : e ∈ G.edges) :
    Agree 7 (pull (edgeWires G e.1 e.2) (sG G)) gs ∧ Agree 7 (pull (edgeWires G e.1 e.2) (vG G)) gv := by
  obtain ⟨k, hk, hev⟩ := cell_step G hG he
  have hz : stepZ G k = edgeWires G e.1 e.2 := by simp [stepZ, hev, evZ]
  have hcase : stepCase G k zeroEps = .cell false false := by simp [stepCase, hev, caseOf, zeroEps]
  obtain ⟨_, hin, hin'⟩ := step_sign G hG zeroEps hk
  rw [hz, hcase] at hin hin'
  obtain ⟨hzinc, _, hzm⟩ := edgeWires_spec G hG he
  -- triples inside `A_e` change only at step `k`
  have hconst : ∀ t : Triple, ValidTriple 7 t →
      (chainSig G 0).at (embT (edgeWires G e.1 e.2) t) = (chainSig G k).at (embT (edgeWires G e.1 e.2) t) ∧
      (chainSig G (k + 1)).at (embT (edgeWires G e.1 e.2) t) =
        (chainSig G (numFactors G)).at (embT (edgeWires G e.1 e.2) t) := by
    intro t ht
    have ht' : ValidTriple (edgeWires G e.1 e.2).length t := by
      rw [(edgeWires_spec G hG he).2.1]; exact ht
    obtain ⟨hval, hins₀⟩ := embT_valid hzinc hzm ht'
    have hins : Inside (stepZ G k) (embT (edgeWires G e.1 e.2) t) := by rw [hz]; exact hins₀
    constructor
    · exact chain_const (chainSig G) _ (Nat.zero_le _)
        (fun l _ hl => no_change_other G hG hk (by omega) (by omega) hval hins)
    · exact chain_const (chainSig G) _ (by omega)
        (fun l hl1 hl2 => no_change_other G hG hk hl2 (by omega) hval hins)
  constructor
  · intro a b c hab hbc hc
    have h1 := (hconst (a, b, c) ⟨hab, hbc, hc⟩).1
    have h2 := hin a b c hab hbc hc
    simp only [pull, SMap.at, embT, chainSig] at h1 h2 ⊢
    rw [show sG G = signVec G.m (W G 0 zeroEps) from rfl, h1, h2]
    rfl
  · intro a b c hab hbc hc
    have h1 := (hconst (a, b, c) ⟨hab, hbc, hc⟩).2
    have h2 := hin' a b c hab hbc hc
    simp only [pull, SMap.at, embT, chainSig] at h1 h2 ⊢
    rw [show vG G = signVec G.m (W G (numFactors G) zeroEps) from rfl, ← h1, h2]
    rfl

end BraidDistance
