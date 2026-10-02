import BraidDistance.StepDecomp
import BraidDistance.BeadFlip
import BraidDistance.BraidFlip
import BraidDistance.LocalReplace

/-!
# One step of the bead sweep (Lemma 4.5) and reducedness of all `W^ε_k`

* `step_path` (Lemma 4.5(b), braid moves): from `W^ε_k` to `W^ε_{k+1}` with `cost` braid moves, by lifting the
  local certificate (Lemma 2.7) into the decomposition of Lemma 4.5(a).
* `W_reduced` (Lemma 4.4): every `W^ε_k` is reduced, from `W^v_G` by bead flips and steps backwards.
* `step_sign` (Lemma 4.5(a), sign vectors): the sign vectors of `W^ε_k` and `W^ε_{k+1}` agree outside the triples
  of `Z`, and on `Z` they are those of the local words `L`, `L'` (Lemma 2.3).

This file is complete given the lemmas it imports.
-/

namespace BraidDistance

/-- Lemma 4.5(b): one step with `cost` braid moves. -/
theorem step_path (G : Graph) (hG : G.Valid) (eps : Nat → Bool) {k : Nat} (hk : k < numFactors G) :
    Path (W G k eps) (W G (k + 1) eps) (stepCase G k eps).cost := by
  obtain ⟨A, C, h1, h2, _⟩ := step_decomp G hG eps hk
  have hloc := ((localPath (stepCase G k eps)).shift (stepWindow G k)).context A C
  exact ((h1.trans hloc).trans h2.symm).cast (by omega)

/-- Lemma 4.4: every `W^ε_k` is reduced. -/
theorem W_reduced (G : Graph) (hG : G.Valid) {k : Nat} (hk : k ≤ numFactors G) (eps : Nat → Bool) :
    Reduced G.m (W G k eps) := by
  have hJ : Reduced G.m (W G (numFactors G) eps) := by
    have hC : ((List.range G.n).filter eps).Nodup := List.Sublist.nodup List.filter_sublist List.nodup_range
    have hCn : ∀ v ∈ (List.range G.n).filter eps, v < G.n := by
      intro v hv
      simp only [List.mem_filter, List.mem_range] at hv
      exact hv.1
    have hp := beads_cover G (numFactors G) _ hC hCn
    have heq : W G (numFactors G) (coverEps ((List.range G.n).filter eps)) = W G (numFactors G) eps := by
      apply W_congr
      intro u hu
      simp [coverEps, hu]
    rw [heq] at hp
    exact Path.reduced (Wv_reduced G hG) hp
  have key : ∀ j, j ≤ numFactors G → Reduced G.m (W G (numFactors G - j) eps) := by
    intro j
    induction j with
    | zero => intro _; simpa using hJ
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hp := step_path G hG eps (k := numFactors G - (j + 1)) (by omega)
      have : numFactors G - (j + 1) + 1 = numFactors G - j := by omega
      rw [this] at hp
      exact Path.reduced h1 hp.symm
  have := key (numFactors G - k) (by omega)
  rwa [show numFactors G - (numFactors G - k) = k by omega] at this

/-- `W^s_G` is reduced. -/
theorem Ws_reduced (G : Graph) (hG : G.Valid) : Reduced G.m (Ws G) :=
  W_reduced G hG (Nat.zero_le _) zeroEps

/-- Lemma 4.5(a), sign vectors. -/
theorem step_sign (G : Graph) (hG : G.Valid) (eps : Nat → Bool) {k : Nat} (hk : k < numFactors G) :
    (∀ t : Triple, ValidTriple G.m t → ¬ Inside (stepZ G k) t →
      (signVec G.m (W G (k + 1) eps)).at t = (signVec G.m (W G k eps)).at t) ∧
    Agree (stepCase G k eps).width (pull (stepZ G k) (signVec G.m (W G k eps)))
      (signVec (stepCase G k eps).width (stepCase G k eps).L) ∧
    Agree (stepCase G k eps).width (pull (stepZ G k) (signVec G.m (W G (k + 1) eps)))
      (signVec (stepCase G k eps).width (stepCase G k eps).L') := by
  obtain ⟨A, C, h1, h2, hz⟩ := step_decomp G hG eps hk
  have hWk := W_reduced G hG (Nat.le_of_lt hk) eps
  have hWk1 := W_reduced G hG (Nat.succ_le_of_lt hk) eps
  have hAL := Path.reduced hWk h1
  have hs1 := Path.zero_sign hWk h1
  have hs2 := Path.zero_sign hWk1 h2
  obtain ⟨hzinc, hzlen, _⟩ := stepZ_spec G hG hk eps
  have hcr := case_reduced (stepCase G k eps)
  have hout := (local_sign_outside hAL hcr.1 hcr.2 hz hzlen).2
  have hin := local_sign_inside hAL hcr.1 hz hzinc hzlen
  have hAL' := Path.reduced hWk1 h2
  have hin' := local_sign_inside hAL' hcr.2 hz hzinc hzlen
  refine ⟨?_, ?_, ?_⟩
  · intro t ht hnot
    rw [← hs1, ← hs2]
    exact hout t ht hnot
  · rw [← hs1]; exact hin
  · rw [← hs2]; exact hin'

end BraidDistance
