import OMDistance.ChiroSetForm
import OMDistance.WalkLemmas

/-!
# Basic facts about uniform chirotopes

* Being a chirotope depends only on the values on bases (`isChirotope_agreeInv`).
* `-χ` is a chirotope if `χ` is (each factor of (GP) changes sign, the products do not).
-/

namespace OMDistance

/-- For an `(r-2)`-subset `σ` of `[M]` and distinct `x, y ∈ [M] ∖ σ`, the set `σ ∪ {x, y}` is a basis. -/
private theorem isRSet_isort_pair {M r : Nat} {σ : List Nat} (hr : 2 ≤ r) (hσ : IsRSet M (r - 2) σ)
    {x y : Nat} (hx : x < M) (hy : y < M) (hxy : x ≠ y) (hxσ : x ∉ σ) (hyσ : y ∉ σ) :
    IsRSet M r (isort (σ ++ [x, y])) := by
  have hnd : (σ ++ [x, y]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hσ.nodup, ?_, ?_⟩
    · simp [hxy]
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact fun h => hxσ (h ▸ ha)
      · exact fun h => hyσ (h ▸ ha)
  refine ⟨?_, isort_strictIncr hnd, ?_⟩
  · rw [length_isort]
    simp [hσ.1]
    omega
  · intro z hz
    rw [mem_isort] at hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | rfl | rfl
    · exact hσ.2.2 z hz
    · exact hx
    · exact hy

/-- `χ(σ, x, y)` depends only on the value of `χ` at the set `σ ∪ {x, y}`. -/
private theorem chiPair_congr {u u' : SignMap} {σ : List Nat} {x y : Nat}
    (h : u (isort (σ ++ [x, y])) = u' (isort (σ ++ [x, y]))) : chiPair u σ x y = chiPair u' σ x y := by
  unfold chiPair tupleVal
  rw [h]

/-- Being a uniform chirotope depends only on the values on the bases. -/
theorem isChirotope_agreeInv (M r : Nat) : AgreeInv M r (IsChirotope M r) := by
  intro u u' hag ⟨h2, hM, hgp⟩
  refine ⟨h2, hM, ?_⟩
  intro σ hσ d hd c hc b hb a ha haσ hbσ hcσ hdσ
  have key : ∀ x y, x < M → y < M → x ≠ y → x ∉ σ → y ∉ σ → chiPair u σ x y = chiPair u' σ x y :=
    fun x y hx hy hxy hxσ hyσ => chiPair_congr (hag _ (isRSet_isort_pair h2 hσ hx hy hxy hxσ hyσ))
  have H := hgp σ hσ d hd c hc b hb a ha haσ hbσ hcσ hdσ
  unfold GP at H ⊢
  rw [key a b (by omega) (by omega) (by omega) haσ hbσ, key a c (by omega) (by omega) (by omega) haσ hcσ,
    key a d (by omega) (by omega) (by omega) haσ hdσ, key b c (by omega) (by omega) (by omega) hbσ hcσ,
    key b d (by omega) (by omega) (by omega) hbσ hdσ, key c d (by omega) (by omega) (by omega) hcσ hdσ] at H
  exact H

/-- `(-χ)(σ, x, y) = -χ(σ, x, y)`. -/
private theorem chiPair_negR (χ : SignMap) (σ : List Nat) (x y : Nat) :
    chiPair (OMDistance.negR χ) σ x y = !chiPair χ σ x y := by
  unfold chiPair tupleVal OMDistance.negR
  split <;> rfl

private theorem smul_not_not (x y : Bool) : smul (!x) (!y) = smul x y := by
  revert x y; decide

/-- `-χ` is a uniform chirotope if `χ` is. -/
theorem IsChirotope.negR {M r : Nat} {χ : SignMap} (h : IsChirotope M r χ) :
    IsChirotope M r (OMDistance.negR χ) := by
  obtain ⟨h2, hM, hgp⟩ := h
  refine ⟨h2, hM, ?_⟩
  intro σ hσ d hd c hc b hb a ha haσ hbσ hcσ hdσ
  have H := hgp σ hσ d hd c hc b hb a ha haσ hbσ hcσ hdσ
  unfold GP at H ⊢
  simp only [chiPair_negR, smul_not_not]
  exact H

end OMDistance
