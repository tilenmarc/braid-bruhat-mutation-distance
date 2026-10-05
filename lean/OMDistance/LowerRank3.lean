import OMDistance.GadgetChiro
import OMDistance.GadgetGeometry
import OMDistance.ChargingT

/-!
# Proposition 7.1: the lower bound for walks of chirotopes

Every walk of chirotopes on `[m] ∪ {∞}` from `Pos₃(s_G)` to `Pos₃(v_G)` of length `k` admits a vertex cover `C`
with `|D| + 2|C| ≤ k`, where `|D| = |D(s_G, v_G)|`.

Proof (as in the paper): let `Y` be the set of bases flipped more often than necessary.
* Every gadget contains a basis of `Y`: restricting the walk to `A_e ∪ {∞}` (Lemma 6.6, `rwalk_pullback`-style
  via `flipWalk_pullback`) gives a walk from `Pos₃ g^s` to `Pos₃ g^v`, which flips some basis more often than
  necessary (`gadget_chiro_extra`); its image lies in `Y` and inside `A_e ∪ {∞}`.
* The charging argument (`charging_abstract`, with the sets `𝒯_u`) gives a vertex cover `C` and a duplicate-free
  list `Ys ⊆ Y` with `|C| ≤ |Ys|`.
* Lemma 2.5 (`parity_boundR`) gives `|D| + 2|Ys| ≤ k`.
-/

namespace OMDistance

open BraidDistance (Graph IsVertexCover hamming sG vG gs gv)

/-- Proposition 7.1. -/
theorem prop_lower (G : Graph) (hG : G.Valid) {k : Nat}
    (hw : ChiroWalk (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) k) :
    ∃ C, IsVertexCover G C ∧ hamming G.m (sG G) (vG G) + 2 * C.length ≤ k := by
  obtain ⟨Xs, hlen, hfw, hend⟩ := rwalk_to_flips (isChirotope_agreeInv _ _) hw
  let χs := posF G.m (sMap G)
  let χv := posF G.m (vMap G)
  let inY : List Nat → Bool := fun B => decide ((if χs B = χv B then 0 else 1) < Xs.count B)
  -- every gadget contains a basis of `Y`
  have hgad : ∀ e ∈ G.edges, ∃ B, IsRSet (G.m + 1) 3 B ∧ InGadget G e B ∧ inY B = true := by
    intro e he
    obtain ⟨hz, hz8, hzM⟩ := gadgetZ_spec G hG he
    let φ : List Nat → List Nat := fun X => X.map fun i => (gadgetZ G e).getD i 0
    have hφ : Relabel 8 3 (G.m + 1) 3 φ := hz8 ▸ relabel_restrict hz hzM
    have hPQ : ∀ u, IsChirotope (G.m + 1) 3 u → IsChirotope 8 3 (fun X => u (φ X)) := by
      intro u hu
      have := restrictR_chirotope hz hzM (by rw [hz8]; decide) hu
      rw [hz8] at this
      exact this
    have hfw' := flipWalk_pullback hφ hPQ (isChirotope_agreeInv 8 3) hfw
    obtain ⟨hrs, hrv⟩ := gadgetZ_restrict G hG he
    have hstart : AgreeR 8 3 (fun X => χs (φ X)) (posF 7 (ofSMap gs)) := hrs
    have hfin : AgreeR 8 3 (flipsR (fun X => χs (φ X)) (preimages 8 3 φ Xs)) (posF 7 (ofSMap gv)) := by
      refine (flipsR_pullback hφ χs Xs).symm.trans (AgreeR.trans ?_ hrv)
      intro X hX
      exact hend (φ X) (hφ.1 X hX)
    obtain ⟨X, hX, hc⟩ := gadget_chiro_extra hfw' hstart hfin
    refine ⟨φ X, hφ.1 X hX, restrict_inGadget G hG he hX, ?_⟩
    have hcount := count_preimages hφ Xs hX
    have e1 : χs (φ X) = posF 7 (ofSMap gs) X := hrs X hX
    have e2 : χv (φ X) = posF 7 (ofSMap gv) X := hrv X hX
    simp only [inY, decide_eq_true_eq]
    rw [e1, e2, ← hcount]
    exact hc
  obtain ⟨C, Ys, hC, hYnd, hYs, hle⟩ := charging_abstract G hG (IsRSet (G.m + 1) 3) inY (InGadget G)
    (bigT G) hgad (fun u hu => bigT_valid G hG hu) (fun u w hu hw B h₁ h₂ => bigT_disjoint G hG hu hw h₁ h₂)
    (fun e he B hB x hx hBx => bigT_inGadget G hG he hB hx hBx)
    (fun e he f hf hef B hB h₁ h₂ => gadget_overlap G hG he hf hef hB h₁ h₂)
  refine ⟨C, hC, ?_⟩
  have hb := parity_boundR hfw.1 hend Ys hYnd (fun B hB => (hYs B hB).1) (fun B hB => by
    have := (hYs B hB).2
    simpa [inY] using this)
  have hD : hamR (G.m + 1) 3 (posF G.m (sMap G)) (posF G.m (vMap G)) = hamming G.m (sG G) (vG G) := by
    rw [hamR_posF, sMap, vMap, hamR_ofSMap]
  omega

end OMDistance
