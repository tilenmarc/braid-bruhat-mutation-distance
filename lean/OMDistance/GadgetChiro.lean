import OMDistance.Sheet
import OMDistance.Bridge3
import BraidDistance.GadgetLower
import BraidDistance.LocalCases

/-!
# The gadget on eight elements (the first step of Proposition 7.1)

The gadget sign vectors `g^s, g^v` live on the seven wires `[7]`; their positive fibres `Pos₃ g^s`, `Pos₃ g^v` live
on `[8]` with `∞ = 7`.  Every walk of chirotopes from `Pos₃ g^s` to `Pos₃ g^v` flips some basis more often than
necessary (`gadget_chiro_extra`).

Proof: otherwise the walk has length exactly `|D_κ| = 30` (Lemma 2.5), so by Lemma 6.10(a) it is a walk of length
`30` in `B(7,2)` from `g^s` to `g^v`, which Lemma 3.3 (`BraidDistance.gadget_lower`) excludes.
-/

namespace OMDistance

open BraidDistance

theorem gadget_hamming : hamming 7 gs gv = 30 := Dkappa_length

/-- Lemma 3.3: there is no walk of length `30` in `B(7,2)` from `g^s` to `g^v`. -/
theorem gadget_no_walk30 : ¬ Walk 7 gs gv 30 := by
  intro hw
  obtain ⟨ts, hlen, hfw, hend⟩ := walk_to_flips hw
  obtain ⟨t, ht, hc⟩ := gadget_lower hfw hend
  have hb := parity_bound hfw.1 hend [t] (by simp)
    (fun t' h => by rw [List.mem_singleton.1 h]; exact ht)
    (fun t' h => by rw [List.mem_singleton.1 h]; exact hc)
  rw [gadget_hamming] at hb
  simp only [List.length_singleton] at hb
  omega

theorem hamR_gadget : hamR 8 3 (posF 7 (ofSMap gs)) (posF 7 (ofSMap gv)) = 30 := by
  rw [hamR_posF, hamR_ofSMap, gadget_hamming]

/-- There is no walk of chirotopes of length `30` on `[8]` from `Pos₃ g^s` to `Pos₃ g^v`. -/
theorem gadget_chiro_no30 : ¬ ChiroWalk 8 3 (posF 7 (ofSMap gs)) (posF 7 (ofSMap gv)) 30 := by
  intro hw
  have h30 : hamR 7 3 (ofSMap gs) (ofSMap gv) = 30 := by rw [hamR_ofSMap, gadget_hamming]
  have hw' : ChiroWalk (7 + 1) 3 (posF 7 (ofSMap gs)) (posF 7 (ofSMap gv)) (hamR 7 3 (ofSMap gs) (ofSMap gv)) := by
    rw [h30]; exact hw
  have hs := sheet_a (by decide) hw'
  rw [h30] at hs
  exact gadget_no_walk30 (sigWalk_to_walk hs)

/-- Every walk of chirotopes on `[8]` from (a map agreeing with) `Pos₃ g^s` to `Pos₃ g^v`, given by its flip list,
flips some basis more often than necessary. -/
theorem gadget_chiro_extra {χ : SignMap} {Xs : List (List Nat)} (hw : FlipWalkR 8 3 (IsChirotope 8 3) χ Xs)
    (hs : AgreeR 8 3 χ (posF 7 (ofSMap gs))) (hend : AgreeR 8 3 (flipsR χ Xs) (posF 7 (ofSMap gv))) :
    ∃ X, IsRSet 8 3 X ∧
      (if posF 7 (ofSMap gs) X = posF 7 (ofSMap gv) X then 0 else 1) < Xs.count X := by
  refine Classical.byContradiction fun hne => ?_
  have hc : ∀ X, IsRSet 8 3 X → Xs.count X ≤ if χ X = posF 7 (ofSMap gv) X then 0 else 1 := by
    intro X hX
    rw [hs X hX]
    exact Nat.not_lt.mp fun h => hne ⟨X, hX, h⟩
  have h1 := length_le_hamR hw.1 hc
  have h2 := hamR_le_length hw.1 hend
  rw [hamR_congr hs (AgreeR.refl _ _ _), hamR_gadget] at h1 h2
  have hw' := flips_to_rwalk hw hend
  have hlen : Xs.length = 30 := by omega
  rw [hlen] at hw'
  exact gadget_chiro_no30 (hw'.congr_start (isChirotope_agreeInv 8 3) hs)

end OMDistance
