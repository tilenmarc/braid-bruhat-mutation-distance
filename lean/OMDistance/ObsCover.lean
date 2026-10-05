import OMDistance.ChiroBasic

/-!
# Walks in the mutation graph and walks of chirotopes (Observation 6.3)

Negation commutes with flips, so a walk of oriented matroids starting at `[χ]` lifts step by step to a walk of
chirotopes starting at `χ` of the same length, which ends at `ψ` or at `-ψ` (`OMWalk.toChiro`).  Conversely a
walk of chirotopes is a walk in the mutation graph (`ChiroWalk.toOM`).  Together with the Hamming bound
(`RWalk.hamR_le`) and `hamR_negR` this gives Observation 6.3:
`d([χ], [ψ]) = min(d_t(χ, ψ), d_t(χ, -ψ))` and `d_t(χ, -ψ) ≥ binom(|Ω|, r) - |D(χ, ψ)|`.
-/

namespace OMDistance

/-- A walk of chirotopes is a walk in the mutation graph. -/
theorem ChiroWalk.toOM {M r : Nat} {χ ψ : SignMap} {k : Nat} (hw : ChiroWalk M r χ ψ k) :
    OMWalk M r χ ψ k := by
  induction hw with
  | nil hu huv => exact OMWalk.nil hu (Or.inl huv)
  | cons hu hd _ ih => exact OMWalk.cons hu (Or.inl hd) ih

/-- Negating all terms of a walk of chirotopes. -/
theorem ChiroWalk.negR {M r : Nat} {χ ψ : SignMap} {k : Nat} (hw : ChiroWalk M r χ ψ k) :
    ChiroWalk M r (OMDistance.negR χ) (OMDistance.negR ψ) k := by
  induction hw with
  | nil hu huv => exact RWalk.nil hu.negR huv.negR
  | cons hu hd _ ih => exact RWalk.cons hu.negR hd.negR ih

/-- Observation 6.3: a walk in the mutation graph from `[χ]` to `[ψ]` lifts to a walk of chirotopes of the same
length from `χ` to `ψ` or to `-ψ`. -/
theorem OMWalk.toChiro {M r : Nat} {χ ψ : SignMap} {k : Nat} (hw : OMWalk M r χ ψ k) :
    ChiroWalk M r χ ψ k ∨ ChiroWalk M r χ (OMDistance.negR ψ) k := by
  induction hw with
  | nil hu huv =>
    rcases huv with h | h
    · exact Or.inl (RWalk.nil hu h)
    · exact Or.inr (RWalk.nil hu h)
  | @cons χ χ' ψ k hu hd _ ih =>
    rcases hd with hd | hd
    · rcases ih with w | w
      · exact Or.inl (RWalk.cons hu hd w)
      · exact Or.inr (RWalk.cons hu hd w)
    · rcases ih with w | w
      · exact Or.inr (RWalk.cons hu hd w.negR)
      · have w' := w.negR
        rw [negR_negR] at w'
        exact Or.inl (RWalk.cons hu hd w')

/-- Observation 6.3, the inequality: a walk of chirotopes from `χ` to `-ψ` has length at least
`binom(M, r) - |D(χ, ψ)|`. -/
theorem ChiroWalk.length_negR {M r : Nat} {χ ψ : SignMap} {k : Nat}
    (hw : ChiroWalk M r χ (OMDistance.negR ψ) k) : binom M r ≤ k + hamR M r χ ψ := by
  have h1 := hw.hamR_le
  have h2 := hamR_negR M r χ ψ
  omega

end OMDistance
