import BraidDistance.PathLemmas
import BraidDistance.Construction

/-!
# Finite facts about the gadget and the local cases (Proposition 3.2(a), Lemma 4.5(b), Table 2)

All statements here are finite computations, checked by `decide`, except `localPath`, which replays the
certificates of `Certificates.lean` through `checkCert_sound`.

* the gadget words are reduced and `D(g^s_ε, g^v_ε) = D_κ` has 30 triples for every `ε` (Proposition 3.2(a));
* (K1)–(K3) for `κ`;
* for every local case, `L` and `L'` are reduced words on `width` wires, their sign vectors differ in `ham`
  triples, never in a bead triple, and there is a path from `L` to `L'` with `cost` braid moves
  (Lemma 4.5(b) and Proposition 3.2(b), upper bounds);
* the factor of an event is the `phi` of its case.
-/

namespace BraidDistance

set_option maxRecDepth 100000

/-- (K1), (K2): `κ` swaps every pair of wires from two different groups `{0,1,2}`, `{3}`, `{4,5,6}` once,
no pair inside a group, and ends with `V` on top, `p` in the middle and `U` at the bottom. -/
theorem kappa_K1K2 :
    (∀ b < 7, ∀ a < b, (swaps 7 kappa).count (a, b) = if b < 3 ∨ (4 ≤ a) then 0 else 1) ∧
    arrAfter 7 kappa = [4, 5, 6, 3, 0, 1, 2] := by
  decide

/-- (K3): the private wire meets the block wires in the order `w₁, u₃, u₂, w₂, w₃, u₁` (0-based
`4, 2, 1, 5, 6, 0`). -/
theorem kappa_K3 : ((swaps 7 kappa).filter fun p => p.1 = 3 ∨ p.2 = 3) =
    [(3, 4), (2, 3), (1, 3), (3, 5), (3, 6), (0, 3)] := by
  decide

theorem gadget_reduced (a b : Bool) : Reduced 7 (gadgetS a b) ∧ Reduced 7 (gadgetV a b) := by
  cases a <;> cases b <;> decide

/-- Proposition 3.2(a). -/
theorem gadget_D (a b : Bool) :
    diffList 7 (signVec 7 (gadgetS a b)) (signVec 7 (gadgetV a b)) = Dkappa := by
  cases a <;> cases b <;> decide

theorem Dkappa_length : Dkappa.length = 30 := by decide

/-- The bead triples are not in `D_κ`. -/
theorem Dkappa_beads : (0, 1, 2) ∉ Dkappa ∧ (4, 5, 6) ∉ Dkappa := by decide

theorem case_reduced (c : Case) : Reduced c.width c.L ∧ Reduced c.width c.L' := by
  cases c with
  | pp => decide
  | Xp a => cases a <;> decide
  | pX a => cases a <;> decide
  | XX a b => cases a <;> cases b <;> decide
  | cell a b => exact gadget_reduced a b

/-- Lemma 4.5(b), the column `|D_k|`. -/
theorem case_ham (c : Case) :
    hamming c.width (signVec c.width c.L) (signVec c.width c.L') = c.ham := by
  cases c with
  | pp => decide
  | Xp a => cases a <;> decide
  | pX a => cases a <;> decide
  | XX a b => cases a <;> cases b <;> decide
  | cell a b => cases a <;> cases b <;> decide

/-- No bead triple changes sign in a step. -/
theorem case_bead (c : Case) :
    ∀ t ∈ c.beadTriples, (signVec c.width c.L).at t = (signVec c.width c.L').at t := by
  cases c with
  | pp => decide
  | Xp a => cases a <;> decide
  | pX a => cases a <;> decide
  | XX a b => cases a <;> cases b <;> decide
  | cell a b => cases a <;> cases b <;> decide

/-- The bead triples of a case are valid local triples. -/
theorem case_beadTriples_valid (c : Case) : ∀ t ∈ c.beadTriples, ValidTriple c.width t := by
  cases c <;> simp [Case.beadTriples, Case.width, ValidTriple]

/-- The local word of an event is the factor of its case. -/
theorem evLocal_eq_phi (eps : Nat → Bool) (ev : Ev) : evLocal ev = (caseOf eps ev).phi := by
  cases ev with
  | mv g h => cases g <;> cases h <;> rfl
  | cell u w => rfl

theorem case_L_eq (c : Case) : ∃ B, c.L = B ++ c.phi := by
  cases c with
  | pp => exact ⟨[], rfl⟩
  | Xp a => exact ⟨bead a 0, rfl⟩
  | pX a => exact ⟨bead a 1, rfl⟩
  | XX a b => exact ⟨bead a 0 ++ bead b 3, rfl⟩
  | cell a b => exact ⟨bead a 0 ++ bead b 4, rfl⟩

/-- Lemma 4.5(b), the column "braid moves", and Proposition 3.2(b), upper bounds. -/
theorem localPath (c : Case) : Path c.L c.L' c.cost := by
  cases c with
  | pp => exact checkCert_sound (ms := cert_pp) (by decide)
  | Xp a => cases a
            · exact checkCert_sound (ms := cert_Xp0) (by decide)
            · exact checkCert_sound (ms := cert_Xp1) (by decide)
  | pX a => cases a
            · exact checkCert_sound (ms := cert_pX0) (by decide)
            · exact checkCert_sound (ms := cert_pX1) (by decide)
  | XX a b => cases a <;> cases b
              · exact checkCert_sound (ms := cert_XX00) (by decide)
              · exact checkCert_sound (ms := cert_XX01) (by decide)
              · exact checkCert_sound (ms := cert_XX10) (by decide)
              · exact checkCert_sound (ms := cert_XX11) (by decide)
  | cell a b =>
    cases a <;> cases b
    · -- turn the bead of `U` over, use the certificate for `(1,0)`, turn it back
      have h1 : Path (gadgetS false false) (gadgetS true false) 1 := by
        have := Path.bead_flip [] (bead false 4 ++ kappa) 0
        simpa [gadgetS] using this
      have h2 : Path (gadgetS true false) (gadgetV true false) 30 :=
        checkCert_sound (ms := cert_cell10) (by decide)
      have h3 : Path (gadgetV true false) (gadgetV false false) 1 := by
        have := (Path.bead_flip (kappa ++ bead false 0) [] 4).symm
        simpa [gadgetV] using this
      exact (h1.trans (h2.trans h3)).cast (by decide)
    · exact checkCert_sound (ms := cert_cell01) (by decide)
    · exact checkCert_sound (ms := cert_cell10) (by decide)
    · exact checkCert_sound (ms := cert_cell11) (by decide)

end BraidDistance
