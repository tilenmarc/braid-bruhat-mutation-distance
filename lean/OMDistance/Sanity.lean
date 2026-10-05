import OMDistance.Chirotope
import OMDistance.Signotope
import OMDistance.Lift
import OMDistance.Instances
import BraidDistance.Gadget

/-!
# Sanity checks of the definitions of Part II

Checked by `decide` (kernel evaluation) against the paper and `../check.py` (whose labels are 1-based; here
everything is 0-based):

* the enumeration `rsets` and the binomial coefficients;
* the numbers of uniform chirotopes and of signotopes on small ground sets, as computed by `check.py`
  (`is_chirotope`, `all_signotopes`): rank-2 chirotopes on 4 elements: 48; rank 3 on 4: 16; rank 3 on 5: 384;
  rank 4 on 5: 32; signotopes of rank 3 on `[4]`: 8, on `[5]`: 62; rank 2 on `[4]`: 24, on `[5]`: 120;
  rank 4 on `[5]`: 10;
* Proposition 6.9 on all maps of rank 3 on `[4]` and of rank 2 on `[4]` (as check [3] of `check.py`);
* the gadget: `Pos₃ g^s` and `Pos₃ g^v` are uniform chirotopes on `[8]` with `|D| = 30`; flipping the basis
  `{0, 2, ∞}` of `Pos₃ g^s` gives a map violating (GP), while `{0, 1, ∞}` is a mutation (a triangle at infinity);
* the graph `K₂` is the gadget: `s_{K₂} = g^s`, `v_{K₂} = g^v` on `[7]`;
* the lift with one new element (`r = 4`, `c = 1`) of `g^s` is a signotope of rank 4 whose positive fibre is a
  uniform chirotope; its Hamming distance to the lift of `g^v` is `58 = Σ_{T ∈ D_κ} binom(1 + min T, 1)`
  (Lemma 8.3(b)); the lift with two new elements and rank 5 is the expansion of the lift with one
  (Lemma 8.3(a)); the minor `χ_Y`, `Y = {0}`, of `Pos₄ (L g^s)` is `Pos₃ g^s` (proof of Proposition 8.5).

The checks are about the definitions only; none of them uses a lemma of the library.
-/

namespace OMDistance.Sanity

open OMDistance BraidDistance

set_option maxRecDepth 100000

/-- The sign map on `[M]` of rank `r` given by the bits of `n` (bit `i` set means `-` on the `i`-th basis in
lexicographic order). -/
def mapOfBits (bases : List (List Nat)) (n : Nat) : SignMap := fun X =>
  match bases.idxOf? X with
  | some i => !(n.testBit i)
  | none => true

/-- The number of uniform chirotopes of rank `r` on `[M]`. -/
def countChiro (M r : Nat) : Nat :=
  ((List.range (2 ^ (rsets M r).length)).filter fun n =>
    decide (IsChirotope M r (mapOfBits (rsets M r) n))).length

/-- The number of signotopes of rank `r` on `[M]`. -/
def countSig (M r : Nat) : Nat :=
  ((List.range (2 ^ (rsets M r).length)).filter fun n =>
    decide (IsSignotopeR M r (mapOfBits (rsets M r) n))).length

theorem rsets_5_3 : rsets 5 3 = [[0, 1, 2], [0, 1, 3], [0, 1, 4], [0, 2, 3], [0, 2, 4], [0, 3, 4], [1, 2, 3],
    [1, 2, 4], [1, 3, 4], [2, 3, 4]] := by decide

theorem rsets_length : (rsets 7 3).length = binom 7 3 ∧ binom 7 3 = 35 ∧ (rsets 8 4).length = binom 8 4 := by
  decide

theorem packet_example (u : SignMap) :
    rpacket u [0, 1, 2, 3] = [u [0, 1, 2], u [0, 1, 3], u [0, 2, 3], u [1, 2, 3]] := by
  rfl

theorem chirotope_counts : countChiro 4 2 = 48 ∧ countChiro 4 3 = 16 ∧ countChiro 5 4 = 32 := by decide

theorem chirotope_count_5_3 : countChiro 5 3 = 384 := by decide

theorem signotope_counts : countSig 4 3 = 8 ∧ countSig 5 3 = 62 ∧ countSig 4 2 = 24 ∧ countSig 5 2 = 120 ∧
    countSig 5 4 = 10 := by decide

/-- Proposition 6.9 on all maps of rank 3 on `[4]` and of rank 2 on `[4]`. -/
theorem fibre_small :
    (∀ n ∈ List.range 16, IsSignotopeR 4 3 (mapOfBits (rsets 4 3) n) ↔
      IsChirotope 5 3 (posF 4 (mapOfBits (rsets 4 3) n))) ∧
    (∀ n ∈ List.range 64, IsSignotopeR 4 2 (mapOfBits (rsets 4 2) n) ↔
      IsChirotope 5 2 (posF 4 (mapOfBits (rsets 4 2) n))) := by decide

theorem gadget_chirotopes : IsChirotope 8 3 (posF 7 (ofSMap gs)) ∧ IsChirotope 8 3 (posF 7 (ofSMap gv)) ∧
    hamR 8 3 (posF 7 (ofSMap gs)) (posF 7 (ofSMap gv)) = 30 := by decide

theorem gadget_flips : ¬ IsChirotope 8 3 (flipR (posF 7 (ofSMap gs)) [0, 2, 7]) ∧
    IsChirotope 8 3 (flipR (posF 7 (ofSMap gs)) [0, 1, 7]) := by decide

theorem gadget_signotopes : IsSignotopeR 7 3 (ofSMap gs) ∧ IsSignotopeR 7 3 (ofSMap gv) := by decide

/-- The graph `K₂`. -/
def K2 : Graph := ⟨2, [(0, 1)]⟩

theorem K2_is_gadget : K2.m = 7 ∧ AgreeR 7 3 (sMap K2) (ofSMap gs) ∧ AgreeR 7 3 (vMap K2) (ofSMap gv) := by
  decide

theorem lift_gadget : IsSignotopeR 8 4 (lift 1 (ofSMap gs)) ∧ IsChirotope 9 4 (posF 8 (lift 1 (ofSMap gs))) ∧
    hamR 8 4 (lift 1 (ofSMap gs)) (lift 1 (ofSMap gv)) = 58 ∧
    ((diffR 7 3 (ofSMap gs) (ofSMap gv)).map fun T => binom (1 + T.headD 0) 1).sum = 58 := by decide

theorem lift_expand_gadget : AgreeR 9 5 (lift 2 (ofSMap gs)) (expand (lift 1 (ofSMap gs))) := by decide

theorem minor_gadget :
    AgreeR 8 3 (fun Z => posF 8 (lift 1 (ofSMap gs)) ([0] ++ Z.map (· + 1))) (posF 7 (ofSMap gs)) := by
  decide

end OMDistance.Sanity
