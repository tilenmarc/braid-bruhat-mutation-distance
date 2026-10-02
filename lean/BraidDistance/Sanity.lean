import BraidDistance.Construction
import BraidDistance.LocalCases

/-!
# Sanity checks against the paper and `check.py`

All checks are proved by `decide` (kernel evaluation, no `native_decide`).  The reference values were computed
with `../check.py` (functions `construct`, `word_with_beads`, `sG_vG`, `sig_of_word`, shifted to 0-based labels)
by `scripts/ref_values.py`; the sign strings of the gadget are those printed in `../README.md`.

* the path `P_3` (`1 - 2 - 3`, Example 4.7): `m = 11`, `W^s_G` has `C(11,2) = 55` letters and equals the word of
  `check.py`, both words are reduced, the shadow sweep is the table of Section 4.2, and the sign vectors equal
  those of `check.py` and differ on `|D| = 84 = 3·3·8 + 6·2` triples;
* the gadget: `D_κ` is the set of 30 triples of Table 2, and `g^s`, `g^v` are the sign strings of `README.md`;
  for `G = K_2` the construction is the gadget (up to the order of two commuting beads);
* `|D| = 3n(m-3) + 6|E|` for `2K_1` (18) and `K_3` (99).

Further values computed with `#eval` (and equal to `check.py`, see `scripts/ref_values.py`):
`K_{1,3}` (star, `n = 4`): `m = 15`, `J = 15`, `|D| = 162`; `C_4`: `m = 16`, `J = 20`, `|D| = 180`.
The structural statements of `Sweep.lean`, `FactorOverlap.lean`, `Blowup.lean`, `SweepCount.lean` and the
decomposition of `StepDecomp.lean` (up to commutation classes) were also checked by evaluation on eleven graphs
(including `K_4`, an unsorted edge list, and the graphs with 0 and 1 vertices) before they were proved.
-/

namespace BraidDistance
namespace Sanity

/-- The path `P_3`: `1 - 2 - 3` (0-based `0 - 1 - 2`). -/
def P3 : Graph := ⟨3, [(0, 1), (1, 2)]⟩
/-- A single edge. -/
def K2 : Graph := ⟨2, [(0, 1)]⟩
/-- Two isolated vertices. -/
def twoK1 : Graph := ⟨2, []⟩
/-- The triangle. -/
def K3 : Graph := ⟨3, [(0, 1), (0, 2), (1, 2)]⟩

set_option maxRecDepth 100000

theorem P3_valid : P3.Valid := by decide
theorem P3_m : P3.m = 11 := by decide
theorem P3_Ws_length : (Ws P3).length = 55 := by decide
theorem P3_Wv_length : (Wv P3).length = 55 := by decide

/-- The shadow sweep of `P_3` (table of Section 4.2): the cell of `12`, `p_23` passes up through `X_1, p_12`,
`X_3` passes up through `X_1, p_12`, the cell of `23`. -/
theorem P3_sweep : sweepEvents P3 =
    [.cell 0 1, .mv (.X 0) (.p 1 2), .mv (.p 0 1) (.p 1 2), .mv (.X 0) (.X 2), .mv (.p 0 1) (.X 2),
     .cell 1 2] := by decide

/-- After the sweep the groups are in reverse label order. -/
theorem P3_final : arrAt P3 (numFactors P3) = [.X 2, .p 1 2, .X 1, .p 0 1, .X 0] := by decide

/-- `W^s_G` equals the word of `check.py` (`word_with_beads(con, 0, {})`, 0-based). -/
theorem P3_Ws_eq : Ws P3 = [0, 1, 0, 4, 5, 4, 8, 9, 8, 3, 2, 1, 0, 3, 2, 4, 3, 2, 1, 5, 4, 3, 2, 3, 6, 5, 4, 3, 7, 6, 5, 8,
      7, 6, 9, 8, 7, 4, 5, 6, 3, 2, 1, 0, 3, 2, 4, 3, 2, 1, 5, 4, 3, 2, 3] := by decide

theorem P3_Ws_reduced : Reduced 11 (Ws P3) := by decide
theorem P3_Wv_reduced : Reduced 11 (Wv P3) := by decide

/-- `s_G` and `v_G` of `P_3`, triples in lexicographic order, equal those of `check.py`. -/
theorem P3_signs :
    (triples 11).map (sG P3).at =
      [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, false, true, true, true, true, false, false, true, true, true, true, false,
      true, true, true, true, true, true, true, true, true, true, true, false, false, false, true,
      true, true, true, true, true, true, true, true, true, false, true, true, true, true, false,
      false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true,
      true, false, false, false, false, false, false, true, true, true, true, false, false, true, true,
      true, true, false, true, true, true, true, true, true, true, true, true, true, true, false,
      false, false, false, false, true, true, true, true, false, true, true, true, true, true, true,
      true, true, true, true, true, false, false, false, true, true, true, true, true, true, true,
      true, true, true, true, false, false, false, false, true, true, true, true, true, true, false,
      false, false, false, false, false, false, false, false, false, false, false, false, true] ∧
    (triples 11).map (vG P3).at =
      [true, false, false, false, false, false, false, false, false, false, false, false, false, false,
      false, false, false, false, false, false, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      false, false, false, false, false, false, false, false, false, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, false, false, false, false, false, false, false,
      false, false, false, false, true, true, true, false, false, false, false, false, true, true,
      true, true, true, false, true, true, true, true, true, true, true, true, true] := by decide

/-- Example 4.7: `|D| = 84 = 3·3·(11-3) + 6·2`. -/
theorem P3_D : hamming 11 (sG P3) (vG P3) = 84 ∧ 84 = 3 * P3.n * (P3.m - 3) + 6 * P3.edges.length := by
  decide

/-- For a single edge the construction is the gadget of Definition 3.1 (in `W^v_G` the two commuting beads are
listed by vertex, so it is `κ β_5 β_1` rather than `κ β_1 β_5`). -/
theorem K2_gadget : Ws K2 = gadgetS false false ∧ Wv K2 = kappa ++ bead false 4 ++ bead false 0 := by
  decide

/-- The sign vectors of the gadget (`README.md`: `g^s = +++++++++++----++++++-------------+`, `g^v = +-----------+++-----+++++-+++++++++`). -/
theorem gadget_signs :
    (triples 7).map gs.at = [true, true, true, true, true, true, true, true, true, true, true, false, false, false, false,
      true, true, true, true, true, true, false, false, false, false, false, false, false, false,
      false, false, false, false, false, true] ∧
    (triples 7).map gv.at = [true, false, false, false, false, false, false, false, false, false, false, false, true, true,
      true, false, false, false, false, false, true, true, true, true, true, false, true, true, true,
      true, true, true, true, true, true] := by decide

/-- `D_κ` is the set of the 30 triples of Table 2 (0-based). -/
theorem Dkappa_eq : Dkappa =
    [(0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 1, 6), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 2, 6),
     (0, 3, 4), (0, 3, 5), (0, 4, 5), (0, 4, 6), (0, 5, 6), (1, 2, 3), (1, 2, 4), (1, 2, 5),
     (1, 2, 6), (1, 3, 4), (1, 3, 6), (1, 4, 5), (1, 4, 6), (1, 5, 6), (2, 3, 5), (2, 3, 6),
     (2, 4, 5), (2, 4, 6), (2, 5, 6), (3, 4, 5), (3, 4, 6), (3, 5, 6)] := by decide

theorem twoK1_D : hamming twoK1.m (sG twoK1) (vG twoK1) = 18 ∧
    18 = 3 * twoK1.n * (twoK1.m - 3) + 6 * twoK1.edges.length := by decide

theorem K3_D : hamming K3.m (sG K3) (vG K3) = 99 ∧
    99 = 3 * K3.n * (K3.m - 3) + 6 * K3.edges.length := by decide

/-- `s_G` and `v_G` of `P_3` are signotopes (Lemma 2.2(b) in an instance). -/
theorem P3_signotopes : IsSignotope 11 (sG P3) ∧ IsSignotope 11 (vG P3) := by decide

end Sanity
end BraidDistance
