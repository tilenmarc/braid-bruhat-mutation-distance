import OMDistance.Basic

/-!
# Adding one element and the lift (Lemma 8.1, Definition 8.2)

Trusted definitions.  Placement of the elements (0-based):

* the new elements `N = {0, …, c-1}`, the old ground set `S = {c, …, c+m-1}`, and (for the positive fibre)
  `∞ = c + m`; so `N < S < ∞` as in Section 8.
* A rank-3 map `s` on `S` is given as a map on `[m]`: the element `c + i` of `S` is the element `i` of `[m]`.

Definitions:

* **`lift c s`** (Definition 8.2, `L s = L^r_N s` with `|N| = c`): at an `r`-set `X` of `N ∪ S = [c+m]`, the value
  `s(top X)` if `|X ∩ S| ≥ 3`, and `+` otherwise; `top X` is the set of the three largest elements of `X` (the last
  three entries of the increasing list `X`), translated back to `[m]` by subtracting `c`.  The rank `r` is implicit
  (the map is evaluated on `r`-sets).
* **`expand v`** (the map `v ↦ v'` of Lemma 8.1): a new element `ℓ` is added below the ground set `[M]`; in
  0-based labels the new ground set is `[M+1]` with `ℓ = 0` and the old element `x` relabelled `x + 1`.  Then
  `v'(Z) = v(Z ∖ min Z)`, i.e. `expand v Z = v ((Z.drop 1).map (· - 1))` for an increasing list `Z`.
-/

namespace OMDistance

/-- The lift `L s` with `c` new elements `0, …, c-1` below `S = {c, …, c+m-1}`: `s(top X)` (translated back to
`[m]`) if `X` has at least three elements in `S`, and `+` otherwise. -/
def lift (c : Nat) (s : SignMap) : SignMap := fun X =>
  if 3 ≤ (X.filter fun x => decide (c ≤ x)).length then s ((X.drop (X.length - 3)).map (· - c)) else true

/-- `v'(Z) = v(Z ∖ min Z)` on the ground set `[M+1]` obtained by adding the new minimum `0` below `[M]` (the old
element `x` becomes `x + 1`). -/
def expand (v : SignMap) : SignMap := fun Z => v ((Z.drop 1).map (· - 1))

end OMDistance
