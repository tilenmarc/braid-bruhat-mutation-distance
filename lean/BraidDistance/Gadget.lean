import BraidDistance.Words
import BraidDistance.Signotope

/-!
# The gadget (Section 3)

All positions and wires are 0-based: the paper's wires `1, …, 7` of the gadget are `0, …, 6` here, so the block
`U = {1,2,3}` is `{0,1,2}`, the private wire `p = 4` is `3`, and the block `V = {5,6,7}` is `{4,5,6}`.  The bead
triples `123` and `567` are `(0,1,2)` and `(4,5,6)`.

* `bead t q` is the bead `β^t_{q+1}` of the paper on the positions `q, q+1, q+2`:
  `β = σ_q σ_{q+1} σ_q` (type `false`, i.e. `0`) and `β' = σ_{q+1} σ_q σ_{q+1}` (type `true`, turned over).
* `kappa` is the word `κ = σ₄σ₃σ₂σ₁·σ₄σ₃·σ₅σ₄σ₃σ₂·σ₆σ₅σ₄σ₃·σ₄` with letters shifted to 0-based positions.
* `gadgetS a b = β^a_1 β^b_5 κ` and `gadgetV a b = κ β^b_1 β^a_5` (Definition 3.1), with sign vectors
  `g^s_{ab}` and `g^v_{ab}`; `gs`, `gv` are the case `a = b = false`.
* `Dkappa` is the list of the 30 triples on which `gs` and `gv` differ (Proposition 3.2(a)).
* `moveWord a b` is the word in which `b` wires pass up, the top one first, through `a` wires lying directly
  above them (the factor of one move of the shadow sweep, Section 4.3).
-/

namespace BraidDistance

/-- The word `κ` (0-based letters). -/
def kappa : List Nat := [3, 2, 1, 0, 3, 2, 4, 3, 2, 1, 5, 4, 3, 2, 3]

/-- The bead on the positions `q, q+1, q+2`: `β = [q, q+1, q]` (type `false`) or
`β' = [q+1, q, q+1]` (type `true`, turned over). -/
def bead (t : Bool) (q : Nat) : List Nat := if t then [q + 1, q, q + 1] else [q, q + 1, q]

/-- `b` wires pass up, the top one first, through `a` wires directly above them, on the positions
`0, …, a+b-1`.  It is `σ_0` for `a = b = 1`, `[2,1,0]` for `(3,1)`, `[0,1,2]` for `(1,3)`, and 9 letters for
`(3,3)`. -/
def moveWord (a b : Nat) : List Nat :=
  (List.range b).flatMap fun j => (List.range a).reverse.map fun i => i + j

/-- The gadget word `β^a_1 β^b_5 κ` on 7 wires. -/
def gadgetS (a b : Bool) : List Nat := bead a 0 ++ bead b 4 ++ kappa

/-- The gadget word `κ β^b_1 β^a_5` on 7 wires. -/
def gadgetV (a b : Bool) : List Nat := kappa ++ bead b 0 ++ bead a 4

/-- `g^s = g^s_{00}`. -/
def gs : SMap := signVec 7 (gadgetS false false)

/-- `g^v = g^v_{00}`. -/
def gv : SMap := signVec 7 (gadgetV false false)

/-- `D_κ = D(g^s, g^v)`, the 30 triples of Table 2. -/
def Dkappa : List Triple := diffList 7 gs gv

end BraidDistance
