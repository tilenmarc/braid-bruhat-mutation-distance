import BraidDistance.Gadget

/-!
# The local words of one step of the bead sweep (Lemma 4.5)

Passing the beads of the construction past one factor `φ` of `Φ̂` is, after commutations, the replacement of a
word `L = (beads before φ) φ` by `L' = φ (beads after φ)` on the `width` consecutive positions of the wires `Z`
of the groups of `φ`.  Read on the wires `0, …, width - 1` (the wires of `Z` in increasing order) there are five
kinds of factors (Section 4.3), and the beads of the blocks involved have types `a, b`:

| case       | groups (top to bottom)      | `width` | `L`                       | `L'`                      |
|------------|-----------------------------|---------|---------------------------|---------------------------|
| `pp`       | private, private            | 2       | `σ₀`                      | `σ₀`                      |
| `Xp a`     | block (type `a`), private   | 4       | `β^a_0 [2,1,0]`           | `[2,1,0] β^a_1`           |
| `pX a`     | private, block (type `a`)   | 4       | `β^a_1 [0,1,2]`           | `[0,1,2] β^a_0`           |
| `XX a b`   | block `a`, block `b`        | 6       | `β^a_0 β^b_3 φ₃₃`         | `φ₃₃ β^b_0 β^a_3`         |
| `cell a b` | block `a`, private, block `b` | 7     | `β^a_0 β^b_4 κ`           | `κ β^b_0 β^a_4`           |

(`β^t_q` is `bead t q`, `φ₃₃ = moveWord 3 3`.)  `cost` is the number of braid moves of the explicit sequences
in `Certificates.lean` (Lemma 4.5(b): `0, 3, 3, 18`, and `30` for a cell with a turned bead; a cell with two
beads of type `β` needs `32`, Proposition 3.2(b)).  `ham` is the Hamming distance `|D_k|` of `L` and `L'`, which
does not depend on the bead types.  `beadTriples` are the bead triples of the blocks, in local coordinates.
-/

namespace BraidDistance

/-- The kind of a factor together with the types of the beads of its blocks. -/
inductive Case where
  | pp
  | Xp (a : Bool)
  | pX (a : Bool)
  | XX (a b : Bool)
  | cell (a b : Bool)
deriving DecidableEq, Repr

namespace Case

/-- The number of wires of the groups of the factor. -/
def width : Case → Nat
  | pp => 2
  | Xp _ => 4
  | pX _ => 4
  | XX _ _ => 6
  | cell _ _ => 7

/-- The factor itself, on the positions `0, …, width - 1`. -/
def phi : Case → List Nat
  | pp => moveWord 1 1
  | Xp _ => moveWord 3 1
  | pX _ => moveWord 1 3
  | XX _ _ => moveWord 3 3
  | cell _ _ => kappa

/-- `L`: the beads of the blocks of the factor (before it), then the factor. -/
def L : Case → List Nat
  | pp => moveWord 1 1
  | Xp a => bead a 0 ++ moveWord 3 1
  | pX a => bead a 1 ++ moveWord 1 3
  | XX a b => bead a 0 ++ bead b 3 ++ moveWord 3 3
  | cell a b => gadgetS a b

/-- `L'`: the factor, then the beads of its blocks (after it). -/
def L' : Case → List Nat
  | pp => moveWord 1 1
  | Xp a => moveWord 3 1 ++ bead a 1
  | pX a => moveWord 1 3 ++ bead a 0
  | XX a b => moveWord 3 3 ++ bead b 0 ++ bead a 3
  | cell a b => gadgetV a b

/-- The number of braid moves of the explicit sequence from `L` to `L'`. -/
def cost : Case → Nat
  | pp => 0
  | Xp _ => 3
  | pX _ => 3
  | XX _ _ => 18
  | cell a b => if a || b then 30 else 32

/-- The Hamming distance of the sign vectors of `L` and `L'` (Lemma 4.5(b)). -/
def ham : Case → Nat
  | pp => 0
  | Xp _ => 3
  | pX _ => 3
  | XX _ _ => 18
  | cell _ _ => 30

/-- The bead triples of the blocks of the factor, in local coordinates. -/
def beadTriples : Case → List Triple
  | pp => []
  | Xp _ => [(0, 1, 2)]
  | pX _ => [(1, 2, 3)]
  | XX _ _ => [(0, 1, 2), (3, 4, 5)]
  | cell _ _ => [(0, 1, 2), (4, 5, 6)]

end Case

end BraidDistance
