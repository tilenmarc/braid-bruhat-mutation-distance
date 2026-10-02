import BraidDistance.Basic

/-!
# Words, reduced words, sign vectors, commutations and braid moves (Definition 2.1)

* A *word* is a `List Nat`.  On `m` wires the letter `i` (the paper's `σ_{i+1}`) exchanges the wires at the
  positions `i` and `i+1`; it is a letter of the word on `m` wires when `i + 1 < m`.
* An *arrangement* is the list of wire labels from top to bottom; initially it is `[0, 1, …, m-1]`.
  `arrFrom arr w` is the arrangement after applying `w` to `arr`, and `arrAfter m w` the one after applying `w`
  to the initial arrangement.
* `swapsFrom arr w` lists, letter by letter, the pair of wires exchanged by each letter of `w` (as a normalized
  pair `(min, max)`), and `swaps m w` does so from the initial arrangement (the paper's swaps `⟨xy⟩`).
* `Reduced m w`: every letter is a letter on `m` wires and every pair `a < b < m` of wires is swapped exactly
  once (a reduced word of the longest permutation `w₀ ∈ S_m`).
* `signVec m w` is the sign vector `s_W` of Definition 2.1: `s_W(abc) = +` iff the swap `⟨ab⟩` precedes the swap
  `⟨bc⟩` (for a reduced word this is the order `⟨ab⟩, ⟨ac⟩, ⟨bc⟩`).
* `Step w w' k` is one commutation (`k = 0`) or one braid move (`k = 1`), anywhere in the word, and
  `Path w w' k` is a finite sequence of such steps from `w` to `w'` with exactly `k` braid moves in total.
  The braid-move distance of the paper is the least `k` with `Path W W' k`.
-/

namespace BraidDistance

/-- Exchange the entries at the positions `i` and `i+1` (no change if `i+1` is out of range). -/
def swapAdj (arr : List Nat) (i : Nat) : List Nat :=
  match arr.drop i with
  | a :: b :: rest => arr.take i ++ b :: a :: rest
  | _ => arr

/-- The arrangement after applying the word `w` to the arrangement `arr`. -/
def arrFrom (arr : List Nat) (w : List Nat) : List Nat := w.foldl swapAdj arr

/-- The arrangement after applying `w` to the initial arrangement `[0, …, m-1]`. -/
def arrAfter (m : Nat) (w : List Nat) : List Nat := arrFrom (List.range m) w

/-- The normalized pair `(min a b, max a b)`. -/
def pairOf (a b : Nat) : Nat × Nat := (min a b, max a b)

/-- The pairs of wires exchanged by the letters of `w`, one per letter, starting from `arr`. -/
def swapsFrom : List Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | arr, i :: w => pairOf (arr.getD i 0) (arr.getD (i + 1) 0) :: swapsFrom (swapAdj arr i) w

/-- The pairs of wires swapped by `w` on `m` wires, in order (the paper's swaps `⟨xy⟩`). -/
def swaps (m : Nat) (w : List Nat) : List (Nat × Nat) := swapsFrom (List.range m) w

/-- Every letter of `w` is a letter on `m` wires. -/
def ValidWord (m : Nat) (w : List Nat) : Prop := ∀ i ∈ w, i + 1 < m

instance (m : Nat) (w : List Nat) : Decidable (ValidWord m w) := by
  unfold ValidWord; infer_instance

/-- A reduced word on `m` wires: it swaps every pair of wires exactly once (Definition 2.1). -/
def Reduced (m : Nat) (w : List Nat) : Prop :=
  ValidWord m w ∧ ∀ b < m, ∀ a < b, (swaps m w).count (a, b) = 1

instance (m : Nat) (w : List Nat) : Decidable (Reduced m w) := by
  unfold Reduced; infer_instance

/-- The sign vector `s_W` (Definition 2.1): `s_W(abc) = +` iff `⟨ab⟩` precedes `⟨bc⟩` in `W`. -/
def signVec (m : Nat) (w : List Nat) : SMap :=
  fun a b c => decide ((swaps m w).idxOf (a, b) < (swaps m w).idxOf (b, c))

/-- Shift every letter by `q` (a word acting on positions `q, q+1, …`). -/
def shiftW (q : Nat) (w : List Nat) : List Nat := w.map (· + q)

/-- One elementary step on words, with its number of braid moves: a commutation
`σ_i σ_j ↔ σ_j σ_i` with `|i - j| ≥ 2` (`0`), or a braid move `σ_i σ_{i+1} σ_i ↔ σ_{i+1} σ_i σ_{i+1}` (`1`). -/
inductive Step : List Nat → List Nat → Nat → Prop where
  | comm (A C : List Nat) (i j : Nat) (h : i + 2 ≤ j ∨ j + 2 ≤ i) :
      Step (A ++ i :: j :: C) (A ++ j :: i :: C) 0
  | braidUp (A C : List Nat) (i : Nat) :
      Step (A ++ i :: (i + 1) :: i :: C) (A ++ (i + 1) :: i :: (i + 1) :: C) 1
  | braidDown (A C : List Nat) (i : Nat) :
      Step (A ++ (i + 1) :: i :: (i + 1) :: C) (A ++ i :: (i + 1) :: i :: C) 1

/-- A sequence of commutations and braid moves from `w` to `w'` with exactly `k` braid moves. -/
inductive Path : List Nat → List Nat → Nat → Prop where
  | refl (w : List Nat) : Path w w 0
  | cons {w₁ w₂ w₃ : List Nat} {a b : Nat} : Step w₁ w₂ a → Path w₂ w₃ b → Path w₁ w₃ (a + b)

end BraidDistance
