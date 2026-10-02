/-!
# Basic objects: triples, sign maps, Hamming distance

Conventions used throughout the library (all labels are 0-based):

* The paper's wires (elements) `1, …, m` are the natural numbers `0, …, m-1`.
* A *triple* is a value `(a, b, c) : Triple = Nat × Nat × Nat`; it stands for the 3-set `{a < b < c}` and is
  *valid* in `[m]` when `a < b < c < m` (`ValidTriple m t`).
* A *sign map* (the paper's map `u : binom([m],3) → {±}`) is an `SMap = Nat → Nat → Nat → Bool`, where `true`
  is the sign `+`.  Only the values on valid triples matter; two maps that agree on all valid triples are
  identified by `Agree m`.
* `diffList m u v` lists the valid triples on which `u` and `v` differ (the paper's `D(u, v)`), in lexicographic
  order, and `hamming m u v` is its length `|D(u, v)|`.
* For an increasing list `z` of labels, `pull z u` is the restriction of `u` to the elements of `z`, renumbered
  `0, …, z.length - 1` in increasing order (deleting all other elements, Section 2.2), and `localize z ts`
  restricts a list of triples to those inside `z`, renumbered in the same way.
-/

namespace BraidDistance

/-- A triple `(a, b, c)`, standing for the 3-set `{a < b < c}`. -/
abbrev Triple := Nat × Nat × Nat

/-- A sign map on triples; `true` is the sign `+`. Only values on valid triples matter. -/
abbrev SMap := Nat → Nat → Nat → Bool

/-- `(a, b, c)` with `a < b < c < m`. -/
def ValidTriple (m : Nat) (t : Triple) : Prop := t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 < m

instance (m : Nat) (t : Triple) : Decidable (ValidTriple m t) := by
  unfold ValidTriple; infer_instance

/-- All valid triples of `[m]`, in lexicographic order. -/
def triples (m : Nat) : List Triple :=
  (List.range m).flatMap fun a =>
    (List.range' (a + 1) (m - (a + 1))).flatMap fun b =>
      (List.range' (b + 1) (m - (b + 1))).map fun c => (a, b, c)

/-- The value of a sign map at a triple. -/
@[inline] def SMap.at (u : SMap) (t : Triple) : Bool := u t.1 t.2.1 t.2.2

/-- `u^T`: the map `u` with the value at the triple `t` negated. -/
def flipT (u : SMap) (t : Triple) : SMap :=
  fun a b c => if (a, b, c) = t then !u a b c else u a b c

/-- Negate the values at the triples of `ts`, one after the other. -/
def flipList (u : SMap) (ts : List Triple) : SMap := ts.foldl flipT u

/-- `u` and `v` agree on all valid triples of `[m]`. -/
def Agree (m : Nat) (u v : SMap) : Prop :=
  ∀ a b c, a < b → b < c → c < m → u a b c = v a b c

/-- The paper's `D(u, v)`: the valid triples of `[m]` on which `u` and `v` differ, in lexicographic order. -/
def diffList (m : Nat) (u v : SMap) : List Triple :=
  (triples m).filter fun t => u.at t != v.at t

/-- The Hamming distance `|D(u, v)|`. -/
def hamming (m : Nat) (u v : SMap) : Nat := (diffList m u v).length

/-- A strictly increasing list of labels. -/
def StrictIncr (z : List Nat) : Prop := z.Pairwise (· < ·)

/-- All three elements of the triple lie in `z`. -/
def Inside (z : List Nat) (t : Triple) : Prop := t.1 ∈ z ∧ t.2.1 ∈ z ∧ t.2.2 ∈ z

instance (z : List Nat) (t : Triple) : Decidable (Inside z t) := by
  unfold Inside; infer_instance

/-- The image of a local triple `(i, j, k)` under the renumbering `z`. -/
def embT (z : List Nat) (t : Triple) : Triple := (z.getD t.1 0, z.getD t.2.1 0, z.getD t.2.2 0)

/-- Restriction of a sign map to the elements of `z`, renumbered `0, …, z.length - 1`. -/
def pull (z : List Nat) (u : SMap) : SMap := fun i j k => u (z.getD i 0) (z.getD j 0) (z.getD k 0)

/-- The triples of `ts` inside `z`, renumbered by their positions in `z` (order and repetitions kept). -/
def localize (z : List Nat) (ts : List Triple) : List Triple :=
  ts.filterMap fun t => if Inside z t then some (z.idxOf t.1, z.idxOf t.2.1, z.idxOf t.2.2) else none

end BraidDistance
