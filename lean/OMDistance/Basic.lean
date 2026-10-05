import BraidDistance.Basic

/-!
# Finite sets, sign maps of any rank, flips, Hamming distance, walks, binomial coefficients

This file is part of the trusted definitions of Part II (Sections 6–8 of the paper).

Conventions (all labels are 0-based):

* A finite set of natural numbers is written as a *strictly increasing list* (`StrictIncr`, from Part I).
  `IsRSet M r X` says that `X` is an `r`-subset of `[M] = {0, …, M-1}`.
* `rsets M r` lists all `r`-subsets of `[M]` in lexicographic order; `mem_rsets` proves that its members are
  exactly the lists with `IsRSet M r`.
* A *sign map* (of any rank) is a `SignMap = List Nat → Bool`, `true` being the sign `+`.  A map
  `u : binom([M], r) → {±}` of the paper is a sign map of which only the values on `r`-subsets of `[M]` matter;
  `AgreeR M r u v` identifies two maps with the same values on all `r`-subsets of `[M]`.
* `flipR u X` is the paper's `u^X` (the value at `X` negated); `flipsR u Xs` flips the sets of `Xs` one after the
  other; `negR u` is `-u`.
* `diffR M r u v` is the paper's `D(u, v)` (the `r`-subsets of `[M]` on which `u` and `v` differ, in
  lexicographic order), and `hamR M r u v = |D(u, v)|` is the Hamming distance.
* `DiffersInOneR M r u v`: `u` and `v` differ in exactly one `r`-subset of `[M]` (`|D(u, v)| = 1`).
* `RWalk M r P u v k` is a walk `u = u₀, u₁, …, u_k` of length `k` in the graph whose vertices are the sign maps
  satisfying `P` and whose edges join maps differing in exactly one `r`-subset of `[M]`; the last map agrees with
  `v` on all `r`-subsets.  Walks of chirotopes and walks in a higher Bruhat order are the instances
  `P = IsChirotope M r` and `P = IsSignotopeR M r` (files `Chirotope.lean`, `Signotope.lean`).
* `binom n k` is the binomial coefficient, defined by Pascal's rule.
-/

namespace OMDistance

open BraidDistance (StrictIncr)

/-- A sign map of any rank: a map from finite sets (strictly increasing lists) to signs; `true` is `+`.
Only the values on the relevant `r`-subsets matter. -/
abbrev SignMap := List Nat → Bool

/-- `X` is an `r`-subset of `[M] = {0, …, M-1}`, written as a strictly increasing list. -/
def IsRSet (M r : Nat) (X : List Nat) : Prop :=
  X.length = r ∧ StrictIncr X ∧ ∀ x ∈ X, x < M

instance (M r : Nat) (X : List Nat) : Decidable (IsRSet M r X) := by
  unfold IsRSet StrictIncr; infer_instance

/-- The strictly increasing lists of length `r` with all entries in `[lo, M)`, in lexicographic order. -/
def rsetsFrom (M : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | r + 1, lo => (List.range' lo (M - lo)).flatMap fun a => (rsetsFrom M r (a + 1)).map (a :: ·)

/-- All `r`-subsets of `[M]`, in lexicographic order. -/
def rsets (M r : Nat) : List (List Nat) := rsetsFrom M r 0

theorem mem_rsetsFrom (M : Nat) : ∀ (r lo : Nat) (X : List Nat),
    X ∈ rsetsFrom M r lo ↔ X.length = r ∧ StrictIncr X ∧ ∀ x ∈ X, lo ≤ x ∧ x < M := by
  intro r
  induction r with
  | zero =>
    intro lo X
    cases X with
    | nil => simp [rsetsFrom, StrictIncr]
    | cons x X => simp [rsetsFrom]
  | succ r ih =>
    intro lo X
    cases X with
    | nil => simp [rsetsFrom]
    | cons x X =>
      simp only [rsetsFrom, List.mem_flatMap, List.mem_range'_1, List.mem_map, ih, List.length_cons,
        StrictIncr, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨a, ⟨h1, h2⟩, Y, ⟨hlen, hinc, hY⟩, hYX⟩
        simp only [List.cons.injEq] at hYX
        obtain ⟨rfl, rfl⟩ := hYX
        refine ⟨by omega, ⟨fun y hy => by have := hY y hy; omega, hinc⟩, ⟨h1, by omega⟩, fun y hy => ?_⟩
        have := hY y hy
        omega
      · rintro ⟨hlen, ⟨hx, hinc⟩, ⟨h1, h2⟩, hX⟩
        refine ⟨x, ⟨h1, by omega⟩, X, ⟨by omega, hinc, fun y hy => ?_⟩, rfl⟩
        have := hx y hy
        have := hX y hy
        omega

/-- The members of `rsets M r` are exactly the `r`-subsets of `[M]`. -/
theorem mem_rsets {M r : Nat} {X : List Nat} : X ∈ rsets M r ↔ IsRSet M r X := by
  unfold rsets IsRSet
  rw [mem_rsetsFrom]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => (h3 x hx).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx => ⟨Nat.zero_le _, h3 x hx⟩⟩

/-- `u` and `v` agree on all `r`-subsets of `[M]`. -/
def AgreeR (M r : Nat) (u v : SignMap) : Prop := ∀ X, IsRSet M r X → u X = v X

instance (M r : Nat) (u v : SignMap) : Decidable (AgreeR M r u v) :=
  decidable_of_iff (∀ X ∈ rsets M r, u X = v X) (by
    unfold AgreeR
    exact ⟨fun h X hX => h X (mem_rsets.2 hX), fun h X hX => h X (mem_rsets.1 hX)⟩)

/-- `-u`: all signs negated. -/
def negR (u : SignMap) : SignMap := fun X => !u X

/-- `u^X`: the value at `X` negated. -/
def flipR (u : SignMap) (X : List Nat) : SignMap := fun Y => if Y = X then !u Y else u Y

/-- Flip the sets of `Xs`, one after the other. -/
def flipsR (u : SignMap) (Xs : List (List Nat)) : SignMap := Xs.foldl flipR u

/-- `D(u, v)`: the `r`-subsets of `[M]` on which `u` and `v` differ, in lexicographic order. -/
def diffR (M r : Nat) (u v : SignMap) : List (List Nat) := (rsets M r).filter fun X => u X != v X

/-- The Hamming distance `|D(u, v)|`. -/
def hamR (M r : Nat) (u v : SignMap) : Nat := (diffR M r u v).length

/-- `u` and `v` differ in exactly one `r`-subset of `[M]`. -/
def DiffersInOneR (M r : Nat) (u v : SignMap) : Prop :=
  ∃ X, IsRSet M r X ∧ u X ≠ v X ∧ ∀ Y, IsRSet M r Y → Y ≠ X → u Y = v Y

/-- A walk of length `k` from `u` to (a map agreeing with) `v` in the graph whose vertices are the sign maps
satisfying `P`, two maps being adjacent if they differ in exactly one `r`-subset of `[M]`: every map of the walk
satisfies `P`, consecutive maps differ in exactly one `r`-subset, and the last map agrees with `v`. -/
inductive RWalk (M r : Nat) (P : SignMap → Prop) : SignMap → SignMap → Nat → Prop where
  | nil {u v : SignMap} : P u → AgreeR M r u v → RWalk M r P u v 0
  | cons {u v w : SignMap} {k : Nat} :
      P u → DiffersInOneR M r u v → RWalk M r P v w k → RWalk M r P u w (k + 1)

/-- The binomial coefficient, by Pascal's rule. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

end OMDistance
