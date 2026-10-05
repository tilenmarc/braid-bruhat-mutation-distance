import OMDistance.Basic

/-!
# Uniform chirotopes, walks of chirotopes and the mutation graph (Definitions 6.1, 6.2)

Trusted definitions.  The ground set is `Ω = [M] = {0, …, M-1}` with its natural order.

* **Ordered tuples.**  A map `χ` on `r`-subsets is extended to ordered tuples `(e₁, …, e_r)` of distinct elements by
  `χ(e₁, …, e_r) = sgn(π) χ({e₁, …, e_r})`, where `π` sorts the tuple (`tupleVal`).  The set `{e₁, …, e_r}` is the
  sorted list `isort [e₁, …, e_r]` (insertion sort), and `sgn(π) = (-1)^inv` where `inv` is the number of
  inversions of the tuple (`inversions`: pairs of positions `i < j` with `e_i > e_j`).  For a tuple of distinct
  entries this is the sign of the sorting permutation.
* **Signs.**  `true` is `+`; the sign of a product of two signs is `smul x y = (x == y)`, and `-x` is `!x`.
* **(GP).**  For an `(r-2)`-subset `σ = {σ₁ < ⋯ < σ_{r-2}}` (a strictly increasing list) and `x, y`,
  `χ(σ, x, y) = χ(σ₁, …, σ_{r-2}, x, y) = tupleVal χ (σ ++ [x, y])` (`chiPair`).  `GP χ σ a b c d` says that
  the three signs `χ(σ,a,b)χ(σ,c,d)`, `-χ(σ,a,c)χ(σ,b,d)`, `χ(σ,a,d)χ(σ,b,c)` are not all equal.
* **`IsChirotope M r χ`** (Definition 6.1): `2 ≤ r ≤ M`, and (GP) holds for every `(r-2)`-subset `σ` of `[M]` and
  all `a < b < c < d` in `[M] ∖ σ`.  These are the uniform chirotopes of rank `r` on `[M]`; the `r`-subsets of
  `[M]` are the *bases*.  Only the values of `χ` on bases are used.
* **Walks of chirotopes** (`ChiroWalk M r χ ψ k`): `χ = χ₀, χ₁, …, χ_k` uniform chirotopes of rank `r` on `[M]`,
  consecutive ones differing in exactly one basis, `χ_k` agreeing with `ψ` on all bases.
* **The mutation graph** (Definition 6.2): its vertices are the uniform oriented matroids `[χ] = {χ, -χ}`, and
  `[χ] ∼ [ψ]` if some representatives differ in exactly one basis.  `OMWalk M r χ ψ k` is a walk of length `k`
  from `[χ]` to `[ψ]`, given by representatives `χ = χ₀, χ₁, …, χ_k`: each `χ_i` is a uniform chirotope, `χ_i` and
  `χ_{i+1}` or `χ_i` and `-χ_{i+1}` differ in exactly one basis (that is, `[χ_i] ∼ [χ_{i+1}]`), and `χ_k` agrees
  with `ψ` or with `-ψ` on all bases (that is, `[χ_k] = [ψ]`).  The mutation distance `d([χ], [ψ])` is the least
  `k` with `OMWalk M r χ ψ k`.

A more convenient equivalent form of (GP), with the values of `χ` taken on sets, is proved in
`ChiroSetForm.lean` (`isChirotope_iff_set`).
-/

namespace OMDistance

/-- The number of inversions of a list: pairs of positions `i < j` with `l[i] > l[j]`. -/
def inversions : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter fun y => decide (y < x)).length + inversions xs

/-- Insert `x` into a sorted list. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

/-- Insertion sort. -/
def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (isort xs)

/-- `χ(e₁, …, e_r) = sgn(π) χ({e₁, …, e_r})`, where `π` sorts the tuple and `sgn(π) = (-1)^(#inversions)`. -/
def tupleVal (χ : SignMap) (e : List Nat) : Bool :=
  if inversions e % 2 = 0 then χ (isort e) else !χ (isort e)

/-- The sign of the product of two signs (`true` is `+`). -/
def smul (x y : Bool) : Bool := x == y

/-- `χ(σ, x, y) = χ(σ₁, …, σ_{r-2}, x, y)`, the value of `χ` at the ordered tuple `σ ++ [x, y]`. -/
def chiPair (χ : SignMap) (σ : List Nat) (x y : Nat) : Bool := tupleVal χ (σ ++ [x, y])

/-- (GP) at `σ` and `a, b, c, d`: the three signs `χ(σ,a,b)χ(σ,c,d)`, `-χ(σ,a,c)χ(σ,b,d)`, `χ(σ,a,d)χ(σ,b,c)`
are not all equal. -/
def GP (χ : SignMap) (σ : List Nat) (a b c d : Nat) : Prop :=
  ¬ (smul (chiPair χ σ a b) (chiPair χ σ c d) = (!smul (chiPair χ σ a c) (chiPair χ σ b d)) ∧
     (!smul (chiPair χ σ a c) (chiPair χ σ b d)) = smul (chiPair χ σ a d) (chiPair χ σ b c))

instance (χ : SignMap) (σ : List Nat) (a b c d : Nat) : Decidable (GP χ σ a b c d) := by
  unfold GP; infer_instance

/-- Definition 6.1: `χ` is a uniform chirotope of rank `r` on `[M]`. -/
def IsChirotope (M r : Nat) (χ : SignMap) : Prop :=
  2 ≤ r ∧ r ≤ M ∧
    ∀ σ, IsRSet M (r - 2) σ → ∀ d < M, ∀ c < d, ∀ b < c, ∀ a < b,
      a ∉ σ → b ∉ σ → c ∉ σ → d ∉ σ → GP χ σ a b c d

/-- (GP) at `σ` and `a, b, c, d` whenever none of `a, b, c, d` lies in `σ` (used for decidability only). -/
def GPOut (χ : SignMap) (σ : List Nat) (a b c d : Nat) : Prop :=
  a ∉ σ → b ∉ σ → c ∉ σ → d ∉ σ → GP χ σ a b c d

instance (χ : SignMap) (σ : List Nat) (a b c d : Nat) : Decidable (GPOut χ σ a b c d) := by
  unfold GPOut; infer_instance

/-- (GP) at `σ` for all `a < b < c < d < M` outside `σ` (used for decidability only). -/
def GPAll (M : Nat) (χ : SignMap) (σ : List Nat) : Prop :=
  ∀ d < M, ∀ c < d, ∀ b < c, ∀ a < b, GPOut χ σ a b c d

instance (M : Nat) (χ : SignMap) (σ : List Nat) : Decidable (GPAll M χ σ) := by
  unfold GPAll; infer_instance

theorem isChirotope_iff_gpAll (M r : Nat) (χ : SignMap) :
    IsChirotope M r χ ↔ (2 ≤ r ∧ r ≤ M ∧ ∀ σ ∈ rsets M (r - 2), GPAll M χ σ) := by
  unfold IsChirotope GPAll GPOut
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun σ hσ => h3 σ (mem_rsets.1 hσ)⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun σ hσ => h3 σ (mem_rsets.2 hσ)⟩⟩

instance (M r : Nat) (χ : SignMap) : Decidable (IsChirotope M r χ) :=
  decidable_of_iff' _ (isChirotope_iff_gpAll M r χ)

/-- A walk of chirotopes of rank `r` on `[M]` of length `k` from `χ` to `ψ`. -/
abbrev ChiroWalk (M r : Nat) : SignMap → SignMap → Nat → Prop := RWalk M r (IsChirotope M r)

/-- A walk of length `k` in the mutation graph of rank `r` on `[M]` from `[χ]` to `[ψ]`, given by
representatives `χ = χ₀, …, χ_k` (see the module docstring). -/
inductive OMWalk (M r : Nat) : SignMap → SignMap → Nat → Prop where
  | nil {χ ψ : SignMap} : IsChirotope M r χ → (AgreeR M r χ ψ ∨ AgreeR M r χ (negR ψ)) → OMWalk M r χ ψ 0
  | cons {χ χ' ψ : SignMap} {k : Nat} : IsChirotope M r χ →
      (DiffersInOneR M r χ χ' ∨ DiffersInOneR M r χ (negR χ')) → OMWalk M r χ' ψ k →
      OMWalk M r χ ψ (k + 1)

end OMDistance
