import BraidDistance.Basic

/-!
# Packets, rank-3 signotopes and walks of signotopes (Section 2.2)

* The *packet* of a 4-set `a < b < c < d` is `u[abcd] = (u(abc), u(abd), u(acd), u(bcd))`.
* A list of signs has *at most one sign change* if, read from left to right, it switches between `+` and `-`
  at most once.
* A *signotope of rank 3* on `[m]` is a sign map all of whose packets (of 4-sets of `[m]`) have at most one sign
  change; these are the vertices of `B(m,2)`.
* `DiffersInOne m u v`: `u` and `v` differ in exactly one valid triple (an edge of `B(m,2)`).
* `Walk m u v k`: a walk `u = u₀, u₁, …, u_k` of signotopes, consecutive maps differing in exactly one triple,
  whose last map agrees with `v` on all valid triples; `k` is its length.  The paper's `d_B(u, v)` is the least
  such `k`.
* `FlipWalk m s ts`: the same walk described by its start `s` and the list `ts` of flipped triples: every
  `flipList s (ts.take i)` is a signotope.  It is the form used in the lower-bound arguments.
-/

namespace BraidDistance

/-- The packet `u[abcd] = (u(abc), u(abd), u(acd), u(bcd))`. -/
def packet (u : SMap) (a b c d : Nat) : List Bool := [u a b c, u a b d, u a c d, u b c d]

/-- The number of sign changes of a list of signs, read from left to right. -/
def signChanges : List Bool → Nat
  | x :: y :: rest => (if x = y then 0 else 1) + signChanges (y :: rest)
  | _ => 0

/-- At most one sign change. -/
def oneChange (l : List Bool) : Bool := decide (signChanges l ≤ 1)

/-- A signotope of rank 3 on `[m]`: every packet has at most one sign change. -/
def IsSignotope (m : Nat) (u : SMap) : Prop :=
  ∀ d < m, ∀ c < d, ∀ b < c, ∀ a < b, oneChange (packet u a b c d) = true

instance (m : Nat) (u : SMap) : Decidable (IsSignotope m u) := by
  unfold IsSignotope; infer_instance

/-- `u` and `v` differ in exactly one valid triple of `[m]`. -/
def DiffersInOne (m : Nat) (u v : SMap) : Prop :=
  ∃ t : Triple, ValidTriple m t ∧ u.at t ≠ v.at t ∧
    ∀ t' : Triple, ValidTriple m t' → t' ≠ t → u.at t' = v.at t'

/-- A walk of signotopes of rank 3 on `[m]` of length `k`, from `u` to (a map agreeing with) `v`:
every map is a signotope and consecutive maps differ in exactly one triple. -/
inductive Walk (m : Nat) : SMap → SMap → Nat → Prop where
  | nil {u v : SMap} : IsSignotope m u → Agree m u v → Walk m u v 0
  | cons {u v w : SMap} {k : Nat} :
      IsSignotope m u → DiffersInOne m u v → Walk m v w k → Walk m u w (k + 1)

/-- A walk of signotopes given by its start `s` and the list of flipped triples `ts`. -/
def FlipWalk (m : Nat) (s : SMap) (ts : List Triple) : Prop :=
  (∀ t ∈ ts, ValidTriple m t) ∧ ∀ i, i ≤ ts.length → IsSignotope m (flipList s (ts.take i))

end BraidDistance
