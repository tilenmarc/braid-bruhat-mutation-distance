import OMDistance.Basic
import BraidDistance.Signotope

/-!
# Signotopes of rank r, higher Bruhat orders and the positive fibre (Definition 6.8, Proposition 6.9)

Trusted definitions.  The ground set is `[M] = {0, …, M-1}`.

* **Packets** (Definition 6.8).  For an `(r+1)`-subset `P = {p₁ < ⋯ < p_{r+1}}` the packet is
  `u[P] = (u(P ∖ p_{r+1}), u(P ∖ p_r), …, u(P ∖ p₁))`, the values on the `r`-subsets of `P` in lexicographic
  order (`rpacket`; `P.eraseIdx i` is `P ∖ p_{i+1}`, and `i` runs from `r` down to `0`).  For `r = 3` this is Part
  I's packet `(u(abc), u(abd), u(acd), u(bcd))`.
* **`IsSignotopeR M r u`**: every packet of an `(r+1)`-subset of `[M]` has at most one sign change (Part I's
  `oneChange`).  These are the vertices of the higher Bruhat order `B([M], r-1)`.
* **`SigWalk M r u v k`**: a walk of length `k` in `B([M], r-1)` (consecutive signotopes differ in exactly one
  `r`-set, i.e. are related by a flip).  The flip distance `d_B(u, v)` is the least such `k`.
* **The positive fibre** (Proposition 6.9).  The ground set `S = [M]` is extended by `∞ = M`, placed above all
  elements, to `Ω = [M+1]`; `posF M u` is `+` on every set containing `∞` and `u(B)` on the other sets.  The rank
  `r` is implicit: `posF M u` is evaluated on `r`-subsets of `[M+1]`.
* **Bridge to Part I.**  Part I's rank-3 sign maps are `SMap = Nat → Nat → Nat → Bool`; `ofSMap u` is the same map
  on 3-sets `[a, b, c]` (and `+` on lists of other shapes, which are never used), and `toSMap χ` is the converse.
-/

namespace OMDistance

/-- The packet `u[P] = (u(P ∖ p_{r+1}), …, u(P ∖ p₁))`: the values on the subsets of `P` with one element
removed, in lexicographic order. -/
def rpacket (u : SignMap) (P : List Nat) : List Bool :=
  (List.range P.length).reverse.map fun i => u (P.eraseIdx i)

/-- Definition 6.8: `u` is a signotope of rank `r` on `[M]` (every packet has at most one sign change). -/
def IsSignotopeR (M r : Nat) (u : SignMap) : Prop :=
  ∀ P, IsRSet M (r + 1) P → BraidDistance.oneChange (rpacket u P) = true

theorem isSignotopeR_iff_rsets (M r : Nat) (u : SignMap) :
    IsSignotopeR M r u ↔ ∀ P ∈ rsets M (r + 1), BraidDistance.oneChange (rpacket u P) = true := by
  unfold IsSignotopeR
  exact ⟨fun h P hP => h P (mem_rsets.1 hP), fun h P hP => h P (mem_rsets.2 hP)⟩

instance (M r : Nat) (u : SignMap) : Decidable (IsSignotopeR M r u) :=
  decidable_of_iff' _ (isSignotopeR_iff_rsets M r u)

/-- A walk of length `k` in the higher Bruhat order `B([M], r-1)` from `u` to `v`. -/
abbrev SigWalk (M r : Nat) : SignMap → SignMap → Nat → Prop := RWalk M r (IsSignotopeR M r)

/-- The positive fibre `Pos_r(u)` on `[M+1] = [M] ∪ {∞}`, `∞ = M`: `+` on sets containing `∞`, `u` otherwise. -/
def posF (M : Nat) (u : SignMap) : SignMap := fun B => if M ∈ B then true else u B

/-- A Part I sign map (on triples) as a sign map on 3-sets. -/
def ofSMap (u : BraidDistance.SMap) : SignMap := fun X =>
  match X with
  | [a, b, c] => u a b c
  | _ => true

/-- A sign map on 3-sets as a Part I sign map. -/
def toSMap (χ : SignMap) : BraidDistance.SMap := fun a b c => χ [a, b, c]

end OMDistance
