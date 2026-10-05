import OMDistance.Lift
import OMDistance.Signotope
import OMDistance.WalkLemmas

/-!
# Adding one element (Lemma 8.1(a))

A new element `ℓ` is added below the ground set; in 0-based labels the ground set `[M]` becomes `[M+1]` with
`ℓ = 0` and the old element `x` relabelled `x + 1`, and `v'(Z) = v(Z ∖ min Z)` is `expand v`.

* (a) If `v` is a signotope of rank `k`, then `v'` is a signotope of rank `k + 1`: the packet of
  `P = {p₁ < ⋯ < p_{k+2}}` under `v'` is the packet of `P ∖ p₁` under `v` followed by a repetition of its last
  entry.
* (b) Let `v` and `v^X` be signotopes of rank `k ≥ 2`, `X = {t₁ < ⋯ < t_k}`.  In the new labels
  `Λ = {ℓ} ∪ {x < t₁} = {0, 1, …, t₁}` and `Q_x = {x} ∪ (X + 1)` (`qsets X`).  Then `v'` and `(v^X)'` differ exactly
  on the sets `Q_x`, and there is a walk in `B([M+1], k)` from `v'` to `(v^X)'` flipping each `Q_x` exactly once.
  The order: start with `(ℓ)` and add the elements `x` of `Λ ∖ {ℓ}` in increasing order, each *early* one
  (`α_x = v(X)`, where `α_x` is the common value of `v((x ∪ X) ∖ t_i)`) at the front and each *late* one at the
  back; then an early `y` precedes, and a late `y` follows, every smaller element of `Λ` (equation (8.1)), which
  keeps every packet with at most one sign change.  Part (b) is `onestep_b` in `OneStepWalk.lean`.
-/

namespace OMDistance

open BraidDistance (StrictIncr signChanges oneChange)

private theorem signChanges_dup (a : Bool) : ∀ L : List Bool,
    signChanges (L ++ [a, a]) = signChanges (L ++ [a])
  | [] => by simp [signChanges]
  | [x] => by simp [signChanges]
  | x :: y :: L => by
    have ih := signChanges_dup a (y :: L)
    simp only [List.cons_append] at ih ⊢
    simp only [signChanges, ih]

private theorem rpacket_last (v : SignMap) (Q : List Nat) (h : Q ≠ []) :
    ∃ A, rpacket v Q = A ++ [v (Q.eraseIdx 0)] := by
  obtain ⟨n, hn⟩ : ∃ n, Q.length = n + 1 := by
    cases Q with
    | nil => exact absurd rfl h
    | cons q Q => exact ⟨Q.length, rfl⟩
  refine ⟨((List.range n).map Nat.succ).reverse.map fun i => v (Q.eraseIdx i), ?_⟩
  unfold rpacket
  rw [hn, List.range_succ_eq_map]
  simp

private theorem map_eraseIdx' (f : Nat → Nat) : ∀ (Q : List Nat) (i : Nat),
    (Q.eraseIdx i).map f = (Q.map f).eraseIdx i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | q :: Q, i + 1 => by simp [map_eraseIdx' f Q i]

private theorem rpacket_expand (v : SignMap) (p : Nat) (Q : List Nat) :
    rpacket (expand v) (p :: Q) = rpacket v (Q.map (· - 1)) ++ [v ((Q.map (· - 1)).eraseIdx 0)] := by
  unfold rpacket
  rw [List.length_cons, List.range_succ_eq_map]
  simp only [List.reverse_cons, List.map_append, List.map_reverse, List.map_map, List.length_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro i _
    simp [expand, Function.comp, List.eraseIdx_cons_succ, map_eraseIdx']
  · simp [expand]

private theorem strictIncr_pred (p : Nat) : ∀ Q : List Nat, StrictIncr (p :: Q) →
    StrictIncr (Q.map (· - 1))
  | [], _ => by simp [StrictIncr]
  | q :: Q, h => by
    simp only [StrictIncr, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    have ih := strictIncr_pred q Q (by simp only [StrictIncr, List.pairwise_cons]; exact ⟨h.2.1, h.2.2⟩)
    simp only [StrictIncr, List.map_cons, List.pairwise_cons, List.mem_map] at ih ⊢
    refine ⟨?_, ih⟩
    rintro _ ⟨x, hx, rfl⟩
    have := h.2.1 x hx
    have := h.1.1
    omega


/-- Lemma 8.1(a). -/
theorem onestep_a {M k : Nat} {v : SignMap} (hv : IsSignotopeR M k v) : IsSignotopeR (M + 1) (k + 1) (expand v) := by
  intro P hP
  obtain ⟨hlen, hinc, hlt⟩ := hP
  cases P with
  | nil => simp at hlen
  | cons p Q =>
    have hQ : IsRSet M (k + 1) (Q.map (· - 1)) := by
      refine ⟨by simp at hlen ⊢; omega, strictIncr_pred p Q hinc, ?_⟩
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 := hlt y (List.mem_cons_of_mem _ hy)
      have h2 : p < y := by
        simp only [StrictIncr, List.pairwise_cons] at hinc
        exact hinc.1 y hy
      omega
    have hne : Q.map (· - 1) ≠ [] := by
      intro h; rw [h] at hQ; simp [IsRSet] at hQ
    have hv' := hv _ hQ
    rw [rpacket_expand]
    obtain ⟨A, hA⟩ := rpacket_last v _ hne
    rw [hA] at hv' ⊢
    simp only [oneChange, List.append_assoc, List.cons_append, List.nil_append] at hv' ⊢
    rw [signChanges_dup]
    exact hv'

/-- The sets `Q_x = {x} ∪ (X + 1)`, `x = 0, 1, …, t₁` (new labels, `t₁ = min X` in old labels). -/
def qsets (X : List Nat) : List (List Nat) := (List.range (X.headD 0 + 1)).map fun x => x :: X.map (· + 1)

end OMDistance
