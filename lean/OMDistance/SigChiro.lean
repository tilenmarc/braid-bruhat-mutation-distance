import OMDistance.SignotopeBasic

/-!
# Every signotope is a uniform chirotope (end of Section 6.2)

Every rank-`r` signotope on `[M]`, `2 ≤ r ≤ M`, extended to ordered tuples as in Definition 6.1, is a uniform
chirotope of rank `r` (Bergold; Miyata).

Proof: fix `σ` and `a < b < c < d` outside `σ`, and let `t_xy = u(σ ∪ {x, y})`.  By `signotope_triple`, for
`x < y < z` in `{a, b, c, d}` the values `(t_xy, t_xz, t_yz)` have at most one sign change; so `t` is a rank-2
signotope on the four points `a, b, c, d`, and the set form of (GP) follows from the finite check
`gp6_of_oneChange` over the 64 sign patterns.
-/

namespace OMDistance

/-- (GP) for rank-2 signotopes on four points: a finite check over the 64 sign patterns. -/
theorem gp6_of_oneChange : ∀ ab ac ad bc bd cd : Bool,
    BraidDistance.oneChange [ab, ac, bc] = true → BraidDistance.oneChange [ab, ad, bd] = true →
    BraidDistance.oneChange [ac, ad, cd] = true → BraidDistance.oneChange [bc, bd, cd] = true →
    gp6 ab ac ad bc bd cd = true := by
  decide

/-- Every signotope of rank `r` on `[M]`, `2 ≤ r ≤ M`, is a uniform chirotope of rank `r`. -/
theorem signotope_isChirotope {M r : Nat} (hr : 2 ≤ r) (hrM : r ≤ M) {u : SignMap}
    (hu : IsSignotopeR M r u) : IsChirotope M r u := by
  rw [isChirotope_iff_set]
  refine ⟨hr, hrM, fun σ hσ d hd c hcd b hbc a hab ha hb hc hdσ => ?_⟩
  have hcM : c < M := Nat.lt_trans hcd hd
  exact gp6_of_oneChange _ _ _ _ _ _
    (signotope_triple hr hu hσ hab hbc hcM ha hb hc)
    (signotope_triple hr hu hσ hab (Nat.lt_trans hbc hcd) hd ha hb hdσ)
    (signotope_triple hr hu hσ (Nat.lt_trans hab hbc) hcd hd ha hc hdσ)
    (signotope_triple hr hu hσ hbc hcd hd hb hc hdσ)

end OMDistance
