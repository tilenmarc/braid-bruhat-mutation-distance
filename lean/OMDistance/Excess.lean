import OMDistance.ExcessUpper
import OMDistance.ExcessLower

/-!
# Proposition 8.5 (excess amplification)

Let `S = [m]` (`m ≥ 3`), `N` a set of `c` new elements below `S`, `r ≥ 4`, `q = r - 3 ≤ c`, and `s, t ∈ B(S, 2)`.
With `h = |D(s,t)|`, `H = |D(L s, L t)|`, `λ = binom(c, q)`, `μ = binom(c + m - 3, q)`, the paper proves

  `λ (d_t(Pos₃ s, Pos₃ t) - h) ≤ d_t(Pos_r L s, Pos_r L t) - H ≤ d_B(L s, L t) - H ≤ μ (d_B(s, t) - h)`.

`prop_excess` states this without minima:
1. `L s` and `L t` are signotopes of rank `r` (so the middle terms are defined);
2. (first inequality) every walk of chirotopes of length `ℓ` from `Pos_r L s` to `Pos_r L t` gives a walk of
   chirotopes of length `k` from `Pos₃ s` to `Pos₃ t` with `λ k + H ≤ ℓ + λ h`;
3. (middle inequality, Lemma 6.10(b)) every walk of length `ℓ` in `B(N ∪ S, r-1)` from `L s` to `L t` is a walk of
   chirotopes of length `ℓ` between the positive fibres;
4. (last inequality) every walk of length `k` in `B(S, 2)` from `s` to `t` gives a walk of length `ℓ` in
   `B(N ∪ S, r-1)` from `L s` to `L t` with `ℓ + μ h ≤ H + μ k`.

Labels: `N = [c]`, `S = {c, …, c+m-1}` (the element `i` of `[m]` is `c + i`), `∞ = c + m`.
-/

namespace OMDistance

/-- Proposition 8.5, stated without minima. -/
theorem prop_excess {m c r : Nat} (hm : 3 ≤ m) (hr : 4 ≤ r) (hc : r - 3 ≤ c) {s t : SignMap}
    (hs : IsSignotopeR m 3 s) (ht : IsSignotopeR m 3 t) :
    IsSignotopeR (c + m) r (lift c s) ∧ IsSignotopeR (c + m) r (lift c t) ∧
    (∀ ℓ, ChiroWalk (c + m + 1) r (posF (c + m) (lift c s)) (posF (c + m) (lift c t)) ℓ →
      ∃ k, ChiroWalk (m + 1) 3 (posF m s) (posF m t) k ∧
        binom c (r - 3) * k + hamR (c + m) r (lift c s) (lift c t) ≤ ℓ + binom c (r - 3) * hamR m 3 s t) ∧
    (∀ ℓ, SigWalk (c + m) r (lift c s) (lift c t) ℓ →
      ChiroWalk (c + m + 1) r (posF (c + m) (lift c s)) (posF (c + m) (lift c t)) ℓ) ∧
    (∀ k, SigWalk m 3 s t k → ∃ ℓ, SigWalk (c + m) r (lift c s) (lift c t) ℓ ∧
      ℓ + binom (c + m - 3) (r - 3) * hamR m 3 s t ≤
        hamR (c + m) r (lift c s) (lift c t) + binom (c + m - 3) (r - 3) * k) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 3 := ⟨r - 3, by omega⟩
  have hq : q + 3 - 3 = q := by omega
  rw [hq] at hc ⊢
  refine ⟨lift_signotope hc hs, lift_signotope hc ht, fun ℓ hw => excess_lower hm hc hw,
    fun ℓ hw => sheet_b (by omega) (by omega) hw, fun k hw => excess_upper hc hw⟩

end OMDistance
