import OMDistance.Binom

/-!
# Arithmetic for Theorem 7.2: `-Pos₃(v_G)` is far

With `m = 3n + e` (`e = |E|`), `|D| = 3n(m-3) + 6e` and `VC(G) ≤ n - 1`, the proof of Theorem 7.2 needs
`2|D| + 2(n-1) < binom(m+1, 3)` when `n ≥ 3`.  (Paper: `2|D| + 2VC ≤ 6n(m-3) + 12(m-3n) + 2n - 2 < n(6m-52) + 12m`,
then `n ≤ m/3` and `binom(m+1,3) - 2m² + 16m/3 = (m/6)(m² - 12m + 31) > 0` for `m ≥ 9`.)
-/

namespace OMDistance

theorem rank3_far {n e m : Nat} (hm : m = 3 * n + e) (hn : 3 ≤ n) :
    2 * (3 * n * (m - 3) + 6 * e) + 2 * (n - 1) < binom (m + 1) 3 := by
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 3 := ⟨n - 3, by omega⟩
  subst hm
  have h6 := binom_three (3 * (a + 3) + e + 1)
  have e1 : 3 * (a + 3) + e - 3 = (3 * a + e) + 6 := by omega
  have e2 : 3 * (a + 3) + e + 1 - 1 = (3 * a + e) + 9 := by omega
  have e3 : 3 * (a + 3) + e + 1 - 2 = (3 * a + e) + 8 := by omega
  have e4 : 3 * (a + 3) + e + 1 = (3 * a + e) + 10 := by omega
  rw [e1]
  rw [e2, e3, e4] at h6
  rw [e4]
  generalize hs : 3 * a + e = s at h6 ⊢
  have hcube : (s + 10) * (s + 9) * (s + 8) = s * s * s + 27 * (s * s) + 242 * s + 720 := by
    grind
  have hlhs : 2 * (3 * (a + 3) * (s + 6) + 6 * e) + 2 * (a + 3 - 1)
      = 6 * (a * s) + 38 * a + 18 * s + 12 * e + 112 := by
    have : 3 * (a + 3) * (s + 6) = 3 * (a * s) + 18 * a + 9 * s + 54 := by grind
    omega
  have has : 3 * (a * s) ≤ s * s := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right s (by omega)
  have hss : s ≤ s * s := by
    cases s with
    | zero => omega
    | succ t => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos t)
  have hsss : 0 ≤ s * s * s := Nat.zero_le _
  omega

end OMDistance
