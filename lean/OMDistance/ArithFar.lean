import OMDistance.Binom

/-!
# Arithmetic for Theorem 8.6: `-Pos_r(L v_G)` is far

For `q ≥ 1`, `m ≥ 3`, `k ≥ 1`, `c = q m (k+1) + q`, `M = c + m`, `r = q + 3`, `μ = binom(c + m - 3, q)`:
`4 μ binom(m, 3) < binom(M, r)`.

Paper: `M ≥ (r-1) m`, `binom(M, r) = μ binom(M, 3) / binom(r, 3)` (`binom_mul_binom`),
`binom(M, 3) ≥ (r-1)³ binom(m, 3)`, and `(r-1)³ / binom(r, 3) = 6 (r-1)² / (r (r-2)) > 4`.
-/

namespace OMDistance

theorem far_bound {q m k : Nat} (hq : 1 ≤ q) (hm : 3 ≤ m) (hk : 1 ≤ k) :
    4 * binom (q * m * (k + 1) + q + m - 3) q * binom m 3 < binom (q * m * (k + 1) + q + m) (q + 3) := by
  generalize hM : q * m * (k + 1) + q + m = M
  have hP : q * m * 2 ≤ q * m * (k + 1) := Nat.mul_le_mul_left _ (by omega)
  have hqm : m ≤ q * m := by
    have := Nat.mul_le_mul_right m hq
    omega
  have hMge : (q + 2) * m ≤ M := by
    have e : (q + 2) * m = q * m + 2 * m := by rw [Nat.add_mul]
    have e2 : q * m * 2 = q * m + q * m := by omega
    omega
  have hqM : q + 3 ≤ M := by
    have : 3 * (q + 2) ≤ (q + 2) * m := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hm
    omega
  have h1 := binom_mul_binom (n := M) (k := q + 3) (j := 3) (by omega) hqM
  rw [show q + 3 - 3 = q by omega] at h1
  have h6M := binom_three M
  have h6m := binom_three m
  have h6B := binom_three (q + 3)
  rw [show q + 3 - 1 = q + 2 by omega, show q + 3 - 2 = q + 1 by omega] at h6B
  -- the (q+2)^3 comparison
  have a1 : (q + 2) * (m - 1) ≤ M - 1 := by
    have : (q + 2) * (m - 1) + (q + 2) = (q + 2) * m := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  have a2 : (q + 2) * (m - 2) ≤ M - 2 := by
    have : (q + 2) * (m - 2) + (q + 2) * 2 = (q + 2) * m := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  have hprod : ((q + 2) * m) * ((q + 2) * (m - 1)) * ((q + 2) * (m - 2)) ≤ M * (M - 1) * (M - 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul hMge a1) a2
  have hX : 0 < m * (m - 1) * (m - 2) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hq3 : 2 * ((q + 3) * (q + 1)) < 3 * ((q + 2) * (q + 2)) := by
    have e1 : (q + 3) * (q + 1) = q * q + 4 * q + 3 := by grind
    have e2 : (q + 2) * (q + 2) = q * q + 4 * q + 4 := by grind
    omega
  have hcmp : 4 * ((q + 3) * (q + 2) * (q + 1)) * (m * (m - 1) * (m - 2))
      < 6 * (((q + 2) * m) * ((q + 2) * (m - 1)) * ((q + 2) * (m - 2))) := by
    have e1 : 4 * ((q + 3) * (q + 2) * (q + 1)) * (m * (m - 1) * (m - 2))
        = (2 * ((q + 3) * (q + 1))) * (2 * (q + 2) * (m * (m - 1) * (m - 2))) := by grind
    have e2 : 6 * (((q + 2) * m) * ((q + 2) * (m - 1)) * ((q + 2) * (m - 2)))
        = (3 * ((q + 2) * (q + 2))) * (2 * (q + 2) * (m * (m - 1) * (m - 2))) := by grind
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_right hq3 (Nat.mul_pos (by omega) hX)
  -- 36 * (4 B bm) < 36 * binom M 3
  have key : 4 * binom (q + 3) 3 * binom m 3 < binom M 3 := by
    have : 36 * (4 * binom (q + 3) 3 * binom m 3) < 36 * binom M 3 := by
      have l : 36 * (4 * binom (q + 3) 3 * binom m 3)
          = 4 * (6 * binom (q + 3) 3) * (6 * binom m 3) := by grind
      have r : 36 * binom M 3 = 6 * (6 * binom M 3) := by grind
      rw [l, r, h6B, h6m, h6M]
      exact Nat.lt_of_lt_of_le hcmp (Nat.mul_le_mul_left 6 hprod)
    omega
  have hμ : 0 < binom (M - 3) q := binom_pos (by omega)
  have hB : 0 < binom (q + 3) 3 := binom_pos (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := binom (q + 3) 3)
  rw [h1]
  have : 4 * binom (q + 3) 3 * binom m 3 * binom (M - 3) q < binom M 3 * binom (M - 3) q :=
    Nat.mul_lt_mul_of_pos_right key hμ
  have e : 4 * binom (M - 3) q * binom m 3 * binom (q + 3) 3
      = 4 * binom (q + 3) 3 * binom m 3 * binom (M - 3) q := by grind
  rw [e]; exact this

end OMDistance
