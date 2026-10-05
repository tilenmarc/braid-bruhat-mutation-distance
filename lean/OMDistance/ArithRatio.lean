import OMDistance.Binom

/-!
# Arithmetic for Theorem 8.6: `μ/λ < (k+1)/k`

For `q ≥ 1`, `k ≥ 1` and `c = q m (k+1) + q`, with `λ = binom(c, q)` and `μ = binom(c + m - 3, q)`:
`μ k < λ (k+1)`.  (Paper: `μ/λ = Π_{j<q} (1 + (m-3)/(c-j)) ≤ (1 + (m-3)/(c-q+1))^q ≤ 1/(1 - q(m-3)/(c-q+1))`
by Bernoulli's inequality, and `c - q + 1 > q m (k+1)` gives `< 1/(1 - 1/(k+1)) = (k+1)/k`.)
-/

namespace OMDistance

/-- Absorption identity: `(q+1) binom(n+1, q+1) = (n+1) binom(n, q)`. -/
private theorem succ_mul_binom_succ (n q : Nat) :
    (q + 1) * binom (n + 1) (q + 1) = (n + 1) * binom n q := by
  induction n generalizing q with
  | zero =>
    cases q with
    | zero => rfl
    | succ q => rw [binom_succ_succ, binom_eq_zero_of_lt (by omega), binom_eq_zero_of_lt (by omega)]; rfl
  | succ n ih =>
    cases q with
    | zero => rw [binom_one, binom_zero_right]; omega
    | succ q =>
      have h1 := ih q
      have h2 := ih (q + 1)
      rw [binom_succ_succ (n + 1) (q + 1)]
      rw [binom_succ_succ n q] at h1 ⊢
      grind

/-- Step 1: `binom(y+q+d, q) (y+1)^q ≤ binom(y+q, q) (y+1+d)^q`. -/
private theorem binom_shift_le (y d q : Nat) :
    binom (y + q + d) q * (y + 1) ^ q ≤ binom (y + q) q * (y + 1 + d) ^ q := by
  induction q with
  | zero => simp [binom_zero_right]
  | succ q ih =>
    have hA := succ_mul_binom_succ (y + q + d) q
    have hB := succ_mul_binom_succ (y + q) q
    have e1 : y + (q + 1) + d = y + q + d + 1 := by omega
    have e2 : y + (q + 1) = y + q + 1 := by omega
    rw [e1, e2]
    have hlin : (y + q + d + 1) * (y + 1) ≤ (y + q + 1) * (y + 1 + d) := by
      have : (y + q + d + 1) * (y + 1) + q * d = (y + q + 1) * (y + 1 + d) := by grind
      omega
    have hprod := Nat.mul_le_mul ih hlin
    apply Nat.le_of_mul_le_mul_left (c := q + 1) _ (by omega)
    calc (q + 1) * (binom (y + q + d + 1) (q + 1) * (y + 1) ^ (q + 1))
        = ((q + 1) * binom (y + q + d + 1) (q + 1)) * (y + 1) ^ (q + 1) := by grind
      _ = (binom (y + q + d) q * (y + 1) ^ q) * ((y + q + d + 1) * (y + 1)) := by
          rw [hA, Nat.pow_succ]; grind
      _ ≤ (binom (y + q) q * (y + 1 + d) ^ q) * ((y + q + 1) * (y + 1 + d)) := hprod
      _ = ((q + 1) * binom (y + q + 1) (q + 1)) * (y + 1 + d) ^ (q + 1) := by
          rw [hB, Nat.pow_succ]; grind
      _ = (q + 1) * (binom (y + q + 1) (q + 1) * (y + 1 + d) ^ (q + 1)) := by grind

/-- Step 2 (Bernoulli): `x (x+d)^q ≤ x^{q+1} + q d (x+d)^q`. -/
private theorem bernoulli (x d q : Nat) :
    x * (x + d) ^ q ≤ x ^ (q + 1) + q * d * (x + d) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hpow : x ^ (q + 1) ≤ (x + d) ^ (q + 1) := Nat.pow_le_pow_left (by omega) _
    have h1 := Nat.mul_le_mul_right (x + d) ih
    have h2 := Nat.mul_le_mul_left d hpow
    calc x * (x + d) ^ (q + 1) = x * (x + d) ^ q * (x + d) := by rw [Nat.pow_succ]; grind
      _ ≤ (x ^ (q + 1) + q * d * (x + d) ^ q) * (x + d) := h1
      _ = x ^ (q + 1 + 1) + d * x ^ (q + 1) + q * d * (x + d) ^ (q + 1) := by
          rw [Nat.pow_succ x (q + 1), Nat.pow_succ (x + d) q]; grind
      _ ≤ x ^ (q + 1 + 1) + d * (x + d) ^ (q + 1) + q * d * (x + d) ^ (q + 1) := by omega
      _ = x ^ (q + 1 + 1) + (q + 1) * d * (x + d) ^ (q + 1) := by grind

theorem ratio_bound {q m k : Nat} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    binom (q * m * (k + 1) + q + m - 3) q * k < binom (q * m * (k + 1) + q) q * (k + 1) := by
  have hLpos : 0 < binom (q * m * (k + 1) + q) q := binom_pos (by omega)
  by_cases hm : m < 3
  · have := binom_mono q (show q * m * (k + 1) + q + m - 3 ≤ q * m * (k + 1) + q by omega)
    have := Nat.mul_le_mul_right k this
    have : binom (q * m * (k + 1) + q) q * k < binom (q * m * (k + 1) + q) q * (k + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hLpos
    omega
  · -- `y = q m (k+1)`, `x = y + 1`, `d = m - 3`.
    obtain ⟨d, rfl⟩ : ∃ d, m = d + 3 := ⟨m - 3, by omega⟩
    generalize hy : q * (d + 3) * (k + 1) = y at hLpos ⊢
    have e : y + q + (d + 3) - 3 = y + q + d := by omega
    rw [e]
    generalize hM : binom (y + q + d) q = M
    generalize hL : binom (y + q) q = L at hLpos ⊢
    have s1 : M * (y + 1) ^ q ≤ L * (y + 1 + d) ^ q := by
      rw [← hM, ← hL]; exact binom_shift_le y d q
    have s2 := bernoulli (y + 1) d q
    generalize hX : (y + 1) ^ q = X at s1 s2
    generalize hP : (y + 1 + d) ^ q = P at s1 s2
    have hXpos : 0 < X := by rw [← hX]; exact Nat.pow_pos (by omega)
    rw [Nat.pow_succ, hX] at s2
    -- `(k+1) q d < y + 1`, since `y = q (d+3) (k+1)`.
    have hqd : (k + 1) * (q * d) + 1 ≤ y + 1 := by
      have : (k + 1) * (q * d) + (k + 1) * (q * 3) = y := by rw [← hy]; grind
      have : 1 ≤ (k + 1) * (q * 3) := Nat.mul_pos (by omega) (by omega)
      omega
    -- `e = x - q d`
    obtain ⟨e, he⟩ : ∃ e, y + 1 = e + q * d := ⟨y + 1 - q * d, by
      have : q * d ≤ (k + 1) * (q * d) := Nat.le_mul_of_pos_left _ (by omega)
      omega⟩
    have hepos : 0 < e := by
      have : q * d ≤ k * (q * d) := Nat.le_mul_of_pos_left _ (by omega)
      have : (k + 1) * (q * d) = k * (q * d) + q * d := by grind
      omega
    -- Bernoulli: `e P ≤ x X`
    have hB : e * P ≤ X * (y + 1) := by
      have : (y + 1) * P = e * P + q * d * P := by rw [he]; grind
      omega
    -- `k x < (k+1) e`
    have h3 : k * (y + 1) < (k + 1) * e := by
      have : (k + 1) * (y + 1) = (k + 1) * e + (k + 1) * (q * d) := by rw [he]; grind
      have : (k + 1) * (y + 1) = k * (y + 1) + (y + 1) := by grind
      omega
    -- Combine: `M k e X ≤ L k e P ≤ L k x X < L (k+1) e X`.
    have c1 : M * k * (e * X) ≤ L * k * (y + 1) * X := by
      have a := Nat.mul_le_mul_left (k * e) s1
      have b := Nat.mul_le_mul_left (L * k) hB
      calc M * k * (e * X) = k * e * (M * X) := by grind
        _ ≤ k * e * (L * P) := a
        _ = L * k * (e * P) := by grind
        _ ≤ L * k * (X * (y + 1)) := b
        _ = L * k * (y + 1) * X := by grind
    have c2 : L * k * (y + 1) * X < L * (k + 1) * (e * X) := by
      have := Nat.mul_lt_mul_of_pos_left h3 (Nat.mul_pos hLpos hXpos)
      calc L * k * (y + 1) * X = L * X * (k * (y + 1)) := by grind
        _ < L * X * ((k + 1) * e) := this
        _ = L * (k + 1) * (e * X) := by grind
    exact Nat.lt_of_mul_lt_mul_right (a := e * X) (Nat.lt_of_le_of_lt c1 c2)

end OMDistance
