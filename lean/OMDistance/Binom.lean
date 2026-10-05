import OMDistance.Basic

/-!
# Binomial coefficients

Elementary facts about `binom` (defined by Pascal's rule in `Basic.lean`).
-/

namespace OMDistance

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

theorem binom_succ_succ (n k : Nat) : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

theorem binom_eq_zero_of_lt {n k : Nat} (h : n < k) : binom n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [binom_succ_succ, ih (by omega), ih (by omega)]

theorem binom_self (n : Nat) : binom n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [binom_succ_succ, ih, binom_eq_zero_of_lt (by omega)]

theorem binom_one (n : Nat) : binom n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [binom_succ_succ, ih, binom_zero_right]; omega

theorem binom_pos {n k : Nat} (h : k ≤ n) : 0 < binom n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [binom_zero_right]; omega
    | succ k => omega
  | succ n ih =>
    cases k with
    | zero => rw [binom_zero_right]; omega
    | succ k =>
      rw [binom_succ_succ]
      have := ih (k := k) (by omega)
      omega

private theorem binom_le_succ (n k : Nat) : binom n k ≤ binom (n + 1) k := by
  cases k with
  | zero => rw [binom_zero_right, binom_zero_right]; omega
  | succ k => rw [binom_succ_succ]; omega

/-- `binom n k` is monotone in `n`. -/
theorem binom_mono {n n' : Nat} (k : Nat) (h : n ≤ n') : binom n k ≤ binom n' k := by
  obtain ⟨d, rfl⟩ : ∃ d, n' = n + d := ⟨n' - n, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega)) (binom_le_succ (n + d) k)

private theorem binom_two (n : Nat) : 2 * binom n 2 = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binom_succ_succ, binom_one, Nat.mul_add, ih]
    cases n with
    | zero => rfl
    | succ m =>
      show 2 * (m + 1) + (m + 1) * m = (m + 1 + 1) * (m + 1)
      grind

/-- `6 binom(n, 3) = n (n-1) (n-2)`. -/
theorem binom_three (n : Nat) : 6 * binom n 3 = n * (n - 1) * (n - 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binom_succ_succ, Nat.mul_add, ih]
    have h2 := binom_two n
    cases n with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => rfl
      | succ m =>
        show 6 * binom (m + 2) 2 + (m + 2) * (m + 1) * m = (m + 3) * (m + 2) * (m + 1)
        have h2' : 2 * binom (m + 2) 2 = (m + 2) * (m + 1) := h2
        grind

/-- `n ≤ binom(n, 3)` for `n ≥ 4`. -/
theorem le_binom_three {n : Nat} (h : 4 ≤ n) : n ≤ binom n 3 := by
  have h3 := binom_three n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e : (m + 4) * (m + 4 - 1) * (m + 4 - 2) = (m + 4) * ((m + 3) * (m + 2)) := by
    show (m + 4) * (m + 3) * (m + 2) = _
    exact Nat.mul_assoc _ _ _
  rw [e] at h3
  have : 6 ≤ (m + 3) * (m + 2) := by
    have := Nat.mul_le_mul (show 3 ≤ m + 3 by omega) (show 2 ≤ m + 2 by omega)
    exact this
  have : (m + 4) * 6 ≤ (m + 4) * ((m + 3) * (m + 2)) := Nat.mul_le_mul_left _ this
  omega

/-- The factorial. -/
private def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

private theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

private theorem binom_mul_fact {n k : Nat} (h : k ≤ n) :
    binom n k * fact k * fact (n - k) = fact n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ n ih =>
    cases k with
    | zero => rw [binom_zero_right, Nat.sub_zero]; show 1 * 1 * fact (n + 1) = fact (n + 1); omega
    | succ k =>
      by_cases hk : k = n
      · subst hk
        rw [binom_self, Nat.sub_self]
        show 1 * fact (k + 1) * 1 = fact (k + 1)
        omega
      · have h1 := ih (k := k) (by omega)
        have h2 := ih (k := k + 1) (by omega)
        rw [binom_succ_succ]
        have e1 : n + 1 - (k + 1) = n - k := by omega
        obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
        have e2 : n - (k + 1) = d := by omega
        rw [e1, hd]
        rw [hd] at h1
        rw [e2] at h2
        show (binom n k + binom n (k + 1)) * ((k + 1) * fact k) * ((d + 1) * fact d)
          = (n + 1) * fact n
        have hn : n + 1 = (k + 1) + (d + 1) := by omega
        rw [hn]
        have h1' : binom n k * fact k * ((d + 1) * fact d) = fact n := h1
        have h2' : binom n (k + 1) * ((k + 1) * fact k) * fact d = fact n := h2
        grind

/-- Subset of a subset: `binom(n, k) binom(k, j) = binom(n, j) binom(n - j, k - j)` for `j ≤ k ≤ n`. -/
theorem binom_mul_binom {n k j : Nat} (hjk : j ≤ k) (hkn : k ≤ n) :
    binom n k * binom k j = binom n j * binom (n - j) (k - j) := by
  have hA := binom_mul_fact hkn
  have hB := binom_mul_fact hjk
  have hC := binom_mul_fact (show j ≤ n by omega)
  have hD := binom_mul_fact (show k - j ≤ n - j by omega)
  have e : n - j - (k - j) = n - k := by omega
  rw [e] at hD
  have hpos : 0 < fact j * fact (k - j) * fact (n - k) :=
    Nat.mul_pos (Nat.mul_pos (fact_pos _) (fact_pos _)) (fact_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have l : binom n k * binom k j * (fact j * fact (k - j) * fact (n - k)) = fact n := by
    rw [← hA, ← hB]; grind
  have r : binom n j * binom (n - j) (k - j) * (fact j * fact (k - j) * fact (n - k)) = fact n := by
    rw [← hC, ← hD]; grind
  rw [l, r]

end OMDistance
