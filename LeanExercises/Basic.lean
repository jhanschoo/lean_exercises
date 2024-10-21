import Mathlib

open Finset BigOperators

/--
  Example
-/
example (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 :=
  by induction n with
  | zero => simp
  | succ n ih =>
  rw [Finset.sum_range_succ]
  rw [ih]
  -- we handle small cases separately so that the general case does not involve subtraction
  cases n with
  | zero => simp
  | succ n =>
  simp
  apply (Nat.mul_right_inj two_ne_zero).mp
  rw [mul_add]
  repeat rw [Nat.mul_div_cancel' (by
    apply even_iff_two_dvd.mp
    rw [Nat.mul_comm]
    exact Nat.even_mul_succ_self _
  )]
  ring

/-- exercise 1 -/
example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  have h₁ : r - 1 ≠ 0 := by
    intro contra
    apply h
    rw [sub_eq_zero] at contra
    exact contra
  induction n with
  | zero =>
    simp
    nth_rw 1 3 [← mul_one a]
    rw [← mul_sub, mul_div_assoc, div_self h₁]
  | succ n ih =>
    rw [sum_range_succ]
    rw [ih]
    have aux : (a * r ^ (n + 1) - a) + a * r ^ (n + 1) * (r - 1) = (a * r ^ (n + 1 + 1) - a) := by ring
    rw [← aux]
    rw [← div_add_div_same, mul_div_assoc, div_self h₁, mul_one]

/-- exercise 2 -/
-- No point in working it out since it would be identical to the Mathlib proofs.
theorem ex2_i_a (n : ℕ) : n.choose 0 = 1 := Nat.choose_zero_right n
theorem ex2_i_b (n : ℕ) : n.choose n = 1 := Nat.choose_self n
theorem ex2_i (n : ℕ) : n.choose 0 = 1 ∧ n.choose n = 1 := ⟨Nat.choose_zero_right n, Nat.choose_self n⟩
theorem ex2_ii (n k : ℕ) (h : k ≤ n) : n.choose k = n.choose (n - k) := (Nat.choose_symm h).symm

/-- exercise 3 -/
-- We extend the definition of the function by the recurrence relation to `0` for simplicity.
def fib5 : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => fib5 (n + 1) + 2 * fib5 n

#eval fib5 2 -- 5

-- We lift the range of (fib5 n) to the integer domain for the subexpression (-1)^n to make sense.
theorem fib5_closed : ∀ n, (fib5 n : ℤ) = 2^n+(-1)^n := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  unfold fib5
  -- we handle fib5 0, fib5 1, fib5 n (where n > 1) separately
  cases n with
  | zero => simp
  | succ n =>
  cases n with
  | zero => simp
  | succ n =>
  simp
  have h1 : (fib5 n : ℤ) = 2 ^ n + (-1) ^ n := ih n (by linarith)
  have h2 : (fib5 (n + 1) : ℤ) = 2 ^ (n + 1) + (-1) ^ (n + 1) := ih (n + 1) (by linarith)
  rw [h1, h2]
  ring

-- The result in the form requested (for positive `n`) is as follows.
theorem fib5_closed' : ∀ n > 0, (fib5 n : ℤ) = 2^n+(-1)^n := by
  intro n _
  exact fib5_closed n
