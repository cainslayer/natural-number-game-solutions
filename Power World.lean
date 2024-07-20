theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
apply pow_zero 0

theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (succ m) = 0 := by
induction m with d hd
rw [pow_succ]
rw [pow_zero, mul_zero]
rfl
rw [pow_succ]
rw [hd]
exact mul_zero 0

theorem pow_one (a : ℕ) : a ^ 1 = a := by
rw [one_eq_succ_zero]
rw [pow_succ]
rw [pow_zero]
rw [one_mul]
rfl

theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
induction m
exact pow_zero 1
rw [pow_succ]
rw [n_ih, mul_one]
rfl

theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
rw [two_eq_succ_one]
rw [pow_succ]
rw [pow_one]
rfl

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
induction m
rw [zero_add, pow_zero, one_mul]
rfl
rw [succ_add]
rw [pow_succ]
rw [n_ih]
rw [mul_assoc]
rw [mul_comm (a^n) a]
rw [← mul_assoc]
rw [pow_succ]
rfl

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
induction n with d hd
repeat rw [pow_zero]
symm
exact mul_one 1
rw [pow_succ,pow_succ]
rw [← mul_assoc]
rw [mul_comm ((a * b) ^ d)]
rw [mul_comm (a ^ d)]
rw [pow_succ]
rw [← mul_assoc]
rw [mul_assoc a (a^d)]
rw [hd]
rfl

theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
induction n with d hd
rw [pow_zero, mul_zero, pow_zero]
rfl
rw [pow_succ, mul_succ]
rw [hd]
rw [← pow_add]
rfl

theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
rw [pow_two]
rw [add_mul]
rw [mul_add, mul_add]
rw [← add_assoc]
rw [add_assoc (a*a)]
rw [mul_comm b]
rw [← two_mul]
rw [← mul_assoc]
rw [add_right_comm]
repeat rw [← pow_two]
rfl

example (a b c n : ℕ) : (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3) := by
  sorry
  -- Wo da sumo, zhende jiade?
