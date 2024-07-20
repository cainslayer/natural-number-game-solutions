theorem mul_one (m : ℕ) : m * 1 = m := by
rw [one_eq_succ_zero]
rw [mul_succ]
rw [mul_zero]
rw [zero_add]
rfl

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
induction m with d hd
rw [mul_zero]
rfl
rw [mul_succ]
rw [hd, add_zero]
rfl

theorem succ_mul (a b : ℕ) : succ a * b = a * b + b := by
induction b with d hd
rw [mul_zero, mul_zero]
rw [add_zero]
rfl
rw [mul_succ]
rw [mul_succ]
rw [hd]
rw [add_succ, add_succ]
rw [add_right_comm ]
rfl

theorem mul_comm (a b : ℕ) : a * b = b * a := by
induction b with d hd
rw [mul_zero, zero_mul]
rfl
rw [mul_succ, succ_mul]
rw [hd]
rfl

theorem one_mul (m : ℕ): 1 * m = m := by
rw [mul_comm]
rw [mul_one]
rfl

theorem two_mul (m : ℕ): 2 * m = m + m := by
rw [mul_comm]
rw [two_eq_succ_one]
rw [mul_succ]
rw [mul_one]
rfl

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
induction c with d hd
rw [add_zero, mul_zero, add_zero]
rfl
rw [add_succ, mul_succ]
rw [hd, mul_succ]
rw [add_assoc]
rfl

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
induction c with d hd
rw [mul_zero,mul_zero,mul_zero]
rw [add_zero]
rfl
rw [mul_succ,mul_succ,mul_succ]
rw [hd]
rw [add_assoc, add_assoc]
rw [← add_assoc (b*d) a b]
rw [← add_assoc a (b*d) b]
rw [add_comm (b*d) a]
rfl

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
induction c with d hd
rw [mul_zero,mul_zero]
rw [mul_zero]
rfl
rw [mul_succ, mul_succ]
rw [mul_add]
rw [hd]
rfl
