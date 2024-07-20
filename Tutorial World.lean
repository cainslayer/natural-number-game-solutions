example (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl

example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]
  rfl

example : 2 = succ (succ 0) := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rfl

example : 2 = succ (succ 0) := by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one ]
  rfl

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero b]
  rw [add_zero c]
  rfl

example (a b c : ℕ) : a + (b + 0) + (c + 0) = a + b + c := by
  rw [add_zero c]
  rw [add_zero]
  rfl

theorem succ_eq_add_one n : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]
  rfl

example : (2 : ℕ) + 2 = 4 := by
  nth_rewrite 2 [two_eq_succ_one]
  rw [add_succ]
  rw [← succ_eq_add_one]
  rw [← three_eq_succ_two]
  rw [four_eq_succ_three]
  rfl
