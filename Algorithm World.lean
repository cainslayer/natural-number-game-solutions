theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
repeat rw [← add_assoc]
rw [add_comm a]
rfl

example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
rw [add_right_comm]
rw [← add_assoc]
rfl

example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
rw [add_comm h]
rw [add_left_comm (d+f)]
rw [add_assoc d]
rw [← add_assoc (a+c) d]
rw [add_comm (g+e)]
rw [add_comm g]
rw [← add_assoc b]
rw [← add_assoc (a + c + d + (f + h))]
rw [add_assoc (a+c+d)]
rw [add_comm (f+h)]
rw [← add_assoc (a+c+d)]
rw [add_right_comm (a+c)]
rw [← add_assoc (a+c)]
rw [add_right_comm a]
rw [add_right_comm (a+b+c)]
rw [← add_assoc (a+b+c+d+e)]
rw [add_right_comm (a + b + c + d + e + f)]
rfl

example (a b c d e f g h : ℕ) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
simp_add

example (a b : ℕ) (h : succ a = succ b) : a = b := by
rw [← pred_succ a]
rw [h]
exact pred_succ b

theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
intro h
rw [← is_zero_succ a]
rw[h]
trivial

theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : succ m ≠ succ n := by
contrapose! h
apply succ_inj at h
exact h

example : (20 : ℕ) + 20 = 40 := by
decide

example : (2 : ℕ) + 2 ≠ 5 := by
decide
