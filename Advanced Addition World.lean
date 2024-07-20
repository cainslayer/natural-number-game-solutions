theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
induction n with d hd
repeat rw [add_zero]
intro h
exact h
repeat rw [add_succ]
intro
apply succ_inj at a_1
apply hd at a_1
exact a_1

theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
rw [add_comm]
nth_rewrite 2 [add_comm]
apply add_right_cancel

theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
intro h
induction y with d hd
rw [add_zero] at h
exact h
rw [add_succ] at h
apply succ_inj at h
apply hd at h
exact h

theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
nth_rewrite 2 [← add_zero x]
exact add_left_cancel y 0 x

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
intro h
cases b with d
rw [add_zero] at h
exact h
rw [add_succ] at h
symm at h
apply zero_ne_succ at h
cases h

theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
rw [add_comm]
exact add_right_eq_zero b a
