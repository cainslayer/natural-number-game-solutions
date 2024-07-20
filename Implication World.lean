example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) : x + y = 37 := by
exact h1

example (x : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
rw [zero_add,zero_add] at h
exact h

example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
apply h2 at h1
exact h1

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
rw [← succ_eq_add_one, four_eq_succ_three] at h
apply succ_inj at h
exact h

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
apply succ_inj
rw [succ_eq_add_one, ← four_eq_succ_three]
exact h

example (x : ℕ) : x = 37 → x = 37 := by
intro h
exact h

example (x : ℕ) : x + 1 = y + 1 → x = y := by
intro h
apply succ_inj
rw [succ_eq_add_one,succ_eq_add_one]
exact h

example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
apply h2 at h1
exact h1

theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
intro h
rw [one_eq_succ_zero] at h
apply zero_ne_succ at h
exact h

theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
intro h
symm at h
apply zero_ne_one at h
exact h

example : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by
intro h
rw [add_succ,add_succ] at h
rw [  add_zero] at h
repeat apply succ_inj at h
apply zero_ne_succ at h
exact h
