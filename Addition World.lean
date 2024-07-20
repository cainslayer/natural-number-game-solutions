theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with d hd
  rw[add_zero]
  rfl
  rw [add_succ]
  rw [hd]
  rfl

theorem succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with d hd
  rw [add_zero]
  rw [add_zero]
  rfl
  rw [add_succ]
  rw [add_succ]
  rw [hd]
  rfl,

theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with d hd
  rw [add_zero, zero_add]
  rfl
  rw [add_succ, succ_add]
  rw [hd]
  rfl

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with d hd
  rw [add_zero, add_zero]
  rfl
  rw [add_succ]
  rw [hd]
  rw [← add_succ]
  rw [← add_succ]
  rfl

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  induction c with d hd
  rw [add_zero, add_zero]
  rfl
  rw [add_succ, add_succ]
  rw [succ_add]
  rw [hd]
  rfl
