theorem le_refl (x : ℕ) : x ≤ x := by
use 0
rw [add_zero]
rfl

theorem zero_le (x : ℕ) : 0 ≤ x := by
use x
rw [zero_add]
rfl

theorem le_succ_self (x : ℕ) : x ≤ succ x := by
use 1
rw [succ_eq_add_one]
rfl

theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
cases hxy with a ha
cases hyz with b hb
rw [ha] at hb
rw [add_assoc] at hb
use (a+b)
exact hb

theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
cases hx with a ha
symm at ha
apply add_right_eq_zero at ha
exact ha

theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
cases hxy with a ha
rw [ha] at hyx
cases hyx with b hb
rw [add_assoc] at hb
rw [add_comm x] at hb
nth_rewrite 1 [← zero_add x] at hb
apply add_right_cancel at hb
symm at hb
apply add_right_eq_zero at hb
rw [hb] at ha
rw [add_zero] at ha
symm at ha
exact ha

example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
cases h with h1 h2
right
exact h1
left
exact h2

theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
induction y with d hd
right
exact zero_le x
cases hd with h1 h2
left
cases h1 with a ha
rw [ha]
rw [← add_succ]
use (  succ a)
rfl
cases h2 with b hb
cases b with c
rw [add_zero] at hb
left
rw [hb]
exact le_succ_self d
right
rw [hb]
rw [add_succ, ← succ_add]
use c
rfl

theorem succ_le_succ (x y : ℕ) (hx : succ x ≤ succ y) : x ≤ y := by
cases hx with a ha
induction x with d hd
rw [succ_add, zero_add] at ha
apply succ_inj at ha
use a
rw [zero_add]
exact ha
rw [succ_add] at ha
apply succ_inj at ha
use a
exact ha

theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
cases x with d
left
rfl
cases hx with a ha
rw [one_eq_succ_zero, succ_add] at ha
apply succ_inj at ha
symm at ha
apply add_right_eq_zero at ha
right
rw [one_eq_succ_zero]
rw [ha]
rfl

theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
cases x with a ha
left
rfl
cases a with b hb
right
left
rw [one_eq_succ_zero]
rfl
cases hx with c hc
rw [two_eq_succ_one, one_eq_succ_zero, succ_add, succ_add] at hc
repeat apply succ_inj at hc
symm at hc
apply add_right_eq_zero at hc
right
right
rw [hc]
rw [two_eq_succ_one, one_eq_succ_zero]
rfl
