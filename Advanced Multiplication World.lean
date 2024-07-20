theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
cases h with c hc
rw [hc]
rw [mul_comm (a+c), mul_add]
rw [mul_comm a]
use t*c
rfl

theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
intro hb
rw [hb] at h
rw [mul_zero] at h
apply h
rfl

theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = succ n := by
cases a with d
tauto
use d
rfl

theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
cases a with d
tauto
use d
rw [add_comm, succ_eq_add_one]
rfl

theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
apply mul_left_ne_zero at h
cases a with d
rw [zero_mul]
exact zero_le 0
apply one_le_of_ne_zero at h
cases h with δ hδ
rw [hδ]
rw [mul_add]
rw [mul_one]
use (succ d * δ)
rfl

theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
have h2 : x*y ≠ 0
rw [h]
exact one_ne_zero
apply le_mul_right at h2
rw [h] at h2
apply le_one at h2
cases h2 with h0 h1
rw [h0] at h
rw [zero_mul] at h
cases h
exact h1

theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
apply eq_succ_of_ne_zero at ha
apply eq_succ_of_ne_zero at hb
cases ha with n1 hn1
cases hb with n2 hn2
rw [hn1, hn2]
rw [mul_succ]
rw [add_succ]
exact succ_ne_zero (succ n1 * n2 + n1)

theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
induction a with d hd
left
rfl
cases b with e
right
rfl
rw [mul_succ] at h
rw [add_succ] at h
contrapose! h
exact succ_ne_zero (succ d * e + d)

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
induction b with d hd generalizing c
rw [mul_zero] at h
symm at h
apply mul_eq_zero at h
symm
cases h with h1 h2
tauto
exact h2
cases c with e
contrapose! h
rw [mul_zero]
exact mul_ne_zero a (succ d) ha h
repeat rw [mul_succ] at h
apply add_right_cancel at h
apply hd e at h
rw [h]
rfl

theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
cases b with d hd
rw [mul_zero] at h
symm at h
tauto
nth_rewrite 2 [← mul_one a] at h
apply mul_left_cancel at h
exact h
exact ha
