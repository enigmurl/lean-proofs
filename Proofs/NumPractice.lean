import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b, mul_assoc, mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm, mul_assoc, mul_comm a]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a, h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check add_assoc
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc (a + b) * (c + d)
    _ = (c + d) * a + (c + d) * b := by rw [mul_comm, mul_add]
    _ = a * (c + d) + b * (c + d) := by rw [mul_comm, mul_comm (c + d)]
    _ = (a * c + a * d) + (b * c + b * d) := by rw [mul_add, mul_add]
    _ = a * c + a * d + b * c + b * d := by rw [add_assoc, ←add_assoc (a * d), ← add_assoc, ← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc (a + b) * (a - b)
    _ = a * (a - b) + b * (a - b) := add_mul a b (a - b)
    _ = a * a - a * b + b * (a - b) := by rw [mul_sub]
    _ = a * a - a * b + b * a - b * b := by rw [mul_sub, add_sub]
    _ = a * a - (a * b - b * a) - b * b := by rw [sub_add]
    _ = a * a - (b * a - b * a) - b * b := by rw [mul_comm a b]
    _ = a * a - (0) - b * b := by rw [sub_self]
    _ = a * a - b * b := by rw [sub_zero]
    _ = a^2 - b^2 := by rw [←pow_two, ←pow_two]

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  have : -a + (a + b) = -a + (a + c) := by rw [h]
  have : b = c := by
    rw [neg_add_cancel_left, neg_add_cancel_left] at this
    exact this
  assumption

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h: 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, add_zero, zero_add]
  exact add_right_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have : a + -a = a + b := by
    rw [add_right_neg, h]
  exact add_left_cancel this

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have : a + b = -b + b := by
    rw [add_comm (-b) b, add_right_neg, h]
  exact add_right_cancel this

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  have : -a + (- -a) = -a + a := by
    rw [add_right_neg, add_comm (-a) a, add_right_neg]
  exact add_left_cancel this

end MyRing
