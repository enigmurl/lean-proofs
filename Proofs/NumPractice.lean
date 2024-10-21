import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic


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
  have q := 1
  
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
  ---
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

#check neg_zero


theorem neg_neg (a : R) : - -a = a := by
  have : -a + (- -a) = -a + a := by
    ---
    rw [add_right_neg, add_comm (-a) a, add_right_neg]
  exact add_left_cancel this

theorem self_sub (a : R) : a - a = 0 := by
  have : a + -a = 0 := add_right_neg a
  rw [←sub_eq_add_neg a a] at this
  exact this

theorem self_sub_real (a : ℝ) : a - a = 0 := by
  have : a + -a = 0 := add_right_neg a
  exact this

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [←one_add_one_eq_two, add_mul, one_mul]

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check abs_le_abs
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)


-- (a^{-1} * a) * a^{-1} = a^{-1}
-- a^{-1} * (a * a^{-1}) = a^{-1}
-- sol manual
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv]
  rw [← h, ← mul_assoc, mul_left_inv, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← mul_left_inv a, ← mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← mul_left_inv (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_right_inv, one_mul, mul_right_inv, mul_one]


example (h₀ : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
  ---
  have : a + d ≤ a + e :=
    add_le_add (le_refl a) h₀
  apply add_le_add
  ---
  . exact le_refl c
  ---
  . apply Real.exp_le_exp.mpr
    ---
    . exact this
example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) := by
  have h₀ : 0 < 1 + Real.exp a := by
    have : 0 < Real.exp a := Real.exp_pos a
    rw [←zero_add 1]
    nth_rewrite 1 [←zero_add 0]
    apply add_lt_add
    . norm_num
    . exact this
  apply Real.log_le_log h₀
  . apply add_le_add
    exact le_refl 1
    exact Real.exp_le_exp.mpr h

example : 0 ≤ a ^ 2 := by
  exact sq_nonneg a

example (h : a ≤ b) : c - Real.exp b ≤ c - Real.exp a := by
  apply sub_le_sub
  . exact le_refl c
  . exact Real.exp_le_exp.mpr h

theorem two_ab_le {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 :=
  calc
    a ^ 2 - 2 * a * b + b ^ 2
    _ = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  /- -/
  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

theorem two_ab_le2 {a b : ℝ} : -2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2 :=
  calc
    a ^ 2 + 2 * a * b + b ^ 2
    _ = (a + b) ^ 2 := by ring
    
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  apply abs_le'.mpr
  apply And.intro
  . have : 2 * a * b ≤ a^2 + b^2 := two_ab_le
    linarith
  . have : -2 * a * b ≤ a^2 + b^2 := two_ab_le2
    linarith
 
#check abs_le'

example (a b : ℝ) : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example (a b : ℝ): min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . have h0 : min a b ≤ a := by apply min_le_left
      have h1 : min (min a b) c ≤ min a b := by apply min_le_left
      exact le_trans h1 h0
    . have h0 : min a b ≤ b := by apply min_le_right
      have h1 : min (min a b) c ≤ min a b := by apply min_le_left
      have h2 : min (min a b) c ≤ c := by apply min_le_right
      apply le_min
      exact le_trans h1 h0
      exact h2
  . show min (min a b) c ≥ min a (min b c)
    apply le_min
        /- -/
    . have h0 : min a (min b c) ≤ a := min_le_left a (min b c)
      have h1 : min a (min b c) ≤ min b c := min_le_right a (min b c)
      have h2 : min b c ≤ b := min_le_left b c
      apply le_min
      exact h0
      apply le_trans h1 h2
    apply le_trans
    apply min_le_right
    apply min_le_right

theorem aux (a b c : ℝ) : min a b + c ≤ min (a + c) (b + c) := by
  ---
  apply le_min
  have : min a b ≤ a := by apply min_le_left
  apply add_le_add 
  exact this 
  exact (le_refl c)
  have : min a b ≤ b := by apply min_le_right
  apply add_le_add this (le_refl c)

example (a b c : ℝ): min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  exact aux a b c
  have h1 : min (a + c) (b + c) -c ≤ min (a + c - c) (b + c -c) := aux (a + c) (b + c) (-c)
  rw [
    sub_eq_add_neg (a + c) c, add_neg_cancel_right a c,
    sub_eq_add_neg (b + c) c, add_neg_cancel_right b c] at h1
  linarith

#check abs
example {a b : ℝ} : |a| - |b| ≤ |a - b| := by
  have : |a - b + b| ≤ |a - b| + |b| := abs_add (a - b) b
  rw [sub_add_cancel] at this
  -- :
  linarith
  
example {x y : ℕ} (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  ---
  apply dvd_add
  apply dvd_add
  rw [mul_comm, mul_assoc]
  exact dvd_mul_right x (z * y)
  apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_left
  exact h

example {m n : ℕ}: Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  ---
  repeat
  apply Nat.dvd_gcd
  . apply Nat.gcd_dvd_right
  . apply Nat.gcd_dvd_left

end MyRing

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

example : x ⊓ y = y ⊓ x := by
  have x_inf_y_le_y_inf_x (u v : α) : (u ⊓ v ≤ v ⊓ u) := by
    apply le_inf
    exact inf_le_right
    exact inf_le_left
  apply le_antisymm
  exact x_inf_y_le_y_inf_x x y
  exact x_inf_y_le_y_inf_x y x

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  -- :
  have x_sup_y_le_y_sup_x (u v : α) : (u ⊔ v ≤ v ⊔ u) := by
    -- :
    apply sup_le
    exact le_sup_right
    exact le_sup_left
  -- :
  apply le_antisymm
  -- :
  exact x_sup_y_le_y_sup_x x y
  -- :
  exact x_sup_y_le_y_sup_x y x

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry


end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

theorem a_le_b (h : a ≤ b) : 0 ≤ b - a := by
  -- :
  suffices a + -a ≤ b + -a by
    -- :
    
    rw [add_right_neg] at this
    rw [sub_eq_add_neg]
    -- :
    exact this
  -- :
  apply add_le_add_right
  exact h

example (h: 0 ≤ b - a) : a ≤ b := by
  have : 0 + a ≤ b - a + a := add_le_add_right h a
  -- :
  rw [zero_add, sub_add, sub_self, sub_zero] at this
  exact this

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h2 : 0 ≤ b - a := a_le_b a b h
  have this :=
    mul_nonneg h2 h'
  rw [sub_mul] at this
  have := add_le_add_right this (a * c)
  rw [sub_add, sub_self, sub_zero, zero_add] at this
  exact this
end
section

variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
#check dist_self y

example (x y : X) : 0 ≤ dist x y := by
  have : dist x x ≤ dist x y + dist y x := dist_triangle x y x
  rw [dist_self x, dist_comm y x, ←two_mul] at this
  -- : 
  apply nonneg_of_mul_nonneg_right
    this
    zero_lt_two
  -- rw [nonneg_of_mul_nonneg_right ] at this
  -- linarith

example : ∀ x : ℕ, x = 1 ∨ x ≠ 1 := by
  intro x
  ---
  cases Classical.em (x = 1)
  case inl hp => 
    ---
    exact Or.inl hp
  case inr hp => 
    ---
    exact eq_or_ne x 1

example : 1 + 1  + 1 + 1 + 1 + 1+ 1 + 1 + 1 + 1 + 1 + 1 +  1 + 1  + 1 + 1 + 1 + 1+ 1 + 1 + 1 + 1 + 1 = 7 := 
    ---
    _

end
