import Mathlib.Data.Nat.Basic

theorem add_zero (n : Nat) : n + 0 = n :=
  by rfl

theorem even_add_even {a b : Nat} (ha : a % 2 = 0) (hb : b % 2 = 0) : (a + b) % 2 = 0 :=
  by rw [Nat.add_mod, ha, hb]

theorem mul_eq_zero {a b : ℕ} : a * b = 0 → a = 0 ∨ b = 0 := sorry
