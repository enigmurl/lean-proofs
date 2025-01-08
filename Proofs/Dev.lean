import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

#check 4
#check ℕ

variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

theorem a_le_b (h : a ≤ b) : 0 ≤ b - a := by
  ---
  suffices a + -a ≤ b + -a by
    ---
    rw [add_right_neg] at this
    rw [sub_eq_add_neg]
    ---
    exact this
  ---
  apply add_le_add_right
  ---
  exact h

def ex (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  ---
  have h2 : 0 ≤ b - a := a_le_b a b h
  have :=
    mul_nonneg h2 h'
  rw [sub_mul] at this
  ---
  have := add_le_add_right this (a * c)
  rw [sub_add, sub_self, sub_zero, zero_add] at this
  exact this

-- def parallogram_squared {k: ℕ} {x y: EuclideanSpace ℝ k} : |x+y|^2 + |x-y|^2 = 2 * |x|^2 + 2 * |y|^2 := by
    ---
    -- calc |x + y| ^ 2 + |x - y| ^ 2 =
         -- 2 * |x| ^ 2 + 2 * |y| ^ 2 := by sorry

def p:= 1
def test_1 := 
    1 
def test_2 : ℕ := 4
def test_3 {a : ℕ}:= 
    a 
def test_4 {a : ℕ} (_b : ℝ) : ℕ := a 
def test_5 (b : ℝ)      := b
def test_6 (a : ℕ) : ℕ := a