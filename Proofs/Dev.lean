import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
def test_4 {a : ℕ} (b : ℝ) : ℕ := a 
def test_5 (b : ℝ)      := b
def test_6 (a : ℕ) : ℕ := a

theorem inf_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ Nat.Prime p := by
    intro n
    let m := 1 + Nat.factorial n
    let p := Nat.minFac m

    have m_pos := Nat.factorial_pos n
    have ne_1 : m ≠ 1 := by
        apply ne_comm.mp
        apply Nat.ne_of_lt
        apply Nat.add_lt_add_left m_pos 1
    have pp : Nat.Prime p := Nat.minFac_prime ne_1

    have : p ≥ n := by
        ---
        by_contra hp
        ---
        have q : p <= n := le_of_lt <| not_le.mp hp
        have p_pos : p > 0 := by exact Nat.minFac_pos m
        have div0 : p ∣ Nat.factorial n := by exact Nat.dvd_factorial p_pos q
        have div1 : p ∣ m := by exact Nat.minFac_dvd m

        have pdiv : p ∣ 1 := by exact (Nat.dvd_add_iff_left div0).mpr div1
        have pnotdiv : ¬(p ∣ 1) := by exact Nat.Prime.not_dvd_one pp
        ---
        exact pnotdiv pdiv

    ---
    exact Exists.intro p (And.intro this pp)
