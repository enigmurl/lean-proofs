import Mathlib.Algebra.BigOperators.Fin

def choose (n k : ℕ) : ℕ := sorry


def x := 3
theorem binomial_theorem (x y n : ℕ) :
    (x + y) ^ n = ∑ k in Finset.range n, (choose n k) * x ^ k * y ^ (n - k) := by
    have z := 3
    ---
    have x := 4
    sorry
