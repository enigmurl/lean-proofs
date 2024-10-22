import Mathlib.Data.Nat.Basic

theorem inf_primes : ∀ n : ℕ, ∃ p, p ≥ n ∧ Nat.Prime p := by
    intro n
    let m := 1 + Nat.factorial n
    let p := Nat.minFac m

    have m_pos := Nat.factorial_pos n
    have ne_1 : m ≠ 1 := by
        ---
        apply ne_comm.mp
        ---
        apply Nat.ne_of_lt
        ---
        apply Nat.add_lt_add_left m_pos 1
    have pp : Nat.Prime p := Nat.minFac_prime ne_1

    have : p ≥ n := by
        ---
        by_contra hp
        ---
        have q : p <= n := le_of_lt <| not_le.mp hp
        have p_pos : p > 0 := by exact Nat.minFac_pos m
        have div0 : p ∣ Nat.factorial n := Nat.dvd_factorial p_pos q
        have div1 : p ∣ m := Nat.minFac_dvd m

        have pdiv : p ∣ 1 := (Nat.dvd_add_iff_left div0).mpr div1
        have pnotdiv : ¬(p ∣ 1) := Nat.Prime.not_dvd_one pp
        exact pnotdiv pdiv

    ---
    exact ⟨p, ⟨this, pp⟩⟩
