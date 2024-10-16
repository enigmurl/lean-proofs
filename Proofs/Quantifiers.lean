open Classical


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  fun witness: (∃ _x: α, r) =>
    match witness with
    | ⟨_w, p⟩ => p
    
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun witness: ∃x, p x ∨ q x =>
      let ⟨w, hpq⟩ := witness
      ---
      Or.elim hpq
        ---
        (fun hp: p w =>
          have he: ∃ k, p k := Exists.intro w hp
          Or.intro_left (∃ k, q k) he)
        ---
        (fun hq: q w =>
          have he: ∃ k, q k := Exists.intro w hq
          Or.intro_right (∃ k, p k) he)
    )
    (fun or: (∃ x, p x) ∨ (∃ x, q x) =>
      ---
      Or.elim or
        ---
        (fun hep: (∃ x, p x) =>
            let ⟨w, phep⟩ := hep
            Exists.intro w (Or.inl phep)
        )
        ---
        (fun heq: (∃ x, q x) =>
            let ⟨w, pheq⟩ := heq
            Exists.intro w (Or.inr pheq)
        )
    )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ (p x)) :=
  Iff.intro
    (fun all_p: ∀ x, p x =>
      byContradiction
      fun contr: ¬ ¬ ∃ x, ¬(p x) =>
        let ⟨w, prf⟩ := not_not.mp contr
        have hpw: p w := all_p w
        show False from prf hpw
    )
    (fun curr: ¬ (∃ x, ¬ p x) =>
      byContradiction
        fun notall: ¬ (∀ x, p x) =>
        have all: ∀ x, p x :=
          fun (β: α) =>
            byContradiction
              fun (hnpx: ¬ p β) =>
                show False from curr (Exists.intro β hnpx)
        show False from notall all
    )

def even (n : Nat) : Prop :=
  ∃ q: Nat, n = 2 * q

def prime (n : Nat) : Prop :=
  ∀ q: Nat, q ∣ n → q = 1 ∨ q = n

def infinitely_many_primes : Prop :=
  ∀ p, prime p → ∃ q, q > p ∧ prime q

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  Or.elim (em (shaves barber barber))
    (fun s: shaves barber barber =>
      have ns: ¬ shaves barber barber := (h barber).mp s
      ns s
    )
    (fun ns: ¬ shaves barber barber =>
      have s: shaves barber barber := (h barber).mpr ns
      ns s
    )
