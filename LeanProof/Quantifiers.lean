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
      Or.elim hpq
        (fun hp: p w =>
          have he: ∃ k, p k := Exists.intro w hp
          Or.intro_left (∃ k, q k) he)
        (fun hq: q w =>
          have he: ∃ k, q k := Exists.intro w hq
          Or.intro_right (∃ k, p k) he)
    )
    (fun or: (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim or
        (fun hep: (∃ x, p x) =>
            let ⟨w, phep⟩ := hep
            Exists.intro w (Or.inl phep)
        )
        (fun heq: (∃ x, q x) =>
            let ⟨w, pheq⟩ := heq
            Exists.intro w (Or.inr pheq)
        )
    )
