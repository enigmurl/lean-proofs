
variable {p q: Prop}

theorem p_and_q : p → q → p ∧ q :=
  fun hp: p =>
  fun hq: q =>
  And.intro hp hq

theorem commutativity_or (both: p ∨ q) : q ∨ p :=
  Or.elim both
    (fun (hp: p) => Or.inr hp)
    (fun (hq: q) => Or.inl hq)
