
variable {p q r: Prop}
theorem p_and_q : p → q → p ∧ q :=
  fun hp: p =>
  fun hq: q =>
  And.intro hp hq

theorem commutativity_or (both: p ∨ q) : q ∨ p :=
  Or.elim both

    (fun (hp: p) => Or.inr hp)

    ( fun (hq: q) =>
    
        Or.inl hq)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro

    (fun (hpqr: (p ∧ q) ∧ r) =>

        have hpq: p ∧ q := hpqr.left
        have hp: p := hpq.left
        have hq: q := hpq.right
        have hr: r := hpqr.right

        And.intro hp (And.intro hq hr)
    )
    (fun (hpqr: p ∧ (q ∧ r)) =>
        have hqr: q ∧ r := hpqr.right
        have hp: p := hpqr.left
        have hq: q := hqr.left
        have hr: r := hqr.right
        And.intro (And.intro hp hq) hr
    )

