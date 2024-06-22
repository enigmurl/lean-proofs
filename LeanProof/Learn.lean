theorem p_and_q {p q: Prop} : p → q → p ∧ q :=
  fun hp: p =>
  fun hq: q =>
  show p ∧ q from And.intro hp hq
