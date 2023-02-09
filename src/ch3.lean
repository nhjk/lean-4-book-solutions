variable (p q r : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
    show False from hnq (hpq hp)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

open Classical
variable (p q : Prop)
#check @em p

-- https://math.stackexchange.com/questions/2902033/double-negation-vs-law-of-excluded-middle

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

-- https://proofassistants.stackexchange.com/questions/1856/lean4-exercise-double-negation-implies-law-of-excluded-middle
example (p : Prop) : p ∨ ¬p :=
  dne fun npnp : ¬(p ∨ ¬p) =>
    show False from
    have hnp : ¬p := fun hp : p =>
      npnp (Or.inl hp)
    npnp (Or.inr hnp)

-- programming language theory <~> theory of computation for lambdas/types/ and stuff?


open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
