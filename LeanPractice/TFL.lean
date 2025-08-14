variable (p q r : Prop)


-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ hpq : p ∧ q => And.intro hpq.right hpq.left)
    (λ hqp : q ∧ p => And.intro hqp.right hqp.left)


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ hpq : p ∨ q =>
      Or.elim hpq
        (λ hp : p => Or.inr hp)
        (λ hq : q => Or.inl hq))
    (λ hqp : q ∨ p =>
      Or.elim hqp
        (λ hq : q => Or.inr hq)
        (λ hp : p => Or.inl hp))


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ hpqr : (p ∧ q) ∧ r =>
      And.intro
        (hpqr.left.left)
        (And.intro hpqr.left.right hpqr.right))
    (λ hpqr : p ∧ (q ∧ r) =>
      And.intro
        (And.intro hpqr.left hpqr.right.left)
        (hpqr.right.right))


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ hpqr : (p ∨ q) ∨ r =>
      Or.elim hpqr
        (λ hpq : p ∨ q =>
          Or.elim hpq
            (λ hp : p => Or.inl hp)
            (λ hq : q => Or.inr $ Or.inl hq))
        (λ hr : r => Or.inr $ Or.inr hr))
    (λ hpqr : p ∨ (q ∨ r) =>
      Or.elim hpqr
        (λ hp : p => Or.inl $ Or.inl hp)
        (λ hqr : q ∨ r =>
          Or.elim hqr
            (λ hq : q => Or.inl $ Or.inr hq)
            (λ hr : r => Or.inr hr)))


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ hpqr : p ∧ (q ∨ r) =>
      Or.elim hpqr.right
        (λ hq : q => Or.inl $ And.intro hpqr.left hq)
        (λ hr : r => Or.inr $ And.intro hpqr.left hr))
    (λ hpqpr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqpr
        (λ hpq : p ∧ q =>
          And.intro hpq.left $ Or.inl hpq.right)
        (λ hpr : p ∧ r =>
          And.intro hpr.left $ Or.inr hpr.right))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (λ hpqr : p ∨ (q ∧ r) =>
      Or.elim hpqr
        (λ hp : p => And.intro (Or.inl hp) (Or.inl hp))
        (λ hqr : q ∧ r => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (λ hpqpr : (p ∨ q) ∧ (p ∨ r) =>
      Or.elim hpqpr.left
        (λ hp : p => Or.inl hp)
        (λ hq : q =>
          Or.elim hpqpr.right
            (λ hp : p => Or.inl hp)
            (λ hr : r => Or.inr $ And.intro hq hr)))


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (λ hpqr : p → (q → r) =>
      λ hpq : p ∧ q =>
        hpqr hpq.left hpq.right)
    (λ hpqr : p ∧ q → r =>
      λ hp : p =>
        λ hq : q => hpqr $ And.intro hp hq)


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (λ hpqr : (p ∨ q) → r =>
      And.intro
        (λ hp : p => hpqr $ Or.inl hp)
        (λ hq : q => hpqr $ Or.inr hq))
    (λ hprqr : (p → r) ∧ (q → r) =>
      λ hpq : p ∨ q =>
        Or.elim hpq
          (λ hp : p => hprqr.left hp)
          (λ hq : q => hprqr.right hq))


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (λ hnpq : ¬(p ∨ q) =>
      And.intro
        (λ hp : p => hnpq $ Or.inl hp)
        (λ hq : q => hnpq $ Or.inr hq))
    (λ hnpnq : ¬p ∧ ¬q =>
      λ hpq : p ∨ q =>
        Or.elim hpq
          (λ hp : p => hnpnq.left hp)
          (λ hq : q => hnpnq.right hq))


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ hnpnq : ¬p ∨ ¬q =>
    λ hpq : p ∧ q =>
      Or.elim hnpnq
        (λ hnp : ¬p => hnp hpq.left)
        (λ hnq : ¬q => hnq hpq.right)


example : ¬(p ∧ ¬p) :=
  λ hpnp : p ∧ ¬p =>
    hpnp.right hpnp.left


example : p ∧ ¬q → ¬(p → q) :=
  λ hpnq : p ∧ ¬q =>
    λ hpq : p → q =>
      hpnq.right $ hpq hpnq.left


example : ¬p → (p → q) :=
  λ hnp : ¬p =>
    λ hp : p => absurd hp hnp


example : (¬p ∨ q) → (p → q) :=
  λ hnpq : ¬p ∨ q =>
    λ hp : p =>
      Or.elim hnpq
        (λ hnp : ¬p => absurd hp hnp)
        (λ hq : q => hq)


example : p ∨ False ↔ p :=
  Iff.intro
    (λ hpf : p ∨ False =>
      Or.elim hpf
        (λ hp : p => hp)
        (λ hf : False => hf.elim))
    (λ hp : p => Or.inl hp)


example : p ∧ False ↔ False :=
  Iff.intro
    (λ hpf : p ∧ False => hpf.right)
    (λ hf : False => hf.elim)


example : (p → q) → (¬q → ¬p) :=
  λ hpq : p → q =>
    λ hnq : ¬q =>
      λ hp : p => hnq $ hpq hp


example : ¬(p ↔ ¬p) :=
  λ hpp : p ↔ ¬p =>
    have hnp : ¬p := λ hp : p => (hpp.mp hp) hp
    have hp : p := hpp.mpr hnp
    hnp hp


open Classical


example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ hpqr : p → q ∨ r =>
    byCases
      (λ hp : p =>
        have hqr : q ∨ r := hpqr hp
        Or.elim hqr
          (λ hq : q => Or.inl $ λ hp : p => hq)
          (λ hr : r => Or.inr $ λ hp : p => hr))
      (λ hnp : ¬p =>
        have hpq : p → q := λ hp : p => absurd hp hnp
        Or.inl hpq)


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ hnpq : ¬(p ∧ q) =>
    byCases
      (λ hp : p =>
        byCases
          (λ hq : q => absurd (And.intro hp hq) hnpq)
          (λ hnq : ¬q => Or.inr hnq))
      (λ hnp : ¬p => Or.inl hnp)


example : ¬(p → q) → p ∧ ¬q :=
  λ hnpq : ¬(p → q) =>
    byCases
      (λ hp : p =>
        have hnq : ¬q := λ hq : q => hnpq (λ hp : p => hq)
        And.intro hp hnq)
      (λ hnp : ¬p =>
        absurd (λ hp : p => absurd hp hnp) hnpq)


example : (p → q) → (¬p ∨ q) :=
  λ hpq : p → q =>
    byCases
      (λ hp : p => Or.inr $ hpq hp)
      (λ hnp : ¬p => Or.inl hnp)


example : (¬q → ¬p) → (p → q) :=
  λ hnqnp : ¬q → ¬p =>
    λ hp : p =>
      byCases
        (λ hq : q => hq)
        (λ hnq : ¬q => absurd hp $ hnqnp hnq)


example : p ∨ ¬p := em p  -- troll

example : p ∨ ¬p :=
  byCases
    (λ hp : p => Or.inl hp)
    (λ hnp : ¬p => Or.inr hnp)


example : (((p → q) → p) → p) :=
  λ hpqp : (p → q) → p =>
    byCases
      (λ hp : p => hp)
      (λ hnp : ¬p =>
        hpqp $ λ hp : p => absurd hp hnp)
