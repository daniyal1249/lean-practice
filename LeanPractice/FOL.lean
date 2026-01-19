variable (α : Type) (p q : α → Prop)
variable (r : Prop)


example : (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (λ hapq : ∀x, p x ∧ q x =>
      And.intro
        (λ x : α => (hapq x).left)
        (λ x : α => (hapq x).right))
    (λ hapaq : (∀x, p x) ∧ (∀x, q x) =>
      λ x : α => And.intro (hapaq.left x) (hapaq.right x))


example : (∀x, p x → q x) → (∀x, p x) → (∀x, q x) :=
  λ hapq : ∀x, p x → q x =>
    λ hap : ∀x, p x =>
      λ x : α => hapq x $ hap x


example : (∀x, p x) ∨ (∀x, q x) → ∀x, p x ∨ q x :=
  λ hapaq : (∀x, p x) ∨ (∀x, q x) =>
    Or.elim hapaq
      (λ hap : ∀x, p x =>
        λ x : α => Or.inl $ hap x)
      (λ haq : ∀x, q x =>
        λ x : α => Or.inr $ haq x)


example : α → ((∀x : α, r) ↔ r) :=
  λ x : α =>
    Iff.intro
      (λ har : ∀x : α, r => har x)
      (λ hr : r => λ x : α => hr)


open Classical


example : (∀x, p x ∨ r) ↔ (∀x, p x) ∨ r :=
  Iff.intro
    (λ hapr : ∀x, p x ∨ r =>
      byCases
        (λ hr : r => Or.inr hr)
        (λ hnr : ¬r => Or.inl λ x : α =>
          Or.elim (hapr x)
            (λ hp : p x => hp)
            (λ hr : r => absurd hr hnr)))
    (λ hapr : (∀x, p x) ∨ r =>
      Or.elim hapr
        (λ hap : ∀x, p x =>
          λ x : α => Or.inl $ hap x)
        (λ hr : r =>
          λ x : α => Or.inr hr))


example : (∀x, r → p x) ↔ (r → ∀x, p x) :=
  Iff.intro
    (λ harp : ∀x, r → p x =>
      λ hr : r =>
        λ x : α => harp x hr)
    (λ hrap : r → ∀x, p x =>
      λ x : α =>
        λ hr : r => hrap hr x)


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀x : men, shaves barber x ↔ ¬shaves x x) : False :=
  have hb := h barber
  have nsbb : ¬shaves barber barber :=
    λ sbb : shaves barber barber => hb.mp sbb sbb
  have sbb : shaves barber barber :=
    hb.mpr nsbb
  show False from nsbb sbb


example : (∃x : α, r) → r :=
  λ her : ∃x : α, r =>
    Exists.elim her λ (x : α) (hr : r) => hr


example (a : α) : r → (∃x : α, r) :=
  λ hr : r => Exists.intro a hr


example : (∃x, p x ∧ r) ↔ (∃x, p x) ∧ r :=
  Iff.intro
    (λ hepr : ∃x, p x ∧ r =>
      Exists.elim hepr
        λ (x : α) (hpr : p x ∧ r) =>
          And.intro
            (Exists.intro x hpr.left)
            (hpr.right))
    (λ hepr : (∃x, p x) ∧ r =>
      Exists.elim hepr.left
        λ (x : α) (hp : p x) =>
          Exists.intro x $ And.intro hp hepr.right)


example : (∃x, p x ∨ q x) ↔ (∃x, p x) ∨ (∃x, q x) :=
  Iff.intro
    (λ hepq : ∃x, p x ∨ q x =>
      Exists.elim hepq
        λ (x : α) (hpq : p x ∨ q x) =>
          Or.elim hpq
            (λ hp : p x => Or.inl $ Exists.intro x hp)
            (λ hq : q x => Or.inr $ Exists.intro x hq))
    (λ hepeq : (∃x, p x) ∨ (∃x, q x) =>
      Or.elim hepeq
        (λ hep : ∃x, p x =>
          Exists.elim hep
            λ (x : α) (hp : p x) =>
              Exists.intro x $ Or.inl hp)
        (λ heq : ∃x, q x =>
          Exists.elim heq
            λ (x : α) (hq : q x) =>
              Exists.intro x $ Or.inr hq))


example : (∀x, p x) ↔ ¬(∃x, ¬p x) :=
  Iff.intro
    (λ hap : ∀x, p x =>
      λ henp : ∃x, ¬p x =>
        Exists.elim henp
          λ (x : α) (hnp : ¬p x) => hnp $ hap x)
    (λ hnenp : ¬(∃x, ¬p x) =>
      λ x : α =>
        byContradiction
          λ hnp : ¬p x =>
            hnenp $ Exists.intro x hnp)


example : (∃x, p x) ↔ ¬(∀x, ¬p x) :=
  Iff.intro
    (λ hep : ∃x, p x =>
      λ hanp : ∀x, ¬p x =>
        Exists.elim hep
          λ (x : α) (hp : p x) => hanp x hp)
    (λ hnanp : ¬(∀x, ¬p x) =>
      byContradiction
        λ hnep : ¬∃x, p x =>
          hnanp $ λ (x : α) =>
            λ hp : p x =>
              hnep $ Exists.intro x hp)


example : (¬∃x, p x) ↔ (∀x, ¬p x) :=
  Iff.intro
    (λ hnep: ¬∃x, p x =>
      λ x : α =>
        λ hp : p x =>
          absurd (Exists.intro x hp) hnep)
    (λ hanp : ∀x, ¬p x =>
      λ hep : ∃x, p x =>
        Exists.elim hep
          λ (x : α) (hp: p x) => hanp x hp)


example : (¬∀x, p x) ↔ (∃x, ¬p x) :=
  Iff.intro
    (λ hnap : ¬∀x, p x =>
      byContradiction
        λ hnenp : ¬∃x, ¬p x =>
          hnap $ λ (x : α) =>
            byContradiction
              λ hnp : ¬p x =>
                hnenp $ Exists.intro x hnp)
    (λ henp : ∃x, ¬p x =>
      λ hap : ∀x, p x =>
        Exists.elim henp
          λ (x : α) (hnp : ¬p x) =>
            hnp $ hap x)


example : (∀x, p x → r) ↔ (∃x, p x) → r :=
  Iff.intro
    (λ hapr : ∀x, p x → r =>
      λ hep : ∃x, p x =>
        Exists.elim hep
          λ (x : α) (hp : p x) => hapr x hp)
    (λ hepr : (∃x, p x) → r =>
      λ x : α =>
        λ hp : p x =>
          hepr $ Exists.intro x hp)


example (a : α) : (∃x, p x → r) ↔ (∀x, p x) → r :=
  Iff.intro
    (λ hepr : ∃x, p x → r =>
      λ hap : ∀x, p x =>
        Exists.elim hepr
          λ (x : α) (hpr : p x → r) => hpr $ hap x)
    (λ hapr : (∀x, p x) → r =>
      byCases
        (λ hap : ∀x, p x =>
          Exists.intro a (λ hp : p a => hapr hap))
        (λ hnap : ¬∀x, p x =>
          Exists.elim
            (byContradiction
              λ hnenp : ¬∃x, ¬p x =>
                hnap $ λ (x : α) =>
                  byContradiction
                    λ hnp : ¬p x =>
                      hnenp $ Exists.intro x hnp)
            λ (x : α) (hnp : ¬p x) =>
              Exists.intro x (λ hp : p x => absurd hp hnp)))


example (a : α) : (∃x, r → p x) ↔ (r → ∃x, p x) :=
  Iff.intro
    (λ herp : ∃x, r → p x =>
      λ hr : r =>
        Exists.elim herp
          λ (x : α) (hrp : r → p x) =>
            Exists.intro x $ hrp hr)
    (λ hrep : r → ∃x, p x =>
      byCases
        (λ hr : r =>
          Exists.elim (hrep hr)
            λ (x : α) (hp : p x) =>
              Exists.intro x (λ hr : r => hp))
        (λ hnr : ¬r =>
          Exists.intro a (λ hr : r => absurd hr hnr)))
