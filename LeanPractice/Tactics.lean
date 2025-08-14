variable (p q r : Prop)


-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  intro h
  constructor
  exact h.right
  exact h.left
  intro h
  constructor
  exact h.right
  exact h.left

example : p ∧ q ↔ q ∧ p := by
  constructor
  intro h
  symm
  assumption
  intro h
  symm
  assumption


example : p ∨ q ↔ q ∨ p := by
  constructor
  intro h
  symm
  assumption
  intro h
  symm
  assumption


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  intro h
  constructor
  exact h.left.left
  constructor
  exact h.left.right
  exact h.right
  intro h
  constructor
  constructor
  exact h.left
  exact h.right.left
  exact h.right.right


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  intro h
  cases h with
    | inl hpq =>
      cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq => exact Or.inr $ Or.inl hq
    | inr hr => exact Or.inr $ Or.inr hr
  intro h
  cases h with
    | inl hp => exact Or.inl $ Or.inl hp
    | inr hqr =>
      cases hqr with
        | inl hq => exact Or.inl $ Or.inr hq
        | inr hr => exact Or.inr hr


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor <;> intro <;> rename_i a <;> cases a
  rename_i hqr <;> cases hqr
  apply Or.inl; constructor <;> assumption
  apply Or.inr; constructor <;> assumption
  all_goals rename_i a <;> cases a <;> constructor <;> try assumption
  apply Or.inl; assumption
  apply Or.inr; assumption


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  intro hpqr
  constructor
  cases hpqr
  apply Or.inl
  assumption
  rename_i hqr
  exact Or.inr hqr.left
  cases hpqr with
    | inl hp => exact Or.inl hp
    | inr hqr => exact Or.inr hqr.right
  intro hpqpr
  cases hpqpr
  rename_i hpq hpr
  if hp : p
  then exact Or.inl hp
  else
    cases hpq
    contradiction
    cases hpr
    contradiction
    rename_i hq hr
    exact Or.inr $ And.intro hq hr


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  intro hpqr hpq
  exact hpqr hpq.left hpq.right
  intro hpqr hp hq
  exact hpqr $ And.intro hp hq


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  intro hpqr
  constructor
  intro hp
  exact hpqr $ Or.inl hp
  intro hq
  exact hpqr $ Or.inr hq
  intro hprqr hpq
  cases hpq with
    | inl hp => exact hprqr.left hp
    | inr hq => exact hprqr.right hq


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  intro hnpq
  constructor
  intro hp
  exact hnpq $ Or.inl hp
  intro hq
  exact hnpq $ Or.inr hq
  intro hnpnq hpq
  cases hnpnq
  cases hpq
  repeat contradiction


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro hnpnq hpq
  cases hpq
  cases hnpnq
  repeat contradiction


example : ¬(p ∧ ¬p) := by
  intro hpnp
  cases hpnp
  contradiction


example : p ∧ ¬q → ¬(p → q) := by
  intro hpnq hpq
  have hq : q := hpq hpnq.left
  have hnq : ¬q := hpnq.right
  contradiction


example : ¬p → (p → q) := by
  intro hnp hp
  contradiction


example : (¬p ∨ q) → (p → q) := by
  intro hnpq hp
  cases hnpq
  contradiction
  assumption


example : p ∨ False ↔ p := by
  constructor
  intro hpf
  cases hpf
  assumption
  contradiction
  intro hp
  exact Or.inl hp


example : p ∧ False ↔ False := by
  constructor
  intro hpf
  exact hpf.right
  intro hf
  contradiction


example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact hnq $ hpq hp


-- Redo

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor <;> intro <;> symm <;> assumption


example : p ∨ q ↔ q ∨ p := by
  constructor <;> intro <;> symm <;> assumption


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor <;> intro h <;> cases h <;> rename_i a b
  all_goals first | cases a | cases b
  all_goals (repeat' constructor) <;> assumption


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor <;> intro h <;> cases h <;> rename_i a <;> try cases a
  all_goals first
    | apply Or.inl; first
      | apply Or.inl; assumption
      | apply Or.inr; assumption
      | assumption
    | apply Or.inr; first
      | apply Or.inl; assumption
      | apply Or.inr; assumption
      | assumption


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor <;> intro h <;> cases h <;> rename_i a <;> cases a
  apply Or.inl; constructor <;> assumption
  apply Or.inr; constructor <;> assumption
  all_goals constructor <;> try assumption
  apply Or.inl; assumption
  apply Or.inr; assumption


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor <;> intro <;> rename_i a <;> cases a
  constructor <;> apply Or.inl <;> assumption
  constructor <;> rename_i hqr <;> cases hqr <;> apply Or.inr <;> assumption
  rename_i hpq hpr; cases hpq <;> cases hpr <;> try apply Or.inl <;> assumption
  apply Or.inr <;> constructor <;> assumption


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor <;> intros
  rename_i hpqr hpq; cases hpq <;> apply hpqr <;> assumption
  rename_i hpqr _ _; apply hpqr <;> constructor <;> assumption


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor <;> intros
  rename_i hpqr; constructor <;> intro <;> apply hpqr
  apply Or.inl; assumption
  apply Or.inr; assumption
  rename_i hprqr hpq; cases hprqr; cases hpq <;> rename_i a b _
  apply a; assumption
  apply b; assumption


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor <;> repeat intro
  constructor <;> intro
  rename_i hp; have : p ∨ q := Or.inl hp; contradiction
  rename_i hq; have : p ∨ q := Or.inr hq; contradiction
  rename_i hnpnq hpq; cases hnpnq; cases hpq <;> contradiction


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  repeat intro
  rename_i hnpnq hpq; cases hpq; cases hnpnq <;> contradiction


example : ¬(p ∧ ¬p) := by
  intro; rename_i hpnp; cases hpnp; contradiction


example : p ∧ ¬q → ¬(p → q) := by
  repeat intro
  rename_i hpnq hpq; cases hpnq
  rename_i hp _; have := hpq hp; contradiction


example : ¬p → (p → q) := by
  intros; contradiction


example : (¬p ∨ q) → (p → q) := by
  intros; rename_i hnpq _; cases hnpq; contradiction; assumption


example : p ∨ False ↔ p := by
  constructor <;> intro
  rename_i hpf; cases hpf; assumption; contradiction
  constructor; assumption


example : p ∧ False ↔ False := by
  constructor <;> intro
  apply And.right <;> assumption
  contradiction


example : (p → q) → (¬q → ¬p) := by
  repeat intro
  rename_i hpq _ hp; have := hpq hp; contradiction
