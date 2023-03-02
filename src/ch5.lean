section ex1

section ch3_with_tactics
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  <;> intros
  <;> constructor
  <;> first | apply And.left ; assumption
            | apply And.right ; assumption

example : p ∨ q ↔ q ∨ p := by
  constructor
  <;> intro h
  <;> apply (Or.elim h)
  <;> intros
  <;> first | apply Or.inl ; assumption
            | apply Or.inr ; assumption
  
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro ⟨⟨hp, hq⟩, hr⟩
    repeat (any_goals constructor)
    all_goals assumption
  . intro ⟨hp, hq, hr⟩
    repeat (any_goals constructor)
    all_goals assumption

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  <;> intro h
  <;> apply (Or.elim h)
  <;> intro g
  . apply (Or.elim g)
    <;> intros
    . apply Or.inl ; assumption
    . apply Or.inr ; apply Or.inl ; assumption
  . apply Or.inr ; apply Or.inr ; assumption
  . apply Or.inl ; apply Or.inl ; assumption
  . apply (Or.elim g)
    <;> intros
    . apply Or.inl ; apply Or.inr ; assumption
    . apply Or.inr ; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro
    | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
    | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩  
  . intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩ 
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro
    | Or.inl hp => constructor <;> apply Or.inl <;> assumption
    | Or.inr ⟨hq, hr⟩ => constructor <;> apply Or.inr <;> assumption
  . intro
    | ⟨Or.inl hp, _⟩ => exact Or.inl hp
    | ⟨Or.inr _, Or.inl hp⟩ => exact Or.inl hp
    | ⟨Or.inr hq, Or.inr hr⟩ => exact Or.inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  <;> intro h
  <;> intro g
  . exact h g.left g.right
  . intros ; exact h (by apply And.intro <;> assumption)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  <;> intro h
  . constructor <;> intro h₂ <;> apply h
    <;> first | apply Or.inl ; assumption | apply Or.inr ; assumption
  . intro
  | Or.inl h₂ => exact h.left h₂
  | Or.inr h₂ => exact h.right h₂

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  <;> intro h
  . constructor
    <;> intro h₂
    <;> apply h
    . apply Or.inl ; assumption
    . apply Or.inr ; assumption
  . intro
    | Or.inl hp => apply h.left ; assumption  
    | Or.inr hq => apply h.right ; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl np => intro npq ; apply np ; exact npq.left
  | Or.inr nq => intro npq ; apply nq ; exact npq.right

example : ¬(p ∧ ¬p) := by intro h ; exact h.right h.left

example : p ∧ ¬q → ¬(p → q) := by intro h hn ; exact h.right (hn h.left)

example : ¬p → (p → q) := by intros ; contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  apply Or.elim h
  <;> intro g
  . contradiction
  . assumption

example : p ∨ False ↔ p := by
  constructor
  <;> intro h
  . apply (Or.elim h)
    <;> intros
    . assumption
    . contradiction
  . exact Or.inl h 

example : p ∧ False ↔ False := by
  constructor
  <;> intro h
  . exact h.right
  . contradiction

example : (p → q) → (¬q → ¬p) := by
  intro h nq np
  apply nq ; apply h ; assumption

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  apply Or.elim (em p)
  <;> intro g
  . apply Or.elim (h g)
    <;> intros
    . apply (Or.inl) ; intro ; assumption
    . apply (Or.inr) ; intro ; assumption
  . apply (Or.inl) ; intro ; contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  apply Or.elim (em p)
  <;> intro
  . apply Or.inr
    intro
    apply h
    constructor <;> assumption
  . apply Or.inl ; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  apply Or.elim (em p)
  <;> intro g
  . constructor
    exact g
    intro hq
    apply h
    exact (λ _ => hq)
  . apply Or.elim (em q)
    <;> intros i
    . have _ : False := (h λ _ => i)
      contradiction
    . have _ : False := h (λ hp => absurd hp g)
      contradiction

example : (p → q) → (¬p ∨ q) := by
  intro h
  apply Or.elim (em p)
  <;> intro g
  . exact Or.inr (h g)
  . exact Or.inl g

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  apply Or.elim (em q)
  <;> intro g
  . assumption
  . have : ¬p := h g
    contradiction

example : p ∨ ¬p := by exact em p

example : (((p → q) → p) → p) := by
  intro h
  apply Or.elim (em p)
  . apply id
  . intros ; apply h ; intros ; contradiction

end ch3_with_tactics



section ch4_with_tactics
section ex1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor <;> intro ha
    . apply And.left ; apply (h ha)
    . apply And.right ; apply (h ha)
  . intro ⟨f, g⟩
    intro ha
    constructor ; exact f ha ; exact g ha

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h₁ h₂ _ ; apply h₁ ; apply h₂

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h ha
  apply (Or.elim h)
  <;> intro g
  . exact Or.inl (g ha)
  . exact Or.inr (g ha)

end ex1


section ex2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by
  intro ha
  constructor
  <;> intro g
  . exact g ha
  . intro ; assumption

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  <;> intro h
  . apply Or.elim (em r)
    . intros ; apply Or.inr ; assumption
    . intro nr
      apply Or.inl
      intro ha
      apply Or.elim (h ha)
      <;> intro
      . assumption
      . contradiction
  . intro ha
    apply (Or.elim h)
    . intro f ; apply Or.inl ; exact f ha
    . intro hr ; apply Or.inr ; assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor <;> intro h₁ _ _ <;> apply h₁ <;> assumption

end ex2


section ex3
open Classical
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  apply Or.elim (em (shaves barber barber))
  <;> intro e
  <;> apply (h barber).mp
  <;> first | assumption
            | exact (h barber).mpr e

end ex3


section ex5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro h
  apply h.elim
  intro ; intro ; assumption

example (a : α) : r → (∃ _ : α, r) := by
  intro hr ; constructor <;> assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor <;> intro h
  . apply h.elim
    intro h₂ h₃
    exact ⟨⟨h₂, h₃.left⟩, h₃.right⟩
  . apply h.left.elim
    intro h₂ h₃
    exact ⟨h₂, ⟨h₃, h.right⟩⟩
  
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor <;> intro h
  . apply h.elim
    intro h₂ h₃
    apply h₃.elim
    . intro ph₂
      exact Or.inl ⟨h₂, ph₂⟩
    . intro qh₂
      exact Or.inr ⟨h₂, qh₂⟩
  . apply h.elim
    . intro ⟨ha, hpa⟩
      exact ⟨ha, Or.inl hpa⟩
    . intro ⟨hq, hqa⟩
      exact ⟨hq, Or.inr hqa⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor <;> intro h₁ h₂
  . cases h₂ with
    | intro ha hpa => exact (hpa (h₁ ha))
  . apply Or.elim (em (p h₂))
    . apply id
    . intro h₃
      have : False := h₁ ⟨h₂, h₃⟩
      contradiction

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor <;> intro h
  . intro hn
    cases h with
    | intro ha hpa => apply hn ; apply hpa
  . apply Or.elim (em (∃ x, p x))
    . apply id
    . intro c ; have : False := by
        apply h
        intro _ _
        apply c
        constructor <;> assumption
      contradiction

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  <;> intro h₁ h₂
  . intro ph₂
    apply h₁ ; constructor <;> assumption
  . cases h₂ with
    | intro ha hpa => exact h₁ ha hpa

-- 112
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  <;> intro h
  . apply byContradiction
    intro c₁ ; apply h ; intro ha
    apply byContradiction
    intro c₂ ; apply c₁ ; exact ⟨ha, c₂⟩
  . intro h₂
    cases h with | intro ha npa => exact npa (h₂ ha)


example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  <;> intro h₁ h₂
  . cases h₂ with | intro ha hpa => exact (h₁ ha) hpa
  . intro ph₂ ; exact h₁ ⟨h₂, ph₂⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  <;> intro h
  . intro h₂
    cases h with | intro ha hpa => exact hpa (h₂ ha)
  . admit

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  <;> intro h
  . intro hr
    cases h with | intro ha hpa => exact ⟨ha, hpa hr⟩
  . apply Or.elim (em r)
    . intro hr
      cases (h hr) with | intro ha hpa =>
        exact ⟨ha, by intro ; assumption ⟩ 
    . intro nr
      constructor
      <;> first | intro ; contradiction | assumption

end ex5
end ch4_with_tactics
end ex1



section ex2
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
-- a long, yet techincally correct, line..
  constructor <;> constructor <;> first | assumption | apply Or.inr <;> first | apply Or.inl ; assumption | apply Or.inr ; assumption

end ex2
