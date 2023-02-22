section ex1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := ⟨
  fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩,
  fun h hx => ⟨h.left hx, h.right hx⟩
⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 h2 h3 => (h1 h3 (h2 h3))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h1 h2 => h1.elim
    (fun h3 => (Or.inl (h3 h2)))
    (fun h3 => (Or.inr (h3 h2)))
end ex1


section ex2
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) :=
  fun ha => ⟨fun h => h ha, fun hr _ => hr⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨
    fun h => byCases
      (fun hr => Or.inr hr)
      (fun nr => Or.inl (fun ha => (h ha).elim id (fun hr => absurd hr nr))),
    fun h =>
      h.elim
        (fun h2 ha => Or.inl (h2 ha))
        (fun hr _ => Or.inr hr)
  ⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := ⟨
  fun h hr ha => h ha hr
, fun h ha hr => h hr ha
⟩
end ex2


section ex3
open Classical

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have dneMpr {p : Prop}: p → ¬¬p := absurd
  have hx {p : Prop} : (p ↔ ¬p) → False := byCases
    (fun hp => fun h2 => absurd hp (h2.mp hp))
    (fun hn => fun h2 => absurd hn (dneMpr (h2.mpr hn)))
  show False from hx (h barber)
end ex3


section ex4
def even (n : Nat) : Prop := ∃ x, 2 * x = n 

def prime (n : Nat) : Prop :=
  have divides (x y : Nat) : Prop := ∃ k, k * x = y
  ∀ (q : Nat), divides q n → q = 1 ∨ q = n  

-- helper for infinitely_many_primes and infinitely_many_Fermat_primes
def infinitely_many : (Nat -> Prop) → Prop :=
  fun h => ∀ (n : Nat), h n → (∃ (m : Nat), h m ∧ m > n)

def infinitely_many_primes : Prop := infinitely_many prime

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ x, 2 ^ (2 ^ x) = n 

def infinitely_many_Fermat_primes : Prop := infinitely_many Fermat_prime

def goldbach_conjecture : Prop :=
  ∀ (n : Nat), n > 2 → ∃ a b, prime a ∧ prime b ∧ n = a + b  

def Goldbach's_weak_conjecture : Prop :=
  ∀ (n : Nat),
    (¬ even n ∧ n > 5) →
      ∃ a b c, prime a ∧ prime b ∧ prime c ∧ n = a + b + c    

def Fermat's_last_theorem : Prop :=
  ∀ (n : Nat), n > 2 → ¬ ∃ a b c, n ^ a + n ^ b = n ^ c
end ex4

section ex5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := λ h => h.elim (λ _ hr => hr)

example (a : α) : r → (∃ _ : α, r) := λ h => ⟨a, h⟩

#check @Exists.elim
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨
  λ h => h.elim (fun ha and => ⟨Exists.intro ha and.left, and.right⟩)
, λ h => h.left.elim (λ ha hpa => ⟨ha, ⟨hpa, h.right⟩⟩)
⟩
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := ⟨
  λ h => h.elim (λ ha or => or.elim
    (λ hpa => Or.inl ⟨ha, hpa⟩)
    (λ hqa => Or.inr ⟨ha, hqa⟩))
, λ h => h.elim
    (λ epx => epx.elim (λ ha hpa => ⟨ha, Or.inl hpa⟩))
    (λ eqx => eqx.elim (λ ha hqa => ⟨ha, Or.inr hqa⟩))
⟩


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := ⟨
  λ h e => e.elim (λ ha n => absurd (h ha) n)
, λ h ha => byContradiction (λ n => absurd ⟨ha, n⟩ h)
⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := ⟨
  λ h n => h.elim (λ ha => n ha) 
, λ h => byContradiction
    λ (ne : ¬ ∃ x, p x) =>
      have nh : ∀ x, ¬ p x := λ ha hpa => absurd ⟨ha, hpa⟩ ne
      absurd nh h
⟩
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := ⟨
  λ h ha => byContradiction (λ x => x (λ y => (h ⟨ha, y⟩)))
, λ h e => e.elim (λ ha => h ha)
⟩
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := ⟨
  λ h => byContradiction
    (λ c₁ => h (λ ha => byContradiction (λ c₂ => c₁ ⟨ha, c₂⟩)))
, λ h => h.elim (λ a b c => b (c a)) 
⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := ⟨
  λ h₁ h₂ => h₂.elim (λ a b => h₁ a b),
  λ h₁ h₂ h₃ => h₁ ⟨h₂, h₃⟩
⟩
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := ⟨
  λ h₁ h₂ => h₁.elim (λ x y => y (h₂ x)) 
  -- difficult.. the solution in the book has 1 byCases and 2 byContradictions
, λ h₁ => byCases
  (λ h₂ : ∀ x, p x => ⟨a, λ _ => h₁ h₂⟩)
  (λ h₂ : ¬ ∀ x, p x => byContradiction
    (λ h₃ => h₃ ⟨a, λ h₄ => sorry⟩))
⟩
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := ⟨
  λ e hr => e.elim λ ha rpa => ⟨ha, rpa hr⟩
, λ h : r → ∃ x, p x =>
  show ∃ x, r → p x from  
  byCases
    (λ hr : r => (h hr).elim
      (λ ha => λ pha => ⟨ha, λ _ => pha⟩))
    (λ hn : ¬r => ⟨a, λ hr => absurd hr hn⟩)
⟩
end ex5
