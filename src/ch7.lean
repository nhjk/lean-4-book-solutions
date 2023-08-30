namespace Hidden
/-
As an exercise, you should think about what the introduction
and elimination rules for these types do. As a further
exercise, we suggest defining boolean operations and, or,
not on the Bool type, and verifying common identities. Note
that you can define a binary operation like and using match:
-/

inductive Bool where
  | t : Bool
  | f : Bool

namespace Bool
def and (a b : Bool) : Bool :=
  match a with
  | t => b
  | f => f

def or (a b : Bool) : Bool :=
  match a with
  | t => t
  | f => b

def not (a : Bool) : Bool :=
  match a with
  | t => f
  | f => t

example (a b : Bool) (h : a = t) : or a b = t := calc
  or a b = or t b := by rw [h]
  _ = t := by rfl

example (a b : Bool) (h : a = t) : and a b = b := by rw [h] ; rfl
end Bool
end Hidden



namespace Hidden
universe u v w
/-
As exercises, we encourage you to develop a notion of composition
for partial functions from α to β and β to γ, and show that it
behaves as expected. We also encourage you to show that Bool and
Nat are inhabited, that the product of two inhabited types is
inhabited, and that the type of functions to an inhabited type is
inhabited.
-/

def comp {α : Type u} {b : Type v} {γ : Type w} (g : α → Option β) (f : β → Option γ) : α → Option γ :=
  λ ha => match (g ha) with
  | some hb => f hb
  | none => none

def sum_fst {α : Type u} {β : Type v} (s : Sum α β) : Option α :=
  match s with
  | Sum.inl ha => some ha
  | _ => none

def sum_snd {α : Type u} {β : Type v} (s : Sum α β) : Option β := 
  match s with
  | Sum.inr hb => some hb
  | _ => none

example : Inhabited Bool := Inhabited.mk Bool.t
example : Inhabited Nat := Inhabited.mk Nat.zero
example (α : Type u) (β : Type v) (hia : Inhabited α) (hib : Inhabited β) : Inhabited (α × β) :=
  Inhabited.mk (hia.default, hib.default)
end Hidden



namespace Hidden
inductive List' (α : Type u) where
| nil  : List' α
| cons : α → List' α → List' α

namespace List'

def append (as bs : List' α) : List' α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List' α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List' α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List' α) : append as nil = as :=
  List'.recOn (motive := λ as => append as nil = as)
    as
    rfl
    λ a as ih => show append (cons a as) nil = cons a as from
      have h1 : append (cons a as) nil = cons a (append as nil) := cons_append a as nil
      have h2 : cons a (append as nil) = cons a as := by rw [ih]
      h1.trans h2

theorem append_assoc (as bs cs : List' α)
        : append (append as bs) cs = append as (append bs cs) :=
  List'.recOn (motive := λ xs => append (append xs bs) cs = append xs (append bs cs))
    as
    (show append (append nil bs) cs = append nil (append bs cs) by rw [nil_append, nil_append])
    λ x xs ih =>
      show
append (append (cons x xs) bs) cs = append (cons x xs) (append bs cs)
      from calc
        _ = cons x (append (append xs bs) cs) := by rw [cons_append, cons_append]
        _ = cons x (append xs (append bs cs)) := by rw [ih]

/-
Try also defining the function
length : {α : Type u} → List α → Nat
that returns the length of a list, and prove that it behaves as
expected (for example, length (append as bs) = length as + length bs).
-/
def length : {α : Type u} → (as : List' α) → Nat :=
  λ as => match as with 
  | nil => 0
  | cons _ as' => 1 + length as'

example : length (append as bs) = length as + length bs :=
  List'.recOn (motive := fun xs => length (append xs bs) = length xs + length bs) as
    (by calc length (append nil bs)
      = length bs := by rw [nil_append]
      _ = 0 + length bs := by rw [Nat.zero_add]
      _ = length nil + length bs := rfl
    )
    (λ a as ih => show length (append (cons a as) bs) = length (cons a as) + length bs
      by calc length (append (cons a as) bs)
        = length (cons a (append as bs)) := by rw [cons_append]
      _ = 1 + length (append as bs) := rfl
      _ = 1 + (length as + length bs) := by rw [ih]
      _ = 1 + length as + length bs := by rw [Nat.add_assoc]
      _ = length (cons a as) + length bs := rfl
    )

end List'
end Hidden



namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  Eq.subst h₂ h₁

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
end Hidden



section Exercise1
/-
Try defining other operations on the natural numbers, such as
multiplication, the predecessor function (with pred 0 = 0),
truncated subtraction (with n - m = 0 when m is greater than or
equal to n), and exponentiation. Then try proving some of their
basic properties, building on the theorems we have already proved.
-/

def multiply (a b : Nat) : Nat :=
  match b with
  | Nat.zero => 0
  | Nat.succ b => a + multiply a b

theorem zero_multiply (n : Nat) : multiply 0 n = 0 :=
  Nat.recOn (motive := λ x => multiply 0 x = 0)
    n
    rfl
    (λ x ih =>
show multiply 0 (Nat.succ x) = 0 from calc
_ = 0 + multiply 0 x := by rw [multiply]
_ = multiply 0 x := by rw [Nat.zero_add]
_ = 0 := by rw [ih]
)

theorem one_multiply (b : Nat) : multiply 1 b = b :=
  Nat.recOn (motive := λ n => multiply 1 n = n)
  b
  (show multiply 1 0 = 0 by rw [multiply])
  (λ n ih => show multiply 1 (Nat.succ n) = Nat.succ n from calc
  _ = 1 + multiply 1 n := by rw [multiply]
  _ = 1 + n := by rw [ih]
  _ = n + 1 := by rw [Nat.add_comm])

theorem succ_multiply (a b : Nat) :
  multiply (Nat.succ a) b = b + multiply a b :=
Nat.recOn (motive := λ n => multiply (Nat.succ a) n = n + multiply a n)
  b
  rfl
  (λ n ih =>
show
  multiply (Nat.succ a) (Nat.succ n) =
  (Nat.succ n) + multiply a (Nat.succ n)
from calc
  _ = Nat.succ a + multiply (Nat.succ a) n := by rw [multiply]
  _ = (Nat.succ a) + (n + multiply a n) := by rw [ih]
  _ = Nat.succ a + n + multiply a n := by rw [Nat.add_assoc]
  _ = Nat.succ (a + n) + multiply a n := by rw [Nat.succ_add]
  _ = (a + Nat.succ n) + multiply a n := rfl
  _ = ((Nat.succ n) + a) + multiply a n := by rw [(Nat.add_comm a (Nat.succ n))]
  _ = Nat.succ n + (a + multiply a n) := by rw [Nat.add_assoc]
  _ = Nat.succ n + multiply a (Nat.succ n) := by rw [multiply]
)

theorem multiply_comm (a b : Nat) : multiply a b = multiply b a :=
  Nat.recOn (motive := λ n => multiply a n = multiply n a)
  b
  (by calc
    multiply a 0 = 0 := by rw [multiply]
    _ = multiply 0 a := by rw [zero_multiply])
  (λ n ih =>
    show
multiply a (Nat.succ n) = multiply (Nat.succ n) a
    from calc
      _ = a + multiply a n := by rw [multiply]
      _ = a + multiply n a := by rw [ih]
      _ = multiply (Nat.succ n) a := by rw [succ_multiply]
  )

infixl:100 "x" => multiply
postfix:1000 "++ " => Nat.succ

theorem distributive (a b c : Nat) : a x (b + c) = (a x b) + (a x c) :=
  Nat.recOn (motive := λ n => n x (b + c) = (n x b) + (n x c))
  a
  (
    show 0 x (b + c) = 0 x b + (0 x c) from calc
    _ = 0 := by rw [zero_multiply]
    _ = 0 + 0 := by rw [Nat.add_zero]
    _ = (0 x b) + (0 x c) := by rw [zero_multiply, zero_multiply]
  )
  (λ n ih => show (n++ x (b + c)) = n++ x b + n++ x c from calc
  _ = b + c + (n x (b + c)) := by rw [succ_multiply]
  _ = b + c + ((n x b) + (n x c)) := by rw [ih]
  _ = b + c + (n x b) + (n x c) := by rw [←Nat.add_assoc]
  _ = c + (b + (n x b)) + (n x c) := by rw [Nat.add_comm b c, ←Nat.add_assoc]
  _ = c + (n++ x b) + (n x c) := by rw [succ_multiply]
  _ = (n++ x b) + c + (n x c) := by rw [Nat.add_comm c]
  _ = (n++ x b) + (c + (n x c)) := by rw [Nat.add_assoc]
  _ = n++ x b + n++ x c := by rw [←succ_multiply])

theorem multiply_assoc (a b c : Nat) : a x b x c = a x (b x c) :=
  Nat.recOn (motive := λ n => n x b x c = n x (b x c))
  a
  (show 0 x b x c = 0 x (b x c) by simp [zero_multiply])
  (λ n ih =>
show (n++ x b) x c = n++ x (b x c)
from calc
  _ = (b + n x b) x c := by rw [succ_multiply]
  _ = c x (b + n x b) := by rw [multiply_comm]
  _ = c x b + c x (n x b) := by rw [distributive]
  _ = c x b + n x b x c := by rw [multiply_comm c (n x b)]
  _ = c x b + n x (b x c) := by rw [ih]
  _ = b x c + n x (b x c) := by rw [multiply_comm]
  _ = n++ x (b x c) := by rw [succ_multiply]
)
end Exercise1



section Exercise2

def length (l : List α) : Nat :=
match l with
| List.nil => 0
| List.cons _ tail => 1 + length tail

def reverse (l : List α) : List α :=
  match l with
  | [] => []
  | List.cons h t => (reverse t) ++ [h]

theorem length_append (s t : List α) : length (s ++ t) = length s + length t :=
  List.recOn (motive := λ l => length (l ++ t) = length l + length t)
  s
  (show length ([] ++ t) = length [] + length t from calc
  _ = length t := by simp
  _ = length [] + length t := by simp [Nat.zero_add, length])
  (λ hd tl ih =>
    have h1 :
      length (hd::tl) + length t = 1 + length tl + length t
    := by rw [length]
    show
      length ((hd::tl) ++ t) = length (hd::tl) + length t
    from calc
      _ = length (hd :: (tl ++ t)) := by rw [List.cons_append]
      _ = 1 + length (tl ++ t) := by rw [length]
      _ = 1 + (length tl + length t) := by rw [ih]
      _ = 1 + length tl + length t := by rw [Nat.add_assoc]
      _ = _ := by rw [Eq.symm h1]
  )

example (t : List α) : length (reverse t) = length t :=
t.rec
(motive := λ l => length (reverse l) = length l)
rfl
λ h l ih => show
  length (reverse (h::l)) = length (h::l)
from calc
  _ = length (reverse l ++ [h]) := rfl
  _ = length (reverse l) + length [h] := by rw [length_append]
  _ = length l + length [h] := by rw [ih]
  _ = length [h] + length l := by rw [Nat.add_comm]
  _ = length ([h] ++ l) := by rw [←length_append]
  _ = length (h::l) := by simp

theorem reverse_append (a b : List α)
: reverse (a ++ b) = reverse b ++ reverse a :=
a.rec
(motive := λ l => reverse (l ++ b) = reverse b ++ reverse l)
(show
  reverse ([] ++ b) = reverse b ++ reverse []
  from calc
    _ = reverse b := by rw [List.nil_append]
    _ = reverse b ++ [] := by rw [List.append_nil]
    _ = (reverse b) ++ (reverse []) := rfl)
(λ h t ih => show
  reverse ((h::t) ++ b) = reverse b ++ reverse (h::t)
  from calc
    _ = reverse (h :: (t ++ b)) := by rw [List.cons_append]
    _ = reverse (t ++ b) ++ [h] := rfl
    _ = (reverse b ++ reverse t) ++ [h] := by rw [ih]
    _ = reverse b ++ (reverse t ++ [h]) := by rw [List.append_assoc]
    _ = reverse b ++ reverse (h::t) := rfl)

example (t : List α) : reverse (reverse t) = t :=
t.rec
(motive := λ l => reverse (reverse l) = l)
rfl
λ h l ih => show 
  reverse (reverse (h::l)) = h::l
from calc
  _ = reverse (reverse l ++ [h]) := rfl
  _ = (reverse [h]) ++ reverse (reverse l) := by rw [reverse_append]
  _ = [h] ++ reverse (reverse l) := rfl
  _ = [h] ++ l := by rw [ih]
  _ = h::l := rfl

end Exercise2



-- for exercise 3 and 4: 3 uses index, 4 uses i
inductive Vector (α : Type u) : Nat → Type u where
| nil  : Vector α 0
| cons : α → {n : Nat} → Vector α n → Vector α (Nat.succ n)
deriving Repr

namespace Vector
def size {s : Nat} {_ : Vector α s} : Nat := s

def index {s : Nat} (v : Vector α s) (i : Nat) {h : i < s} : α :=
  if h₁ : (Nat.succ i) < s then
    match v with
    | Vector.cons _ v' => 
      @index α v'.size v' i (Nat.lt_of_succ_lt_succ h₁)
    | Vector.nil      => absurd h (Nat.not_lt_zero i)
  else
    match v with
    | Vector.cons a _ => a
    | Vector.nil => absurd h (Nat.not_lt_zero i)

def i (v : Vector α s) (index : Nat) : Option α :=
  if index == s - 1 then
    match v with
    | Vector.cons a _ => a
    | Vector.nil => none
  else if index < s - 1 then
    match v with
    | Vector.cons _ v' => i v' index
    | Vector.nil => none
  else
    none
def nth (v : Vector α s) (index : Nat) : Option α := i v index
end Vector



section Exercise3
/-
Define an inductive data type consisting of terms built up from the
following constructors:
- const n, a constant denoting the natural number n
- var n, a variable, numbered n
- plus s t, denoting the sum of s and t
- times s t, denoting the product of s and t

Recursively define a function that evaluates any such term with respect
to an assignment of values to the variables.
-/
inductive Foo : Nat → Type where
| const (n : Nat) : Foo 0
| var (i : Nat) : Foo i
| plus (a : Foo s) (b : Foo t) : Foo (s + t)

theorem lt_add {a b c : Nat} (h : a + b < c) : a < c :=
  have h₁ : a ≤ a + b := Nat.recOn b (by simp) (λ _ ih => Nat.le_succ_of_le ih)
  Nat.lt_of_le_of_lt h₁ h

def eval {n m : Nat} {h : n < m} (f : Foo n) (vars : Vector Nat m) : Nat :=
  match f with
  | Foo.const n => n
  | Foo.var i   => @Vector.index Nat vars.size vars i h
  | @Foo.plus s t a b => eval a vars (h := lt_add h) +
      eval b vars (h := lt_add (by rw [Nat.add_comm] at h; exact h))

def a : Vector Nat 2 := Vector.cons 1 (Vector.cons 2 Vector.nil)
#eval Vector.index a (i := 0) (h := by simp)
def b := Foo.plus (Foo.var 0) (Foo.var 1)
#eval eval b a (h := by simp)
end Exercise3



section Exercise4
/-
Similarly, define the type of propositional formulas, as well as
functions on the type of such formulas: an evaluation function,
functions that measure the complexity of a formula, and a function
that substitutes another formula for a given variable.
-/
inductive PropFormula : Nat → Type where
| var (i : Nat) : PropFormula i
| and (_ : PropFormula s) (_ : PropFormula t) : PropFormula (max s t)
| or (_ : PropFormula s) (_ : PropFormula t) : PropFormula (max s t)
| not (_ : PropFormula s) : PropFormula (max s t)
| iff (_ : PropFormula s) (_ : PropFormula t) : PropFormula (max s t)
| true' : PropFormula 0
| false' : PropFormula 0

namespace PropFormula
def eval_formula (f : PropFormula n) (vars : Vector Bool m) : Option Bool :=
  match f with
  | var i => vars.i i
  | and a b =>
      match eval_formula a vars with
      | none => none
      | some p =>
        match eval_formula b vars with
        | none => none
        | some q => some (p ∧ q)
  | or a b => 
      match eval_formula a vars with
      | none => none
      | some p =>
        match eval_formula b vars with
        | none => none
        | some q => some (p ∨ q)
  | not a => 
      match eval_formula a vars with
      | none => none
      | some p => some (¬ p)
  | iff a b => 
      match eval_formula a vars with
      | none => none
      | some p =>
        match eval_formula b vars with
        | none => none
        | some q => some (p ↔ q)
  | true' => true
  | false' => false

def vars : Vector Bool 3 := open Vector in 
  cons true (cons false (cons false nil))
#eval eval_formula (or (and (var 0) (var 1)) (var 2)) vars
end PropFormula
end Exercise4