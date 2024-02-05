/-!Old version with nested functions-/
def apply4' {α : Type}: (α → α) → α → α 
| f => fun a => f (f (f (f (a))))

/-!New version with composition (backslash o)-/
def apply4 {α : Type}: (α → α) → α → α 
| f => fun a => (f ∘ f ∘ f ∘ f) a

/-!Apply a function an arbitrary number of times-/
def applyN {α : Type} : Nat → (α → α) → α → α
| Nat.zero, _ => fun a => a
| Nat.succ n', f => fun a => f (applyN n' f a)

def sq : Nat → Nat
|n => n*n

#eval (applyN 5 Nat.succ 0)

#eval (applyN 5 sq 2)

#check @List

def e : List Nat := List.nil
def e' : List Nat := [] --Just notation, the same

def l1 : List Nat := List.cons 1 e
def l1' : List Nat := 1::e --:: as notation for cons
def l1'' : List Nat := [1]

def l2 : List Nat := List.cons 0 l1
def l2' : List Nat := 0::l1'
def l2'' : List Nat := [0,1]

/-!Case analysis example for list length-/
def ListLen {α : Type} : List α → Nat
|List.nil => 0
|List.cons _ l' => 1 + ListLen l'

#eval ListLen [1,2,3]

--Continued 1/31
--applyN version using the apply, proper parenthesis is key

def applyN' {α : Type} : Nat → (α → α) → α → α
| Nat.zero, _ => fun a => a
| Nat.succ n', f => fun a => (f ∘ applyN n' f) a

--Look ma, no Lambda (for the recursive case anyway, get the function from the zero case)
def applyN'' {α : Type} : Nat → (α → α) → α → α
| Nat.zero, _ => fun a => a
| Nat.succ n', f => f ∘ applyN n' f

#eval (applyN' 5 Nat.succ 0)

#eval (applyN' 5 sq 2)

def my_comp {α β γ : Type} :  (α → β) → (β → γ) → (α → γ)
|f, g => fun a => (g ∘ f) a

--prev version for comparison, managed to recreate but swapped the input functions
def comp (α β γ : Type) : (β → γ) → (α → β) → (α → γ)
|g, f => fun a => g (f a)
