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
