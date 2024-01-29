/-!generalized Nat addition v1-/
def add' : Nat → Nat → Nat
|a, b => a+b

#eval add' 5 7

--I assume you wanted case analysis, so here's a more convoluted version
def add : Nat → Nat → Nat
| a, Nat.zero => a
| a, Nat.succ b' => add (Nat.succ a) b'

#eval add 5 7

/-!Polymorphic list append-/
def ListApp {α : Type} : List α → List α → List α
|List.nil, l2 => l2
|List.cons h l1', l2 => List.cons h (ListApp l1' l2)

#eval ListApp [1,2,3] [4,5,6]