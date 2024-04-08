

/-!
Basic predicate for the set of even natural numbers
evens := { n : Nat | isEven n}
-/
def isEven : Nat → Prop := λ n=>  n%2 ==0 --basic predicate example

def lessEq: Nat → Nat → Prop := λ n m => n <= m



/-!
Properties of sets and relations:

-/

def isSym {a:Type} := ∀  (r : α → α → Prop), ∀  (a b : α) => r a b → r b a
