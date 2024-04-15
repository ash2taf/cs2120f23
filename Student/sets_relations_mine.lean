import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
binary relation on a type, α
- reflexive
- symmetric
- transitive
- equivalence (Core.lean)
- asymmetric
- antisymmetric
- closures -- combine with some other relation, do everything to make it true
- inverse

- empty relation λ a b, a → b → False --no relations are present
- complete relation λ a b, a → b → True --All relations are present
- subrelation

binary relation from α → β, etc
- compose
- join

inverse image
-/

/-
order relations
- partial order: reflexive, antisymmetric, transitive
- poset: a set α along with a partial order on α
- total order: partial order ∧ ∀ a b, a < b ∨ b < a
-/

/-
functions
- a single-valued relation is a function

- domain of definition
- codomain
- domain
- range
- partial
- total

- identity function -- See Mathlib.Logic.Function.Basic

- one-to-one (vs many-to-one, injective)
- onto (surjective)
- bijective

- composition
- inverse
- etc
-/

inductive Person : Type
|lu
|mary
|jane

open Person

def likes : Person → Person → Prop :=
λ p1 p2 => p1 = Person.lu ∧ p2 = Person.mary

def likes' : Person → Person → Prop :=
λ p1 p2 =>
(p1 = Person.lu ∧ p2 = Person.mary) ∨
(p2 = Person.lu ∧ p1 = Person.mary)



#reduce likes Person.lu Person.mary

#reduce likes' lu jane

example : likes Person.lu Person.mary := ⟨rfl, rfl⟩
example : likes' Person.mary Person.lu := Or.inr ⟨rfl, rfl⟩

example : ¬likes' lu jane := --this is almost right, still some syntax fuckery. Prof will circle back later
λ h : likes' lu jane =>
by
  unfold likes' at h
  cases h
  | Or.inl l => nomatch l.2
  | Or.inr r => nomatch r.1
