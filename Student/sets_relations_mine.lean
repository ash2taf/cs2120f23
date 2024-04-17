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
  cases h with
  | inl l => nomatch l.2
  | inr r => nomatch r.1


  --Sets, not relations
def a_set : Set Nat := {1, 2, 3} --these are predicates, can apply to args
def b_set : Set Nat := {3, 4, 5} --see notation below for intuition on predicate useage

def c_set : Set Nat := {n : Nat | 0 < n ∧ n < 10} -- type comprehension notation, can do other declaritive sets
#check c_set

example : 1 ∈ a_set := by
  show a_set 1 --optional, rewrite goal with any equivalent
  unfold a_set --optional
  show 1=1 ∨ 1=2 ∨ 1=3 --optional, dumb but valid expansion
  exact Or.inl rfl --exact means that the following term is exactly (equivalent) to the current goal


example : 3 ∈ a_set ∩ b_set := by --set intersection proof now
  show 3 ∈ a_set ∧ 3 ∈ b_set -- optional, rewrite without intersection
  exact ⟨Or.inr (Or.inr rfl),Or.inl rfl⟩

example : 2 ∈ a_set ∪ b_set := by
  show (2 ∈ a_set) ∨ (2 ∈ b_set)
  exact Or.inl (Or.inr (Or.inl rfl))

example : 2 ∈ a_set \ b_set := by
  exact ⟨Or.inr (Or.inl rfl), nomatch 2 ⟩

example : 3 ∉ a_set \ b_set := by _


--lean defs for properties we've mentioned
#check(@Reflexive)
#check(@Symmetric)
#check(@Transitive)
#check(@Equivalence)

lemma eq_is_refl : Reflexive (@Eq Nat):=
by
  unfold Reflexive
  intros x
  rfl

lemma eq_is_symm : Symmetric (@Eq Nat):=
by
  unfold Symmetric
  intros x y --intros and intro are functionally identical for us
  intro hxy
  rw [hxy]

lemma eq_is_trans : Transitive (@Eq Nat):=
by
  unfold Transitive
  intros x y z
  intros hxy hyz
  rw [hxy]
  rw [hyz]

theorem eq_N_is_equiv : Equivalence (@Eq Nat) :=
  Equivalence.mk @eq_is_refl @eq_is_symm @eq_is_trans


--Congruence mod n is equivalent example
def cong_mod_n : Nat → Nat → Nat → Prop := λ n a b => a%n = b%n

theorem cong_mod_n_equiv: ∀ n, Equivalence (cong_mod_n n) := by
  intros n
  exact Equivalence.mk _ _ _

lemma cong_mod_n_refl : ∀ (n:Nat), Reflexive (cong_mod_n n):= by
  intros n
  unfold cong_mod_n
  unfold Reflexive
  intros a
  exact rfl


lemma cong_mod_n_symm : ∀ (n:Nat), Symmetric (cong_mod_n n):= by
  intros n a b h
  unfold cong_mod_n
  unfold cong_mod_n at h
  rw [h]

lemma cong_mod_n_trans : ∀ (n:Nat), Transitive (cong_mod_n n):= by
  intros n a b c h1 h2
  unfold cong_mod_n
  unfold cong_mod_n at h1
  unfold cong_mod_n at h2
  rw [h1, h2] --combining rw is ok

theorem cong_mod_n_equiv': ∀ n, Equivalence (cong_mod_n n) := by
  intros n
  exact Equivalence.mk (@cong_mod_n_refl n) (@cong_mod_n_symm n) (@cong_mod_n_trans n)

theorem cong_mod_n_equiv'': ∀ n, Equivalence (cong_mod_n n) := by
  intro n
  unfold cong_mod_n
  exact Equivalence.mk
    (by intro x; rfl)
    (by intro x y h; rw[h])
    (by intros x y z hxy hyz; rw [hxy, hyz])
