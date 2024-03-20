/-!
Propositions as types, proofs as values
-/
inductive BobStudiesatUVA
| attendsClasses
| paidTuition

inductive MaryStudiesatUVA
| attendsClasses
| paidTuition

inductive JimStudiesatUVA --no proofs because not true

def neg (α : Type) := α → Empty

example : neg JimStudiesatUVA :=
λ j : JimStudiesatUVA => nomatch j --no cases to consider, so case analysis autocompletes (no matches)

inductive BobandMaryStudyatUVA
| and (b : BobStudiesatUVA) (m : MaryStudiesatUVA)


def b : BobStudiesatUVA := BobStudiesatUVA.paidTuition

def m : MaryStudiesatUVA := MaryStudiesatUVA.attendsClasses
example : BobandMaryStudyatUVA := BobandMaryStudyatUVA.and b m

inductive BoborMaryStudyatUVA
| l (b : BobStudiesatUVA)
| r (m : MaryStudiesatUVA)

example : BoborMaryStudyatUVA := BoborMaryStudyatUVA.l b

--And, Or and Not as types, isomorphic to lots

inductive MyAnd (α β :Type)
|mk (a:α) (b:β)

inductive MyOr (α β : Type)
| inr (a : α)
| inl (b : β)

def MyNot (α : Type) := α → Empty


--Lean and uses ×, '\x', Product
example : BobStudiesatUVA × MaryStudiesatUVA := (b, m)

example : BobStudiesatUVA × MaryStudiesatUVA → BobStudiesatUVA := λ p => p.fst --first element of the prod
example : BobStudiesatUVA × MaryStudiesatUVA → MaryStudiesatUVA := λ p => p.2

--Lean uses Sum for or, uses ⊕  '\o+'
example : Sum BobStudiesatUVA MaryStudiesatUVA := Sum.inl b
example : BobStudiesatUVA  ⊕ JimStudiesatUVA := Sum.inr sorry --no proof of jim, would work with inl and b

--Proof of disjunction
example : BobStudiesatUVA ⊕ JimStudiesatUVA → BobStudiesatUVA
| Sum.inl l => l
| Sum.inr r => nomatch r

--proof of negation
example : neg JimStudiesatUVA := λ p : JimStudiesatUVA => nomatch p

example : neg (MaryStudiesatUVA × JimStudiesatUVA) := λ p : (MaryStudiesatUVA × JimStudiesatUVA) => nomatch p.2

/-!
Proof Irrelevance
new versions of prod and sum for props, PProd and presumably PSum
also MProd where α and β must come from the same universe
Lean And takes 2 props, no more of this computational type nonsense

need new props for new toys
-/

inductive B : Prop
| paid
| attend

inductive M : Prop
| paid
| attend

inductive K : Prop

example : B ∧ M := And.intro B.paid M.attend
example :  And B M := ⟨ B.paid, M.attend ⟩
def b_m_true : B ∧ M := And.intro B.paid M.attend
theorem b_m_true' : B ∧ M := And.intro B.paid M.attend

--quick toy proof that order is irrelevant for AND
example (P Q : Prop) : P ∧ Q → Q ∧ P := λ (a : P ∧ Q)  => And.intro a.right  a.left
example (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨p, q⟩ => And.intro q p

--quick toy proof that AND implies OR
example (P Q : Prop) : P ∧ Q → P ∨ Q := λ (a : P ∧ Q)  => Or.inl a.left

--back to more general AND syntax
example : B ∧ M → M := λ p => p.right
example : B ∧ M → B := λ p => p.1

example : B ∧ ¬K := And.intro B.paid (λ k => nomatch k)
example : B ∧ Not K := ⟨B.attend, λ k => nomatch k⟩

example : B ∨ K := Or.inl B.attend
example : B ∨ K → B :=
λ bk => match bk with
| Or.inl b => b
| Or.inr k => nomatch k

example : ∀ (P Q R : Prop),
(P ∨ Q) →
(P → R) →
(Q → R) → R :=
λ _ _ _ porq pr qr => match porq with
| Or.inl p => pr p
| Or.inr q => qr q

--quick toy proof that OR is commutative (order flippable)
example (P Q : Prop) : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q

--Not
--into: prove ¬P by showing P → False (assume p, show contradiction (p implies false))
  -- aka proof by negation, NOT proof by contradiction (similar, but not same)
  --contradiction says prove p by assumeing ¬p, show ¬¬p, but only in classical logic/under EM
-- elim: as with any function, elim by apply
def notK : ¬K := λ k => nomatch k

--elim example (theorem/law of no contradiction - can't have P and ¬P)
example (P : Prop): ¬P → P → False :=
λ np p => np p

/-!
example (P : Prop) : ¬¬P → P
|nnp => _ --no place to get a proof of p
-/

--but you can do it if all props are either true or false
--this is the law of the excluded middle, that always P or ¬P for every proposition
example (P : Prop) : (P ∨ ¬P) → (¬¬P → P) :=
λ pornp => match pornp with
  | Or.inl p => λ _ => p --technically can skip the lambda here?
  | Or.inr np => λ nnp => nomatch (nnp np)

--EM axiom:
-- ∀(P : Prop), P ∨ ¬P
--can't do proof by contradiction in lean because you don't have this

--lean classical logic space
#check Classical.em
--redo of negation elimination proof with Classical.em as the version of EM
example (P : Prop) : ¬¬P → P :=
match Classical.em P with
| Or.inl p => λ _ => p
| Or.inr np => λ _ => by contradiction --lean tactic language, more powerful than the direct stuff we've been doing
--basically just telling lean to try to find the ingredients to do something, in this case find proofs of P and ¬P


-- Implication (P → Q)
-- intro: show that you can derive a proof of Q from a proof of P
-- elim: apply function to proof of P to get a proof of Q

--intro example
def notK' : K → False := λ k => nomatch k


#check Lean.Parser.Tactic.contradiction
--elimination rule for equality, using lean rewrite tactic
def one_not_eq_zero' (n:Nat): n = 1 → n ≠ 0 :=
λ (neq1 : n=1) => λ neq0 => by
rw [neq1] at neq0 --rewrite neq0 with neq1
cases neq0 --check cases, there are none so we finished

--Lean Equality
#check 1=0
--#check Eq.refl 1 0 --eq.refl only takes on input, so confused
#check Eq 1 0 --this works, Eq takes 2 inputs
#check Eq.refl 1 -- this works, only the one input now

example : 1=1 := Eq.refl 1

--Quantifiers
-- Intro to forall: pick arbitrary member of given set, show the arbitrary member fulfill conditions
-- Use function to show that it works, need general P → Q func
-- ∀ P, Q := λ p : P => _ => q --not correct formatting, just explanation
-- once you have, can apply to any member of p to show that Q (elimination, universal specialization rule)

--intro to exists: show an example/witness (exists a number even and prime: 2)
-- or, pick a specific object and show that it meets the required properties (2 is even, 2 is prime)
-- CANT get back the example that you used however
