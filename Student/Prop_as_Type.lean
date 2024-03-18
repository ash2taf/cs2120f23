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

--Not
--into: prove ¬P by showing P → False
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

-- Implication (P → Q)
-- intro: show that you can derive a proof of Q from a proof of P
-- elim: apply function to proof of P to get a proof of Q

--intro example
def notK' : K → False := λ k => nomatch k

--Quantifiers
