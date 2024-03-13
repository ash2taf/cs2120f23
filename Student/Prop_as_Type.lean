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
