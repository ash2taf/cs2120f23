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
example : BobStudiesatUVA  ⊕ JimStudiesatUVA := Sum.inr _ --no proof of jim, would work with inl and b

--Proof of disjunction
example : BobStudiesatUVA ⊕ JimStudiesatUVA → BobStudiesatUVA
| Sum.inl l => l
| Sum.inr r => nomatch r
