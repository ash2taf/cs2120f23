import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.AddTorsor

inductive Person

inductive Loves : Person → Person → Prop

def els : Prop :=  ∀ (p:Person), ∃ (q:Person), Loves p q

def sel : Prop := ∃ (q:Person), ∀ (p:Person), Loves p q

  --alternate:
example:
∀ (Person : Type)
  (Loves: Person → Person → Prop),
  (∃ (q : Person), ∀ (p:Person), Loves p q) →
  (∀ (p:Person), ∃ (q:Person), Loves p q) :=
λ _ _ sel k => match sel with--need to break down sel now, destructure
| ⟨joe, elovesj⟩ => ⟨ joe, elovesj k⟩

/-!
example:
∀ (Person : Type)
  (Loves: Person → Person → Prop),
  (∃ (q : Person), ∀ (p:Person), Loves p q) →
  (∀ (p:Person), ∃ (q:Person), Loves p q) :=
by
  intros _ _ sel lvr
  cases sel
-/

/-!
Lean Global assumptions: variable
-/
variable
  (Ball : Type)
  (Heavy : Ball → Prop)
  (Red: Ball → Prop)

example: (∃ (b:Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨rhb, rhb_proof⟩ => ⟨rhb, rhb_proof.left⟩

example: (∃ (b:Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b ∨ Heavy b) :=
λ h => match h with
| ⟨rhb, rhb_proof⟩ => ⟨rhb, Or.inr rhb_proof.right⟩ --prove the exists with a witness and a proof, just like you use them

example: ¬ (∀ (b:Ball), Red b) → (b:Ball) → ∃ (b:Ball), ¬(Red b) :=
λ nabr aball => ⟨ aball, λ rb => _  ⟩

example: (∃ (b:Ball), ¬(Red b)) → (¬ (∀ (b:Ball), Red b))  :=
λ ebnr=> match ebnr with
| ⟨nrb, nrb_nr⟩ => λ abr =>
  let rb := (abr nrb) -- create new intermediate variable with 'let'
  --nomatch nrb_nr rb --nomatch is the same as false.elim
  by contradiction --mixing terms and tactics works! contradition automates false elimination/nomatch
