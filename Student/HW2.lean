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

def mult : Nat → Nat → Nat
| _, Nat.zero => 0
| n, Nat.succ (m') => add n (mult n m')
--n, (m'+1) also workes, don't need Nat.succ

#eval mult 4 5
#eval mult 1 27

def exp : Nat → Nat → Nat
| _, Nat.zero => 1
| n, Nat.succ (m') => mult n (exp n m')

#eval exp 2 5
#eval exp 1 53
#eval exp 34 0

/-! Basic Data types intro
Type with only one value? Void, ie public static void
why? as a placeholder, to differentiate from a failure
can still edit other things, side effects
return values is functional, updating databases or controlling things irl are side effects, not functional
Type with no Values? Null/Empty
-/

#check (@Empty)
#check (Unit)
#check (@Prod)
#check (@Sum)

--defining a data type
#check Bool
/-!
inductive Bool : Type where
  /-- The boolean value `false`, not to be confused with the proposition `False`. -/
  | false : Bool
  /-- The boolean value `true`, not to be confused with the proposition `True`. -/
  | true : Bool
-/
inductive myEmp : Type

/-!
works even with empty, assumes that an arg is given
however, can't be sued because you would need to pass it an empty arg
-/
def e2e : Empty → Empty
|e => e

--Can't do _ to empty, need the intro to be empty to have an empty to return