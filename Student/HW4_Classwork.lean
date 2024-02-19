structure monoid (α : Type) where
(op: α → α → α)
(id: α)

def foldr {α : Type} : monoid α → List α → α
|m, [] => m.id
|m, h::t => m.op h (foldr m t)

--packaging args into data structure
#eval foldr (monoid.mk Nat.add 0) [1,5,7,8]
#eval foldr (monoid.mk Nat.mul 1) [1,1,3,5,1]
#eval foldr (monoid.mk String.append "") ["Hello ", "how", " are ", "you?"]

--using foldr to create functions
--generalized functions take 0+ args instead of exactly 2 from normal binary ops
def gen_add := foldr (monoid.mk Nat.add 0) --version of add that takes any number of inputs based on binary op
#eval gen_add [1,5,7,8]
#check gen_add


/-! There are a huge number of possible qualified Monoids in the world, we cover some simple ones here
Intro to including proofs in our definitions, propositions (as types) and proofs (as values of those types)
-/
structure my_monoid (α : Type) where
(op: α → α → α)
(id: α)
(left_id: ∀ a, op id a = a)
(right_id: ∀ a, op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)

def my_foldr {α : Type} : my_monoid α → List α → α
|m, [] => m.id
|m, h::t => m.op h (my_foldr m t)

def nat_add_monoid: my_monoid Nat :=
my_monoid.mk Nat.add 0 sorry sorry sorry

#eval my_foldr nat_add_monoid [1,2,3,4,5]

--Lean notation for constructors:
def nat_add_monoid' : my_monoid Nat :=
⟨
  Nat.add,
  0, --wrong val breaks proofs
λ a => by simp (Nat.add), --this proof is in the definition of addition
λ a => by simp (Nat.add), --nat.add is so common that it is tried by default, so it's optional (but good practice)
Nat.add_assoc --there is a pre-existing proof, but it doesn't quite match our definition
  ⟩

def nat_mul_monoid : my_monoid Nat :=
⟨
  Nat.mul,
  1,
λ a => by simp,
λ a => by simp,
sorry --Nat.mul_assoc exists, but doesn't match our definition of my_monoid
  ⟩

def nary_mul : List Nat → Nat := my_foldr (my_monoid.mk Nat.mul 1 λ a => by simp λ a => by simp λ a => sorry)
#eval nary_mul [1,2,3,4,5]

--new object: functr
--convert list of one type of object to another type
--similar to map function?
#check Option --either has nothing, or one value of the given type

def pred : Nat → Option Nat
| Nat.zero => Option.none
| Nat.succ a => a --don't need to do option.some, assumed

#reduce pred 3
#reduce pred 0

def list_map {α β : Type} : (α → β) → List α → List β
|_, List.nil => List.nil
|f, h::t => (f h)::(list_map f t)

-- Takes a function and an Option input, and either provides none if the input is none or the function applied to the value otherwise
def option_map {α β : Type} : (α → β) → Option α → Option β
|_, Option.none => Option.none
|f, Option.some n => Option.some (f n)

--
inductive Tree (α : Type) : Type
|empty
|node : α → Tree α → Tree α → Tree α
--|node (a : α) (l r :Tree α) : Tree α --this also works, names the inputs

def tree_map {α β :Type} : (α → β) → Tree α → Tree β
|_, Tree.empty => Tree.empty
|f, Tree.node v l r => Tree.node (f v) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

def a_tree :=
  Tree.node
  1
  (Tree.node 2 Tree.empty Tree.empty)
  (Tree.node 3 Tree.empty Tree.empty)

#reduce tree_map Nat.succ a_tree

/-! Now we have 3 similar datastructures and similar map functions, but they aren't quite the same
parametricity doesn hold as structures are too different, so can't do standard polymorphism approach
in languages like Java, use supertypes and adh-hoc polymorphism instead (different implementation for each type supported)
-/
#check List --List has type 'Type → Type', as do the others
#check Option
#check Tree


structure functor {α β :Type} (c: Type → Type) : Type where--(c α) → (c β)
map (f: α → β) (ic : c α) : c β

--key idea, takes a container type and a mapping function in order to be polymorphic
def list_functr {α β :Type}: @functor α β List:= functor.mk list_map
def opt_functr {α β :Type}: @functor α β Option := functor.mk option_map

#check @list_functr
--really polymorphic, takes a function α → β, converts via a functr container type
def convert {α β :Type} (c: Type → Type) (m: @functor α β c): (f: α → β) → c α → c β
| f, c  =>  m.map f c

#reduce convert List list_functr Nat.succ [1,2,3,4,5]
#reduce convert Option opt_functr Nat.succ (Option.some 3)

--can't do this because no map funciton or functr
inductive box (α : Type)
|contents (a : α)



--first version doesn't constrain map at all though, want some guarantees
structure functor' {α β :Type} (c: Type → Type) (f: α → β) : Type where--(c α) → (c β)
map (f: α → β) (ic : c α) : c β
