/-!
We've seen that we can generalize the notion of
mapping objects of one container-like type to
objects of a correspond value of the same type
by replacing each *element* in one container
corresponding objects computed by applying an
element-wise conversion function to each object
in the input container. Here we give two examples
that we saw in class: functions for mapping over
Lists, and functions for mapping over Options.
-/

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-!
We now present two more "container-like" types that
we saw in class. The Box type is a container type for
exactly one object some type, α, and Tree is such a
type for representing binary trees of such objects.
-/
inductive Box (α : Type)
| contents (a : α)

inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

/-! Problem #1
Define box_map and tree_map functions and
use #eval to give examples of applying these
functions to a few arguments.
-/

def box_map {α β : Type} : (α → β) → Box α → Box β
|f, Box.contents a => Box.contents (f a)

def box_a := Box.contents "interesting"
#reduce box_map String.length box_a
#reduce box_map Nat.succ (Box.contents 23)

--Tree_map from class Wed, with example
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

/-! Can't do eval because lean doesn't eval on our custom data types, #reduce instead
ie, '#eval tree_map Nat.succ a_tree' gives an error
-/

--Note from class: using Reduce is fine, eval doesn't work because don't know how to print custom things

/-!
The functor type, below, generalizes the idea
that we can map over *any* polymorphic container
type. The functor type takes a polymorphic type
(builder), such as List or Option, and augments
it with a map function for objects of that type.
Here we don't try to specify rules for functors.
We'll see them shortly. For now the definition
follows has everything we need.
-/

structure functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β
--important: the c term is a polymorhpic container type, ie List, Tree, etc
--containers are not types without their polymorphic type, ie List Nat but not List

--new functor that is a class:

class functor' (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-!
Here are functor *instances* for the polymorphic
container-like List and Option types.
-/

def list_functor : functor List  := functor.mk list_map
def option_functor : functor Option  := functor.mk option_map

--new functor' versions (class)
def list_functor' : functor' List  := functor'.mk list_map
def option_functor' : functor' Option  := functor'.mk option_map

/-! Problem #2

Complete the definition of a polymorphic do_map
function. Note that this function, map, is not
the same as the functor field value, functor.map.
Hint: See the "convert" function from class.
-/

def do_map {α β : Type} {c : Type → Type} (m : functor c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

--new version with functor' class from class
def do_map' {α β : Type} {c : Type → Type} (m : functor' c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

-- These test cases should succeed when do_map is right
#eval do_map list_functor Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map option_functor (λ s => s ++ "!") (some "Hi")

#eval do_map' list_functor' Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map' option_functor' (λ s => s ++ "!") (some "Hi")


/-! Problem #3

Briefly explain why you can't apply map to a value of type
(Tree Nat) at this point.

Here: We haven't created functor instances for Tree or Box yet
-/



/-! Problem #4

Define functor instances for Box and Tree.
-/

def tree_functor : functor Tree  := functor.mk tree_map
def box_functor : functor Box  := functor.mk box_map

--functor' class versions
def tree_functor' : functor' Tree  := functor'.mk tree_map
def box_functor' : functor' Box  := functor'.mk box_map

/-! Problem #5

Give working examples, using #eval, of applying do_map
to a Box Nat and Tree String values.
-/

#reduce do_map box_functor Nat.succ (Box.contents 5)
#reduce do_map box_functor String.length (Box.contents "hooray")
#reduce do_map tree_functor Nat.succ (Tree.node 1 (Tree.node 0 Tree.empty Tree.empty) (Tree.node 2 Tree.empty Tree.empty))
#reduce do_map tree_functor String.length (Tree.node "Be" (Tree.node "to" Tree.empty Tree.empty) (Tree.node "not" Tree.empty Tree.empty))

/-!
Here's an infix notation for do_map and a few examples
of its use.
Note: $ is the standard version for Haskell and OCaml, which is why it's the default
-/

infix:50 "<$>"  => do_map
#eval Nat.succ <$> [1,2,3]
#eval (λ s => s ++ "!") <$> ["Hi", "Yo"]

/-!
this is where things broke on the homework, need to change the do_map
infix can't handle the 3 args needed in the original
a do_map that has a functor instance that lean can find removes one of the inputs needed
square brackets tell lean to go find the instance
this version has 4 implicit parameters and 2 explicit
the implicit arg m term imposes a constraint on c: must be a container type which has a defined functor'
-/

def do_map'' {α β : Type} {c : Type → Type} [m : functor' c] :
  (f : α → β) → c α → c β
| f, c => m.map f c

/-!
Also need to create appropriate instances so it can be found
can only do this because functor is a class, not a simple structure
these typeclass instances add metadata/structures around the type given
here we're associating the map instances with the base container types
-/
instance : functor' List := ⟨list_map⟩
instance : functor' Option := ⟨option_map⟩
instance : functor' Box := ⟨box_map⟩
instance : functor' Tree := ⟨tree_map⟩

#reduce do_map'' Nat.succ [1,2,3]
#reduce do_map'' Nat.succ (Option.some 3)
#reduce do_map'' Nat.succ (Box.contents 23)
#reduce do_map'' Nat.succ a_tree

-- so now we have a working 2 input version of do_map, so long as there are instances on the functor'

infix:50 "<%>"  => do_map''
#eval Nat.succ <%> [1,2,3]
#eval (λ s => s ++ "!") <%> ["Hi", "Yo"]
#reduce Nat.succ <%> (Box.contents 3)
#reduce Nat.succ <%> a_tree

/-!
Lean has a Functor version, capitalized, and has a bunch of stuff predefined
we would get a clash if we tried using the $ version with an ambiguous error, switching the symbol avoided here

-/

/-! Problem #6

Rewrite your/our examples of mapping over List,
Option, Box, and Tree values using <$> notation.
-/
#reduce Nat.succ <$> [1,2,3] --verifying that reduce doesn't cause issues

/-! This is the old error tests from the HW, see proper version above with the <%> operator

--do_map takes 3 inputs and doesn't have a functor here, so is upset
--not sure why the list and option just work
--maybe difference between existing containter types vs custom?
--some way to intuit the functor and skip the extra input
#reduce box_map String.length box_a
#reduce String.length <$> box_a
#reduce box_map String.length <$> box_a
#reduce box_map <$> String.length box_a
#reduce (box_map String.length) <$> box_a

#reduce box_map Nat.succ (Box.contents 23)
#reduce Nat.succ <$> (Box.contents 23) --similar problem, wants a functor input but can't synthesize

#reduce tree_map Nat.succ a_tree
#reduce Nat.succ <$> a_tree --and again

--asked a freind in class, they had similar problems but got this format:
#reduce (box_map <$> String.length) box_a --which still doesn't fly for me


-/
--my list and option examples from last class work fine
#reduce list_map Nat.succ [1,2,3,4,5]
#reduce Nat.succ <$> [1,2,3,4,5]
#reduce option_map Nat.succ (Option.some 3)
#reduce Nat.succ <$> (Option.some 3)
