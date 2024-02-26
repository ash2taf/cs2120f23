import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs

inductive Orient where
  | O0
  | O120
  | O240

inductive Rotate where
  | R0
  | R120
  | R240




def act : Rotate → Orient → Orient := _

open Orient Rotate

def rAdd : Rotate → Rotate → Rotate
| Rotate.R0, a => a
| a, Rotate.R0 => a
| Rotate.R120, Rotate.R120 => Rotate.R240
| Rotate.R120, Rotate.R240 => Rotate.R0
| Rotate.R240, Rotate.R120 => Rotate.R0
| Rotate.R240, Rotate.R240 => Rotate.R120

/-!
first arg minus second arg
(operation to get first arg if starting at second arg state)
-/
def oSub : Orient → Orient → Rotate
| O0, O0 => R0
| O0, O120 => R240
| O0, O240 => R120
|O120, O120 => R0
| O120, O0 => R120
| O120, O240 => R240
| O240, O240 => R0
| O240, O120 => R120
| O240, O0 => R240

/-!
Subracting orientations makes sense, but adding doesn't (clock analogy)
Adding rotatations makes sense though still

This is analgous to an Affine Space (vector stuff)
states as points, rotations as vectors
vectors act on points to transform them

Orientations/states not monoid, can't add or mult
Rotations might be a monoid, can add
-/

#check Monoid --go to lean website to learn more here
/-! Default Monoid in Lean is multiplicative, also has AddMonoid which we want
These are both SemiGroups, semigroups are like monoids but without the added requirement
-/
#check AddMonoid

instance : Add Rotate := ⟨rAdd⟩
#reduce R120 + R120 --this is overloaded, get extra functionalities like this once instance established

instance : AddSemigroup Rotate := {} --do this for HW, finish so monoid typeclass instance for rotations
--could you also get an inverse? yes, with our 3 angles options can get inverse and therefore go beyond monoid to group
--need additional inverse function for that though (r to r). this would be called a symmetry group (for equilateral triangles)




/-! My nonsense based on the textbook stuff-/
structure leanba where
  o : Orient

def rotL (l : leanba) : Rotate → leanba
| R0=> _
| R120 => _
| R240 => _
