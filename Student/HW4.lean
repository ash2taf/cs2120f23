/-!
Your homework, due before class on Wednesday, is to complete the definition of the general foldr function,
with the reduction of lists of strings to Boolean values as a test case,
true if every string in a list is of even length, and false otherwise.
Your foldr function must be completely general and not test-case specific,
however the function that we are calling "combine" will be application/test-case specific.
To do the homework, complete the following definitions by replacing the underscores with your own code.
-/

def isEvenLen : String → Bool := λ s => s.length % 2 == 0
def combine : String → Bool → Bool
| a,b => isEvenLen a && b
def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => foldr op (op h id) t


#eval foldr combine true ["oh", "no", "fails"]
#eval foldr combine true ["hooray", "this", "doesnt"]
