/-!
new version of functor that is a class
-/


class functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β


#check Functor

/-!
--if object has a field with type n, overall structure has type n+1 (universe levels)
universe u
structure Box {α :Type u} (a : α)

def box_map {α β : Type u}  : (α → β) → Box α → Box β
|f, (Box.mk a) => Box.mk (f a)
-/
inductive Box (α : Type)
| contents (a : α)

def box_map {α β : Type} : (α → β) → Box α → Box β
|f, Box.contents a => Box.contents (f a)

def box_mapC : {α β :Type u} → α → f β --to be continued, will fill second arg

instance : Functor Box := ⟨ box_map, _ ⟩

#reduce Nat.succ <$> Box.contents 2
