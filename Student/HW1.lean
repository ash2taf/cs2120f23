/-!Old version with nested functions-/
def apply4' {α : Type}: (α → α) → α → α 
| f => fun a => f (f (f (f (a))))

/-!New version with composition (backslash o)-/
def apply4 {α : Type}: (α → α) → α → α 
| f => fun a => (f ∘ f ∘ f ∘ f) a