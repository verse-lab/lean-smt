import Smt

namespace SharedSort

-- The two child types are identical at every level. Traversing them independently
-- exhausts the heartbeat budget while preparing the uninterpreted sort.
def Tree : Nat → Type
  | 0 => Bool
  | n + 1 => Tree n × Tree n

def Root := Tree 21

set_option maxHeartbeats 10000 in
example (p q : Root → Prop) (x : Root) (h : ∀ y, p y → q y) (hx : p x) : q x := by
  smt [h, hx]

-- A result for Box Unit must not be reused for Box (Fin 0).
private structure Box (α : Type) where value : α
private structure Mixed where
  left : Box Unit
  right : Box (Fin 0)
private def Wrapped := Mixed

example : True := by
  fail_if_success have : ∃ x : Wrapped, x = x := by smt -embeddings +trust
  trivial

end SharedSort
