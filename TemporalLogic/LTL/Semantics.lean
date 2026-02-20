module

public meta import TemporalLogic.LTL.Syntax
public import TemporalLogic.LTL.Syntax

namespace TemporalLogic.LTL.Semantics
open Syntax

public abbrev State := Nat

public structure TS where
  St : List State
  V : AP → List State
  t : State → State

public inductive Stream (α : Type u) where
  | nil : Stream α
  | cons (head : α) (tail : Thunk (Stream α)) : Stream α

public def Stream.isNil : Stream α → Bool
  | .nil => True
  | _ => False

public def Stream.head? : Stream α → Option α
  | .nil => .none
  | .cons head _ => .some head

public def Stream.tail? : Stream α → Option (Stream α)
  | .nil => .none
  | .cons _ tail => .some tail.get

public def Stream.drop? : Nat → Stream α → Option (Stream α)
  | 0, s => .some s
  | n + 1, s => match s.tail? with
    | .none => .none
    | .some tail => tail.drop? n

public abbrev Path := Stream Nat

public def entails (ts : TS) (path : Path) : Formula → Prop
  | .t => True
  | .ap p =>
      match path.head? with
      | .none => False
      | .some x => (ts.V p).contains x = true
  | .not φ => ¬(entails ts path φ)
  | .and φ ψ => entails ts path φ ∧ entails ts path ψ
  | .x φ =>
      match path.tail? with
      | .none => False
      | .some tail => entails ts tail φ
  | .u φ ψ =>
      ∃ (i : Nat) (path_i : Path),
        path.drop? i = some path_i ∧ entails ts path_i ψ ∧
        ∀ (j : Nat), j < i → ∃ (path_j : Path), path.drop? j = some path_j ∧ entails ts path_j φ

notation "(" ts "," path ")" "⊧" f => entails ts path f


open Meta in
theorem entailsF (M : TS) (p : Path) (φ : Formula) :
  ((M, p) ⊧ ([LTL| F φ])) ↔
  ∃ (i : Nat) (path_j : Path),
    p.drop? i = some path_j ∧
    ((M, path_j) ⊧ [LTL| φ])
  := by
  sorry
open Meta in
def xx (f : Formula) := [LTL| F φ]
end TemporalLogic.LTL.Semantics
