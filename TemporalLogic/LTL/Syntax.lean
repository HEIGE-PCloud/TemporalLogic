module

public import Lean

namespace LTL.Syntax
abbrev AP := String

inductive Formula where
  | t : Formula
  | ap : AP → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | x : Formula → Formula
  | u : Formula → Formula → Formula
deriving BEq, DecidableEq

def Formula.toString : Formula → String
  | t => "⊤"
  | not t => "⊥"
  | ap a => s!"({a})"
  | and e1@(not (and f1 (not f2))) e2@(not (and f3 (not f4))) =>
      if f1 == f4 && f2 == f3 then
        s!"({f1.toString} ↔ {f2.toString})"
      else
        s!"({e1.toString} ∧ ({e2.toString})"
  | not (and (not f1) (not f2)) => s!"({f1.toString} ∨ {f2.toString})"
  | not (and f1 (not f2)) => s!"({f1.toString} → {f2.toString})"
  | u t f => s!"(F {f.toString})"
  | not (u t (not f)) => s!"(G {f.toString})"
  | not f => s!"(¬{f.toString})"
  | and f1 f2 => s!"({f1.toString} ∧ {f2.toString})"
  | x f => s!"(X {f.toString})"
  | u f1 f2 => s!"({f1.toString} U {f2.toString})"

instance : ToString Formula where
  toString := Formula.toString


namespace Meta

open Lean Lean.Elab Lean.Meta

declare_syntax_cat LTLFormula

syntax ident : LTLFormula
syntax str : LTLFormula
syntax "true" : LTLFormula
syntax "⊤" : LTLFormula
syntax "¬" LTLFormula : LTLFormula
syntax LTLFormula "∧" LTLFormula : LTLFormula
syntax "X" LTLFormula : LTLFormula
syntax LTLFormula "U" LTLFormula : LTLFormula
syntax "(" LTLFormula ")" : LTLFormula
macro "false" : LTLFormula => `(LTLFormula| ¬ true)
macro "⊥" : LTLFormula => `(LTLFormula| ¬ true)
macro l:LTLFormula "∨" r:LTLFormula : LTLFormula =>
  `(LTLFormula| ¬(¬($l) ∧ ¬($r)))
macro l:LTLFormula "→" r:LTLFormula : LTLFormula =>
  `(LTLFormula| ¬(($l) ∧ (¬($r))))
macro l:LTLFormula "↔" r:LTLFormula : LTLFormula =>
  `(LTLFormula| (($l) → ($r)) ∧ (($r) → ($l)))
macro "F" f:LTLFormula : LTLFormula =>
  `(LTLFormula| (true U ($f)))
macro "G" f:LTLFormula : LTLFormula =>
  `(LTLFormula| ¬(true U ¬($f)))

meta partial def elabLTL : Syntax → TermElabM Lean.Expr
  | `(LTLFormula| $a:ident) => do
      let apName := a.getId.toString
      mkAppM ``Formula.ap #[mkStrLit apName]
  | `(LTLFormula| $s:str) => do
      let apName := s.getString
      mkAppM ``Formula.ap #[mkStrLit apName]
  | `(LTLFormula| true) | `(LTLFormula| ⊤) => mkAppM ``Formula.t #[]
  | `(LTLFormula| ¬$f) => do
      let fExpr ← elabLTL f
      mkAppM ``Formula.not #[fExpr]
  | `(LTLFormula| $f1 ∧ $f2) => do
      let f1Expr ← elabLTL f1
      let f2Expr ← elabLTL f2
      mkAppM ``Formula.and #[f1Expr, f2Expr]
  | `(LTLFormula| X $f) => do
      let fExpr ← elabLTL f
      mkAppM ``Formula.x #[fExpr]
  | `(LTLFormula| $f1 U $f2) => do
      let f1Expr ← elabLTL f1
      let f2Expr ← elabLTL f2
      mkAppM ``Formula.u #[f1Expr, f2Expr]
  | `(LTLFormula| ($f)) => elabLTL f
  | stx => do
      match (← liftMacroM <| Macro.expandMacro? stx) with
      | some expanded => elabLTL expanded
      | none => throwUnsupportedSyntax

elab "[LTL|" f:LTLFormula "]" : term => elabLTL f

section
def example1 := [LTL| X ("x = 1")]
def example2 := [LTL| "x < 2" ∨ G("x = 1")]
def example3 := [LTL| X("x = 1" ∨ G X "x ≥ 3")]
def example4 := [LTL| X(true U "x = 1") → G("x = 1")]
def example5 := [LTL| false]
def example6 := [LTL| true ↔ false]

#eval example6
end
end Meta

end LTL.Syntax
