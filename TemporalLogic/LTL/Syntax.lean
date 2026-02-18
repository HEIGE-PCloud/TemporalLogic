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

def Formula.toString : Formula → String
  | t => "true"
  | not t => "false"
  | ap a => a
  | not (and (not f1) (not f2)) => s!"({f1.toString} ∨ {f2.toString})"
  | not (and f1 (not f2)) => s!"({f1.toString} → {f2.toString})"
  | u t f => s!"F {f.toString}"
  | not (u t (not f)) => s!"G {f.toString}"
  | not f => s!"¬{f.toString}"
  | and f1 f2 => s!"({f1.toString} ∧ {f2.toString})"
  | x f => s!"X {f.toString}"
  | u f1 f2 => s!"({f1.toString} U {f2.toString})"

instance : ToString Formula where
  toString := Formula.toString


namespace Meta

open Lean Lean.Elab Lean.Meta

declare_syntax_cat LTLFormula

syntax ident : LTLFormula
syntax str : LTLFormula
syntax "true" : LTLFormula
syntax "¬" LTLFormula : LTLFormula
syntax LTLFormula "∧" LTLFormula : LTLFormula
syntax "X" LTLFormula : LTLFormula
syntax LTLFormula "U" LTLFormula : LTLFormula
syntax "(" LTLFormula ")" : LTLFormula
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
  | `(LTLFormula| true) => mkAppM ``Formula.t #[]
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

example := [LTL| X ("x = 1")]
example := [LTL| "x < 2" ∨ G("x = 1")]
example := [LTL| X("x = 1" ∨ G X "x ≥ 3")]
example := [LTL| X(true U "x = 1") → G("x = 1")]
end Meta

end LTL.Syntax
