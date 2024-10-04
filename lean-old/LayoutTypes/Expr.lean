/- Expressions in the document language -/

import Mathlib.Data.Rat.Init
import Batteries.Data.List.Init.Attach
import «LayoutTypes».Document

inductive Expr where
  | string (s : String)
  | number (n : ℚ)
  | text (s : String)
  | bold (inls: List Expr)
  | para (inls : List Expr) (fontSize : Expr) (lineHeight : Expr)
  | document (bs : List Expr)

def eval (e : Expr) : Option Expr :=
  match e with
  | .string s => some (.string s)
  | .number n => some (.number n)
  | .text s => some (.text s)
  | .bold is => do
    let is ← is.attach.mapM (eval ·.val)
    pure (.bold is)
  | .para is fontSize lineHeight => do
    let is ← is.attach.mapM (eval ·.val)
    let fontSize ← eval fontSize
    let lineHeight ← eval lineHeight
    pure (.para is fontSize lineHeight)
  | .document bs => do
    let is ← bs.attach.mapM (eval ·.val)
    pure (.document is)
decreasing_by
  try any_goals { simp_wf; decreasing_trivial }
  try any_goals { rename _ => x; have := x.property; simp_wf; decreasing_trivial }
  simp_wf

notation "〚" e "〛" => eval e

def Expr.toString (e : Expr) : Option String :=
  match e with
  | Expr.string s => some s
  | _ => none

def Expr.toNumber (e : Expr) : Option ℚ :=
  match e with
  | .number n => some n
  | _ => none

def Expr.toInline (e : Expr) : Option Inline :=
  match e with
  | .text s => some (.text s)
  | .bold is => do
    let is ← is.attach.mapM (·.val.toInline)
    pure (.bold is)
  | _ => none
decreasing_by
  all_goals { rename _ => x; have := x.property; simp_wf; decreasing_trivial }

def Expr.toBlock (e : Expr) : Option Block :=
  match e with
  | .para is fontSize lineHeight => do
    let is ← is.attach.mapM (·.val.toInline)
    let fontSize ← fontSize.toNumber
    let lineHeight ← lineHeight.toNumber
    if h : 0 ≤ fontSize ∧ 0 ≤ lineHeight then
      pure (.para (Para.mk is ⟨fontSize, h.left⟩ ⟨lineHeight, h.right⟩))
    else none
  | _ => none

def Expr.toDocument (e : Expr) : Option Document :=
  match e with
  | .document bs => do
    let bs ← bs.attach.mapM (·.val.toBlock)
    pure (Document.mk bs)
  | _ => none
