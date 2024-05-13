/- Types and type-checking of the document language -/

import «LayoutTypes».Expr

inductive Ty where
  | string
  | number
  | inline
  | block
  | document
deriving DecidableEq

structure Tcx

def Tcx.check (Γ : Tcx) (e : Expr) : Option Ty :=
  match e with
  | .string _ => some .string
  | .number _ => some .number
  | .text _ => some .inline
  | .bold inls => do
    let tys ← inls.attach.mapM (Γ.check ·.val)
    if tys.all (· = .inline) then some .inline
    else none
  | .para inls fontSize lineHeight => do
    let inlTys ← inls.attach.mapM (Γ.check ·.val)
    let fontSizeTy ← Γ.check fontSize
    let lineHeightTy ← Γ.check lineHeight
    if inlTys.all (· = .inline) ∧
      fontSizeTy = .number ∧
      lineHeightTy = .number then
      some .block
    else none
  | .document bs => do
    let bTys ← bs.attach.mapM (Γ.check ·.val)
    if bTys.all (· = .block) then some .document
    else none
decreasing_by
  try any_goals { simp_wf; decreasing_trivial }
  try any_goals { rename _ => x; have := x.property; simp_wf; decreasing_trivial }
  simp_wf
