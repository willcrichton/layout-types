import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Basic

def List.fins {α} (l : List α) : List (Fin l.length) :=
  let ns := List.range l.length
  ns.attach.map (λ (i : {n // n ∈ ns}) =>
    ⟨i, List.mem_range.mp i.prop⟩)

def List.acc_sum {α} [Zero α] [Add α] (l : List α) : List α :=
  l.fins.map (λ (i : Fin l.length) => (l.take i).sum)

def Prod.nth {α} (p : α × α) (n : Fin 2) : α :=
  if n = 0 then p.fst
  else p.snd

def Prod.nth_vec {α} [Zero α] (p : α × α) (dim : Fin 2) : α × α :=
  if dim = 0 then ⟨p.fst, 0⟩
  else ⟨0, p.snd⟩