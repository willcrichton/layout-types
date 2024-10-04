/- Random utilities that aren't in the stdlib or mathlib. -/

import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.Group.Prod

notation "ℚ⁺" => NNRat

instance : Repr NNRat where
  reprPrec q := (inferInstance : Repr Rat).reprPrec q.val

@[simp] instance : HAdd ℚ ℚ⁺ ℚ where
  hAdd x y := x + y

def List.fins {α} (l : List α) : List (Fin l.length) :=
  let ns := List.range l.length
  ns.attach.map (λ (i : {n // n ∈ ns}) =>
    ⟨i, List.mem_range.mp i.prop⟩)

def List.accSum {α} [Zero α] [Add α] (l : List α) : List α :=
  l.fins.map (λ (i : Fin l.length) => (l.take i).sum)

def Fin.other (n : Fin 2) : Fin 2 :=
  if n = 0 then ⟨1, by trivial⟩
  else ⟨0, by trivial⟩

def Prod.nth {α} (p : α × α) (n : Fin 2) : α :=
  if n = 0 then p.fst
  else p.snd

def Prod.nthVec {α} [Zero α] (p : α × α) (dim : Fin 2) : α × α :=
  if dim = 0 then ⟨p.fst, 0⟩
  else ⟨0, p.snd⟩

def Rat.toVec (n : ℚ) (dim : Fin 2) : ℚ × ℚ :=
  if dim = 0 then ⟨n, 0⟩
  else ⟨0, n⟩

def Int.toFloat (n : ℤ) : Float :=
  match n with
  | ofNat n => n.toFloat
  | negSucc n => n.toFloat * -1

instance {α} [Repr α] : ToString α where
  toString a := (reprPrec a 0).pretty 60 2

def List.IsStrictSuffix {α} (l1 l2 : List α) := ∃ t ≠ [], t ++ l1 = l2

def List.recSuffix {α} {motive : List α → Sort _}
  (ind : ∀ l, (∀ l', l'.IsStrictSuffix l → motive l') → motive l)
  (l : List α) : motive l := ind l fun l' _h => List.recSuffix ind l'
termination_by l.length
decreasing_by
  simp_wf
  obtain ⟨t, ⟨h1, h2⟩⟩ := _h
  rw [←h2]
  simp [h1, List.length_pos]

def List.suffix_induction {α} {p : List α → Prop}
  (l : List α)
  (nil : p nil)
  (cons : ∀ head tail, (∀ l', l'.IsStrictSuffix (head :: tail) → p l') → p (head :: tail))
  : p l :=
  l.recSuffix (λ l ih => match l with
    | List.nil => nil
    | List.cons head tail => cons head tail ih)

-- protected theorem strong_induction_on {p : Nat → Prop} (n : Nat)
--     (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
--   Nat.strongRecOn n h

-- def List.strongRecOn (t : Nat) {motive : Nat → Sort _}
--   (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive t := Nat.strongRec ind t
