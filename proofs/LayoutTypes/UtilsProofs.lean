import Mathlib.Data.List.Basic

import «LayoutTypes».Utils

theorem List.length_fins {α} (l : List α) : l.fins.length = l.length
  := by simp [fins]

theorem List.get_fins {α} (l : List α) (i : Fin l.fins.length)
  : (l.fins.get i).val = i.val
  := by simp [fins]

theorem List.length_acc_sum {α} [AddCommMonoid α] (l : List α)
  : l.acc_sum.length = l.length
  := by simp [acc_sum, length_fins]

theorem List.get_acc_sum {α} [AddCommMonoid α] {l : List α} {i : Fin l.acc_sum.length}
  : l.acc_sum.get i = (l.take i).sum
  := by simp [acc_sum, fins]

def Fin.two_eq_or (n : Fin 2) : n = 0 ∨ n = 1 := by omega

theorem Prod.nth_or {α} (p : α × α) (i : Fin 2)
  : p.nth i = p.fst ∨ p.nth i = p.snd
  := by
  cases i.two_eq_or
  case inl h => simp [nth, h]
  case inr h => simp [nth, h]

theorem forall_prop_of_tail {α} {p : α → Prop} {x : α} {xs : List α}
  (h : ∀ x' ∈ x :: xs, p x') : ∀ x' ∈ xs, p x' := by
  intro x' h_in
  exact h x' (xs.mem_cons_of_mem x h_in)
