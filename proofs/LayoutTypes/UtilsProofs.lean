import Mathlib.Data.List.Basic

import «LayoutTypes».Utils

theorem List.length_fins {α} (l : List α) : l.fins.length = l.length
  := by simp [fins]

theorem List.get_fins {α} (l : List α) (i : Fin l.fins.length)
  : (l.fins.get i).val = i.val
  := by simp [fins]

theorem List.accSum_length {α} [AddCommMonoid α] (l : List α)
  : l.accSum.length = l.length
  := by simp [List.accSum, length_fins]

theorem List.accSum_get {α} [AddCommMonoid α] {l : List α} {i : Fin l.accSum.length}
  : l.accSum.get i = (l.take i).sum
  := by simp [List.accSum, fins]

def Fin.two_eq_or (n : Fin 2) : n = 0 ∨ n = 1 := by omega

theorem Prod.nth_or {α} (p : α × α) (i : Fin 2)
  : p.nth i = p.fst ∨ p.nth i = p.snd
  := by
  cases i.two_eq_or
  case inl h => simp [nth, h]
  case inr h => simp [nth, h]

theorem Prod.nth_dist (p1 p2 : ℚ × ℚ) (dim : Fin 2)
  : (p1 + p2).nth dim = p1.nth dim + p2.nth dim
  := by
  cases dim.two_eq_or
  case inl h => simp [h, nth]
  case inr h => simp [h, nth]

theorem forall_prop_of_tail {α} {p : α → Prop} {x : α} {xs : List α}
  (h : ∀ x' ∈ x :: xs, p x') : ∀ x' ∈ xs, p x' := by
  intro x' h_in
  exact h x' (xs.mem_cons_of_mem x h_in)

theorem Prod.nth_add_eq_toVec {k : ℚ} {p : ℚ × ℚ} {dim : Fin 2}
  : (p.nth dim + k = (p + k.toVec dim).nth dim) := by
  cases dim.two_eq_or
  case inl h => simp [h, nth, Rat.toVec]
  case inr h => simp [h, nth, Rat.toVec]

theorem Rat.toVec_pos {n : ℚ} {dim : Fin 2} (h : 0 ≤ n) : 0 ≤ n.toVec dim := by
  apply Prod.le_def.mpr
  cases dim.two_eq_or
  case inl h' => simp [h, toVec, h']
  case inr h' => simp [h, toVec, h']
