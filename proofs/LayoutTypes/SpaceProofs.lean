import «LayoutTypes».Space
import «LayoutTypes».Utils
import «LayoutTypes».UtilsProofs

theorem Pos.nle_iff_parts_lt (p1 p2 : Pos) : ¬(p1 ≤ p2) ↔ p2.x < p1.x ∨ p2.y < p1.y := by
  unfold LE.le; simp [Prod.instLE_mathlib, -not_and]; rw [not_and_or]; simp

theorem disjoint_iff_disjoint_inf {α} [Lattice α] [@DecidableRel α (· ≤ ·)] (i1 i2 : NonemptyInterval α)
  : i1.disjoint_inf i2 ↔ i1.disjoint i2
  := by
  simp [NonemptyInterval.disjoint_inf, Inf.inf, NonemptyInterval.disjoint]
  rw [←not_and_or]
  simp

theorem Box.sup_eq_pos_inf (b1 b2 : Box) : (b1 ⊔ b2).pos = b1.pos ⊓ b2.pos := by simp [boxSup]

theorem Box.disjoint_if_dim_disjoint (b1 b2 : Box) (dim : Fin 2)
  (h : b1.hi.nth dim < b2.lo.nth dim)
  : b1.disjoint b2
  := by
  simp [disjoint, NonemptyInterval.disjoint]
  cases dim.two_eq_or
  case inl h_eq =>
    simp [Prod.nth, h_eq] at h
    apply Or.intro_right
    apply (b2.pos.nle_iff_parts_lt _).mpr
    simp
    apply Or.intro_left
    assumption
  case inr h_eq =>
    simp [Prod.nth, h_eq] at h
    apply Or.intro_right
    apply (b2.pos.nle_iff_parts_lt _).mpr
    simp
    apply Or.intro_right
    assumption
