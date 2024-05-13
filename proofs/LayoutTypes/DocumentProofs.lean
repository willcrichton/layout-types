import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.List.Basic
import Mathlib.Order.Lattice

import «LayoutTypes».Space
import «LayoutTypes».SpaceProofs
import «LayoutTypes».Document

theorem Element.set_pos_changes_pos (e : Element) (pos : Pos)
  : (e.setPos pos).box = {e.box with pos} := by
  cases e
  case text t =>
    cases t; simp only [Element.pos, Element.setPos, Text.setPos, Element.box]

  case frame f =>
    obtain ⟨origin, els⟩ := f
    simp [
      Element.setPos, Element.pos, Element.box, Frame.box, Frame.setPos, boxCover,
      List.attach, List.map_pmap, Box.offset, List.attachWith
    ]

    cases els
    case nil => simp; trivial
    case cons el els =>
      simp [List.foldl_map]
      let boxSup := (· ⊔ box ·)
      let posInf := fun x y => x ⊓ (box y).pos
      suffices (els.foldl boxSup el.box).pos = els.foldl posInf el.box.pos by
        linear_combination this + pos

      induction els
      case nil => simp
      case cons el els ih =>
        simp only [List.foldl_cons, List.foldl_map]
        rw [
          List.foldl_hom (· ⊔ box el) boxSup _ _ _ (by simp [boxSup, sup_right_comm]),
          List.foldl_hom (· ⊓ (box el).pos) posInf _ _ _ (by simp [posInf, inf_right_comm])
        ]
        rw [←ih]
        apply Box.sup_eq_pos_inf

theorem Element.set_pos_preserves_inner_disjoint (e : Element) (pos : Pos)
  (h_disj : e.inner_disjoint) : (e.setPos pos).inner_disjoint
  := by
  cases e
  case text _ => simp [inner_disjoint, setPos]
  case frame f =>
    unfold inner_disjoint
    obtain ⟨origin, els⟩ := f
    simp [setPos, Frame.setPos, inner_disjoint] at *
    exact h_disj

-- This is necessary because Inline uses nested inductive types
@[induction_eliminator]
def Inline.induction_principle
  (i : Inline)
  (p : Inline → Prop)
  (text : ∀ (s : String), p (text s))
  (bold : ∀ (is : List Inline), (∀ i ∈ is, p i) → p (bold is))
  : p i
  := @Inline.rec
    p
    (λ is => ∀ i ∈ is, p i)
    text
    bold
    (List.forall_mem_nil p)
    (λ _ _ h_head h_tail => List.forall_mem_cons.mpr (And.intro h_head h_tail))
    i
