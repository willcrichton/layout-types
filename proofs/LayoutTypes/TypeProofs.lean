import «LayoutTypes».Data
import «LayoutTypes».Types
import «LayoutTypes».Layout
import «LayoutTypes».LayoutProofs

theorem para_layout_safe (Γ : Tcx) (l : Layout) (p : Para) (h : Γ.para p)
  : ∃ boxes, boxes = l.para p ∧ boxes_disjoint boxes
  := l.para_disjoint p h

-- theorem block_layou

-- theorem disjoint_safety (l : Layout) (p : Para)
--   : tc_para p → ∃ boxes, boxes = l.para p ∧ boxes_disjoint boxes
--   := by
