import «LayoutTypes».Data
import «LayoutTypes».Types
import «LayoutTypes».Layout
import «LayoutTypes».LayoutProofs

theorem disjoint_safety (p : Para) (wrapper : LineWrapper)
  : tc_para p → ∃ boxes, boxes = layout_para p wrapper ∧ boxes_disjoint boxes
  := by
  intros h_tc
  apply layout_para_disjoint p wrapper
  exact h_tc
