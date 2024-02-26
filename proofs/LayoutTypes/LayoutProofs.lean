import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend

import «LayoutTypes».Data
import «LayoutTypes».Layout

lemma scaled_lt_preserves_le {n1 n2 : ℕ} {x: ℝ} {r : ℝ⁺}
  (h_n_le : n1 < n2) (h_x_le : r ≥ x)
  : (n1 : ℝ) * r  + x ≤ n2 * r := by
  have h : (↑n1 + (1 : ℝ)) ≤ ↑n2 := by norm_cast
  have : (↑n1 + 1) * (r : ℝ) ≤ n2 * r := mul_le_mul_of_nonneg_right h r.isPos
  linarith

def boxes_disjoint (boxes : List Box) :=
  ∀ (n1 n2 : Fin boxes.length), n1 ≠ n2 → (boxes.get n1).disjoint (boxes.get n2)

theorem layout_lines_disjoint (lines : List Size) (font_size line_height : ℝ⁺)
  (h_line_bounded : ∀ (s : Size), s ∈ lines → font_size ≥ s.h)
  (h_height_ge_font : (line_height : ℝ) ≥ font_size)
  : ∃ boxes, boxes = layout_lines lines line_height ∧ boxes_disjoint boxes
  := by
    -- Start by "calling" the function.
    let boxes := layout_lines lines line_height; exists boxes; simp
    unfold boxes_disjoint; intros n1 n2 hneq

    -- Convert the indices n1/n2 into corresponding Fin types
    -- for each intermediate list.
    have : lines.length = boxes.length := by simp [layout_lines]
    let n1_enum : Fin lines.enum.length := Fin.mk n1.val (by simp [*])
    let n2_enum : Fin lines.enum.length := Fin.mk n2.val (by simp [*])
    let n1_lines : Fin lines.length := Fin.mk n1.val (by simp [*])
    let n2_lines : Fin lines.length := Fin.mk n2.val (by simp [*])

    -- Reduce the proof term given the definitions of all relevant functions.
    simp [
      layout_lines,
      lines.get_enum n1_enum, lines.get_enum n2_enum,
      Box.disjoint, Interval.disjoint,
      Size.w, Size.h
    ]

    -- Apply h_line_bounded and h_line_height to show each line's height is less than line_height.
    have h_n1_le_font : line_height ≥ (lines.get n1_lines).h := by
      have := h_line_bounded (lines.get n1_lines) (List.get_mem lines n1_lines.val n1_lines.isLt)
      linarith
    have h_n2_le_font : line_height ≥ (lines.get n2_lines).h := by
      have := h_line_bounded (lines.get n2_lines) (List.get_mem lines n2_lines.val n2_lines.isLt)
      linarith

    -- We're going to show that the height ranges of the bboxes are disjoint.
    apply Or.inr

    -- Either the first box is below the second, or vice versa.
    cases Nat.lt_or_ge n1 n2 with
    | inl h_lt =>
      -- If n1 < n2..
      apply Or.inr
      apply scaled_lt_preserves_le h_lt h_n1_le_font
    | inr h_ge =>
      -- Else n2 ≤ n1..
      cases Nat.eq_or_lt_of_le h_ge with
      | inl h_eq =>
        -- n1 = n2 is a contradiction
        have : n1 = n2 := by rw [Iff.mp (Fin.val_eq_val n2 n1) h_eq]
        contradiction
      | inr h_lt =>
        -- Then we show for n2 < n1
        apply Or.inl
        apply scaled_lt_preserves_le h_lt h_n2_le_font

theorem layout_para_disjoint (p : Para) (wrapper : LineWrapper)
  (h_height_ge_font : (p.line_height : ℝ) ≥ p.font_size)
  : ∃ boxes, boxes = layout_para p wrapper ∧ boxes_disjoint boxes
  := by
  -- Start by calling and unfolding layout_para.
  let boxes := layout_para p wrapper; exists boxes; simp
  simp [layout_para]

  -- Apply layout_lines_disjoint to show that layout_para is correct.
  let wrapped : WrappedLines p.font_size := wrapper p.contents p.font_size
  have := layout_lines_disjoint wrapped.lines p.font_size p.line_height
    wrapped.height_bounded h_height_ge_font
  apply Exists.elim this; intro boxes' h

  -- Unpack the conclusions and substitute as needed.
  have h_eq := And.right h
  have h_disjoint := And.left h
  apply Eq.subst h_disjoint h_eq
