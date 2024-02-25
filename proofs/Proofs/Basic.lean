import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend
-- import LeanCopilot

structure Interval where
  lo : ℝ
  hi : ℝ

namespace Interval
  def disjoint (i1 i2 : Interval) : Prop :=
    i1.lo ≥ i2.hi ∨ i1.hi ≤ i2.lo
end Interval

structure Vec2 where
  x : ℝ
  y : ℝ

structure Size where
  size : Vec2
  positive : size.x ≥ 0 ∧ size.y ≥ 0

namespace Size
  def w (s : Size) : ℝ := s.size.x
  def h (s : Size) : ℝ := s.size.y
end Size

structure Box where
  pos : Vec2
  size : Size

namespace Box
  def disjoint (b1 b2 : Box) : Prop :=
    let b1w := Interval.mk b1.pos.x (b1.pos.x + b1.size.w)
    let b1h := Interval.mk b1.pos.y (b1.pos.y + b1.size.h)
    let b2w := Interval.mk b2.pos.x (b2.pos.x + b2.size.w)
    let b2h := Interval.mk b2.pos.y (b2.pos.y + b2.size.h)
    (b1w.disjoint b2w) ∨ (b1h.disjoint b2h)
end Box

def layout_lines (lines : List Size) (font_size : ℝ) : List Box :=
  lines.enum.map λ (idx, size) =>
    let y := idx * font_size
    let pos := Vec2.mk 0 y
    Box.mk pos size

theorem scaled_lt_preserves_le {n1 n2 : ℕ} {x r : ℝ} (h_r : r ≥ 0) (h_n_le : n1 < n2) (h_x_le : x ≤ r)
  : n1 * r + x ≤ n2 * r := by
  have h : (↑n1 + (1 : ℝ)) ≤ ↑n2 := by norm_cast
  have : (↑n1 + 1) * r ≤ n2 * r := mul_le_mul_of_nonneg_right h h_r
  linarith

theorem line_layout_no_overlap (lines : List Size) (font_size : ℝ)
  (n1 n2 : Fin lines.length)
  (hneq : n1 ≠ n2) (hsize : ∀ (s : Size), s ∈ lines → s.h ≤ font_size) (hpos : font_size ≥ 0)
  : ∃ boxes, boxes = layout_lines lines font_size ∧
    ∃ (n1' n2' : Fin boxes.length), n1.val = n1'.val ∧ n2.val = n2'.val ∧
    (boxes.get n1').disjoint (boxes.get n2')
  := by
    -- Start by "calling" the function.
    let boxes := layout_lines lines font_size; exists boxes; simp

    -- Convert the indices n1/n2 into corresponding Fin types
    -- for each intermediate list.
    let n1_enum : Fin lines.enum.length := Fin.mk n1.val (by simp [*])
    let n2_enum : Fin lines.enum.length := Fin.mk n2.val (by simp [*])
    have : boxes.length = lines.length := by simp [layout_lines]
    let n1' : Fin boxes.length := Fin.mk n1.val (by simp [*])
    let n2' : Fin boxes.length := Fin.mk n2.val (by simp [*])
    exists n1'; simp; exists n2'; simp

    -- Reduce the proof term given the definitions of all relevant functions.
    simp [
      layout_lines,
      lines.get_enum n1_enum, lines.get_enum n2_enum,
      Box.disjoint, Interval.disjoint,
      Size.w, Size.h
    ]

    -- Apply hsize to show each line's height is less than font_size.
    have h_n1_le_font : (lines.get n1).h ≤ font_size :=
      hsize (lines.get n1) (List.get_mem lines n1.val n1.isLt)
    have h_n2_le_font : (lines.get n2).h ≤ font_size :=
      hsize (lines.get n2) (List.get_mem lines n2.val n2.isLt)

    -- We're going to show that the height ranges of the bboxes are disjoint.
    apply Or.inr

    -- Either the first box is below the second, or vice versa.
    cases Nat.lt_or_ge n1 n2 with
    | inl h_lt =>
      -- If n1 < n2..
      apply Or.inr
      apply scaled_lt_preserves_le hpos h_lt h_n1_le_font
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
        apply scaled_lt_preserves_le hpos h_lt h_n2_le_font
