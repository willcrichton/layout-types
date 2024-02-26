import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import «LayoutTypes».Data

def layout_lines (lines : List Size) (line_height : ℝ⁺) : List Box :=
  lines.enum.map λ (idx, size) =>
    let y := (idx : ℝ) * line_height
    let pos := Vec2.mk 0 y
    Box.mk pos size

structure WrappedLines (font_size : ℝ⁺) where
  lines : List Size
  height_bounded : ∀ s, s ∈ lines → font_size ≥ s.h

def LineWrapper := (s : String) → (font_size : ℝ⁺) → WrappedLines font_size

def layout_para (p : Para) (wrapper : LineWrapper) : List Box :=
  let wrapped := wrapper p.contents p.font_size
  layout_lines wrapped.lines p.line_height
