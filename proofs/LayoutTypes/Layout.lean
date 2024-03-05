import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.BigOperators.Defs
import «LayoutTypes».Data

structure WrappedLines (font_size : ℝ⁺) where
  lines : List Size
  height_bounded : ∀ s ∈ lines, font_size ≥ s.h

def LineWrapper := (s : String) → (font_size : ℝ⁺) → WrappedLines font_size

def vert_layout (sizes_at_y : List (Size × ℝ)) : List Box :=
  sizes_at_y.map λ (size, y) => Box.mk (Vec2.mk 0 y) size

def vert_layout_scaled (sizes : List Size) (scale : ℝ⁺) : List Box :=
  let sizes_at_y := sizes.enum.map λ (idx, size) => (size, idx * scale)
  vert_layout sizes_at_y

def scan_sum (ns : List ℝ⁺) : List ℝ⁺ :=
  (List.range ns.length).map λ i => (ns.take i).sum

def vert_layout_fluid (sizes : List Size) : List Box :=
  let ys := scan_sum (sizes.map Size.h)
  let sizes_at_y := sizes.zip (ys.map Coe.coe)
  vert_layout sizes_at_y

structure Layout where
  wrapper : LineWrapper

def Layout.para (l : Layout) (p : Para) : List Box :=
  let wrapped := l.wrapper p.contents p.font_size
  vert_layout_scaled wrapped.lines p.line_height

def Layout.block (l : Layout) (b : Block) : List Box :=
  match b with
  | Block.para p => l.para p

def Layout.blocks (l : Layout) (bs : List Block) : List Box :=
  (bs.map l.block).join

def Layout.document (l : Layout) (d : Document) : List Box :=
  l.blocks d.blocks
