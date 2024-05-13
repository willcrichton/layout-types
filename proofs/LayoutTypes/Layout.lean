/- Document layout algorithms -/

import «LayoutTypes».Space
import «LayoutTypes».Document
import «LayoutTypes».Utils


/- Line wrapping -/

def wrap_lines_greedy (els : List Element) (width : ℚ⁺) : List (List Element) :=
  let rec aux := λ (els : List Element) (cur : List Element) (x : ℚ⁺) => match els with
    | [] => [cur]
    | el :: els =>
      let w := el.box.size.w
      let x' := x + w
      if x' > width then cur :: (aux els [el] w)
      else aux els (cur ++ [el]) x'
  aux els [] 0


/- Arranging lists of boxes -/

def AccUpdate := Element → Pos → Pos

def layout_list_acc (f : AccUpdate) (els : List Element) : Element :=
  let rec aux := λ (els : List Element) (pos : Pos) => match els with
    | [] => []
    | el :: els =>
      let el' := el.setPos pos
      el' :: aux els (f el pos)
  let els' := aux els 0
  Element.frame (Frame.mk 0 els')

def left_align : AccUpdate := (·.box.size.nth_vec 0 + ⟨1, 0⟩ + ·)
def layout_left_align := layout_list_acc left_align

def vert_stack : AccUpdate := (·.box.size.nth_vec 1 + ⟨0, 1⟩ + ·)
def layout_vert_stack := layout_list_acc vert_stack

def vert_fixed (y : ℚ) : AccUpdate := fun _ h => ⟨0, y⟩ + h
def layout_vert_fixed (y : ℚ) := layout_list_acc (vert_fixed y)


/- Text shaping -/

structure ShapedText (font_size : ℚ⁺) where
  box : Box
  height_bounded : font_size ≥ box.size.h

def TextShaper := (font_size : ℚ⁺) → (s : String) → ShapedText font_size


/- Layout algorithm that walks the source document -/

structure GlobalLayoutCtx where
  shaper : TextShaper

structure InlineLayoutCtx where
  globalCtx  : GlobalLayoutCtx
  blockWidth : ℚ⁺
  lineHeight : ℚ⁺
  fontSize   : ℚ⁺
  bold       : Bool

mutual
  def InlineLayoutCtx.collect_inline (icx : InlineLayoutCtx) (i : Inline) : List Element := match i with
    | Inline.text s =>
      let shaped := icx.globalCtx.shaper icx.fontSize s
      let style := Style.mk icx.fontSize icx.bold
      let text := Text.mk shaped.box s style
      [Element.text text]
    | Inline.bold is =>
      {icx with bold := true}.collect_inline_seq is

  def InlineLayoutCtx.collect_inline_seq (icx : InlineLayoutCtx) (is : List Inline) : List Element :=
    (is.attach.map λ i : { x // x ∈ is } => icx.collect_inline i.val).join
  decreasing_by have := i.prop; simp_wf; decreasing_trivial
end

def InlineLayoutCtx.layout_lines (icx : InlineLayoutCtx) (is : List Inline) : Element :=
  let els := icx.collect_inline_seq is
  let lines := wrap_lines_greedy els icx.blockWidth
  let line_els := lines.map layout_left_align
  layout_vert_fixed (icx.lineHeight + 1) line_els

def GlobalLayoutCtx.layout_para (gcx : GlobalLayoutCtx) (p : Para) : Element :=
  let icx : InlineLayoutCtx := {
    globalCtx := gcx,
    blockWidth := 120,
    lineHeight := p.lineHeight
    fontSize := p.fontSize
    bold := false
  }
  icx.layout_lines p.inls

def GlobalLayoutCtx.layout_block (gcx : GlobalLayoutCtx) (b : Block) : Element := match b with
  | Block.para p => gcx.layout_para p

def GlobalLayoutCtx.layout_block_seq (gcx : GlobalLayoutCtx) (bs : List Block) : Element :=
  layout_vert_stack (bs.map gcx.layout_block)

def GlobalLayoutCtx.layout_document (gcx : GlobalLayoutCtx) (d : Document) : Element :=
  gcx.layout_block_seq d.blocks

def Document.layout (d : Document) (shaper : TextShaper) : Element :=
  let ctx : GlobalLayoutCtx := { shaper }
  ctx.layout_document d


section Examples

def sample_doc : Document :=
  let text := "This is a very long line";
  let inls := text.splitOn.map Inline.text |>.intersperse (Inline.text " ");
  { blocks := [
    Block.para {
      inls := [
        Inline.text "Hello",
        Inline.bold [Inline.text " World. "]
      ] ++ inls,
      fontSize := 12,
      lineHeight := 12
    }
  ]}

def naive_shaper (font_size : ℚ⁺) (s : String) : ShapedText font_size :=
  let char_width := font_size * 0.5
  let box : Box := { pos := 0, size := ⟨char_width * s.length, font_size⟩ }
  have height_bounded : font_size ≥ box.size.h := by trivial
  { box, height_bounded }

#html (sample_doc.layout naive_shaper).to_svg 150 100

end Examples
