/- Document layout algorithms -/

import «LayoutTypes».Space
import «LayoutTypes».Document
import «LayoutTypes».Utils


/- Line wrapping -/

def wrapLinesGreedy (els : List Element) (width : ℚ⁺) : List (List Element) :=
  let rec aux := λ (els : List Element) (cur : List Element) (x : ℚ⁺) => match els with
    | [] => [cur]
    | el :: els =>
      let w := el.box.size.w
      let x' := x + w
      if x' > width then cur :: (aux els [el] w)
      else aux els (cur ++ [el]) x'
  aux els [] 0


/- Arranging lists of boxes -/

structure FluidEl where
  el : Element
  prevMargin : ℚ
  nextMargin : ℚ

def layoutFluid (dim : Fin 2) (els : List FluidEl) : Element :=
  let rec aux := λ (els : List FluidEl) (pos : Pos) => match els with
    | [] => []
    | {el, prevMargin, nextMargin} :: els =>
      let elPos := pos + prevMargin.toVec dim
      let el' := el.setPos elPos
      let nextPos := elPos + el.box.size.nthVec dim + (1 + nextMargin).toVec dim
      el' :: aux els nextPos
  let els' := aux els 0
  Element.frame (Frame.mk 0 els')

def layoutFluidX := layoutFluid 0
def layoutFluidY := layoutFluid 1


/- Text shaping -/

structure ShapedText (fontSize : ℚ⁺) where
  box : Box
  height_bounded : fontSize ≥ box.size.h

def TextShaper := (fontSize : ℚ⁺) → String → ShapedText fontSize


/- Layout algorithm that walks the source document -/

structure GlobalLayoutCtx where
  shaper : TextShaper

structure InlineLayoutCtx where
  gcx        : GlobalLayoutCtx
  blockWidth : ℚ⁺
  lineHeight : ℚ
  fontSize   : ℚ⁺
  bold       : Bool

mutual
  def InlineLayoutCtx.collectInline (icx : InlineLayoutCtx) (i : Inline) : List Element := match i with
    | .text s =>
      let shaped := icx.gcx.shaper icx.fontSize s
      let style := Style.mk icx.fontSize icx.bold
      let text := Text.mk shaped.box s style
      [Element.text text]
    | .bold is =>
      let icx' := {icx with bold := true}
      icx'.collectInlineSeq is

  def InlineLayoutCtx.collectInlineSeq (icx : InlineLayoutCtx) (is : List Inline) : List Element :=
    (is.attach.map λ i : { x // x ∈ is } => icx.collectInline i.val).join
  decreasing_by have := i.prop; simp_wf; decreasing_trivial
end

def InlineLayoutCtx.layoutLines (icx : InlineLayoutCtx) (is : List Inline) : Element :=
  let els := icx.collectInlineSeq is
  let lines := wrapLinesGreedy els icx.blockWidth
  let lineEls := lines.map (λ line => layoutFluidX (line.map (FluidEl.mk · 0 0)))
  layoutFluidY (lineEls.map (FluidEl.mk · 0 icx.lineHeight))

def GlobalLayoutCtx.layoutPara (gcx : GlobalLayoutCtx) (p : Para) : Element :=
  let icx : InlineLayoutCtx := {
    gcx,
    blockWidth := 120,
    lineHeight := p.lineHeight
    fontSize := p.fontSize
    bold := false
  }
  icx.layoutLines p.inls

def GlobalLayoutCtx.layoutBlock (gcx : GlobalLayoutCtx) (bk : BlockKind) : Element := match bk with
  | .para p => gcx.layoutPara p

def GlobalLayoutCtx.layoutBlockSeq (gcx : GlobalLayoutCtx) (bs : List Block) : Element :=
  layoutFluidY (bs.map λ b =>
    FluidEl.mk (gcx.layoutBlock b.kind) b.attrs.marginTop b.attrs.marginBot)

def GlobalLayoutCtx.layoutDocument (gcx : GlobalLayoutCtx) (d : Document) : Element :=
  gcx.layoutBlockSeq d.blocks

def Document.layout (d : Document) (shaper : TextShaper) : Element :=
  let ctx : GlobalLayoutCtx := { shaper }
  ctx.layoutDocument d

section Examples

def sampleDoc : Document :=
  let text := "This is a really long line.";
  let inls := text.splitOn.map Inline.text |>.intersperse (Inline.text " ");
  { blocks := [
     {
      kind := .para {
        inls := [
          Inline.text "Hello",
          Inline.bold [Inline.text " World. "]
        ] ++ inls,
        fontSize := 12,
        lineHeight := 0,
      },
      attrs := {
        marginTop := 0,
        marginBot := 20
      }
     },
    {
      kind := .para {
        inls := [
          Inline.text "Hello",
          Inline.bold [Inline.text " World. "]
        ] ++ inls,
        fontSize := 12,
        lineHeight := 0,
      },
      attrs := {
        marginTop := -20,
        marginBot := 0
      }
     }
  ]}

def naiveShaper (fontSize : ℚ⁺) (s : String) : ShapedText fontSize :=
  let charWidth := fontSize * 0.5
  let box : Box := { pos := 0, size := ⟨charWidth * s.length, fontSize⟩ }
  have height_bounded : fontSize ≥ box.size.h := by trivial
  { box, height_bounded }

#html (sampleDoc.layout naiveShaper).toSvg 150 100

end Examples
