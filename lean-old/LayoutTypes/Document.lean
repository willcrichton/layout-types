/- Source and target document data structures. -/

import «LayoutTypes».Space
import «LayoutTypes».Utils
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay


/- Source documents. -/

inductive Inline where
  | text (s : String)
  | bold (inls: List Inline)
deriving Repr

structure Para where
  inls : List Inline
  fontSize : ℚ⁺
  lineHeight : ℚ

def Para.wf (p : Para) : Prop :=
  0 ≤ p.lineHeight

inductive BlockKind where
  | para : Para → BlockKind

def BlockKind.wf (bk : BlockKind) : Prop :=
  match bk with
  | .para p => p.wf

structure BlockAttrs where
  marginTop: ℚ
  marginBot: ℚ

structure Block where
  kind : BlockKind
  attrs : BlockAttrs

def Block.wf (b : Block) : Prop :=
  b.kind.wf

def block_seq_wf (bs : List Block) : Prop :=
  List.Chain' (λ b1 b2 => 0 ≤ b1.attrs.marginBot + b2.attrs.marginTop) bs ∧
  ∀ b ∈ bs, b.wf

structure Document where
  blocks : List Block

def Document.wf (d : Document) : Prop :=
  block_seq_wf d.blocks


/- Target documents. -/

structure Style where
  fontSize : ℚ
  bold : Bool
deriving Repr

mutual
  inductive Text | mk
    (box : Box)
    (s : String)
    (style : Style)
  deriving Repr

  inductive Frame | mk
    (origin : Pos)
    (els : List Element)
  deriving Repr

  inductive Element
    | text : Text → Element
    | frame : Frame → Element
  deriving Repr
end


/- Methods on the target document domain. -/

mutual
  def Frame.box (frame : Frame) : Box :=
    let ⟨origin, els⟩ := frame
    let boxes := els.attach.map λ el : { x // x ∈ els } => Element.box el.val
    let cover := boxCover 0 boxes
    cover.offset origin
  decreasing_by have := el.prop; simp_wf; decreasing_trivial

  def Element.box : Element → Box
    | Element.text ⟨box, _, _⟩ => box
    | Element.frame f => f.box
end

def Element.pos (e : Element) : Pos := e.box.pos

mutual
  def Text.setPos (text : Text) (pos : Pos) : Text :=
    let ⟨box, s, style⟩ := text
    ⟨{box with pos}, s, style⟩

  def Frame.setPos (frame : Frame) (pos : Pos) : Frame :=
    let ⟨_, els⟩ := frame
    let overflow := els.map (·.pos) |>.foldl (· ⊓ ·) 0
    ⟨pos - overflow, els⟩

  def Element.setPos (e : Element) (pos : Pos) : Element := match e with
    | Element.text t => Element.text (t.setPos pos)
    | Element.frame f => Element.frame (f.setPos pos)
end

def Element.disjoint (e1 e2 : Element) : Prop :=
  e1.box.disjoint e2.box

def elements_disjoint (els : List Element) : Prop :=
  List.Pairwise Element.disjoint els

def Element.inner_disjoint (e : Element) : Prop := match e with
  | Element.text _ => True
  | Element.frame (Frame.mk _ els) =>
    elements_disjoint els ∧ ∀ el ∈ els, el.inner_disjoint


/- Utility widget for looking at elements in the proof view. -/

def Element.toSvgParts (e : Element) : ProofWidgets.Html :=
  open scoped ProofWidgets.Jsx in
  match e with
  | text t =>
    let ⟨box, s, style⟩ := t;
    let fontSize := toString style.fontSize;
    let fontWeight := if style.bold then "bold" else "normal";
    <text
      x={toString box.lo.x.toFloat}
      y={toString box.lo.y.toFloat}
      style={json% {
        fontSize: $(fontSize),
        fontWeight: $(fontWeight),
        whiteSpace: "pre"
      }}
    >
      {.text s}
    </text>
  | frame f =>
    let ⟨origin, els⟩ := f;
    let elSvgs := els.attach.map (λ el : {x // x ∈ els} => el.val.toSvgParts) |>.toArray;
    let transform := s! "translate({origin.x.toFloat}, {origin.y.toFloat})";
    <g transform={transform} >{...elSvgs}</g>
decreasing_by have := el.prop; simp_wf; decreasing_trivial

def Element.toSvg (e : Element) (width height : ℚ) : ProofWidgets.Html :=
  open scoped ProofWidgets.Jsx in
  <svg xmlns="http://www.w3.org/2000/svg"
      version="1.1"
      width={toString width}
      height={toString height}
      style={json% {
        dominantBaseline: "hanging",
        fontFamily: "Inconsolata"
      }}>
    {e.toSvgParts}
  </svg>
