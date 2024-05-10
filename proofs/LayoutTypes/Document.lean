import «LayoutTypes».Space

structure Style where
  bold : Bool

mutual
  inductive Text | mk
    (box : Box)
    (s : String)
    (style : Style)

  inductive Frame | mk
    (origin : Pos)
    (els : List Element)

  inductive Element
    | text : Text → Element
    | frame : Frame → Element
end

mutual
  def Frame.box (frame : Frame) : Box :=
    let ⟨origin, els⟩ := frame
    let boxes := els.attach.map λ el : { x // x ∈ els } => Element.box el.val
    let cover := boxCover boxes
    cover.offset origin
  decreasing_by have := el.prop; simp_wf; decreasing_trivial

  def Element.box
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

inductive Inline where
  | text (s : String)
  | bold (inls: List Inline)

structure Para where
  inls : List Inline
  fontSize : ℚ⁺
  lineHeight : ℚ⁺

inductive Block where
  | para (p : Para)

structure Document where
  blocks : List Block
