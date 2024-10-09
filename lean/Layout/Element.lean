import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import «Layout».Space

structure Style where
  fontSize : ℚ
  bold : Bool
deriving Repr

structure Text where
  pos : Pos
  s : String
  style : Style
deriving Repr

instance : Bounded Text where
  bounds t :=
    let w := t.style.fontSize * t.s.length
    let h := t.style.fontSize
    {pos := t.pos, size := !![w, h]}

instance : Positioned Text where
  pos t := t.pos
  setPos t pos := {t with pos}

mutual
  inductive Element
    | text : Text → Element
    | frame : Frame → Element

  inductive Frame
    | mk : Pos → List Element → Frame
end

mutual
  def Element.bounds (el : Element) : Rect := match el with
    | .text t => Bounded.bounds t
    | .frame f => f.bounds

  def Frame.bounds (f : Frame) : Rect :=
    let ⟨origin, els⟩ := f
    let elBounds := els.attach.map (λ el => el.val.bounds) |>.foldl Rect.union 0
    {elBounds with pos := origin + elBounds.pos}
  decreasing_by have := el.property; decreasing_trivial
end

instance : Bounded Frame where
  bounds := Frame.bounds

instance : Bounded Element where
  bounds := Element.bounds

instance : Positioned Frame where
  pos f :=
    let ⟨pos, _⟩ := f
    pos
  setPos f pos :=
    let ⟨_, bounds⟩ := f
    Frame.mk pos bounds

instance : Positioned Element where
  pos el := match el with
    | .text t => Positioned.pos t
    | .frame f => Positioned.pos f
  setPos el pos := match el with
    | .text t => Element.text (Positioned.setPos t pos)
    | .frame f => Element.frame (Positioned.setPos f pos)

def Element.toSvgParts (e : Element) : ProofWidgets.Html :=
  open scoped ProofWidgets.Jsx in
  match e with
  | text {pos, s, style} =>
    let fontSize := toString style.fontSize;
    let fontWeight := if style.bold then "bold" else "normal";
    <text
      x={toString pos.x.toFloat}
      y={toString pos.y.toFloat}
      style={json% {
        fontSize: $(fontSize),
        fontWeight: $(fontWeight),
        whiteSpace: "pre"
      }}
    >
      {.text s}
    </text>
  | frame f =>
    let ⟨origin, els⟩ := f
    let elSvgs := els.attach.map (λ el : {x // x ∈ els} => el.val.toSvgParts) |>.toArray;
    let transform := s! "translate({origin.x.toFloat}, {origin.y.toFloat})";
    <g transform={transform} >{...elSvgs}</g>
decreasing_by have := el.property; simp_wf; decreasing_trivial

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
