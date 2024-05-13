import «LayoutTypes».Space
import «LayoutTypes».UtilsProofs

theorem Box.zero_size_zero : (0 : Box).size = 0 := by rfl

theorem Pos.nle_iff_parts_lt (p1 p2 : Pos) : ¬(p1 ≤ p2) ↔ p2.x < p1.x ∨ p2.y < p1.y := by
  unfold LE.le; simp [Prod.instLE_mathlib, -not_and]; rw [not_and_or]; simp

theorem disjoint_iff_disjoint_inf {α} [Lattice α] [@DecidableRel α (· ≤ ·)] (i1 i2 : NonemptyInterval α)
  : i1.disjoint_inf i2 ↔ i1.disjoint i2
  := by
  simp [NonemptyInterval.disjoint_inf, Inf.inf, NonemptyInterval.disjoint]
  rw [←not_and_or]
  simp

theorem Box.sup_eq_pos_inf (b1 b2 : Box) : (b1 ⊔ b2).pos = b1.pos ⊓ b2.pos := by simp [boxSup]

theorem Box.disjoint_if_dim_disjoint (b1 b2 : Box) (dim : Fin 2)
  (h : b1.hi.nth dim < b2.lo.nth dim)
  : b1.disjoint b2
  := by
  simp [disjoint, NonemptyInterval.disjoint]
  cases dim.two_eq_or
  case inl h_eq =>
    simp [Prod.nth, h_eq] at h
    apply Or.intro_right
    apply (b2.pos.nle_iff_parts_lt _).mpr
    simp
    apply Or.intro_left
    assumption
  case inr h_eq =>
    simp [Prod.nth, h_eq] at h
    apply Or.intro_right
    apply (b2.pos.nle_iff_parts_lt _).mpr
    simp
    apply Or.intro_right
    assumption

theorem boxCover.size_eq_extrema_diff (b : Box) (bs : List Box) :
  (boxCover b bs).size = boxMax b bs - boxMin b bs
  := by
  simp [boxCover, boxMax, boxMin]
  induction bs generalizing b
  case nil => simp
  case cons b' bs ih =>
    simp
    have ih := ih (b ⊔ b')
    rw [ih.left]
    rw [ih.right]
    simp [
      max, min, WithTop.some, WithBot.some, regionSize,
      SemilatticeSup.toSup, Sup.sup, Option.liftOrGet,
      regionSize, Option.getD, Lattice.toInf, Inf.inf
    ]

theorem foo {a b n : ℚ} (h1 : n ≤ a) (h2 : n ≤ b) : n ≤ min a b := by
  exact le_min h1 h2

theorem boxMin.bounded (b : Box) (bs : List Box) (dim : Fin 2) (n : ℚ)
  (h_bounded : ∀ b2 ∈ b :: bs, n ≤ b2.pos.nth dim) : n ≤ (boxMin b bs).nth dim
  := by
  simp [boxMin]
  induction bs generalizing b
  case nil => simp [h_bounded]
  case cons b' bs ih =>
    have ih := ih b' (forall_prop_of_tail h_bounded)
    cases dim.two_eq_or
    case inl h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (min b.pos.1) min min _ _ (by simp [min_assoc])]
      exact le_min h_bounded.left ih
    case inr h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (min b.pos.2) min min _ _ (by simp [min_assoc])]
      exact le_min h_bounded.left ih

theorem boxMax.bounded (b : Box) (bs : List Box) (dim : Fin 2) (n : ℚ)
  (h_bounded : ∀ b2 ∈ b :: bs, b2.hi.nth dim ≤ n) : (boxMax b bs).nth dim ≤ n
  := by
  simp [instHAdd, Add.add, -List.mem_cons] at h_bounded
  simp [boxMax]
  induction bs generalizing b
  all_goals simp [-List.mem_cons] at h_bounded ⊢
  case nil => assumption
  case cons b' bs ih =>
    have ih := ih b' (forall_prop_of_tail h_bounded)
    cases dim.two_eq_or
    case inl h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (max (b.pos.1 + b.size.1)) max max _ _ (by simp [max_assoc])]
      exact max_le h_bounded.left ih
    case inr h =>
      simp [h, Prod.nth] at *
      rw [List.foldl_hom (max (b.pos.2 + b.size.2)) max max _ _ (by simp [max_assoc])]
      exact max_le h_bounded.left ih
