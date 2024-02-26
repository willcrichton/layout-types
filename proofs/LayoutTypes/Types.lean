import Mathlib.Data.Real.Basic

import «LayoutTypes».Data

def tc_para (p : Para) : Prop :=
  (p.line_height : ℝ) ≥ p.font_size
