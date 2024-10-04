use crate::math::Number;

pub enum Inline {
  Text { contents: String, font_size: Number },
}

pub type InlineSeq = Vec<Inline>;

pub enum Block {
  Para {
    children: InlineSeq,
    line_height: Number,
  },
}

pub type BlockSeq = Vec<Block>;

pub struct Document {
  pub blocks: BlockSeq,
}
