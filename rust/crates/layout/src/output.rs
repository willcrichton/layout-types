use crate::math::{Number, Vec2};

#[derive(Debug)]
pub enum ElementKind {
  Text { contents: String, font_size: Number },
}

#[derive(Debug)]
pub struct Element {
  pub kind: ElementKind,
  pub position: Vec2,
}

pub type Document = Vec<Element>;
