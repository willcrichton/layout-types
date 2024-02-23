use std::rc::Rc;

use crate::{
  input::{self, Block, Inline},
  math::Number,
  output::{self, Element, ElementKind},
  shaper::{Shaper, TextRenderOptions},
  wrapper::Wrapper,
};
use anyhow::Result;
use nalgebra::vector;

pub struct Viewport {
  pub width: f64,
  pub height: f64,
}

pub struct LayoutEngine {
  wrapper: Wrapper,
  shaper: Rc<Shaper>,
}

struct LayoutContext<'a> {
  engine: &'a LayoutEngine,
  viewport: &'a Viewport,
}

impl LayoutContext<'_> {
  fn layout_block_seq(&self, block_seq: &input::BlockSeq) -> output::Document {
    block_seq
      .iter()
      .flat_map(|block| self.layout_block(block))
      .collect()
  }

  fn layout_block(&self, block: &input::Block) -> output::Document {
    match block {
      Block::Para {
        children,
        line_height,
      } => LayoutInlineContext {
        ctx: self,
        line_height: *line_height,
      }
      .layout_inline_seq(children),
    }
  }
}

struct LayoutInlineContext<'a, 'b> {
  ctx: &'b LayoutContext<'a>,
  line_height: Number,
}

impl LayoutInlineContext<'_, '_> {
  fn layout_inline_seq(&self, inline_seq: &input::InlineSeq) -> output::Document {
    inline_seq
      .iter()
      .flat_map(|inline| self.layout_inline(inline))
      .collect()
  }

  fn layout_inline(&self, inline: &input::Inline) -> output::Document {
    match inline {
      Inline::Text {
        contents,
        font_size,
      } => {
        let font_size = *font_size;

        let options = TextRenderOptions { font_size };
        let wrapper = &self.ctx.engine.wrapper;
        let lines = wrapper
          .wrap(contents, self.ctx.viewport.width, &options)
          .unwrap();

        lines
          .into_iter()
          .enumerate()
          .flat_map(|(line_idx, line)| self.layout_line(line_idx, &line, &options))
          .collect()
      }
    }
  }

  fn layout_line(
    &self,
    line_idx: usize,
    line: &str,
    options: &TextRenderOptions,
  ) -> output::Document {
    let line_y = self.line_height.as_pixels(options.font_size) * line_idx as f64;
    let line_origin = vector![0., line_y];
    let shaped_glyphs = self.ctx.engine.shaper.shape(line, options).unwrap();
    shaped_glyphs
      .map(move |glyph: crate::shaper::ShapedGlyph| {
        let contents = String::from_iter(glyph.chars);
        let kind = ElementKind::Text {
          contents,
          font_size: options.font_size,
        };
        let position = glyph.pos + line_origin;
        Element { kind, position }
      })
      .collect()
  }
}

impl LayoutEngine {
  pub fn new(font_data: &[u8]) -> Result<Self> {
    let shaper = Rc::new(Shaper::new(font_data)?);
    let wrapper = Wrapper::new(&shaper)?;
    Ok(LayoutEngine { shaper, wrapper })
  }

  pub fn layout(&self, input: &input::Document, viewport: &Viewport) -> Result<output::Document> {
    Ok(
      LayoutContext {
        engine: self,
        viewport,
      }
      .layout_block_seq(&input.blocks),
    )
  }
}
