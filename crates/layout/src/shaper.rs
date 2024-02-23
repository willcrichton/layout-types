use std::cell::RefCell;

use allsorts::{
  binary::read::ReadScope,
  font::MatchingPresentation,
  font_data::{DynamicFontTableProvider, FontData},
  glyph_position::{GlyphLayout, TextDirection},
  gsub::{FeatureMask, Features},
  tag,
  tinyvec::TinyVec,
};
use anyhow::Result;
use nalgebra::vector;

use crate::math::{Number, Vec2};

pub struct Shaper {
  font: RefCell<allsorts::Font<DynamicFontTableProvider<'static>>>,
}

pub struct ShapedGlyph {
  pub chars: TinyVec<[char; 1]>,
  pub pos: Vec2,
  pub width: f64,
}

pub struct TextRenderOptions {
  pub font_size: Number,
}

impl Shaper {
  pub fn new(font_data: &[u8]) -> Result<Self> {
    let font_data = font_data.to_vec().leak();
    let scope = ReadScope::new(font_data);
    let font_file = scope.read::<FontData<'_>>()?;
    let provider = font_file.table_provider(0)?;
    let font = RefCell::new(allsorts::Font::new(provider)?.unwrap());
    Ok(Shaper { font })
  }

  pub fn measure(&self, text: &str, options: &TextRenderOptions) -> Result<f64> {
    let shapes = self.shape(text, options)?;
    Ok(shapes.map(|shape| shape.width).sum())
  }

  pub fn shape(
    &self,
    text: &str,
    options: &TextRenderOptions,
  ) -> Result<impl Iterator<Item = ShapedGlyph>> {
    let mut font = self.font.borrow_mut();
    let glyphs = font.map_glyphs(text, tag::LATN, MatchingPresentation::NotRequired);
    let infos = font
      .shape(
        glyphs,
        tag::LATN,
        Some(tag::from_string("ENG ").unwrap()),
        &Features::Mask(FeatureMask::default()),
        true,
      )
      .map_err(|(err, _)| err)?;
    let mut layout = GlyphLayout::new(&mut font, &infos, TextDirection::LeftToRight, false);
    let positions = layout.glyph_positions()?;
    let mut cur_x = 0;
    let mut cur_y = 0;

    let head = font.head_table()?.unwrap();
    let font_size = options.font_size.as_pixels(options.font_size);
    let scale = font_size / f64::from(head.units_per_em);

    Ok(
      infos
        .into_iter()
        .zip(positions)
        .map(move |(info, glyph_pos)| {
          let chars = info.glyph.unicodes;
          let x = (cur_x + glyph_pos.x_offset) as f64;
          let y = (cur_y + glyph_pos.y_offset) as f64;
          cur_x += glyph_pos.hori_advance;
          cur_y += glyph_pos.vert_advance;
          let pos = vector![x * scale, font_size + y * scale];
          let width = glyph_pos.hori_advance as f64 * scale;
          ShapedGlyph { chars, pos, width }
        }),
    )
  }
}
