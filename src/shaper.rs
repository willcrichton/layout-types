use allsorts::{
  binary::read::ReadScope,
  font::MatchingPresentation,
  font_data::{DynamicFontTableProvider, FontData},
  glyph_position::{GlyphLayout, TextDirection},
  gsub::{FeatureMask, Features},
  pathfinder_geometry::vector::Vector2F,
  tag,
};
use anyhow::Result;

pub struct Shaper {
  font: allsorts::Font<DynamicFontTableProvider<'static>>,
}

pub struct ShapedGlyph {
  pub id: u16,
  pub pos: Vector2F,
  pub width: f32,
}

pub struct TextRenderOptions {
  pub font_size: f32,
}

impl Shaper {
  pub fn new(fontkit_font: &font_kit::font::Font) -> Result<Self> {
    let font_data = fontkit_font.copy_font_data().unwrap().to_vec().leak();
    let scope = ReadScope::new(font_data);
    let font_file = scope.read::<FontData<'_>>()?;
    let provider = font_file.table_provider(0)?;
    let font = allsorts::Font::new(provider)?.unwrap();
    Ok(Shaper { font })
  }

  pub fn measure(&mut self, text: &str, options: &TextRenderOptions) -> Result<f32> {
    let shapes = self.shape(text, options)?;
    Ok(shapes.map(|shape| shape.width).sum())
  }

  pub fn shape(
    &mut self,
    text: &str,
    options: &TextRenderOptions,
  ) -> Result<impl Iterator<Item = ShapedGlyph>> {
    let glyphs = self
      .font
      .map_glyphs(text, tag::LATN, MatchingPresentation::NotRequired);
    let infos = self
      .font
      .shape(
        glyphs,
        tag::LATN,
        Some(tag::from_string("ENG ").unwrap()),
        &Features::Mask(FeatureMask::default()),
        true,
      )
      .map_err(|(err, _)| err)?;
    let mut layout = GlyphLayout::new(&mut self.font, &infos, TextDirection::LeftToRight, false);
    let positions = layout.glyph_positions()?;
    let mut cur_x = 0;
    let mut cur_y = 0;

    let head = self.font.head_table()?.unwrap();
    let font_size = options.font_size;
    let scale = font_size / f32::from(head.units_per_em);

    Ok(
      infos
        .into_iter()
        .zip(positions)
        .map(move |(info, glyph_pos)| {
          let glyph_id = info.glyph.glyph_index;
          let x = cur_x + glyph_pos.x_offset;
          let y = cur_y + glyph_pos.y_offset;
          cur_x += glyph_pos.hori_advance;
          cur_y += glyph_pos.vert_advance;
          let pos = Vector2F::new(x as f32 * scale, font_size + y as f32 * scale);
          ShapedGlyph {
            id: glyph_id,
            pos,
            width: glyph_pos.hori_advance as f32 * scale,
          }
        }),
    )
  }
}
