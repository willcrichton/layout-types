use allsorts::pathfinder_geometry::{
  transform2d::Transform2F,
  vector::{Vector2F, Vector2I},
};
use anyhow::Result;
use font_kit::{
  canvas::{Canvas, Format, RasterizationOptions},
  font::Font,
  hinting::HintingOptions,
};
use ndarray::{s, ArrayView, ArrayViewMut2};
use winit::dpi::PhysicalSize;

use crate::shaper::TextRenderOptions;

pub struct Rasterizer {
  canvas: Canvas,
  font: Font,
}

impl Rasterizer {
  pub fn new(size: PhysicalSize<u32>, font: Font) -> Self {
    let canvas = Canvas::new(
      Vector2I::new(size.width as i32, size.height as i32),
      Format::Rgba32,
    );
    Rasterizer { font, canvas }
  }

  pub fn rasterize(
    &mut self,
    glyph_id: u16,
    pos: Vector2F,
    options: &TextRenderOptions,
  ) -> Result<()> {
    self.font.rasterize_glyph(
      &mut self.canvas,
      glyph_id as u32,
      options.font_size,
      Transform2F::from_translation(pos),
      HintingOptions::None,
      RasterizationOptions::GrayscaleAa,
    )?;
    Ok(())
  }

  pub fn resize(&mut self, size: PhysicalSize<u32>) {
    self.canvas = Canvas::new(
      Vector2I::new(size.width as i32, size.height as i32),
      Format::Rgba32,
    );
  }

  pub fn copy(&self, mut dst: ArrayViewMut2<'_, u32>) {
    let canvas_nd = ArrayView::from_shape(
      (self.canvas.size.y() as usize, self.canvas.size.x() as usize),
      bytemuck::cast_slice::<u8, u32>(&self.canvas.pixels),
    )
    .unwrap();
    dst.assign(&canvas_nd);
  }
}
