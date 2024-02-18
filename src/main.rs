use allsorts::pathfinder_geometry::vector::Vector2F;
use anyhow::Result;

use shaper::TextRenderOptions;

use std::{cell::RefCell, rc::Rc};

use winit::{
  dpi::LogicalSize,
  event::{Event, WindowEvent},
  event_loop::EventLoop,
  window::WindowBuilder,
};

mod canvas;
mod finder;
mod rasterizer;
mod shaper;
mod wrapper;

const TEXT: &str = "Call me Ishmael. Some years ago—never mind how long precisely—having little or no money in my purse, and nothing particular to interest me on shore, I thought I would sail about a little and see the watery part of the world. It is a way I have of driving off the spleen and regulating the circulation. Whenever I find myself growing grim about the mouth; whenever it is a damp, drizzly November in my soul; whenever I find myself involuntarily pausing before coffin warehouses, and bringing up the rear of every funeral I meet; and especially whenever my hypos get such an upper hand of me, that it requires a strong moral principle to prevent me from deliberately stepping into the street, and methodically knocking people’s hats off—then, I account it high time to get to sea as soon as I can. This is my substitute for pistol and ball. With a philosophical flourish Cato throws himself upon his sword; I quietly take to the ship. There is nothing surprising in this. If they but knew it, almost all men in their degree, sometime or other, cherish very nearly the same feelings towards the ocean with me.";

const FONT_FAMILY: &str = "Linux Libertine";

type Document = Vec<(u16, Vector2F)>;

fn layout(
  wrapper: &wrapper::Wrapper,
  shaper: &RefCell<shaper::Shaper>,
  options: &TextRenderOptions,
  line_width: f32,
) -> Result<Document> {
  let lines = wrapper.wrap(TEXT, line_width, options)?;

  let mut shaper = shaper.borrow_mut();
  let mut base = Vector2F::new(0., 0.);
  let mut glyphs = Vec::new();
  for line in lines {
    for glyph in shaper.shape(&line, options)? {
      let pos = glyph.pos + base;
      glyphs.push((glyph.id, pos));
    }
    base.set_y(base.y() + 32.);
  }

  Ok(glyphs)
}

fn draw(
  doc: &Document,
  rasterizer: &mut rasterizer::Rasterizer,
  options: &TextRenderOptions,
) -> Result<()> {
  for (glyph_id, pos) in doc {
    rasterizer.rasterize(*glyph_id, *pos, options)?;
  }
  Ok(())
}

fn main() -> Result<()> {
  let font = finder::find_font(FONT_FAMILY)?;
  let shaper = Rc::new(RefCell::new(shaper::Shaper::new(&font)?));
  let wrapper = wrapper::Wrapper::new(&shaper)?;

  let event_loop = EventLoop::new().unwrap();

  let window = WindowBuilder::new()
    .with_title("doc-render")
    .with_inner_size(LogicalSize::new(628.0, 512.0))
    .build(&event_loop)
    .unwrap();
  let window = Rc::new(window);

  let mut rasterizer = rasterizer::Rasterizer::new(window.inner_size(), font);
  let options = TextRenderOptions { font_size: 32. };

  let mut canvas = canvas::Canvas::new(&window)?;

  Ok(event_loop.run(move |event, elwt| match event {
    Event::WindowEvent { event, window_id } if window_id == window.id() => match event {
      WindowEvent::CloseRequested => elwt.exit(),
      WindowEvent::Resized(..) => {
        canvas.resize(&window);
        rasterizer.resize(window.inner_size());

        let doc = layout(&wrapper, &shaper, &options, window.inner_size().width as f32).unwrap();
        draw(&doc, &mut rasterizer, &options).unwrap();
      }
      WindowEvent::RedrawRequested => {
        // let mut frame_buffer = canvas.frame_buffer().unwrap();
        // rasterizer.copy(frame_buffer.mut_view());
        // frame_buffer.present().unwrap();
      }
      _ => (),
    },
    Event::AboutToWait => {
      window.request_redraw();
    }

    _ => (),
  })?)
}
