use std::rc::Rc;

use anyhow::Result;
use winit::window::Window;

pub struct Canvas {}

impl Canvas {
  pub fn new(window: &Rc<Window>) -> Result<Self> {

    Ok(Canvas {})
  }
}

// use anyhow::{anyhow, Result};
// use ndarray::ArrayViewMut2;
// use softbuffer::{Buffer, Surface};
// use std::{num::NonZeroU32, rc::Rc};

// use winit::{dpi::PhysicalSize, window::Window};

// pub struct Canvas {
//   surface: Surface<Rc<Window>, Rc<Window>>,
//   size: PhysicalSize<u32>,
// }

// impl Canvas {
//   pub fn new(window: &Rc<Window>) -> Result<Self> {
//     let context = softbuffer::Context::new(window.clone()).map_err(|e| anyhow!("{e}"))?;
//     let surface = softbuffer::Surface::new(&context, window.clone()).map_err(|e| anyhow!("{e}"))?;
//     let mut canvas = Canvas {
//       surface,
//       size: PhysicalSize::new(0, 0),
//     };
//     canvas.resize(window);
//     Ok(canvas)
//   }

//   pub fn resize(&mut self, window: &Window) {
//     self.size = window.inner_size();
//     self
//       .surface
//       .resize(
//         NonZeroU32::new(self.size.width).unwrap(),
//         NonZeroU32::new(self.size.height).unwrap(),
//       )
//       .unwrap();
//   }

//   pub fn frame_buffer(&mut self) -> Result<FrameBuffer<'_>> {
//     let buffer = self.surface.buffer_mut().map_err(|e| anyhow!("{e}"))?;
//     Ok(FrameBuffer {
//       size: self.size,
//       buffer,
//     })
//   }
// }

// pub struct FrameBuffer<'a> {
//   size: PhysicalSize<u32>,
//   buffer: Buffer<'a, Rc<Window>, Rc<Window>>,
// }

// impl FrameBuffer<'_> {
//   pub fn mut_view(&mut self) -> ArrayViewMut2<'_, u32> {
//     ArrayViewMut2::from_shape(
//       (self.size.height as usize, self.size.width as usize),
//       self.buffer.as_mut(),
//     )
//     .unwrap()
//   }

//   pub fn present(self) -> Result<()> {
//     self.buffer.present().map_err(|e| anyhow!("{e}"))?;
//     Ok(())
//   }
// }
