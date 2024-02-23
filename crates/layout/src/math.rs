use nalgebra::Vector2;

pub type Vec2 = Vector2<f64>;

#[derive(Copy, Clone, Debug)]
pub enum Unit {
  Pixel,
  Point,
  Em,
}

#[derive(Copy, Clone, Debug)]
pub struct Number {
  pub value: f64,
  pub unit: Unit,
}

impl Number {
  pub fn points(value: f64) -> Self {
    Number {
      value,
      unit: Unit::Point,
    }
  }

  pub fn ems(value: f64) -> Self {
    Number {
      value,
      unit: Unit::Em,
    }
  }

  pub fn as_pixels(self, font_size: Number) -> f64 {
    debug_assert!(!matches!(font_size.unit, Unit::Em));
    match self.unit {
      Unit::Pixel => self.value,
      Unit::Point => self.value * 96. / 72.,
      Unit::Em => font_size.as_pixels(font_size) * self.value,
    }
  }

  pub fn as_points(self, font_size: Number) -> f64 {
    debug_assert!(!matches!(font_size.unit, Unit::Em));
    match self.unit {
      Unit::Pixel => self.value * 72. / 96.,
      Unit::Point => self.value,
      Unit::Em => font_size.as_points(font_size) * self.value,
    }
  }
}
