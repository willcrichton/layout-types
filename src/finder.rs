use anyhow::Result;
use font_kit::{family_name::FamilyName, properties::Properties, source::SystemSource};

pub fn find_font(family: &str) -> Result<font_kit::font::Font> {
  let font_handle = SystemSource::new().select_best_match(
    &[FamilyName::Title(String::from(family))],
    &Properties::new(),
  )?;
  Ok(font_handle.load()?)
}
