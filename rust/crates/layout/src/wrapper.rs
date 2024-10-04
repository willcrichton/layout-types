use std::rc::Rc;

use crate::shaper::{Shaper, TextRenderOptions};
use anyhow::Result;

use hyphenation::Load;
use textwrap::{
  core::{Fragment, Word},
  wrap_algorithms::Penalties,
  WordSeparator::UnicodeBreakProperties,
  WordSplitter,
};

pub struct Wrapper {
  shaper: Rc<Shaper>,
  splitter: WordSplitter,
}
#[derive(Debug)]
struct ShapedWord<'a> {
  word: Word<'a>,
  width: f64,
  whitespace_width: f64,
  penalty_width: f64,
}

impl Fragment for ShapedWord<'_> {
  fn width(&self) -> f64 {
    self.width
  }

  fn whitespace_width(&self) -> f64 {
    self.whitespace_width
  }

  fn penalty_width(&self) -> f64 {
    self.penalty_width
  }
}

impl Wrapper {
  pub fn new(shaper: &Rc<Shaper>) -> Result<Self> {
    let shaper = Rc::clone(shaper);

    let dictionary = hyphenation::Standard::from_embedded(hyphenation::Language::EnglishUS)?;
    let splitter = WordSplitter::Hyphenation(dictionary);

    Ok(Wrapper { shaper, splitter })
  }

  pub fn wrap(
    &self,
    text: &str,
    line_width: f64,
    options: &TextRenderOptions,
  ) -> Result<Vec<String>> {
    let words = UnicodeBreakProperties.find_words(text);
    let split_words = textwrap::word_splitters::split_words(words, &self.splitter);

    let shaped_words = split_words
      .map(|word| {
        let width = self.shaper.measure(word.word, options)?;
        let whitespace_width = self.shaper.measure(word.whitespace, options)?;
        let penalty_width = self.shaper.measure(word.penalty, options)?;
        Ok(ShapedWord {
          word,
          width,
          whitespace_width,
          penalty_width,
        })
      })
      .collect::<Result<Vec<_>>>()?;

    let penalties = Penalties::new();
    let line_words =
      textwrap::wrap_algorithms::wrap_optimal_fit(&shaped_words, &[line_width], &penalties)?;

    let line_strings = line_words
      .into_iter()
      .map(|words| {
        let (last, rest) = words.split_last().unwrap();
        let mut text = String::new();

        for word in rest {
          text.push_str(word.word.word);
          text.push_str(word.word.whitespace);
        }

        text.push_str(last.word.word);
        text.push_str(last.word.penalty);

        text
      })
      .collect::<Vec<_>>();

    Ok(line_strings)
  }
}
