use layout::{
  input,
  math::Number,
  output::{self, ElementKind},
  Viewport,
};
use yew::prelude::*;

const SAMPLE_FONT: &[u8] = include_bytes!("../assets/LinLibertine_R.otf");

const TEXT: &str = "Call me Ishmael. Some years ago—never mind how long precisely—having little or no money in my purse, and nothing particular to interest me on shore, I thought I would sail about a little and see the watery part of the world. It is a way I have of driving off the spleen and regulating the circulation. Whenever I find myself growing grim about the mouth; whenever it is a damp, drizzly November in my soul; whenever I find myself involuntarily pausing before coffin warehouses, and bringing up the rear of every funeral I meet; and especially whenever my hypos get such an upper hand of me, that it requires a strong moral principle to prevent me from deliberately stepping into the street, and methodically knocking people’s hats off—then, I account it high time to get to sea as soon as I can. This is my substitute for pistol and ball. With a philosophical flourish Cato throws himself upon his sword; I quietly take to the ship. There is nothing surprising in this. If they but knew it, almost all men in their degree, sometime or other, cherish very nearly the same feelings towards the ocean with me.";

// const FONT_FAMILY: &str = "Linux Libertine";

fn sample_document() -> input::Document {
  use input::*;
  Document {
    blocks: vec![Block::Para {
      children: vec![Inline::Text {
        contents: TEXT.into(),
        font_size: Number::points(16.),
      }],
      line_height: Number::ems(1.5),
    }],
  }
}

fn output_to_svg(viewport: &Viewport, doc: &output::Document) -> Html {
  let width = format!("{}", viewport.width);
  let height = format!("{}", viewport.height);
  let elements = doc
    .iter()
    .map(|el| {
      let x = format!("{}", el.position.x);
      let y = format!("{}", el.position.y);
      match &el.kind {
        ElementKind::Text {
          contents,
          font_size,
        } => {
          let font_size = format!("{}pt", font_size.as_points(*font_size));
          html! {
            <text x={x} y={y} font-size={ font_size }>{ contents }</text>
          }
        }
      }
    })
    .collect::<Html>();
  html! {
    <div class="render">
    <svg
      xmlns="http://www.w3.org/2000/svg"
      width={width}
      height={height}
    >
    {elements}</svg>
    </div>
  }
}

#[function_component]
fn App() -> Html {
  let layout_engine = use_state(|| layout::LayoutEngine::new(SAMPLE_FONT).unwrap());

  let input = use_state(sample_document);

  let layouts = [100., 200., 400., 800.]
    .into_iter()
    .map(|width| {
      let viewport = Viewport {
        width,
        height: 400.,
      };

      let output = layout_engine.layout(&input, &viewport).unwrap();

      output_to_svg(&viewport, &output)
    })
    .collect::<Html>();

  html! {
    <div class="renders">
      { layouts }
    </div>
  }
}

fn main() {
  wasm_logger::init(wasm_logger::Config::default());
  yew::Renderer::<App>::new().render();
}
