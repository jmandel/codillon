// The witness track: a row above the step slider for what the input search found.
// A witness that has not been replayed is a dashed darkred track ("not replayed");
// clicking it loads that input as the run, shown as a solid "replayed" pill.
// While searching, or when nothing was found, a quiet slategray note.

use crate::{
    delegate_element_component,
    dom_struct::DomStruct,
    dom_text::DomText,
    jet::{AccessToken, ElementFactory},
};
use web_sys::HtmlDivElement;

type TrackDiv = DomStruct<(DomText, ()), HtmlDivElement>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrackState {
    Hidden,
    Note,        // searching, or no counterexample found
    NotReplayed, // a witness, not yet the run
    Replayed,    // the witness is the run
}

pub struct WitnessTrack {
    contents: TrackDiv,
    state: TrackState,
}

impl WitnessTrack {
    pub fn new(factory: &ElementFactory) -> Self {
        let mut contents = DomStruct::new((DomText::new(""), ()), factory.div());
        contents.set_attribute("class", "witness-track hidden");
        Self {
            contents,
            state: TrackState::Hidden,
        }
    }

    pub fn state(&self) -> TrackState {
        self.state
    }

    pub fn set(&mut self, state: TrackState, text: &str, title: &str) {
        self.state = state;
        let class = match state {
            TrackState::Hidden => "witness-track hidden",
            TrackState::Note => "witness-track note",
            TrackState::NotReplayed => "witness-track not-replayed",
            TrackState::Replayed => "witness-track replayed",
        };
        self.contents.set_attribute("class", class);
        if self.contents.get().0.get() != text {
            self.contents.get_mut().0.set_data(text);
        }
        if title.is_empty() {
            self.contents.remove_attribute("title");
        } else {
            self.contents.set_attribute("title", title);
        }
    }
}

delegate_element_component!(WitnessTrack, contents, HtmlDivElement);
