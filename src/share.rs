// A small "share" affordance: copies a `#src=` link to the current program and step.
// In embed mode it instead opens the same state in a new tab ("open in editor ↗").

use crate::{
    delegate_element_component,
    dom_struct::DomStruct,
    dom_text::DomText,
    jet::{AccessToken, ElementFactory},
};
use web_sys::HtmlDivElement;

type ShareDiv = DomStruct<(DomText, ()), HtmlDivElement>;

pub struct ShareButton {
    contents: ShareDiv,
    embed: bool,
}

impl ShareButton {
    const LABEL: &'static str = "share link";
    const EMBED_LABEL: &'static str = "open in editor \u{2197}";

    pub fn new(factory: &ElementFactory) -> Self {
        let mut contents = DomStruct::new((DomText::new(Self::LABEL), ()), factory.div());
        contents.set_attribute("class", "share-button");
        contents.set_attribute("title", "copy a link to this program and step");
        Self {
            contents,
            embed: false,
        }
    }

    pub fn set_embed(&mut self, embed: bool) {
        self.embed = embed;
        self.reset_label();
    }

    pub fn is_embed(&self) -> bool {
        self.embed
    }

    pub fn reset_label(&mut self) {
        let label = if self.embed {
            Self::EMBED_LABEL
        } else {
            Self::LABEL
        };
        if self.contents.get().0.get() != label {
            self.contents.get_mut().0.set_data(label);
        }
        self.contents.set_attribute("class", "share-button");
    }

    // Record the most recent link (also readable by tests and automation).
    pub fn set_link(&mut self, url: &str) {
        self.contents.set_attribute("data-link", url);
    }

    pub fn flash(&mut self, msg: &str) {
        self.contents.get_mut().0.set_data(msg);
        self.contents.set_attribute("class", "share-button flashed");
    }
}

delegate_element_component!(ShareButton, contents, HtmlDivElement);
