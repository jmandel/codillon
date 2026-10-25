// An individual line of code in the editor. The CodeLine struct
// enforces consistency between the text in the line, the kind and
// "is_instr" status of the line (i.e. whether it's a well-formed
// *and* active instruction), and its CSS presentation.

use crate::{
    dom_struct::DomStruct,
    dom_text::DomText,
    graphics::indent_px,
    jet::{
        AccessToken, Component, ElementFactory, NodeRef, WebOffset, WithElement,
        set_selection_range,
    },
    symbolic::{LineSymbols, parse_line_symbols},
    syntax::{
        FuncPart, InstrKind, LineAnnotation, LineKind, ModulePart, SyntheticWasm, parse_line_spec,
    },
    utils::{AnimationRequest, Tween, find_comment},
};
use anyhow::{Result, bail};
use std::{cell::Cell, mem::swap};
use web_sys::{HtmlBrElement, HtmlDivElement, HtmlSpanElement};

type DomBr = DomStruct<(), HtmlBrElement>;
type TextSpan = DomStruct<(DomText, ()), HtmlSpanElement>;
type EmptySpan = DomStruct<(), HtmlSpanElement>;
type LinePara = DomStruct<(TextSpan, (TextSpan, (EmptySpan, (DomBr, ())))), HtmlDivElement>;

pub const INDENT_PX: usize = 25;
/// the fact lane (design 16 §8): extra room between each line's fraction and its code, where
/// proof cups and fact chips are drawn
pub const LANE_PX: usize = 28;

#[derive(Default, Copy, Clone, PartialEq, Debug)]
pub enum Activity {
    #[default]
    Active,
    Inactive(&'static str), // reason
}

impl PartialEq<bool> for Activity {
    fn eq(&self, val: &bool) -> bool {
        (self == &Activity::Active) == *val
    }
}

thread_local! {
    static NEXT_LINE_ID: Cell<u32> = Default::default();
}

#[derive(Debug, Clone)]
pub struct LineInfo {
    pub id: u32,
    pub kind: LineKind,
    pub active: Activity,
    pub indent: Option<u16>,
    pub synthetic_before: SyntheticWasm,
    pub invalid: Option<String>,
    pub runtime_error: Option<String>,
    pub symbols: LineSymbols,
    /// the plain-WAT text this line erases to (v2), when it differs from the line's text
    pub erased: Option<String>,
    /// what the proof kernel says about this line (drawn by proof_view)
    pub proof: crate::proof_view::LineProof,
}

impl Default for LineInfo {
    fn default() -> Self {
        let ret = Self {
            id: NEXT_LINE_ID.get(),
            kind: LineKind::Empty,
            active: Default::default(),
            indent: None,
            synthetic_before: Default::default(),
            invalid: None,
            runtime_error: None,
            symbols: Default::default(),
            erased: None,
            proof: Default::default(),
        };
        NEXT_LINE_ID.replace(ret.id + 1);
        ret
    }
}

impl LineInfo {
    pub fn is_active(&self) -> bool {
        self.active == true
    }

    pub fn is_well_formed(&self) -> bool {
        self.is_active() && matches!(self.kind, LineKind::Instr(_) | LineKind::Other(_))
    }

    pub fn is_instr(&self) -> bool {
        self.is_active() && matches!(self.kind, LineKind::Instr(_))
    }

    pub fn is_structured(&self) -> bool {
        self.is_active()
            && matches!(
                self.kind,
                LineKind::Instr(InstrKind::If)
                    | LineKind::Instr(InstrKind::Loop)
                    | LineKind::Instr(InstrKind::OtherStructured)
            )
    }

    pub fn paren_depths(&self) -> (i32, i32) {
        // indent change before first displayed char, other indent changes
        let mut initial = 0;
        for part in &self.synthetic_before.module_field_syntax {
            match part {
                FuncPart::LParen => initial += 1,
                FuncPart::RParen => initial -= 1,
                _ => {}
            }
        }

        let mut rest = 0;
        if self.is_active()
            && let LineKind::Other(ModulePart::Func(parts)) = &self.kind
        {
            let mut first_letter = true;
            for part in parts {
                match part {
                    FuncPart::RParen if first_letter => initial -= 1,
                    FuncPart::RParen => rest -= 1,
                    FuncPart::LParen => rest += 1,
                    _ => {}
                }
                first_letter = false;
            }
        }

        (initial, rest)
    }

    // Number of opcodes (synthetic and user-entered) in the line
    pub fn num_ops(&self) -> usize {
        self.synthetic_before.num_ops() + self.is_instr() as usize
    }

    // Number of well-formed strings (synthetic and user-entered) in the line
    pub fn num_well_formed_strs(&self) -> usize {
        self.synthetic_before.num_strs() + self.is_well_formed() as usize
    }

    // Return well-formed (non-comment) Wasm string #n (both instructions and module-scope syntax)
    pub fn well_formed_str<'a>(&'a self, idx: usize, instr_text: &'a str) -> &'a str {
        if idx < self.synthetic_before.num_strs() {
            self.synthetic_before.str(idx)
        } else if self.is_well_formed() && idx == self.synthetic_before.num_strs() {
            self.erased.as_deref().unwrap_or(instr_text)
        } else {
            panic!("index out of range");
        }
    }
}

#[derive(Default)]
struct AnimationState {
    browser_animation: BrowserAnimation,
    indent: Tween,
}

#[derive(Default)]
enum BrowserAnimation {
    #[default]
    Normal,
    Shake(bool),
    Reveal(bool),
    FlyEnd(bool),
}

pub struct CodeLine {
    contents: LinePara,
    /// the caret is on this line (its proof account is shown)
    cursor: bool,
    info: LineInfo,
    animation_state: AnimationState,
}

impl WithElement for CodeLine {
    type Element = HtmlDivElement;
    fn with_element<T, F: FnMut(&HtmlDivElement) -> T>(&self, f: F, g: AccessToken) -> T {
        self.contents.with_element(f, g)
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Position {
    pub in_instr: bool,
    pub offset: usize, // bytes
}

impl Position {
    pub fn begin() -> Position {
        Position::instr(0)
    }

    fn instr(offset: usize) -> Position {
        Position {
            in_instr: true,
            offset,
        }
    }

    fn comment(offset: usize) -> Position {
        Position {
            in_instr: false,
            offset,
        }
    }
}
#[derive(Clone)]
pub struct PositionRange {
    pub start_line: usize,
    pub start_pos: Position,
    pub end_line: usize,
    pub end_pos: Position,
}

impl Component for CodeLine {
    #[cfg(debug_assertions)]
    fn audit(&self) {
        assert_eq!(
            self.info.kind,
            crate::syntax::parse_line(self.instr().get())
        );
        assert_eq!(self.contents.get_attribute("class").unwrap(), &self.class());
        let comment = self.contents.get().1.0.get_attribute("data-commentary");
        if let Some(msg) = &self.info.runtime_error
            && !msg.is_empty()
        {
            assert_eq!(comment, Some(msg.as_str()));
        } else if let LineKind::Malformed(reason) = &self.info.kind {
            assert_eq!(comment, Some(reason.as_str()));
        } else if let Activity::Inactive(reason) = &self.info.active
            && !reason.is_empty()
        {
            assert_eq!(comment, Some(*reason));
        } else if let Some(reason) = &self.info.invalid
            && !reason.is_empty()
        {
            assert_eq!(comment, Some(reason.as_str()));
        } else {
            assert_eq!(comment, None);
        }

        self.contents.audit();
    }
}

impl CodeLine {
    pub fn instr(&self) -> &DomText {
        &self.contents.get().0.get().0
    }

    fn instr_mut(&mut self) -> &mut DomText {
        &mut self.contents.get_mut().0.get_mut().0
    }

    pub fn comment(&self) -> &DomText {
        &self.contents.get().1.0.get().0
    }

    fn comment_mut(&mut self) -> &mut DomText {
        &mut self.contents.get_mut().1.0.get_mut().0
    }

    pub fn well_formed_str(&self, idx: usize) -> &str {
        self.info.well_formed_str(idx, self.instr().get())
    }

    pub fn end_position(&self) -> Position {
        if self.comment().is_empty() {
            Position::instr(self.instr().len())
        } else {
            Position::comment(self.comment().len())
        }
    }

    pub fn all_whitespace(&self) -> bool {
        self.instr().get().chars().all(|c| c.is_whitespace())
            && self.comment().get().chars().all(|c| c.is_whitespace())
    }

    pub fn position_to_absolute_offset(&self, pos: Position) -> Result<usize> {
        if pos.in_instr {
            if pos.offset > self.instr().len() {
                bail!("invalid instr offset");
            }
            Ok(pos.offset)
        } else {
            if pos.offset > self.comment().len() {
                bail!("invalid comment offset");
            }
            Ok(self.instr().len() + pos.offset)
        }
    }

    pub fn absolute_offset_to_position(&self, offset: usize) -> Result<Position> {
        if offset <= self.instr().len() {
            Ok(Position {
                in_instr: true,
                offset,
            })
        } else if offset <= self.instr().len() + self.comment().len() {
            Ok(Position {
                in_instr: false,
                offset: offset - self.instr().len(),
            })
        } else {
            bail!("invalid absolute offset");
        }
    }

    pub fn get_position(&self, node: NodeRef, offset: WebOffset) -> Result<Position> {
        let instr_end = Position::instr(self.instr().len());

        // If the position is in the top-level div element, the offset counts nodes
        // within the line.
        if node.is_same_node(&self.contents) {
            return Ok(match offset.u32() {
                0 => Position::begin(),
                1 => instr_end,
                _ => self.end_position(),
            });
        }

        // Position in instruction or comment text nodes.
        if node.is_same_node(self.instr()) {
            return Ok(Position::instr(self.instr().utf16_to_byte_idx(offset)?));
        } else if node.is_same_node(self.comment()) {
            return Ok(if offset.u32() == 0 {
                instr_end
            } else {
                Position::comment(self.comment().utf16_to_byte_idx(offset)?)
            });
        }

        // Position in the instruction or comment spans.
        if node.is_same_node(&self.contents.get().0) {
            return Ok(match offset.u32() {
                0 => Position::begin(),
                1 => instr_end,
                _ => bail!("unexpected instr span position {offset:?}"),
            });
        } else if node.is_same_node(&self.contents.get().1.0) {
            return Ok(match offset.u32() {
                0 => instr_end,
                1 => self.end_position(),
                _ => bail!("unexpected comment span position {offset:?}"),
            });
        } else if node.is_same_node(&self.contents.get().1.1.0) {
            return Ok(match offset.u32() {
                0 => self.end_position(),
                _ => bail!("unexpected debug span position {offset:?}"),
            });
        }

        bail!("position in unknown node");
    }

    fn class(&self) -> String {
        let prefix = if self.info.runtime_error.is_some() {
            "line runtime-error-line"
        } else if !self.info.is_active() {
            "line malformed-line"
        } else if self.info.invalid.is_some() {
            "line invalid-line"
        } else {
            match self.info.kind {
                LineKind::Malformed(_) => "line malformed-line",
                // a proof declaration erases to a comment but keeps its number
                LineKind::Empty if self.info.erased.is_some() => "line spec-line numbered-line",
                LineKind::Empty => "line",
                LineKind::Other(_) => "line meta-line numbered-line",
                LineKind::Instr(_) if self.is_proof_line() => {
                    "line instr-line spec-line numbered-line"
                }
                LineKind::Instr(_) => "line instr-line numbered-line",
            }
        }
        .to_string();
        let prefix = prefix
            + if self.info.proof.wide {
                " wide-line"
            } else {
                ""
            }
            + if self.info.proof.locked {
                " locked-line"
            } else {
                ""
            }
            + if self.info.proof.never {
                " never-runs"
            } else {
                ""
            }
            + if self.info.proof.explain.is_some() {
                " has-account"
            } else {
                ""
            }
            + if self.cursor { " cursor-line" } else { "" };

        use BrowserAnimation::*;
        fn ab(x: bool) -> &'static str {
            if x { "a" } else { "b" }
        }

        prefix
            + &match self.animation_state.browser_animation {
                Shake(x) => String::from(" shake-") + ab(x),
                Reveal(x) => String::from(" reveal-") + ab(x),
                FlyEnd(x) => String::from(" flyend-") + ab(x),
                Normal => String::new(),
            }
    }

    /// a line that is all proof (`prove`, `lemma`, `unfold`, `assume`): erased to `nop` or a comment
    pub fn is_proof_line(&self) -> bool {
        let t = self.instr().get().trim_start();
        self.info.erased.is_some()
            && ["prove", "lemma", "unfold", "assume"].iter().any(|k| {
                t.strip_prefix(k)
                    .is_some_and(|r| r.is_empty() || r.starts_with(char::is_whitespace))
            })
    }

    /// Install what the proof kernel says about this line.
    pub fn set_proof(&mut self, proof: crate::proof_view::LineProof) {
        if self.info.proof != proof {
            self.info.proof = proof;
            self.conform();
        }
    }

    /// Is this line counted in the gutter's line numbers?
    pub fn is_numbered(&self) -> bool {
        let c = self.class();
        c.contains("numbered-line")
            || c.contains("invalid-line")
            || c.contains("runtime-error-line")
    }

    pub fn shake(&mut self) {
        use BrowserAnimation::*;
        self.animation_state.browser_animation = match self.animation_state.browser_animation {
            Shake(false) => Shake(true),
            _ => Shake(false),
        };
        self.conform();
    }

    pub fn reveal(&mut self) {
        use BrowserAnimation::*;
        self.animation_state.browser_animation = match self.animation_state.browser_animation {
            Reveal(false) => Reveal(true),
            _ => Reveal(false),
        };
        self.conform();
    }

    pub fn fly_end(&mut self) {
        use BrowserAnimation::*;
        self.animation_state.browser_animation = match self.animation_state.browser_animation {
            FlyEnd(false) => FlyEnd(true),
            _ => FlyEnd(false),
        };
        self.conform();
    }

    pub fn new(contents: &str, factory: &ElementFactory) -> Self {
        let mut ret = Self {
            contents: LinePara::new(
                (
                    TextSpan::new((DomText::new(contents), ()), factory.span()),
                    (
                        TextSpan::new((DomText::default(), ()), factory.span()),
                        (
                            DomStruct::new((), factory.span()),
                            (DomBr::new((), factory.br()), ()),
                        ),
                    ),
                ),
                factory.div(),
            ),
            info: LineInfo::default(),
            animation_state: Default::default(),
            cursor: false,
        };

        ret.contents.get_mut().0.set_attribute("class", "instr");
        ret.contents.get_mut().1.0.set_attribute("class", "comment");
        ret.contents.get_mut().1.1.0.set_attribute("class", "debug");
        ret.conform_to_text().unwrap();

        ret
    }

    // Make the element presentation (CSS class) match the status.
    // This needs to happen when the active status changes.
    fn conform(&mut self) {
        // the commentary (cut short when long, so its full text is also the hover title)
        let commentary = if let Some(msg) = &self.info.runtime_error
            && !msg.is_empty()
        {
            Some(match &self.info.proof.note {
                // a stale-fact hint names the lines to look at: first, so a cut-short
                // commentary never loses them (review 20 D.2.5)
                Some(note) if note.contains(" is about the old ") => format!("{note} — {msg}"),
                Some(note) => format!("{msg} — {note}"),
                None => msg.to_string(),
            })
        } else if let LineKind::Malformed(reason) = &self.info.kind {
            Some(reason.to_string())
        } else if let Activity::Inactive(reason) = &self.info.active
            && !reason.is_empty()
        {
            Some(reason.to_string())
        } else if let Some(reason) = &self.info.invalid
            && !reason.is_empty()
        {
            Some(reason.to_string())
        } else if let Some((t, "reject")) = &self.info.proof.vnote {
            Some(t.clone())
        } else {
            self.info.proof.note.clone()
        };
        // a vericoding note (lock, mutant) or a quiet note (a runtime-checked cup) when there is
        // nothing darkred to say
        let vtone = match (&commentary, &self.info.proof.vnote) {
            (None, Some((_, tone))) => Some(*tone),
            (Some(_), Some((_, "reject"))) => Some("reject"),
            _ => None,
        };
        let quiet = if commentary.is_none() {
            match &self.info.proof.vnote {
                Some((t, _)) => Some(t.clone()),
                None => self.info.proof.quiet.clone(),
            }
        } else {
            None
        };
        let comment = &mut self.contents.get_mut().1.0;
        match commentary.as_ref().or(quiet.as_ref()) {
            Some(msg) => {
                comment.set_attribute("data-commentary", msg);
                comment.set_attribute("title", msg);
            }
            None => {
                comment.remove_attribute("data-commentary");
                comment.remove_attribute("title");
            }
        }
        // what the line's proof cups need and the facts it gives: always on, quiet, right of
        // the code, left of any commentary (both share the row and shrink, never overlapping)
        match &self.info.proof.label {
            Some(t) => {
                comment.set_attribute("data-label", t);
                // "show all proofs": the label and the reason in brief, under it
                match &self.info.proof.brief {
                    Some(b) => comment.set_attribute("data-label-all", &format!("{t}\n{b}")),
                    None => comment.set_attribute("data-label-all", t),
                }
            }
            None => {
                comment.remove_attribute("data-label");
                comment.remove_attribute("data-label-all");
            }
        }
        match vtone {
            Some(t) => comment.set_attribute("data-tone", t),
            None if quiet.is_some() => comment.set_attribute("data-tone", "quiet"),
            None => comment.remove_attribute("data-tone"),
        }
        // the account of the line's proofs, in the gap below the line, starting under the code
        // (shown for the cursor line, on hover, and under "show all proofs")
        let left = 70.0 + (indent_px(4 + self.info.indent.unwrap_or(0)) + LANE_PX) as f64;
        let acct = &mut self.contents.get_mut().1.1.0;
        match &self.info.proof.explain {
            Some(t) => {
                acct.set_attribute("data-why", t);
                acct.set_attribute("style", &format!("left: {left:.0}px;"));
            }
            None => {
                acct.remove_attribute("data-why");
                acct.remove_attribute("style");
            }
        }
        let instr = &mut self.contents.get_mut().0;
        match &self.info.proof.title {
            Some(t) => instr.set_attribute("title", t),
            None => instr.remove_attribute("title"),
        }
        match &self.info.proof.badge {
            Some((text, kind)) => {
                instr.set_attribute("data-badge", text);
                instr.set_attribute("data-badge-kind", kind);
            }
            None => {
                instr.remove_attribute("data-badge");
                instr.remove_attribute("data-badge-kind");
            }
        }
        // the fact lane left of the code: hovering the row's margin reads the chips there
        match &self.info.proof.lane {
            Some(t) => self.contents.set_attribute("title", t),
            None => self.contents.remove_attribute("title"),
        }

        self.contents.set_attribute("class", &self.class());
    }

    // Make the instr/comment split, the kind, and the CSS presentation consistent with the text contents.
    // This needs to happen when the text changes. Returns number of whitespace bytes trimmed from start.
    fn conform_to_text(&mut self) -> Result<usize> {
        // Re-split text nodes at beginning of line comment (if any)
        match find_comment(self.instr().get(), self.comment().get()) {
            None if self.comment().is_empty() => {}
            None => {
                let comment = self.comment_mut().take();
                self.instr_mut().push_str(&comment);
            }
            Some(x) if x == self.instr().len() => {}
            Some(x) => {
                let concat = self.instr().get().to_owned() + self.comment().get();
                self.instr_mut().set_data(&concat[0..x]);
                self.comment_mut().set_data(&concat[x..]);
            }
        }
        // Trim whitespace at front of instruction
        let ws_bytes = self.instr().len()
            - self
                .instr()
                .get()
                .trim_start_matches(|x: char| x.is_whitespace() && x != '\n')
                .len();
        if ws_bytes != 0 {
            self.instr_mut().replace_range(0, ws_bytes, "")?;
        }
        // Update kind, symbols, commentary, and active status
        // (the annotation, if any, is for a proof kernel; none is wired in yet)
        let (kind, annotation) = parse_line_spec(self.instr().get());
        self.info.kind = kind;
        self.info.erased = annotation.map(|LineAnnotation::Erased(e)| e);
        let text = self
            .info
            .erased
            .clone()
            .unwrap_or_else(|| self.instr().get().to_string());
        self.info.symbols = parse_line_symbols(&text, &self.info.kind);
        self.conform();
        Ok(ws_bytes)
    }

    /// Set the line's erased text from the whole-document v2 erasure (lemma bodies and fact
    /// handles erase by context), re-classifying the line if it changed.
    pub fn set_erasure(&mut self, erased: Option<String>) {
        if self.info.erased == erased {
            return;
        }
        let text = erased
            .clone()
            .unwrap_or_else(|| self.instr().get().to_string());
        self.info.erased = erased;
        self.info.kind = crate::syntax::parse_line_spec(&text).0;
        self.info.symbols = parse_line_symbols(&text, &self.info.kind);
        self.conform();
    }

    // Activate or deactivate the line.
    pub fn set_active_status(&mut self, new_val: Activity) {
        if new_val != self.info.active {
            self.info.active = new_val;
            self.conform();
        }
    }

    pub fn set_synthetic_before(&mut self, synth: SyntheticWasm) {
        if !synth.module_field_syntax.is_empty() {
            self.contents
                .get_mut()
                .0
                .set_attribute("data-synthetic-before", &synth.render_module_field_syntax());
        } else {
            self.contents
                .get_mut()
                .0
                .remove_attribute("data-synthetic-before");
        }

        self.info.synthetic_before = synth;
        self.conform();
    }

    pub fn suffix(&self, pos: Position) -> Result<String> {
        Ok(match pos.in_instr {
            true => String::from(self.instr().suffix(pos.offset)) + self.comment().get(),
            false => self.comment().suffix(pos.offset).to_string(),
        })
    }

    pub fn first_newline(&self) -> Option<Position> {
        if let Some(idx) = self.instr().get().find('\n') {
            Some(Position::instr(idx))
        } else {
            self.comment().get().find('\n').map(Position::comment)
        }
    }

    // Modify the contents. This calls replace_range on one of the inner DomTexts (or both), then
    // makes the comment split, kind, and CSS presentation consistent with the new contents.
    pub fn replace_range(
        &mut self,
        mut a: Position,
        b: Position,
        mut string: &str,
    ) -> Result<Position> {
        // Special-case the creation or deletion of the comment separator (";;").
        if a == b && a.in_instr && string == ";" {
            string = ";;"; // type the whole ";;" separator on one ";" keystroke
        } else if a == b
            && b == Position::comment(2)
            && self.comment().get().starts_with(";;")
            && string == ";"
        {
            string = ""; // if user types two ";" characters, give them two total (ignore second one)
        } else if a == Position::comment(1)
            && b == Position::comment(2)
            && string.is_empty()
            && self.comment().get().starts_with(";;")
        {
            a = Position::comment(0); // if user deletes from end of ";;", delete both
        }

        // Do the replacement in the appropriate components (text or comment).
        let mut total_pos = match (a.in_instr, b.in_instr) {
            (true, true) => self.instr_mut().replace_range(a.offset, b.offset, string)?,
            (false, false) => {
                self.instr().len()
                    + self
                        .comment_mut()
                        .replace_range(a.offset, b.offset, string)?
            }
            (true, false) => {
                self.comment_mut().replace_range(0, b.offset, "")?;
                let instr_len = self.instr().len();
                self.instr_mut()
                    .replace_range(a.offset, instr_len, string)?
            }
            (false, true) => bail!("unhandled comment -> instr range"),
        };

        total_pos = total_pos.saturating_sub(self.conform_to_text()?);

        Ok(if total_pos <= self.instr().len() {
            Position::instr(total_pos)
        } else {
            let comment_pos = total_pos - self.instr().len();
            debug_assert!(comment_pos <= self.comment().len());
            Position::comment(comment_pos)
        })
    }

    pub fn set_cursor_position(&self, pos: Position) -> Result<()> {
        let (node, offset) = self.position_to_node_and_weboffset(pos)?;
        set_selection_range(node, offset, node, offset);
        self.contents.scroll_into_view();
        Ok(())
    }

    pub fn info(&self) -> &LineInfo {
        &self.info
    }

    pub fn id(&self) -> u32 {
        self.info.id
    }

    pub fn swap_ids(&mut self, other: &mut CodeLine) {
        swap(&mut self.info.id, &mut other.info.id);
    }

    pub fn position_to_node_and_weboffset(&self, pos: Position) -> Result<(&DomText, WebOffset)> {
        Ok(match pos.in_instr {
            true => (self.instr(), self.instr().byte_idx_to_utf16(pos.offset)?),
            false => (
                self.comment(),
                self.comment().byte_idx_to_utf16(pos.offset)?,
            ),
        })
    }

    pub fn animated_indent(&self) -> Option<f64> {
        self.animation_state.indent.value()
    }

    // Returns whether future animation is desired
    pub fn set_indent(&mut self, val: u16) -> AnimationRequest {
        if let Some(cur_indent) = self.info.indent
            && !self.all_whitespace()
            && (cur_indent != val || self.animation_state.indent.is_pending().0)
        {
            // animate change
            self.animation_state
                .indent
                .approach((indent_px(4 + val) + LANE_PX) as f64);
            let moved = self.info.indent != Some(val);
            self.info.indent = Some(val);
            if moved && self.info.proof.explain.is_some() {
                self.conform();
            }
            return AnimationRequest(true);
        }

        // otherwise, snap change
        self.info.indent = Some(val);
        self.animation_state
            .indent
            .snap((indent_px(4 + val) + LANE_PX) as f64);
        self.contents.get_mut().0.set_attribute(
            "style",
            &format!(
                "margin-left: {}px;",
                self.animation_state.indent.value().unwrap()
            ),
        );
        if self.info.proof.explain.is_some() {
            self.conform();
        }
        AnimationRequest(false)
    }

    pub fn unset_indent(&mut self) {
        self.info.indent = None;
        self.animation_state.indent = Default::default();
    }

    pub fn animate(&mut self, t: f64) -> AnimationRequest {
        self.animation_state.indent.animate(t);
        self.contents.get_mut().0.set_attribute(
            "style",
            &format!(
                "margin-left: {}px;",
                self.animation_state.indent.value().unwrap()
            ),
        );

        self.animation_state.indent.is_pending()
    }

    pub fn set_invalid(&mut self, reason: Option<String>) {
        if let Some(ref reason) = reason
            && (reason.starts_with("type mismatch: expected ")
                || reason.starts_with("type mismatch: values remaining"))
        {
            // ignore; UI shows visually
            self.info.invalid = Some(String::new());
        } else {
            self.info.invalid = reason;
        }
        self.conform();
    }

    pub fn set_runtime_error(&mut self, msg: Option<String>) {
        self.info.runtime_error = msg;
        self.conform();
    }

    pub fn set_type_annotation(&mut self, value: Option<&String>) {
        if let Some(text) = value {
            self.contents.get_mut().0.set_attribute("data-debug", text);
        } else {
            self.contents.get_mut().0.remove_attribute("data-debug");
        }
    }

    pub fn set_debug_annotation(&mut self, value: Option<&String>) {
        if let Some(text) = value {
            self.contents
                .get_mut()
                .1
                .1
                .0
                .set_attribute("data-debug", text);
        } else {
            self.contents.get_mut().1.1.0.remove_attribute("data-debug");
        }
    }

    /// Mark this line as the caret's line (its proof account shows below it).
    pub fn set_cursor(&mut self, on: bool) {
        if self.cursor != on {
            self.cursor = on;
            self.conform();
        }
    }

    pub fn set_highlight(&mut self, add_highlight: bool) {
        if add_highlight {
            self.contents.get_mut().0.set_attribute("highlight", "");
        } else {
            self.contents.get_mut().0.remove_attribute("highlight");
        }
    }
}
