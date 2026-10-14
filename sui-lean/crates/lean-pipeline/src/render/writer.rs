//! Line-based writer for generating Lean source.
//!
//! Tracks indentation; each call to [`LeanWriter::write`] inserts the
//! current indent prefix at line starts. Two convenience modes:
//!
//! - multi-line (default): emits real newlines + indent.
//! - inline (via [`LeanWriter::new_inline`]): collapses newlines to `; `,
//!   never indents. Used for one-liner snapshots.
//!
//! Lifted with minor adaptations from the legacy
//! `move-prover-lean-backend::renderer::lean_writer`.

use std::fmt::Write;

pub struct LeanWriter<W: Write> {
    out: W,
    indent: usize,
    at_line_start: bool,
    inline: bool,
}

impl<W: Write> LeanWriter<W> {
    pub fn new(out: W) -> Self {
        Self {
            out,
            indent: 0,
            at_line_start: true,
            inline: false,
        }
    }

    /// Write `s`, expanding newlines to indented or inline output.
    pub fn write(&mut self, s: &str) {
        for c in s.chars() {
            if c == '\n' {
                if self.inline {
                    write!(self.out, "; ").unwrap();
                    self.at_line_start = false;
                } else {
                    writeln!(self.out).unwrap();
                    self.at_line_start = true;
                }
            } else {
                if self.at_line_start && !self.inline {
                    for _ in 0..self.indent {
                        write!(self.out, "  ").unwrap();
                    }
                }
                self.at_line_start = false;
                write!(self.out, "{}", c).unwrap();
            }
        }
    }

    /// Write `s` followed by a newline.
    pub fn line(&mut self, s: &str) {
        self.write(s);
        self.write("\n");
    }

    /// Increase indentation. `newline=true` emits a newline first
    /// (block-start convention).
    pub fn indent(&mut self, newline: bool) {
        if newline {
            self.write("\n");
        }
        if !self.inline {
            self.indent += 1;
        }
    }

    /// Decrease indentation. `newline=true` emits a newline after.
    pub fn dedent(&mut self, newline: bool) {
        if !self.inline && self.indent > 0 {
            self.indent -= 1;
        }
        if newline {
            self.write("\n");
        }
    }

    pub fn newline(&mut self) {
        self.write("\n");
    }

    pub fn into_inner(self) -> W {
        self.out
    }
}

/// Render to a `String` using multi-line mode.
pub fn render_to_string<F>(f: F) -> String
where
    F: FnOnce(&mut LeanWriter<String>),
{
    let mut writer = LeanWriter::new(String::new());
    f(&mut writer);
    writer.into_inner()
}
