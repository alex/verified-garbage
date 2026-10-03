//! The test vectors of RFC 8439: ChaCha20's block function and encryption
//! (§2.3.2, §2.4.2, Appendices A.1 and A.2) and its Poly1305 key generation
//! (§2.6.2, Appendix A.4), Poly1305 (Appendix A.3) and ChaCha20-Poly1305
//! (§2.8.2, Appendix A.5).
//!
//! The RFC is vendored under `vectors/rfc8439/` (see
//! `vectors/sources/rfc8439.toml` for where it comes from) and compiled into
//! the test binary, so these tests always run. Each value is read from the
//! RFC's text: the rows of hex after its label, or the `name = value` of a
//! line.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]

mod chacha20;
mod chacha20poly1305;
mod poly1305;

const TEXT: &str = include_str!("../../vectors/rfc8439/rfc8439.txt");

/// A test vector: the lines of its text that are not rows of hex, each with
/// the bytes of the rows of hex that follow it (none if it is not the label
/// of a value).
struct Vector(Vec<(&'static str, Vec<u8>)>);

impl Vector {
    /// Whether the vector has a line `label` (with or without colons after
    /// it). Only the Poly1305 vectors need it.
    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86"
    ))]
    fn has(&self, label: &str) -> bool {
        self.0.iter().any(|(l, _)| l.trim_end_matches(':') == label)
    }

    /// The value labelled `label` (with or without colons after it).
    fn get(&self, label: &str) -> &[u8] {
        let mut values = self
            .0
            .iter()
            .filter(|(l, _)| l.trim_end_matches(':') == label);
        let (_, value) = values.next().unwrap();
        assert!(values.next().is_none(), "{label} is not unique");
        assert!(!value.is_empty(), "{label} has no value");
        value
    }

    /// The text after `name = ` on the line starting with `name`, and on the
    /// lines after it while the value is a list of bytes ending with `:`.
    fn assignment(&self, name: &str) -> String {
        let prefix = format!("{name} = ");
        let start = self.0.iter().position(|(l, _)| l.starts_with(&prefix));
        let mut lines = self.0[start.unwrap()..].iter().map(|(l, _)| *l);
        let mut text = lines.next().unwrap()[prefix.len()..].to_string();
        while text.ends_with(':') {
            text.push_str(lines.next().unwrap());
        }
        text
    }

    /// The bytes `name = xx:xx:…` or `name = (xx:xx:…)` of a bulleted
    /// list (§2.3.2, §2.4.2), up to the `.` or `)` after them.
    fn bytes(&self, name: &str) -> Vec<u8> {
        let text = self.assignment(&format!("o  {name}"));
        let text = text.trim_start_matches('(');
        let text = text.split(['.', ')']).next().unwrap();
        text.split(':').map(|b| byte(b).unwrap()).collect()
    }

    /// The decimal number `name = n`, which may be followed by a `.`.
    fn number(&self, name: &str) -> u32 {
        self.assignment(name).trim_end_matches('.').parse().unwrap()
    }
}

/// The test vectors of the section from the line starting with `from` to the
/// next one starting with `to`: one for each `Test Vector #…` in it (ignoring
/// the text before the first), or the whole section if it has none. Blank
/// lines, `====` underlines and page breaks are skipped, so a value continues
/// on the next page.
fn vectors(from: &str, to: &str) -> Vec<Vector> {
    let lines = TEXT
        .lines()
        .skip_while(|l| !l.starts_with(from))
        .take_while(|l| !l.starts_with(to))
        .map(str::trim)
        .filter(|l| {
            !(l.is_empty()
                || l.starts_with("===")
                || l.starts_with("Nir & Langley ")
                || l.starts_with("RFC 8439 "))
        });
    let mut vectors = vec![Vector(Vec::new())];
    for line in lines {
        if line.starts_with("Test Vector #") {
            vectors.push(Vector(Vec::new()));
        }
        let lines = &mut vectors.last_mut().unwrap().0;
        match hex_row(line) {
            Some(row) => lines.last_mut().unwrap().1.extend(row),
            None => lines.push((line, Vec::new())),
        }
    }
    if vectors.len() > 1 {
        vectors.remove(0);
    }
    vectors
}

/// The bytes of a row of hex: a hex dump row (`000  00 01 …  ascii`), 16
/// bytes separated by spaces (`FF FF …`) or bytes separated by colons
/// (`22:4f:…`, with or without one at the end).
fn hex_row(line: &str) -> Option<Vec<u8>> {
    dump_row(line).or_else(|| plain_row(line)).or_else(|| {
        let bytes: Option<Vec<u8>> = line.trim_end_matches(':').split(':').map(byte).collect();
        bytes.filter(|b| b.len() > 1)
    })
}

/// The bytes of a hex dump row (`000  00 01 …  ascii`): the offset, then up
/// to 16 bytes in the 47 columns before the text.
fn dump_row(line: &str) -> Option<Vec<u8>> {
    let (offset, rest) = line.split_at_checked(3)?;
    if !offset.bytes().all(|b| b.is_ascii_digit()) || !rest.starts_with("  ") {
        return None;
    }
    let hex = rest[2..].get(..47).unwrap_or(&rest[2..]);
    hex.split_whitespace().map(byte).collect()
}

/// The bytes of a row of 16 bytes in hex (`FF FF …`).
fn plain_row(line: &str) -> Option<Vec<u8>> {
    let bytes: Option<Vec<u8>> = line.split_whitespace().map(byte).collect();
    bytes.filter(|b| b.len() == 16)
}

fn byte(s: &str) -> Option<u8> {
    (s.len() == 2).then(|| u8::from_str_radix(s, 16).ok())?
}
