//! Loading and validating Wycheproof test vector files.
//!
//! A test vector file is loaded as a [`TestFile`], parameterized by the
//! algorithm-specific fields of its test groups (`P`) and of its tests
//! (`T`). Algorithm tests declare structs for those fields and iterate over
//! [`TestFile::tests`]; loading checks that the file is internally
//! consistent, so a test can never silently run on fewer vectors than the
//! file contains.

// Each algorithm test module uses a different subset of the harness.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashSet};
use std::path::{Path, PathBuf};

use serde::Deserialize;
use serde::de::DeserializeOwned;

/// The environment variable pointing at a checkout of
/// <https://github.com/C2SP/wycheproof>. A relative path is relative to the
/// crate root.
pub const ROOT_VAR: &str = "WYCHEPROOF_ROOT";

/// The directory containing the Wycheproof test vectors, or `None` if
/// `WYCHEPROOF_ROOT` is not set (the tests are then skipped).
pub fn vectors_dir() -> Option<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join(std::env::var_os(ROOT_VAR)?);
    let dir = root.join("testvectors_v1");
    assert!(dir.is_dir());
    Some(dir)
}

/// Every test vector file, sorted by name; `None` if the vectors are not
/// available.
pub fn all_files() -> Option<Vec<String>> {
    let mut names: Vec<String> = std::fs::read_dir(vectors_dir()?)
        .expect("reading the Wycheproof directory")
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.ends_with(".json"))
        .collect();
    names.sort();
    Some(names)
}

/// Skip the calling test (by returning early) if the vectors are not available.
#[macro_export]
macro_rules! require_vectors {
    () => {
        if $crate::harness::vectors_dir().is_none() {
            eprintln!(
                "skipping: set {} to a checkout of https://github.com/C2SP/wycheproof",
                $crate::harness::ROOT_VAR
            );
            return;
        }
    };
}

/// The expected outcome of a test.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Expectation {
    /// The operation must succeed with the given result.
    Valid,
    /// The operation must fail (or the result must be rejected).
    Invalid,
    /// Either outcome is allowed; the test's `flags` say why.
    Acceptable,
}

/// A note describing a test flag.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Note {
    /// The class of bug the flagged tests look for.
    pub bug_type: Option<String>,
    /// A description of the flag.
    pub description: Option<String>,
}

/// One test.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Test<T> {
    /// The test's id, unique within the file.
    pub tc_id: u64,
    #[serde(default)]
    pub comment: String,
    /// Usually keys into [`TestFile::notes`].
    #[serde(default)]
    pub flags: Vec<String>,
    pub result: Expectation,
    /// The algorithm-specific fields.
    #[serde(flatten)]
    pub case: T,
}

/// A group of tests sharing parameters (key, sizes, …).
#[derive(Debug, Clone, Deserialize)]
pub struct TestGroup<P, T> {
    /// The algorithm-specific group fields.
    #[serde(flatten)]
    pub params: P,
    pub tests: Vec<Test<T>>,
}

/// A test vector file.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TestFile<P, T> {
    pub algorithm: Option<String>,
    pub schema: String,
    pub number_of_tests: usize,
    #[serde(default)]
    pub notes: BTreeMap<String, Note>,
    pub test_groups: Vec<TestGroup<P, T>>,
}

/// Untyped fields, for tests that only look at the file structure.
pub type Fields = serde_json::Map<String, serde_json::Value>;

impl<P, T> TestFile<P, T> {
    /// Every test, with its group.
    pub fn tests(&self) -> impl Iterator<Item = (&TestGroup<P, T>, &Test<T>)> {
        self.test_groups
            .iter()
            .flat_map(|g| g.tests.iter().map(move |t| (g, t)))
    }
}

/// Parse a test vector file and check that it is internally consistent:
/// the number of tests matches `numberOfTests` and test ids are unique.
/// (Not every flag is described in `notes` upstream, so that is not checked.)
pub fn parse<P: DeserializeOwned, T: DeserializeOwned>(name: &str, json: &str) -> TestFile<P, T> {
    let file: TestFile<P, T> = serde_json::from_str(json).unwrap_or_else(|e| panic!("{name}: {e}"));
    let mut ids = HashSet::new();
    let mut count = 0;
    for (_, t) in file.tests() {
        count += 1;
        assert!(ids.insert(t.tc_id), "{name}: duplicate tcId {}", t.tc_id);
    }
    assert_eq!(count, file.number_of_tests, "{name}: numberOfTests");
    file
}

/// Load and validate the test vector file `name` (e.g. `"aes_gcm_test.json"`).
/// Tests calling this must start with `require_vectors!()`.
pub fn load<P: DeserializeOwned, T: DeserializeOwned>(name: &str) -> TestFile<P, T> {
    let path = vectors_dir()
        .expect("Wycheproof vectors not available; use require_vectors!()")
        .join(name);
    let json = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
    parse(name, &json)
}
