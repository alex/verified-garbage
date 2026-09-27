//! Wycheproof (<https://github.com/C2SP/wycheproof>) tests.
//!
//! Every algorithm gets a module here that loads its test vector files with
//! [`harness::load`] and checks each vector against the crate's public API.
//! A `valid` vector must produce exactly the expected result, an `invalid`
//! one must be rejected, and for an `acceptable` one either outcome is fine
//! (but a result, if produced, must be the expected one).

mod harness;

use harness::{Expectation, Fields, Hex};

/// Every test vector file parses, and is internally consistent. This keeps
/// the harness honest as the vendored vectors are updated.
#[test]
fn all_vector_files_are_well_formed() {
    let files = harness::all_files();
    assert!(!files.is_empty());
    for name in &files {
        let file = harness::load::<Fields, Fields>(name);
        assert!(!file.schema.is_empty(), "{name}: missing schema");
    }
}

#[test]
fn harness_parses_typed_vectors() {
    #[derive(serde::Deserialize)]
    struct Group {
        #[serde(rename = "keySize")]
        key_size: usize,
    }
    #[derive(serde::Deserialize)]
    struct Case {
        key: Hex,
        msg: Hex,
    }
    let json = r#"{
        "algorithm": "EXAMPLE", "schema": "example_schema.json", "numberOfTests": 2,
        "notes": {"Edge": {"bugType": "EDGE_CASE", "description": "an edge case"}},
        "testGroups": [{"keySize": 16, "type": "Example", "tests": [
            {"tcId": 1, "comment": "", "flags": [], "key": "000102", "msg": "", "result": "valid"},
            {"tcId": 2, "flags": ["Edge"], "key": "ff", "msg": "AbCd", "result": "acceptable"}
        ]}]
    }"#;
    let file = harness::parse::<Group, Case>("example", json);
    let tests: Vec<_> = file.tests().collect();
    assert_eq!(tests.len(), 2);
    let (g, t) = tests[1];
    assert_eq!(g.params.key_size, 16);
    assert_eq!(t.result, Expectation::Acceptable);
    assert_eq!(t.flags, ["Edge"]);
    assert_eq!(*t.case.key, [0xff]);
    assert_eq!(*t.case.msg, [0xab, 0xcd]);
    assert_eq!(*tests[0].1.case.key, [0, 1, 2]);
    assert!(tests[0].1.case.msg.is_empty());
}

#[test]
#[should_panic(expected = "numberOfTests")]
fn harness_rejects_wrong_test_count() {
    let json = r#"{"schema": "s", "numberOfTests": 2, "testGroups": [
        {"tests": [{"tcId": 1, "result": "valid"}]}]}"#;
    harness::parse::<Fields, Fields>("example", json);
}

#[test]
#[should_panic(expected = "duplicate tcId")]
fn harness_rejects_duplicate_ids() {
    let json = r#"{"schema": "s", "numberOfTests": 2, "testGroups": [
        {"tests": [{"tcId": 1, "result": "valid"}, {"tcId": 1, "result": "invalid"}]}]}"#;
    harness::parse::<Fields, Fields>("example", json);
}
