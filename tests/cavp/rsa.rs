//! The RSADP component vectors of SP 800-56B (vectors/nist-cavp-rsadp/),
//! as RSAEP: each passing vector's `k` encrypts to its `c`, and each failing
//! vector's `c` is not below its modulus.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use verified_garbage::rsa::{Error, PublicKey};

use super::unhex;

#[test]
fn rsadp_component() {
    let text = include_str!("../../vectors/nist-cavp-rsadp/RSADPComponent800_56B.rsp");
    let (mut pass, mut fail) = (0, 0);
    for v in text.split("COUNT = ").skip(1) {
        let field = |name: &str| {
            v.lines()
                .find_map(|l| l.split_once(" = ").filter(|(k, _)| k.trim() == name))
                .map(|(_, x)| x.trim())
        };
        let n = unhex(field("n").unwrap());
        // NIST writes the exponent as a number, in an odd number of digits
        // when its top byte is below 0x10.
        let e = field("e").unwrap();
        let e = unhex(&format!("{}{e}", "0".repeat(e.len() % 2)));
        let c = unhex(field("c").unwrap());
        let key = PublicKey::new(&n, &e).unwrap();
        let mut out = vec![0xa5; n.len()];
        if field("Result") == Some("Pass") {
            let k = unhex(field("k").unwrap());
            key.public_op(&k, &mut out).unwrap();
            assert_eq!(out, c);
            pass += 1;
        } else {
            assert_eq!(field("Result"), Some("Fail"));
            assert_eq!(key.public_op(&c, &mut out), Err(Error::InputOutOfRange));
            assert_eq!(out, vec![0; n.len()]);
            fail += 1;
        }
    }
    assert_eq!((pass, fail), (40, 20));
}
