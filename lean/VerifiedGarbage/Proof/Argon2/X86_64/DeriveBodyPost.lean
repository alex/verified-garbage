import VerifiedGarbage.Proof.Argon2.X86_64.DeriveInputBytes

/-! The complete body's digest is the public API postcondition on original input memory. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_done_post {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    (Spec.Argon2.deriveContract X86_64.abi 344).post s u := by
  have words := private_words h prepared
  have password := private_input_bytes h prepared (104, 96) (by decide)
  have salt := private_input_bytes h prepared (88, 80) (by decide)
  have secret := private_input_bytes h prepared (200, 208) (by decide)
  have ad := private_input_bytes h prepared (216, 224) (by decide)
  change Initial.inputBytes t 104 96 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 104) (Initial.wordAt t 96).toNat at password
  change Initial.inputBytes t 88 80 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 88) (Initial.wordAt t 80).toNat at salt
  change Initial.inputBytes t 200 208 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 200) (Initial.wordAt t 208).toNat at secret
  change Initial.inputBytes t 216 224 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 216) (Initial.wordAt t 224).toNat at ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  have digest := done.digest
  change Spec.Blake2.bytesAt u.mem (Initial.wordAt t 256) (abiParams s).tagLen =
    Spec.Argon2.derive (abiParams s) (Initial.inputBytes t 104 96)
      (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) at digest
  rw [words.output, password, salt, secret, ad] at digest
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  exact digest

end VG.Proof.Argon2.X86_64.Derive
