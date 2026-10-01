import VerifiedGarbage.Proof.Argon2.HPrime

/-! # H₀ as a sequence of BLAKE2b streaming inputs -/

namespace VG.Proof.Argon2

open VG.Spec.Argon2

def initialHeader (p : Params) : List Byte :=
  le32 p.lanes ++ le32 p.tagLen ++ le32 p.memory ++ le32 p.passes ++
    le32 0x13 ++ le32 p.variant.code

def appendInput (before input : List Byte) : List Byte :=
  before ++ le32 input.length ++ input

def initialInput (p : Params) (password salt secret ad : List Byte) : List Byte :=
  appendInput (appendInput (appendInput (appendInput (initialHeader p) password) salt) secret) ad

theorem le32_length (n : Nat) : (le32 n).length = 4 := by
  simp only [le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]

theorem initialHeader_length (p : Params) : (initialHeader p).length = 24 := by
  simp only [initialHeader, List.length_append, le32_length]

theorem appendInput_length (before input : List Byte) :
    (appendInput before input).length = before.length + 4 + input.length := by
  simp only [appendInput, List.length_append, le32_length]

theorem initialInput_length (p : Params) (password salt secret ad : List Byte) :
    (initialInput p password salt secret ad).length =
      40 + password.length + salt.length + secret.length + ad.length := by
  simp only [initialInput, appendInput_length, initialHeader_length]
  omega

theorem initialInput_bound (p : Params) (password salt secret ad : List Byte)
    (hp : password.length < 2 ^ 32) (hs : salt.length < 2 ^ 32)
    (hk : secret.length < 2 ^ 32) (ha : ad.length < 2 ^ 32) :
    (initialInput p password salt secret ad).length < 2 ^ 64 := by
  rw [initialInput_length]
  omega

theorem initialHash_eq (p : Params) (password salt secret ad : List Byte) :
    initialHash p password salt secret ad = H 64 (initialInput p password salt secret ad) := rfl

theorem initialHash_stream (p : Params) (password salt secret ad : List Byte) :
    initialHash p password salt secret ad =
      (Spec.Blake2.finalHash Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b 64 0)
        (initialInput p password salt secret ad)).take 64 := by
  rw [initialHash_eq, H_stream]

theorem initialHash_length (p : Params) (password salt secret ad : List Byte) :
    (initialHash p password salt secret ad).length = 64 :=
  H_length 64 _ (by decide)

end VG.Proof.Argon2
