import VerifiedGarbage.TCB.Mem

/-!
# RC4 (ARCFOUR)

**Trusted.** Key scheduling and stream generation are transcribed from
draft-kaukonen-cipher-arcfour-03 §§3.1–3.2
(https://www.ietf.org/archive/id/draft-kaukonen-cipher-arcfour-03.txt).
This expired Internet-Draft describes the algorithm; it is not an IETF
standard. RFC 6229 supplies independent published known answers.

The API accepts 1–256 key bytes, the nonempty keys that fit the 256-byte
key-scheduling cycle; longer keys are rejected, not truncated. Indices and
table entries are bytes, so additions wrap modulo 256. The PRGA starts
with both indices zero, independently of the KSA's final index.

This is raw RC4: no nonce, padding, authentication or automatic stream
discard. Encryption and decryption are the same XOR operation. Updates
consume exactly their input length and preserve the next stream position;
finalization emits nothing. These are value definitions, not permission
to leak table indices: key bytes, the permutation and `j` remain secret.
RC4 is obsolete and insecure (see RFC 6229 §3 and RFC 7465).
-/

namespace VG.Spec.Rc4

abbrev Table := Vector Byte 256

structure Context where
  table : Table
  i : Byte
  j : Byte
  deriving DecidableEq

/-- Swap from the original table, including when the indices coincide. -/
def swap (s : Table) (i j : Byte) : Table :=
  (s.set! i.toNat (s.getD j.toNat 0)).set! j.toNat (s.getD i.toNat 0)

/-- §3.1: identity permutation, then 256 sequential key-scheduling swaps.
Total for all lists; `init` accepts only nonempty keys of at most 256 bytes. -/
def keySchedule (key : List Byte) : Table := Id.run do
  let mut s : Table := Vector.ofFn fun i => BitVec.ofNat 8 i.val
  let mut j : Byte := 0
  for i in List.range 256 do
    j := j + s.getD i 0 + key.getD (i % key.length) 0
    s := swap s (BitVec.ofNat 8 i) j
  return s

inductive Error | invalidKeyLength
  deriving DecidableEq, Repr

/-- §3.1: schedule the key and reset both stream indices to zero. -/
def init (key : List Byte) : Except Error Context :=
  if 1 ≤ key.length ∧ key.length ≤ 256 then
    .ok { table := keySchedule key, i := 0, j := 0 }
  else .error .invalidKeyLength

/-- §3.2: advance the indices, swap, then read from the updated table. -/
def step (ctx : Context) : Context × Byte :=
  let i := ctx.i + 1
  let j := ctx.j + ctx.table.getD i.toNat 0
  let s := swap ctx.table i j
  ({ table := s, i, j }, s.getD ((s.getD i.toNat 0 + s.getD j.toNat 0).toNat) 0)

/-- XOR each input byte with the next PRGA byte. Empty updates preserve
the entire context; no byte is buffered between calls. -/
def update (ctx : Context) : List Byte → Context × List Byte
  | [] => (ctx, [])
  | b :: bs =>
    let (next, k) := step ctx
    let (last, rest) := update next bs
    (last, (b ^^^ k) :: rest)

/-- Raw RC4 has no final block or tag. The Rust API may consume its context. -/
def finalize (_ctx : Context) : List Byte := []

/-! ## Byte-oriented memory layout, shared by all targets -/

def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- A 258-byte context: the 256-byte table, then the PRGA indices `i`, `j`.
There is no target-dependent word encoding or padding. -/
def contextAt (m : Mem) (p : Addr) : Context where
  table := Vector.ofFn fun i => m (p + BitVec.ofNat 64 i.val)
  i := m (p + 256)
  j := m (p + 257)

end VG.Spec.Rc4
