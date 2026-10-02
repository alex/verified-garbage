import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic

/-!
# PBKDF2-HMAC over a Merkle–Damgård hash function: one step as two compressions

For a key `K₀` of one block, both hashes of HMAC of a `D`-byte `U` are of `B +
D`-byte messages: a block (`K₀ ⊕ ipad` or `K₀ ⊕ opad`) whose compression is
the hash value of the streaming state `init` leaves, then `D` bytes, which the
padding (`pad`) completes to a second block (`block`). So a step of PBKDF2's
iteration is two compressions (`step`), for any hash function the streaming
proofs describe (`Md`), whatever the target. `Link` is what ties a hash
function of the specification (`StreamingHash`) to its `Md`. HMAC's outer
hash, of a key's outer block and an inner digest, is likewise one compression
(`Link.hash_block`), which HMAC's `finalize` computes.
-/

namespace VG.Proof.MdStream.Md

open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

variable {B N L : Nat} (H : Md B N L)

/-- The padding of a `B + D`-byte message after its last `D` bytes: `0x80`,
zeros, and the length field. -/
def tailPad (D : Nat) : List Byte := [0x80] ++ List.replicate (B - L - 1 - D) 0 ++ H.lenBytes (B + D)

theorem tailPad_length {D : Nat} (h : D + L < B) : (H.tailPad D).length = B - D := by
  simp only [tailPad, List.length_append, List.length_singleton, List.length_replicate, H.lenBytes_length]
  omega

/-- The start of the padding. -/
theorem tailPad_take {D n : Nat} (h₁ : 0 < n) (h₂ : D + n + L ≤ B) :
    (H.tailPad D).take n = [0x80] ++ List.replicate (n - 1) 0 := by
  have hr : (List.replicate (B - L - 1 - D) (0 : Byte)).take (n - 1) = List.replicate (n - 1) 0 := by
    rw [List.take_replicate, Nat.min_eq_left (by omega)]
  rw [tailPad, List.take_append_of_le_length (by simp; omega), List.take_append, List.length_singleton, hr,
    List.take_of_length_le (by simp; omega)]

/-- The last block of a `B + D`-byte message whose last `D` bytes are `x`. -/
def tailBlock (D : Nat) (x : List Byte) : H.Blk := H.parse fun t => (x ++ H.tailPad D).getD t 0

/-- The block in memory at `p`, of `D` bytes of message and the padding after
them. -/
theorem blockAt_eq {D : Nat} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 D) (B - D) = H.tailPad D) :
    H.blockAt m p = H.tailBlock D (Spec.Sha256.bytesAt m p D) := by
  simp only [blockAt, tailBlock]
  refine H.parse_congr fun k hk => ?_
  have e := Hmac.Common.bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, Hmac.Common.bytesAt_getD' _ _ hk]

/-- A `B + D`-byte message is hashed with one more compression. -/
theorem hash_block (iv : H.HV) {p x : List Byte} {D : Nat} (hp : p.length = B) (hx : x.length = D)
    (h : D + L < B) :
    H.hash iv (p ++ x) = H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x)) := by
  have hB : 0 < B := by omega
  have hl : (p ++ x).length = B + D := by simp [hp, hx]
  have hmod : (p ++ x).length % B = D := by
    rw [hl, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (p ++ x).length / B = 1 := by
    rw [hl, show B + D = D + B * 1 by omega, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (by omega)]
  rw [hash_one H hB (by rw [hmod]; omega), hdiv, compressList_append H (by rw [hp]; omega), hmod, hl]
  have hr : rest B (p ++ x) = x := by
    simp only [rest, hdiv, Nat.mul_one]
    rw [← hp, List.drop_left]
  rw [hr]
  simp only [tailBlock, tailPad, List.append_assoc]

/-- A step of the iteration, from the hash values `hi` and `ho` of the key's
inner and outer blocks: two compressions, each of the digest (of `D` bytes)
of the previous one padded. -/
def step (D : Nat) (hi ho : H.HV) (u : List Byte) : List Byte :=
  (H.digest (H.compress ho (H.tailBlock D ((H.digest (H.compress hi (H.tailBlock D u))).take D)))).take D

theorem step_length {D : Nat} (h : D ≤ N) (hi ho : H.HV) (u : List Byte) : (H.step D hi ho u).length = D := by
  simp only [step, List.length_take, H.digest_length]; omega

/-- A hash function of the specification (`S`, with a `D`-byte digest) is the
`Md` hash function `H` from the initial hash value `iv`, with its digest
truncated to `D` bytes, and its streaming state is `H`'s: the hash value
(`N` bytes) followed by a block (`B` bytes). -/
structure Link (S : StreamingHash) (iv : H.HV) (D : Nat) : Prop where
  hB : S.H.blockSize = B
  hS : S.stateBytes = N + B
  hD : S.digestBytes = D
  repr : ∀ m p x, S.Repr m p x → H.Repr iv m p x
  hash : ∀ x, S.H.hash x = (H.hash iv x).take D
  DN : D ≤ N
  DL : D + L < B

variable {H}

/-- The hash of a block `p` and `D` bytes `x` (HMAC's outer hash, of the
key's outer block and the inner digest) is one compression, of the hash
value of `p` with the block of `x` and the padding. -/
theorem Link.hash_block {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {p x : List Byte}
    (hp : p.length = B) (hx : x.length = D) :
    S.H.hash (p ++ x) = (H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x))).take D := by
  rw [hl.hash, Md.hash_block H iv hp hx hl.DL]

/-- One step of the iteration is HMAC, for a key whose blocks' hash values
are `hi` and `ho`. -/
theorem hmac_step {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 u : List Byte}
    (hk : k0.length = B) (hu : u.length = D) :
    hmacBlockKey S.H k0 u =
      H.step D (H.compressList iv (xorPad k0 ipad) 1) (H.compressList iv (xorPad k0 opad) 1) u := by
  have li : (xorPad k0 ipad).length = B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  simp only [hmacBlockKey, step]
  rw [hl.hash_block li hu, hl.hash_block lo (x := List.take D _)
    (by simp only [List.length_take, H.digest_length]; exact Nat.min_eq_left hl.DN)]

/-- The hash value stored at an address depends only on the bytes there, not
on the address. -/
def Reloc : Prop := ∀ (m m' : Mem) (p q : Addr),
  (∀ i < N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → H.stateAt m' q = H.stateAt m p

/-- The hash value of a streaming state that represents one block. -/
theorem stateAt_of_repr {iv : H.HV} {m : Mem} {p : Addr} {x : List Byte} (hB : 0 < B) (hx : x.length = B)
    (h : H.Repr iv m p x) : H.stateAt m p = H.compressList iv x 1 := by
  rw [h.1, hx, Nat.div_self hB]

/-- Steps that agree on `D`-byte inputs give the same iteration. -/
theorem iterate_congr {D : Nat} {f g : List Byte → List Byte} (hfg : ∀ u, u.length = D → f u = g u)
    (hg : ∀ u, (g u).length = D) :
    ∀ n u t, u.length = D → Spec.Pbkdf2.iterate f n u t = Spec.Pbkdf2.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.Pbkdf2.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

/-- PBKDF2's iteration with HMAC as its pseudorandom function is the
iteration of `step`, from the hash values of a key's streaming states. -/
theorem iterate_hmac {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 : List Byte}
    (hk : k0.length = S.H.blockSize) {mem : Mem} {p q : Addr} (hi : S.Repr mem p (xorPad k0 ipad))
    (ho : S.Repr mem q (xorPad k0 opad)) (n : Nat) {u t : List Byte} (hu : u.length = D) :
    Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n u t =
      Spec.Pbkdf2.iterate (H.step D (H.stateAt mem p) (H.stateAt mem q)) n u t := by
  have hB : 0 < B := by have := hl.DL; omega
  rw [hl.hB] at hk
  have li : (xorPad k0 ipad).length = B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  rw [stateAt_of_repr hB li (hl.repr _ _ _ hi), stateAt_of_repr hB lo (hl.repr _ _ _ ho)]
  exact iterate_congr (fun u hu => hmac_step hl hk hu) (fun u => step_length H hl.DN _ _ u) n u t hu

/-- HMAC's outer hash, for a key whose outer block's hash value is `ho`, of
the inner digest `x`: one compression of the block `x ‖ pad`. -/
theorem hmac_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 text : List Byte}
    (hk : k0.length = S.H.blockSize) {mem : Mem} {p : Addr} (ho : S.Repr mem p (xorPad k0 opad)) :
    hmacBlockKey S.H k0 text =
      (H.digest (H.compress (H.stateAt mem p) (H.tailBlock D (S.H.hash (xorPad k0 ipad ++ text))))).take D := by
  have hB : 0 < B := by have := hl.DL; omega
  rw [hl.hB] at hk
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  have hx : (S.H.hash (xorPad k0 ipad ++ text)).length = D := by
    rw [hl.hash, List.length_take, Md.hash, H.digest_length]; exact Nat.min_eq_left hl.DN
  rw [hmacBlockKey, hl.hash, hash_block H iv lo hx hl.DL, stateAt_of_repr hB lo (hl.repr _ _ _ ho)]

end VG.Proof.MdStream.Md
