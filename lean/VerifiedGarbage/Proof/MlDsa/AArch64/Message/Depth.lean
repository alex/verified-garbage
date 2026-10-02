import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst

/-!
# ML-DSA on AArch64: how deep the frames of signing and verification nest

Untrusted: everything here is checked by Lean. Frames nest at most once in
`vg_mldsa*_sign` and `vg_mldsa*_verify`, with any implementation of the
Keccak permutation (`sign_dle`, `verify_dle`): their own code has no frames,
and those of the functions they call nest at most once (`DLe`, from the
structure of the code, `dle_tac`). So their calls use the 16 bytes of stack
below the stack pointer.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64

/-- Frames nest at most `d` deep in `c` and the functions it calls (a
structure, so that unification never unfolds it into a computation of the
depth). -/
structure DLe (d : Nat) (c : Prog isa) : Prop where
  le : c.aarch64Depth ≤ d

section
variable {d : Nat}

theorem DLe.block (is : List Instr) : DLe d (.block is) := ⟨Nat.zero_le _⟩

theorem DLe.seq {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.seq a b) := ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.ite {c : isa.Cond} {a b : Prog isa} (ha : DLe d a) (hb : DLe d b) : DLe d (.ite c a b) :=
  ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩⟩

theorem DLe.loop {c : isa.Cond} {a : Prog isa} (ha : DLe d a) : DLe d (.loop a c) := ⟨ha.1⟩

theorem DLe.call {c : Prog isa} (n : String) (h : DLe d c) : DLe d (.call n c) := ⟨h.1⟩

theorem DLe.seqR {f : Nat → Prog isa} (h : ∀ k, DLe d (f k)) :
    ∀ a n, DLe d (Impl.MlDsa.AArch64.seqR f a n)
  | _, 0 => DLe.block _
  | a, n + 1 => DLe.seq (h a) (DLe.seqR h (a + 1) n)

theorem DLe.of_fd {c : Prog isa} (h : 16 * c.aarch64Depth ≤ 16) : DLe 1 c := ⟨by omega⟩

end

/-- `DLe` of code from its structure, given that of the functions it calls. -/
macro "dle_tac" : tactic =>
  `(tactic| repeat' (first
    | (apply DLe.call; assumption)
    | apply DLe.seq
    | apply DLe.ite
    | apply DLe.loop
    | (apply DLe.seqR; intro)
    | apply DLe.block))

end VG.Proof.MlDsa.AArch64.Message

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.Sign.Prims) (p : Spec.MlDsa.Params)
    (ha : DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : DLe 1 P.ntt) (h2 : DLe 1 P.invNtt) (h3 : DLe 1 P.mul) (h4 : DLe 1 P.mulAdd) (h5 : DLe 1 P.add)
    (h6 : DLe 1 P.sub) (h7 : DLe 1 P.rejNTT) (h8 : DLe 1 P.expandMask) (h9 : DLe 1 P.ball)
    (h10 : DLe 1 P.highBits) (h11 : DLe 1 P.lowBits) (h12 : DLe 1 P.normLt) (h13 : DLe 1 P.makeHint)
    (h14 : DLe 1 P.simpleBitPack) (h15 : DLe 1 P.bitPack) (h16 : DLe 1 P.bitUnpack) (h17 : DLe 1 P.hintBitPack)
include ha hp hs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 in
theorem sign_dle : DLe 1 (Impl.MlDsa.AArch64.Sign.signWith c P p) := by
  unfold Impl.MlDsa.AArch64.Sign.signWith
  dle_tac
end

section
variable (c : Impl.Sha3.AArch64.Callee) (P : Impl.MlDsa.AArch64.KeyGen.Prims) (p : Spec.MlDsa.Params)
    (ha : DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith c)) (hp : DLe 1 (Impl.Sha3.AArch64.Stream.padWith c))
    (hs : DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith c))
    (h1 : DLe 1 P.ntt) (h2 : DLe 1 P.invNtt) (h3 : DLe 1 P.mul) (h4 : DLe 1 P.mulAdd)
    (h6 : DLe 1 P.sub) (h7 : DLe 1 P.rejNtt) (h9 : DLe 1 P.ball)
    (h11 : DLe 1 P.useHint) (h12 : DLe 1 P.normLt) (h13 : DLe 1 P.simpleBitPack) (h15 : DLe 1 P.bitUnpack) (h16 : DLe 1 P.unpackT1) (h17 : DLe 1 P.hintUnpack)

include ha hp hs h1 h2 h3 h4 h6 h7 h9 h11 h12 h13 h15 h16 h17 in
theorem verify_dle : DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith c P p) := by
  unfold Impl.MlDsa.AArch64.Verify.verifyWith
  dle_tac
end

section
variable (v : Proof.Sha3.AArch64.Permutation)

theorem keccak_dle :
    DLe 1 (Impl.Sha3.AArch64.Stream.absorbWith v.callee) ∧ DLe 1 (Impl.Sha3.AArch64.Stream.padWith v.callee) ∧
      DLe 1 (Impl.Sha3.AArch64.Stream.squeezeWith v.callee) :=
  ⟨⟨by rw [v.absorb_depth]⟩, ⟨by rw [v.pad_depth]⟩, ⟨by rw [v.squeeze_depth]⟩⟩

/-- `vg_mldsa*_sign`, with the Keccak permutation of `v`. -/
theorem signWith_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.signWith v.callee (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := keccak_dle v
  exact sign_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.add.fd) (.of_fd C.sub.fd) (.of_fd C.rejNTT.fd) (.of_fd C.expandMask.fd) (.of_fd C.ball.fd)
    (.of_fd C.highBits.fd) (.of_fd C.lowBits.fd) (.of_fd C.normLt.fd) (.of_fd C.makeHint.fd)
    (.of_fd C.simpleBitPack.fd) (.of_fd C.bitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.hintBitPack.fd)

/-- `vg_mldsa*_verify`, with the Keccak permutation of `v`. -/
theorem verifyWith_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) := by
  have C := KeyGen.prims_okWith (keccak := v)
  obtain ⟨ha, hp, hs⟩ := keccak_dle v
  exact verify_dle _ _ p ha hp hs (.of_fd C.ntt.fd) (.of_fd C.invNtt.fd) (.of_fd C.mul.fd) (.of_fd C.mulAdd.fd)
    (.of_fd C.sub.fd) (.of_fd C.rejNtt.fd) (.of_fd C.ball.fd) (.of_fd C.useHint.fd) (.of_fd C.normLt.fd)
    (.of_fd C.simpleBitPack.fd) (.of_fd C.bitUnpack.fd) (.of_fd C.unpackT1.fd) (.of_fd C.hintUnpack.fd)

end

end VG.Proof.MlDsa.AArch64.Message
