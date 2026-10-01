import VerifiedGarbage.Proof.MlDsa.X86.Sign.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on x86 (32-bit): the primitives it calls

Untrusted: everything here is checked by Lean. What the proofs need of the
implementations of the primitives (`PrimsOk`): each is verified against its
shared contract (`Spec/MlDsa/Poly.lean`), with 16 bytes of stack (56 for
the samplers, which call the sponge functions), and never writes `esp`
(`COk`); and, of the two samplers whose result signing branches on, that
the result is a function of their public data (`rejF`, `ballF`) that is 1
only when the algorithm finishes within `maxBounds`.

Each call (`…_piece`) is made from `Ctx`, with its buffers named as `Buf`s;
what it leaves unchanged is stated with the frame `FR s₀ bs 80` (its
buffers, and the stack below the function's own frame).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `k`, with the value returned in `eax` a function `F` of the entry state. -/
def withRet (k : Contract isa) (F : State → BitVec 32) : Contract isa :=
  { k with post := fun s s' => k.post s s' ∧ s'.gpr .eax = F s }

theorem verified_withRet {c : Prog isa} {k : Contract isa} {F : State → BitVec 32} (hv : Verified X86.target c k)
    (hr : ∀ s, k.pre s → ∀ t s', Exec isa c s t s' → s'.gpr .eax = F s) : Verified X86.target c (withRet k F) :=
  ⟨fun s hs => by
    obtain ⟨t, s', e, a, po⟩ := hv.1 s hs
    exact ⟨t, s', e, a, po, hr s hs t s' e⟩, hv.2.1, hv.2.2⟩

/-- What `vg_mldsa_rej_ntt_poly` returns, from its seed. -/
abbrev rejK (F : List Byte → Bool) : Contract isa :=
  withRet (rejNTTContract X86.abi 56) fun s => if F (bytesAt s.mem ((arg s 0).setWidth 64) 34) then 1 else 0

/-- What `vg_mldsa_sample_in_ball` returns, from `τ` and its seed. -/
abbrev ballK (F : Nat → List Byte → Bool) : Contract isa :=
  withRet (sampleInBallContract X86.abi 56) fun s =>
    if F (arg s 2).toNat (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) then 1 else 0

/-- What the proofs need of the implementations `P` of the primitives. -/
structure PrimsOk (P : Prims) where
  ntt : Verified X86.target P.ntt (nttContract X86.abi 16)
  invNtt : Verified X86.target P.invNtt (nttInvContract X86.abi 16)
  mul : Verified X86.target P.mul (mulContract X86.abi 16)
  mulAdd : Verified X86.target P.mulAdd (mulAddContract X86.abi 16)
  add : Verified X86.target P.add (addContract X86.abi 16)
  sub : Verified X86.target P.sub (subContract X86.abi 16)
  expandMask : Verified X86.target P.expandMask (expandMaskContract X86.abi 56)
  highBits : Verified X86.target P.highBits (highBitsContract X86.abi 16)
  lowBits : Verified X86.target P.lowBits (lowBitsContract X86.abi 16)
  normLt : Verified X86.target P.normLt (normLtContract X86.abi 16)
  makeHint : Verified X86.target P.makeHint (makeHintContract X86.abi 16)
  simpleBitPack : Verified X86.target P.simpleBitPack (simpleBitPackContract X86.abi 16)
  bitPack : Verified X86.target P.bitPack (bitPackContract X86.abi 16)
  bitUnpack : Verified X86.target P.bitUnpack (bitUnpackContract X86.abi 16)
  hintBitPack : Verified X86.target P.hintBitPack (hintBitPackContract X86.abi 16)
  /-- Whether `vg_mldsa_rej_ntt_poly` succeeds on a seed. -/
  rejF : List Byte → Bool
  rejNTT : Verified X86.target P.rejNTT (rejK rejF)
  rejMax : ∀ B, rejF B = true → (rejNTTPoly maxBounds.rejNTT B).isSome
  /-- Whether `vg_mldsa_sample_in_ball` succeeds on `τ` and a seed. -/
  ballF : Nat → List Byte → Bool
  ball : Verified X86.target P.ball (ballK ballF)
  ballMax : BallF ballF
  ok : ∀ c ∈ [P.ntt, P.invNtt, P.mul, P.mulAdd, P.add, P.sub, P.rejNTT, P.expandMask, P.ball, P.highBits,
    P.lowBits, P.normLt, P.makeHint, P.simpleBitPack, P.bitPack, P.bitUnpack, P.hintBitPack], COk c

/-- The returned `u32` is the low word, `eax`, of the returned pair. -/
theorem sw32 (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

/-! ## Frames -/

/-- The frame of a call: its buffers, its arguments and its stack, within `FR s₀ bs 80`. -/
theorem fr80 {p : Params} {s₀ : State} {bs : List Buf} {N M : Nat} (hN : N ≤ 80) (hM : M ≤ 80) {m m' : Mem} (hp : TPre (Y p) s₀)
    (fr : Frame ((bs.map (Buf.rgn s₀) ++ [below (E1 s₀) N]) ++ [below (E1 s₀) M]) m m') : Frame (FR s₀ bs 80) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hN (by show 80 + 16 ≤ 96; omega)⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stk_sub hp hM (by show 80 + 16 ≤ 96; omega)⟩

end VG.Proof.MlDsa.X86.Sign
