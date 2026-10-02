import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same

/-!
# ML-DSA key generation on x86-64, with this library's primitives

Untrusted: everything here is checked by Lean. The x86-64 implementations of
the primitives (`prims`) are verified, use at most 16 bytes of stack (24
for `vg_mldsa_rej_ntt_poly4`), and never write `rsp` but by calls nested at
most twice (three times for `vg_mldsa_rej_ntt_poly4`), with any implementation
`v` of the polynomial arithmetic (`prims_okWith`), so key generation with
them is verified (`keyGen_verifiedWith`).
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl Comp Same Same.ok Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

/-- A function of the polynomial arithmetic satisfies what the proofs of key generation need of it. -/
theorem calleeOf {k : Nat → Contract isa} {c : Prog isa} (h : FnOk k c) : Callee c k :=
  ⟨⟨0, by decide, h.ver⟩, h.nosp, h.depth⟩

theorem prims_okWith (v : ArithImpl) : PrimsOk (primsWith v.code) where
  ntt := calleeOf v.ok.ntt
  invNtt := calleeOf v.ok.invNtt
  mul := calleeOf v.ok.mul
  mulAdd := calleeOf v.ok.mulAdd
  add := calleeOf v.ok.add
  rejNtt := (⟨⟨16, by decide, Sample.rejNTT_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    Callee prims.rejNtt _)
  rejBounded := (⟨⟨16, by decide, Sample.rejBounded_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    Callee prims.rejBounded _)
  power2Round := (⟨⟨0, by decide, Round.power2Round_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    Callee prims.power2Round _)
  simpleBitPack := (⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, nosp_of (by decide +kernel),
    by decide +kernel⟩ : Callee prims.simpleBitPack _)
  bitPack := (⟨⟨0, by decide, Pack.bitPack_verified⟩, nosp_of (by decide +kernel), by decide +kernel⟩ :
    Callee prims.bitPack _)
  rej4 := ⟨v.ok.rej4.ver, v.ok.rej4.nosp, v.ok.rej4.depth⟩

/-! For any implementation of the polynomial arithmetic, that key
generation never writes `rsp` is checked by evaluating it with every
function of it empty (`keyGen_same`, as `sign_same`). -/

theorem keyGen_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h2 : mc B.invNtt = true) (h3 : mc B.mul = true) (h4 : mc B.mulAdd = true) (h5 : mc B.add = true)
    (h6 : mc B.rej4 = true) (p : Spec.MlDsa.Params) : Same m (keyGen (primsWith B) p) (keyGen (primsWith .empty) p) := by
  unfold keyGen
  same_tac hm

theorem keyGen0_sp {p : Spec.MlDsa.Params}
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    (keyGen (primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

variable (v : ArithImpl) {p : Spec.MlDsa.Params}
  (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
include hp

theorem keyGen_spSafe : (keyGen (primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (keyGen_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.invNtt.sp) (Code.allInstrs_of_all v.ok.mul.sp)
    (Code.allInstrs_of_all v.ok.mulAdd.sp) (Code.allInstrs_of_all v.ok.add.sp)
    (Code.allInstrs_of_all v.ok.rej4.sp) p) (keyGen0_sp hp))

theorem keyGen_verifiedWith :
    Verified X86_64.target (keyGen (primsWith v.code) p) (Spec.MlDsa.keyGenContract p X86_64.abi 32) :=
  keyGen_verified (prims_okWith v) p hp

end VG.Proof.MlDsa.X86_64.KeyGen
