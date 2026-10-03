import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224

/-!
# HMAC-SHA-224 and PBKDF2-HMAC-SHA-224 over the compression function on x86 (32-bit), for every backend

SHA-224 as a `Hash` of `Impl/Pbkdf2/Md/X86.lean` with a backend's SHA-256
compression function and streaming functions
(`Proof.Sha256.X86.Variants.mdHash224`), what the proofs know of it
(`sha224Ok`): SHA-256's `Md` (`Proof/Sha256/Md.lean`) from `H0_224`, with the
digest the first 28 bytes of the final hash value, the digest SHA-256's
streaming code writes (`Proof.Sha256.X86.Stream.shape`), and the backend's
verified compression function, whose contract is `cmpK`; and the generic
proofs of HMAC's `init` and `finalize` and PBKDF2's iteration at it, moved to
the shared contracts of `Spec.Hmac.sha224I`, as for SHA-256 (`Sha256.lean`).
Their taint checks depend only on the sizes, so they are evaluated once, for
every backend (`sha224Shape`).
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream sha224OK)
open VG.Proof.Sha256.X86.Variants (mdHash224)

/-- SHA-224 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha224M (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  mdHash224 v.suffix cmpN cmpC v.upd v.fin

/-- `MdOk` for SHA-224, for any backend: its streaming functions `v` and its
verified compression function `cmpC`. -/
def sha224Ok (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa} (hc : CompOk Proof.Sha256.md 112 cmpC) :
    MdOk (sha224M v cmpN cmpC) where
  hH := sha224OK v
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, show 28 ≤ 32 by decide, show 28 + 8 < 64 by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  tail := sha224_tail
  out := outOk_of_shape Proof.Sha256.X86.Stream.shape
  comp := hc
  sizes := sha224_sizes
where
  sha224_tail : Proof.Sha256.md.tailPad 28 = (sha224M v cmpN cmpC).tailB := by
    show Proof.Sha256.md.tailPad 28 = Impl.Pbkdf2.Md.X86.tail 64 28 8 true
    decide
  sha224_sizes : Sizes (sha224M v cmpN cmpC) :=
    ⟨show 64 = 64 ∨ 64 = 128 by decide, show 0 < 32 ∧ 32 ≤ 64 ∧ 32 % 4 = 0 by decide,
      show 0 < 28 ∧ 28 ≤ 32 ∧ 28 % 4 = 0 by decide, show 28 + 8 + 4 ≤ 64 by decide,
      show 96 = 32 + 64 from rfl, show 112 ≤ 8 * 20 by decide, show 20 ≤ 64 by decide,
      show 28 ≤ 32 ∧ 32 ≤ 64 by decide⟩

/-- SHA-224's sizes and digest code, without the functions: the code between
the calls depends on nothing else. -/
def sha224Shape : Hash := mdHash224 "" "" (.block []) (.block []) (.block [])

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (Sha256Stream initW initG finW finG iterW iterG countF)

theorem sha224Shape_iterChecks : Iterate.Checks sha224Shape where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha224Shape_initChecks : HmacInit.Checks sha224Shape where
  pro := ⟨_, by taint_decide⟩
  blocks := ⟨_, by taint_decide⟩
  toOuter := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha224Shape_finChecks : HmacFin.Checks sha224Shape where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha224_iterChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    Iterate.Checks (sha224M v cmpN cmpC) :=
  let h := sha224Shape_iterChecks
  ⟨h.pro, h.load, h.mid, h.tail, h.restore⟩

theorem sha224_initChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacInit.Checks (sha224M v cmpN cmpC) :=
  let h := sha224Shape_initChecks
  ⟨h.pro, h.blocks, h.toOuter, h.restore⟩

theorem sha224_finChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacFin.Checks (sha224M v cmpN cmpC) :=
  let h := sha224Shape_finChecks
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem sha224_iterImp : (iterW Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 96 28 104
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 96 28 104

theorem sha224_initImp : (initW Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 104
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 104

theorem sha224_finImp : (finW Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 96 28 104
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 96 28 104

/-- PBKDF2's iteration for SHA-224 with any backend. -/
theorem sha224_iterate (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).iterate (Spec.Hmac.sha224I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW (sha224Ok v cmpN hc) (sha224_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 + 64 ≤ 8 * 104 by decide) sha224_iterImp.sat_left).of_implies sha224_iterImp

/-- HMAC's `finalize` for SHA-224 with any backend. -/
theorem sha224_finalize (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).hmacFin (Spec.Hmac.sha224I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW (sha224Ok v cmpN hc) (sha224_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 ≤ 8 * 104 by decide) sha224_finImp.sat_left).of_implies sha224_finImp

/-- HMAC's `init` for SHA-224 with any backend. -/
theorem sha224_init (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha224M v cmpN cmpC).hmacInit (Spec.Hmac.sha224I.initContract X86.abi 48) :=
  (HmacInit.verifiedW (sha224Ok v cmpN hc) (sha224_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 104 by decide) sha224_initImp.sat_left).of_implies sha224_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
