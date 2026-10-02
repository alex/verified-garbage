import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Hmac.Generic.X86.Sha256

/-!
# HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 over the compression function on x86 (32-bit), for every backend

SHA-256 as a `Hash` of `Impl/Pbkdf2/Md/X86.lean` with a backend's
compression function and streaming functions
(`Proof.Sha256.X86.Variants.mdHash`), what the proofs know of it (`sha256Ok`):
SHA-256's `Md` (`Proof/Sha256/Md.lean`) from `H0`, the digest its streaming
code writes (`Proof.Sha256.X86.Stream.shape`), and the backend's verified
compression function, whose contract is `cmpK`; and the generic proofs of
HMAC's `finalize` and PBKDF2's iteration (`HmacFinCT.lean`, `IterateCT.lean`)
at it, moved to the shared contracts of `Spec.Hmac.sha256I`. Their taint
checks depend only on the sizes, so they are evaluated once, for every
backend (`sha256Shape`).
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Hmac.Generic.X86 (Sha256Stream sha256OK)
open VG.Proof.Sha256.X86.Variants (mdHash)

/-- SHA-256 with the compression function `cmpN`/`cmpC` and the streaming
functions `v` calling it. -/
abbrev sha256M (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) : Hash :=
  mdHash v.suffix cmpN cmpC v.upd v.fin

/-- `MdOk` for SHA-256, for any backend: its streaming functions `v` and its
verified compression function `cmpC`. -/
def sha256Ok (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa} (hc : CompOk Proof.Sha256.md 112 cmpC) :
    MdOk (sha256M v cmpN cmpC) where
  hH := sha256OK v
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    show 32 ≤ 32 by decide, show 32 + 8 < 64 by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  tail := sha256_tail
  out := outOk_of_shape Proof.Sha256.X86.Stream.shape
  comp := hc
  sizes := sha256_sizes
where
  sha256_tail : Proof.Sha256.md.tailPad 32 = (sha256M v cmpN cmpC).tailB := by
    show Proof.Sha256.md.tailPad 32 = Impl.Pbkdf2.Md.X86.tail 64 32 8 true
    decide
  sha256_sizes : Sizes (sha256M v cmpN cmpC) :=
    ⟨show 64 = 64 ∨ 64 = 128 by decide, show 0 < 32 ∧ 32 ≤ 64 ∧ 32 % 4 = 0 by decide,
      show 0 < 32 ∧ 32 ≤ 32 ∧ 32 % 4 = 0 by decide, show 32 + 8 + 4 ≤ 64 by decide,
      show 96 = 32 + 64 from rfl, show 112 ≤ 8 * 20 by decide, show 20 ≤ 64 by decide,
      show 32 ≤ 32 ∧ 32 ≤ 64 by decide⟩

/-- SHA-256's sizes and digest code, without the functions: the code between
the calls depends on nothing else. -/
def sha256Shape : Hash := mdHash "" "" (.block []) (.block []) (.block [])

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Hmac.Generic.X86 (Sha256Stream initW initG finW finG iterW iterG countF)

theorem sha256Shape_iterChecks : Iterate.Checks sha256Shape where
  pro := ⟨_, by taint_decide⟩
  load := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256Shape_initChecks : HmacInit.Checks sha256Shape where
  pro := ⟨_, by taint_decide⟩
  blocks := ⟨_, by taint_decide⟩
  toOuter := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256Shape_finChecks : HmacFin.Checks sha256Shape where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  mid := ⟨_, by taint_decide⟩
  out := ⟨_, by taint_decide⟩

theorem sha256_iterChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    Iterate.Checks (sha256M v cmpN cmpC) :=
  let h := sha256Shape_iterChecks
  ⟨h.pro, h.load, h.mid, h.tail, h.restore⟩

theorem sha256_initChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacInit.Checks (sha256M v cmpN cmpC) :=
  let h := sha256Shape_initChecks
  ⟨h.pro, h.blocks, h.toOuter, h.restore⟩

theorem sha256_finChecks (v : Sha256Stream) (cmpN : String) (cmpC : Prog isa) :
    HmacFin.Checks (sha256M v cmpN cmpC) :=
  let h := sha256Shape_finChecks
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem sha256_iterImp : (iterW Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.iterateContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := iterSat_args 96 32 104
  sig_implies [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, iterW, iterG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, iterSat] using iterSat 96 32 104

theorem sha256_initImp : (initW Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.initContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 104
  sig_implies [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, initW, initG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 104

theorem sha256_finImp : (finW Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 96 32 104
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finW, finG, countF, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 96 32 104

/-- PBKDF2's iteration for SHA-256 with any backend. -/
theorem sha256_iterate (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).iterate (Spec.Hmac.sha256I.iterateContract X86.abi 48) :=
  (Iterate.verifiedW (sha256Ok v cmpN hc) (sha256_iterChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 + 64 ≤ 8 * 104 by decide) sha256_iterImp.sat_left).of_implies sha256_iterImp

/-- HMAC's `finalize` for SHA-256 with any backend. -/
theorem sha256_finalize (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).hmacFin (Spec.Hmac.sha256I.finalizeContract X86.abi 48) :=
  (HmacFin.verifiedW (sha256Ok v cmpN hc) (sha256_finChecks v cmpN cmpC)
    (show 8 * 20 + 16 + 32 ≤ 8 * 104 by decide) sha256_finImp.sat_left).of_implies sha256_finImp

end VG.Proof.Pbkdf2.Md.X86.Instances

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Hmac.Generic.X86 (Sha256Stream)

/-- HMAC's `init` for SHA-256 with any backend. -/
theorem sha256_init (v : Sha256Stream) (cmpN : String) {cmpC : Prog isa}
    (hc : CompOk Proof.Sha256.md 112 cmpC) :
    Verified X86.target (sha256M v cmpN cmpC).hmacInit (Spec.Hmac.sha256I.initContract X86.abi 48) :=
  (HmacInit.verifiedW (sha256Ok v cmpN hc) (sha256_initChecks v cmpN cmpC)
    (show 8 * 20 + 16 ≤ 8 * 104 by decide) sha256_initImp.sat_left).of_implies sha256_initImp

end VG.Proof.Pbkdf2.Md.X86.Instances
