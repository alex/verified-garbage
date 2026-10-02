import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Pbkdf2CT
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.HmacFin

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the functions, verified

Untrusted: everything here is checked by Lean. What the kernel checks of a
hash function's code does not depend on its compression function or its
streaming `init`, which our functions only call: `core H` is `H` with both
replaced by empty code, and the facts about every instruction of `H`'s
functions follow from those about `core H` and about the two callees
(`core_pbkdf2`, …). `CoreOK` is what the kernel checks of `core H`, once for
each hash function; `Callees` is what each implementation of the
compression function brings. From them, HMAC's `init` and `finalize`,
`iterate` and `pbkdf2` are verified against the shared contracts of
`Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64 (initG finG)
open VG.Proof.Pbkdf2.X86_64 (iterK iterImp)

/-- No instruction of `c` writes `rsp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by
    have h' := List.all_eq_true.mp ((Code.allInstrs_eq _ c) ▸ h) i hi
    revert h'; cases Taint.clobbers i .rsp <;> simp

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash := ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", "", "", "", ""⟩

/-! ## Every instruction, from the own code and the callees' -/

section
variable {H : Hash} {p : Instr → Bool} (hc : H.compC.allInstrs p = true) (hi : H.initC.allInstrs p = true)
include hc hi

theorem core_pbkdf2 (h : (core H).pbkdf2.allInstrs p = true) : H.pbkdf2.allInstrs p = true := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Hmac.Generic.X86_64.Hash.init,
    Impl.Hmac.Generic.X86_64.Hash.callInit, Impl.Hmac.Generic.X86_64.Hash.callUpd,
    Impl.Hmac.Generic.X86_64.Hash.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.allInstrs, hc, hi, Bool.and_true, Bool.true_and] at h ⊢
  exact h

theorem core_hmacInit (h : (core H).hmacInit.allInstrs p = true) : H.hmacInit.allInstrs p = true := by
  simp only [Hash.hmacInit, Hash.updC, Hash.stream,
    Impl.Hmac.Generic.X86_64.Hash.init, Impl.Hmac.Generic.X86_64.Hash.callInit,
    Impl.Hmac.Generic.X86_64.Hash.callUpd,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, hi, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_hmacFin (h : (core H).hmacFin.allInstrs p = true) : H.hmacFin.allInstrs p = true := by
  simp only [Hash.hmacFin, Hash.finMid, Hash.finOut, Hash.finC, Hash.stream,
    Impl.Hmac.Generic.X86_64.Hash.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_iterate (h : (core H).iterate.allInstrs p = true) : H.iterate.allInstrs p = true := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_updC (h : (core H).updC.allInstrs p = true) : H.updC.allInstrs p = true := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

omit hi in
theorem core_finC (h : (core H).finC.allInstrs p = true) : H.finC.allInstrs p = true := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.allInstrs, hc, Bool.and_true, Bool.true_and] at h ⊢
  exact h

end

/-! ## How deeply calls nest -/

section
variable {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
include hc hi

theorem core_hmacInit_depth (h : (core H).hmacInit.depth ≤ 2) : H.hmacInit.depth ≤ 2 := by
  simp only [Hash.hmacInit, Hash.updC, Hash.stream,
    Impl.Hmac.Generic.X86_64.Hash.init, Impl.Hmac.Generic.X86_64.Hash.callInit,
    Impl.Hmac.Generic.X86_64.Hash.callUpd,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.depth, hc, hi] at h ⊢
  exact h

omit hi in
theorem core_hmacFin_depth (h : (core H).hmacFin.depth ≤ 2) : H.hmacFin.depth ≤ 2 := by
  simp only [Hash.hmacFin, Hash.finC, Hash.stream, Impl.Hmac.Generic.X86_64.Hash.callFin,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_iterate_depth (h : (core H).iterate.depth ≤ 2) : H.iterate.depth ≤ 2 := by
  simp only [Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_updC_depth (h : (core H).updC.depth ≤ 1) : H.updC.depth ≤ 1 := by
  simp only [Hash.updC, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    core, Code.depth, hc] at h ⊢
  exact h

omit hi in
theorem core_finC_depth (h : (core H).finC.depth ≤ 1) : H.finC.depth ≤ 1 := by
  simp only [Hash.finC, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, core, Code.depth, hc] at h ⊢
  exact h

end

/-! ## The taint checks, which look only at the own code -/

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (core H)) : Pbk.Checks H :=
  ⟨h.load, h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.loopRegs, h.pieceA, h.finArgs,
    h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`), the
same for every implementation of its compression function: the taint checks
of the pieces between calls, that no instruction loads MXCSR or writes
`rsp`, and how deeply calls nest. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.X86_64.Checks C.P C.D
  hinit : Hmac.Generic.X86_64.Init.Checks C.stream
  hfin : HmacFin.Checks C
  pbkMx : C.pbkdf2.allInstrs (fun i => !loadsMxcsr i) = true
  pbkSp : C.pbkdf2.allInstrs (fun i => !isa.writesSp i) = true
  hinitMx : C.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true
  hinitSp : C.hmacInit.allInstrs (fun i => !isa.writesSp i) = true
  hinitNs : C.hmacInit.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hinitD : C.hmacInit.depth ≤ 2
  hfinMx : C.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true
  hfinSp : C.hmacFin.allInstrs (fun i => !isa.writesSp i) = true
  hfinNs : C.hmacFin.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  hfinD : C.hmacFin.depth ≤ 2
  iterMx : C.iterate.allInstrs (fun i => !loadsMxcsr i) = true
  iterSp : C.iterate.allInstrs (fun i => !isa.writesSp i) = true
  iterNs : C.iterate.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iterD : C.iterate.depth ≤ 2
  updMx : C.updC.allInstrs (fun i => !loadsMxcsr i) = true
  updNs : C.updC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  updD : C.updC.depth ≤ 1
  finMx : C.finC.allInstrs (fun i => !loadsMxcsr i) = true
  finNs : C.finC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  finD : C.finC.depth ≤ 1
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf + 2 * C.stream.B ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-- What the kernel checks of the functions a hash function's code calls:
its compression function and its streaming `init`. -/
structure Callees (H : Hash) : Prop where
  cMx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true
  cSp : H.compC.allInstrs (fun i => !isa.writesSp i) = true
  cNs : H.compC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  cD : H.compC.depth = 0
  iMx : H.initC.allInstrs (fun i => !loadsMxcsr i) = true
  iSp : H.initC.allInstrs (fun i => !isa.writesSp i) = true
  iNs : H.initC.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  iD : H.initC.depth = 0

namespace Callees

variable {H : Hash} (K : Callees H) (C : CoreOK (core H))
include K C

theorem updMx : H.updC.allInstrs (fun i => !loadsMxcsr i) = true := core_updC K.cMx C.updMx
theorem finMx : H.finC.allInstrs (fun i => !loadsMxcsr i) = true := core_finC K.cMx C.finMx
theorem updSp : NoSp H.updC := nosp_of (core_updC K.cNs C.updNs)
theorem finSp : NoSp H.finC := nosp_of (core_finC K.cNs C.finNs)
theorem updD : H.updC.depth ≤ 1 := core_updC_depth K.cD C.updD
theorem finD : H.finC.depth ≤ 1 := core_finC_depth K.cD C.finD

end Callees

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`; the stack arguments
(`out_len` and `scratch`) are zero, so `scratch` is at address 0. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 16⟩]
  wr := [⟨0x30000, 0⟩, ⟨0, sc * 8⟩]

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
include hH C K

theorem hmacInit_ok (hsat : ∃ s, (Spec.Hmac.initContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH H.W) :=
  Hmac.Generic.X86_64.Init.verified hH.stream (Hmac.Generic.X86_64.Instances.Init.Checks.of_eq (H := (core H).stream) rfl rfl C.hinit)
    C.fitI (core_hmacInit K.cMx K.iMx C.hinitMx) (Hmac.Generic.X86_64.Instances.initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF (core_hmacFin K.cMx C.hfinMx)
    (Hmac.Generic.X86_64.Instances.finImp _ _ hsat).sat_left

omit K in
theorem iterate_ok (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hmx : H.compC.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.X86_64.verified hH.iterOk C.iter hH.comp (core_iterate hmx C.iterMx) (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Spec.Hmac.initContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (Spec.Hmac.initContract hH.SH H.W X86_64.abi 16) :=
  (hmacInit_ok hH C K hsat).of_implies (Hmac.Generic.X86_64.Instances.initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (Spec.Hmac.finalizeContract hH.SH H.W X86_64.abi 16) :=
  (hmacFin_ok hH C K hsat).of_implies (Hmac.Generic.X86_64.Instances.finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8) :=
  (iterate_ok hH C hsat K.cMx).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Spec.Hmac.initContract hH.SH H.W X86_64.abi 16).pre s)
    (hsF : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W X86_64.abi 16).pre s)
    (hsT : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W X86_64.abi 8).pre s)
    (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2Contract hH.SH (H.W + H.S) X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (Spec.Pbkdf2.pbkdf2Contract hH.SH (H.W + H.S) X86_64.abi 24) :=
  (Pbk.verified hH hH.psizes (Pbk.Checks.of_core C.pbk)
    (hmacInit_ok hH C K hsI) (nosp_of (core_hmacInit K.cNs K.iNs C.hinitNs)) (core_hmacInit_depth K.cD K.iD C.hinitD)
    (hmacFin_ok hH C K hsF) (nosp_of (core_hmacFin K.cNs C.hfinNs)) (core_hmacFin_depth K.cD C.hfinD)
    (iterate_ok hH C hsT K.cMx) (nosp_of (core_iterate K.cNs C.iterNs)) (core_iterate_depth K.cD C.iterD)
    (core_pbkdf2 K.cMx K.iMx C.pbkMx) (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

omit hH in
theorem hmacInit_sp : H.hmacInit.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_hmacInit K.cSp K.iSp C.hinitSp)

omit hH in
theorem hmacFin_sp : H.hmacFin.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_hmacFin K.cSp C.hfinSp)

omit hH in
theorem iterate_sp : H.iterate.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_iterate K.cSp C.iterSp)

omit hH in
theorem pbkdf2_sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (core_pbkdf2 K.cSp K.iSp C.pbkSp)

end

end VG.Proof.Pbkdf2.Md.X86_64
