import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Pbkdf2CT
import VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacFin

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the functions, verified

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Md/X86_64/Core.lean`): what the kernel checks of a hash
function's code does not depend on its compression function or its
streaming functions, which our functions only call: `core H` is `H` with
them replaced by empty code, and `CoreOK` is what the kernel checks of
`core H` (the taint checks of the pieces between calls and that HMAC's
buffers fit), once for each hash function. How deeply frames nest in our
functions follows from the callees' (`hmacInit_fdepth`, …): ours push none.
From them, HMAC's `init` and `finalize`, `iterate` and `pbkdf2` are verified
against the shared contracts of `Spec/Hmac/Generic.lean` and
`Spec/Pbkdf2/Generic.lean`.

There is no stack pointer to check (`writesSp` is always `false` on AArch64),
so the artifacts' `spSafe` is `Code.all_of_forall`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64 (initG finG)
open VG.Proof.Pbkdf2.AArch64 (iterK iterImp)

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash :=
  ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

/-! ## How deeply frames nest -/

theorem fdepth_of_noFrames {I C : Type} {c : Code I C} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

section
variable {H : Hash}

theorem hmacInit_fdepth (hi : H.initC.fdepth ≤ 1) (hu : H.updC.fdepth ≤ 1) : H.hmacInit.fdepth ≤ 1 := by
  simp only [Hash.hmacInit, Hash.stream, Impl.Hmac.Generic.AArch64.Hash.init,
    Impl.Hmac.Generic.AArch64.Hash.initKeys, Impl.Hmac.Generic.AArch64.Hash.keyLoop,
    Impl.Hmac.Generic.AArch64.Hash.padLoop, Impl.Hmac.Generic.AArch64.Hash.callInit,
    Impl.Hmac.Generic.AArch64.Hash.callUpd, Code.fdepth]
  omega

theorem hmacFin_fdepth (hf : H.finC.fdepth ≤ 1) : H.hmacFin.fdepth ≤ 1 := by
  simp only [Hash.hmacFin, Hash.stream, Impl.Hmac.Generic.AArch64.Hash.callFin, Code.fdepth]
  omega

theorem iterate_fdepth (hc : H.compC.noFrames = true) : H.iterate.fdepth ≤ 1 := by
  simp only [Hash.iterate, Impl.Pbkdf2.AArch64.iterate, Impl.Pbkdf2.AArch64.main,
    Impl.Pbkdf2.AArch64.body, Impl.Pbkdf2.AArch64.compressBlock, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Code.fdepth, fdepth_of_noFrames hc]
  omega

end

/-! ## The taint checks, which look only at the own code -/

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.fin2, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (core H)) : Pbk.Checks H :=
  ⟨h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.keyShr, h.keySub, h.short, h.su1, h.su3, h.loopRegs,
    h.pieceA, h.finArgs, h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`): the
taint checks of the pieces between calls, and that HMAC's buffers fit in
the working space. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.AArch64.Checks C.P C.D
  hinit : Hmac.Generic.AArch64.Init.Checks C.stream
  hfin : HmacFin.Checks C
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf + 2 * C.stream.B ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x4 => 1 | .x5 => 0x30000 | .x7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩]
  wr := [⟨0x30000, 0⟩, ⟨0x40000, sc * 8⟩]

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H))
include hH C

theorem hmacInit_ok (hsat : ∃ s, (Spec.Hmac.initContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (initG hH.SH H.W) :=
  Hmac.Generic.AArch64.Init.verified hH.stream
    (Hmac.Generic.AArch64.Instances.Init.Checks.of_eq (H := (core H).stream) rfl rfl rfl C.hinit)
    C.fitI (Hmac.Generic.AArch64.Instances.initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF
    (Hmac.Generic.AArch64.Instances.finImp _ _ hsat).sat_left

theorem iterate_ok (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.AArch64.verified hH.iterOk C.iter hH.comp (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Spec.Hmac.initContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (Spec.Hmac.initContract hH.SH H.W AArch64.abi 16) :=
  (hmacInit_ok hH C hsat).of_implies (Hmac.Generic.AArch64.Instances.initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (Spec.Hmac.finalizeContract hH.SH H.W AArch64.abi 16) :=
  (hmacFin_ok hH C hsat).of_implies (Hmac.Generic.AArch64.Instances.finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi) :=
  (iterate_ok hH C hsat).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Spec.Hmac.initContract hH.SH H.W AArch64.abi 16).pre s)
    (hsF : ∃ s, (Spec.Hmac.finalizeContract hH.SH H.W AArch64.abi 16).pre s)
    (hsT : ∃ s, (Spec.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s)
    (hsat : ∃ s, (Spec.Pbkdf2.pbkdf2Contract hH.SH (H.W + H.S) AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (Spec.Pbkdf2.pbkdf2Contract hH.SH (H.W + H.S) AArch64.abi 16) :=
  (Pbk.verified hH (Pbk.Checks.of_core C.pbk)
    (hmacInit_ok hH C hsI) (hmacInit_fdepth hH.stream.initDepth hH.stream.updDepth)
    (hmacFin_ok hH C hsF) (hmacFin_fdepth hH.stream.finDepth)
    (iterate_ok hH C hsT) (iterate_fdepth hH.comp.noFrames)
    (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.AArch64
