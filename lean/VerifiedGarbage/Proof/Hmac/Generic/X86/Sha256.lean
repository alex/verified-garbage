import VerifiedGarbage.Proof.Hmac.Generic.X86.InitAny
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant

/-!
# HMAC-SHA-256 on x86 (32-bit), over any compression function

Untrusted: everything here is checked by Lean. SHA-256's streaming
functions are the generic streaming code with a compression function
(`Impl/MdStream/X86.lean`), which has several implementations (the
backends of `Proof/Sha256/X86/Variants/Interface.lean`): HMAC's `initAny`
and `finalize` are proven once for any of them (`sha256H`), given what each
backend proves of its code (`Sha256Facts`), and emitted for each
(`Generic/Sha256/X86/Hmac.lean`).
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Proof.Hmac.Generic.Common (sha256_repr)

/-- SHA-256 with the compression function `cmpC` (named `cmpN`), whose
streaming functions are named with `suffix`. -/
def sha256H (cmpN : String) (cmpC : Prog isa) (suffix : String) : Hash :=
  ⟨64, 96, 32, 32, 20, "vg_sha256_init", Impl.Sha256.X86.Stream.init,
    "vg_sha256_update" ++ suffix, Impl.MdStream.X86.update Proof.Sha256.X86.Stream.params cmpN cmpC,
    "vg_sha256_finalize" ++ suffix, Impl.MdStream.X86.finalize Proof.Sha256.X86.Stream.params cmpN cmpC⟩

/-- What a backend proves of its streaming code: that its compression
function is verified, and of the streaming code built with it, that it is
constant time, does not write `esp` and uses at most 20 bytes of stack. -/
structure Sha256Facts (cmpN : String) (cmpC : Prog isa) : Prop where
  callee : CalleeOk (P := Proof.Sha256.X86.Stream.params) Proof.Sha256.md cmpC
  updCt : ConstantTime isa (MdStream.X86.updK (P := Proof.Sha256.X86.Stream.params) Proof.Sha256.md 160).pre
    (MdStream.X86.updK (P := Proof.Sha256.X86.Stream.params) Proof.Sha256.md 160).pub
    (Impl.MdStream.X86.update Proof.Sha256.X86.Stream.params cmpN cmpC)
  finCt : ConstantTime isa (MdStream.X86.finK (P := Proof.Sha256.X86.Stream.params) Proof.Sha256.md 160).pre
    (MdStream.X86.finK (P := Proof.Sha256.X86.Stream.params) Proof.Sha256.md 160).pub
    (Impl.MdStream.X86.finalize Proof.Sha256.X86.Stream.params cmpN cmpC)
  updSp : NoSp (Impl.MdStream.X86.update Proof.Sha256.X86.Stream.params cmpN cmpC)
  finSp : NoSp (Impl.MdStream.X86.finalize Proof.Sha256.X86.Stream.params cmpN cmpC)
  updSU : stackUse (Impl.MdStream.X86.update Proof.Sha256.X86.Stream.params cmpN cmpC) ≤ 20
  finSU : stackUse (Impl.MdStream.X86.finalize Proof.Sha256.X86.Stream.params cmpN cmpC) ≤ 20

variable {cmpN : String} {cmpC : Prog isa} (suffix : String)

def sha256OK (h : Sha256Facts cmpN cmpC) : HashOK (sha256H cmpN cmpC suffix) where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 32 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 32 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := sha256_repr
  init := Proof.Sha256.X86.Stream.init_verified
  upd := (Proof.Sha256.X86.Stream.update_of (name := cmpN) h.callee h.updCt).of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := (Proof.Sha256.X86.Stream.update_of (name := cmpN) h.callee h.updCt).2.2 }
  fin := (Proof.Sha256.X86.Stream.finalize_of (name := cmpN) h.callee h.finCt).of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := (Proof.Sha256.X86.Stream.finalize_of (name := cmpN) h.callee h.finCt).2.2 }
  initSp := (nosp_of (by lit_decide) : NoSp Impl.Sha256.X86.Stream.init)
  updSp := h.updSp
  finSp := h.finSp
  initSU := (by lit_decide : stackUse Impl.Sha256.X86.Stream.init ≤ 20)
  updSU := h.updSU
  finSU := h.finSU

end VG.Proof.Hmac.Generic.X86

namespace VG.Proof.Hmac.Generic.X86.Instances

open VG.X86
open VG.Proof.Hmac.Generic.X86

/-- The taint checks look at the sizes of the hash function only: they are
evaluated for one instance (`sha256H₀`), whose code the kernel can evaluate. -/
abbrev sha256H₀ : Impl.Hmac.Generic.X86.Hash := sha256H "" (.block []) ""

theorem sha256_initChecks₀ : Init.Checks sha256H₀ where
  keys := ⟨_, by taint_decide⟩
  states := ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256_finChecks₀ : Finalize.Checks sha256H₀ where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256_initAnyChecks₀ : InitAny.Checks sha256H₀ where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

variable (cmpN : String) (cmpC : Prog isa) (suffix : String)

theorem sha256_initChecks : Init.Checks (sha256H cmpN cmpC suffix) :=
  ⟨sha256_initChecks₀.keys, sha256_initChecks₀.states, sha256_initChecks₀.upd, sha256_initChecks₀.restore⟩

theorem sha256_finChecks : Finalize.Checks (sha256H cmpN cmpC suffix) :=
  ⟨sha256_finChecks₀.pro, sha256_finChecks₀.fin1, sha256_finChecks₀.copy1, sha256_finChecks₀.upd,
    sha256_finChecks₀.fin2, sha256_finChecks₀.copy2, sha256_finChecks₀.restore⟩

theorem sha256_initAnyChecks : InitAny.Checks (sha256H cmpN cmpC suffix) :=
  ⟨sha256_initAnyChecks₀.cmp, sha256_initAnyChecks₀.pro, sha256_initAnyChecks₀.argU, sha256_initAnyChecks₀.argF,
    sha256_initAnyChecks₀.args⟩

theorem sha256_initAnyImp :
    (initAnyG Spec.Hmac.sha256S 200).Implies (Spec.Hmac.sha256I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 96 200
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
    initAnyG, initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 96 200

theorem sha256_finImp : (finW Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.finalizeContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, e, esp⟩ := finSat_args 96 32 104
  sig_implies [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finW, finG, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp, finSat] using finSat 96 32 104

variable {cmpN cmpC}

theorem sha256_initAny (h : Sha256Facts cmpN cmpC) :
    Verified X86.target (sha256H cmpN cmpC suffix).initAny (Spec.Hmac.sha256I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny (sha256OK suffix h) (sha256_initChecks cmpN cmpC suffix)
    (sha256_initAnyChecks cmpN cmpC suffix) (by simp only [sha256H, Impl.Hmac.Generic.X86.Hash.ext, Impl.Hmac.Generic.X86.Hash.buf]; decide) (show 32 ≤ 64 by decide)
    sha256_initAnyImp.sat_left).of_implies
    sha256_initAnyImp

theorem sha256_finalize (h : Sha256Facts cmpN cmpC) :
    Verified X86.target (sha256H cmpN cmpC suffix).finalize (Spec.Hmac.sha256I.finalizeContract X86.abi 48) :=
  (Finalize.verifiedW (sha256OK suffix h) (sha256_finChecks cmpN cmpC suffix) (show 176 + 32 ≤ 8 * 104 by decide)
    sha256_finImp.sat_left).of_implies sha256_finImp

end VG.Proof.Hmac.Generic.X86.Instances
