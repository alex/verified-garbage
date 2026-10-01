import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Hash
import VerifiedGarbage.Proof.Blake2.X86_64.Backend

/-! # H′ uses any BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

/-- The symbols and code of one BLAKE2b streaming backend. -/
def hash (v : Proof.Blake2.X86_64.Backend) : Impl.Argon2.X86_64.HPrime.Hash where
  initName := Spec.Blake2.initBApi.name
  init := v.init
  updateName := v.updateName
  update := v.update
  finalizeName := v.finalizeName
  finalize := v.finalize

private theorem nosp_of_check {c : Prog isa}
    (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi

private theorem callee_check (v : Proof.Blake2.X86_64.Backend) :
    v.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simpa only [Bool.not_eq_true'] using v.callee.nosp i hi

open Impl.Blake2.X86_64.Stream in
private theorem update_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp v.update := by
  apply nosp_of_check
  simp only [Proof.Blake2.X86_64.Backend.update, Proof.Blake2.X86_64.Backend.hashCallee,
    update, updateStart, save, saved, bufLen, head, fill, copyLoop, compressBuf,
    compressWith, rest, direct, tail, restore, Code.allInstrs]
  rw [callee_check v]
  decide +kernel

open Impl.Blake2.X86_64.Stream in
private theorem finalize_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp v.finalize := by
  apply nosp_of_check
  simp only [Proof.Blake2.X86_64.Backend.finalize, Proof.Blake2.X86_64.Backend.hashCallee,
    finalize, save, saved, bufLen, pad, zeroLoop, compressLast, compressWith, output,
    restore, Code.allInstrs]
  rw [callee_check v]
  decide +kernel

open Impl.Blake2.X86_64.Stream in
theorem hash_ok (v : Proof.Blake2.X86_64.Backend) : HashOk (hash v) := by
  refine ⟨v.init_verified, v.update_verified, v.finalize_verified, ?_, update_nosp v,
    finalize_nosp v, ?_, ?_, ?_⟩
  · apply nosp_of_check
    change (init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  · rfl
  · simp only [hash, Proof.Blake2.X86_64.Backend.update, Proof.Blake2.X86_64.Backend.hashCallee,
      update, bufLen, head, fill, copyLoop, compressBuf, compressWith, rest, direct, tail,
      Code.depth, v.callee.depth]
    rfl
  · simp only [hash, Proof.Blake2.X86_64.Backend.finalize, Proof.Blake2.X86_64.Backend.hashCallee,
      finalize, bufLen, pad, zeroLoop, compressLast, compressWith, Code.depth, v.callee.depth]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
