import VerifiedGarbage.Proof.Argon2.AArch64.InitialBody
import VerifiedGarbage.Proof.Argon2.AArch64.InitialCT
import VerifiedGarbage.Proof.Argon2.AArch64.InitFillCT

/-! Complete derivation reveals only its reviewed filling reference sequence. -/

namespace VG.Proof.Argon2.AArch64.InitialBody

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt)

def initial (p : Params) (s : State) : FillState := initMemory p (initialHash p
  (Initial.inputBytes s passwordOffset passwordLenOffset)
  (Initial.inputBytes s saltOffset saltLenOffset)
  (Initial.inputBytes s secretOffset secretLenOffset)
  (Initial.inputBytes s adOffset adLenOffset))

structure Related (p : Params) (s t : State) : Prop where
  left : Ready p s
  right : Ready p t
  hashing : Initial.Related s t
  matrices : FillKernel.matrix s = FillKernel.matrix t
  outputs : FinalOutput.output s = FinalOutput.output t
  works : FinalOutput.work s = FinalOutput.work t
  indices : (Proof.Argon2.iterations p 0 p.passes (initial p s)).indices =
    (Proof.Argon2.iterations p 0 p.passes (initial p t)).indices

theorem code_rel (v : HPrime.Backend) (name : String) (p : Params) :
    RelCT isa (Related p) (Impl.Argon2.AArch64.InitialBody.code name v.hash) (fun _ _ => True) := by
  have hashed := ((Initial.code_rel v).mono (P' := Related p) (fun _ _ h => h.hashing)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Initial.initialHash_ok v s h.left.hashSpace h.left.inputs p h.left.header,
        Initial.initialHash_ok v t h.right.hashSpace h.right.inputs p h.right.header⟩)
  refine hashed.seq ((InitFill.code_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, hp, ⟨da, ha⟩, ⟨db, hb⟩⟩
  have baseA : FillKernel.matrix a = FillKernel.matrix s := ha.frame_word hp.left.hashSpace 232 (by decide) (by decide)
  have baseB : FillKernel.matrix b = FillKernel.matrix t := hb.frame_word hp.right.hashSpace 232 (by decide) (by decide)
  have outputA : FinalOutput.output a = FinalOutput.output s := ha.frame_word hp.left.hashSpace 256 (by decide) (by decide)
  have outputB : FinalOutput.output b = FinalOutput.output t := hb.frame_word hp.right.hashSpace 256 (by decide) (by decide)
  have workA : FinalOutput.work a = FinalOutput.work s := ha.frame_word hp.left.hashSpace 248 (by decide) (by decide)
  have workB : FinalOutput.work b = FinalOutput.work t := hb.frame_word hp.right.hashSpace 248 (by decide) (by decide)
  refine ⟨hashed_ready hp.left.filling hp.left.hashSpace ha, hashed_ready hp.right.filling hp.right.hashSpace hb,
    ha.x19.trans (hp.hashing.bp.trans hb.x19.symm), ha.sp.trans (hp.hashing.sp.trans hb.sp.symm),
    baseA.trans (hp.matrices.trans baseB.symm), outputA.trans (hp.outputs.trans outputB.symm),
    workA.trans (hp.works.trans workB.symm), ?_⟩
  unfold InitFill.initial
  rw [ha.x19, hb.x19, da, db]
  exact hp.indices

end VG.Proof.Argon2.AArch64.InitialBody
