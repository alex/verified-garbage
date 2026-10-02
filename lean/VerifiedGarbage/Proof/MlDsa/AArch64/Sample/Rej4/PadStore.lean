import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pad

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq only_write)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (tailStore)

theorem tailStore_ok {s : State} {p : Addr} (hp : s.gpr .x2 = p)
    (hw4 : InRegions s.wr (wordAddr p 4) 16) (hw20 : InRegions s.wr (wordAddr p 20) 16) :
    WP isa (.block tailStore) s fun t => RegKeep [.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 4) 16 (ofVDwords (s.gpr .x6) (s.gpr .x7))).write
        (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) := by
  unfold tailStore
  refine wp_vop (d := .v0) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p 4) (by decide)
    (by rw [h2.gpr,h1.gpr,hp]; rfl) (by rw [h2.wr,h1.wr]; exact hw4) fun s3 h3 => ?_
  let s4 := s3.write .x .x9 (0x8000000000000000 : BitVec 64)
  refine VG.Proof.Sha3.AArch64.WP.cons (s' := s4) rfl ?_
  have h4 := only_write s3 .x .x9 (0x8000000000000000 : BitVec 64)
  refine wp_vop (d := .v0) rfl fun s5 h5 => ?_
  refine wp_strq (a := wordAddr p 20) (by decide)
    (by rw [h5.gpr,h4.get .x2,h3.gpr,h2.gpr,h1.gpr,hp]; rfl)
    (by rw [h5.wr,h4.wr,h3.wr,h2.wr,h1.wr]; exact hw20) fun t h6 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((((RegKeep.vupd h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3)).trans
      (RegKeep.only h4)).trans (RegKeep.vupd h5)).trans (RegKeep.vmem h6) |>.mono (by simp)
  · rw [h6.mem,h5.v,VG.AArch64.RegUpd.gpr_write_self,h5.mem,h4.mem,h3.mem,h2.v,h1.v,
      h1.gpr,h2.mem,h1.mem,setLane_pair_hi]
    rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4
