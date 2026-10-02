import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.Sha3.Seed34

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedWord)

/-- Load one complete word from each seed and pack the independent streams. -/
theorem seedWord_ok {s : State} {p a b : Addr} {j : Nat} (hj : j < 4)
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (hina : InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hinb : InRegions (s.rd++s.wr) (b+BitVec.ofNat 64 (8*j)) 8)
    (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block (seedWord j)) s fun t => RegKeep [.x6,.x7] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16 (ofVDwords
        (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64) (s.mem.readW (b+BitVec.ofNat 64 (8*j)) 64)) := by
  unfold seedWord
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [ha]) hina fun s1 h1 => ?_
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [h1.other .x4 (by decide),hb])
    (by rw [h1.rd,h1.wr]; exact hinb) fun s2 h2 => ?_
  refine wp_vop (d := .v0) rfl fun s3 h3 => wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := wordAddr p j) (by omega)
    (by rw [h4.gpr,h3.gpr,h2.other .x2 (by decide),h1.other .x2 (by decide),hp]; rfl)
    (by rw [h4.wr,h3.wr,h2.wr,h1.wr]; exact hw) fun t h5 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((((RegKeep.upd h1).trans (RegKeep.upd h2)).trans (RegKeep.vupd h3)).trans
      (RegKeep.vupd h4)).trans (RegKeep.vmem h5) |>.mono (by simp)
  · rw [h5.mem,h4.v,h3.v,h3.gpr,h2.gpr,h2.other .x6 (by decide),h1.gpr,
      h4.mem,h3.mem,h2.mem,h1.mem,setLane_pair_hi]
end VG.Proof.MlDsa.AArch64.Sample.Rej4
