import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrb wp_lsl wp_add)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedLast)

def lastWord (m : Mem) (p : Addr) : BitVec 64 :=
  (m (p+32)).setWidth 64 + ((m (p+33)).setWidth 64 <<< 8)

/-- Read exactly the final two seed bytes into the low 16 bits of a scalar word. -/
theorem seedLast_ok {s : State} {r n : Reg} {a : Addr} (hr8 : r ≠ .x8)
    (hnr : n ≠ r) (ha : s.gpr n = a)
    (hin32 : InRegions (s.rd++s.wr) (a+32) 1)
    (hin33 : InRegions (s.rd++s.wr) (a+33) 1) :
    WP isa (.block (seedLast r n)) s fun t => Only [r,.x8] s t ∧ t.gpr r = lastWord s.mem a := by
  unfold seedLast
  refine wp_ldrb (a := a+32) (by decide) (by rw [ha]; rfl) hin32 fun s1 h1 e1 => ?_
  refine wp_ldrb (a := a+33) (by decide) (by rw [h1.get n (by simpa using hnr),ha]; rfl)
    (by rw [h1.rd,h1.wr]; exact hin33) fun s2 h2 e2 => ?_
  refine wp_lsl (by decide) fun s3 h3 e3 => wp_add fun t h4 e4 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact (((h1.trans h2).trans h3).trans h4).mono (by simp)
  · rw [e4,e3,h3.get r (by simpa using hr8),h2.get r (by simpa using hr8),e1,e2,h1.mem]
    rfl
end VG.Proof.MlDsa.AArch64.Sample.Rej4
