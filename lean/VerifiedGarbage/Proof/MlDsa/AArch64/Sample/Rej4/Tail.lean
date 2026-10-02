import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.PadStore

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (seedTail tailPack)

theorem seedTail_ok {s : State} {p a b : Addr}
    (hp : s.gpr .x2 = p) (ha : s.gpr .x3 = a) (hb : s.gpr .x4 = b)
    (ha32 : InRegions (s.rd++s.wr) (a+32) 1) (ha33 : InRegions (s.rd++s.wr) (a+33) 1)
    (hb32 : InRegions (s.rd++s.wr) (b+32) 1) (hb33 : InRegions (s.rd++s.wr) (b+33) 1)
    (hw4 : InRegions s.wr (wordAddr p 4) 16) (hw20 : InRegions s.wr (wordAddr p 20) 16) :
    WP isa (.block seedTail) s fun t => RegKeep [.x6,.x7,.x8,.x9] s t ∧
      t.mem = (s.mem.write (wordAddr p 4) 16 (ofVDwords (tailWord s.mem a) (tailWord s.mem b))).write
        (wordAddr p 20) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) ∧
      Frame [pairR p] s.mem t.mem := by
  unfold seedTail
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (seedLast_ok (by decide) (by decide) ha ha32 ha33) fun s1 ⟨h1,e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedLast_ok (by decide) (by decide) ((h1.get .x4).trans hb)
    (by rw [h1.rd,h1.wr]; exact hb32) (by rw [h1.rd,h1.wr]; exact hb33)) fun s2 ⟨h2,e2⟩ => ?_
  unfold tailPack
  rw [WP.block_append_iff]
  refine WP.mono (tailAdd_ok s2) fun s3 ⟨h3,e3,e4⟩ => ?_
  refine WP.mono (tailStore_ok ((h3.get .x2).trans ((h2.get .x2).trans ((h1.get .x2).trans hp)))
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw4)
    (by rw [h3.wr,h2.wr,h1.wr]; exact hw20)) fun t ⟨h4,hm⟩ => ?_
  have e6 : s3.gpr .x6 = tailWord s.mem a := by rw [e3,h2.get .x6,e1]; rfl
  have e7 : s3.gpr .x7 = tailWord s.mem b := by rw [e4,e2,h1.mem]; rfl
  rw [e6,e7,h3.mem,h2.mem,h1.mem] at hm
  refine ⟨(((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.only h3)).trans h4 |>.mono (by simp),hm,?_⟩
  rw [hm]
  exact ((Frame.refl _ _).write (List.mem_singleton_self _) _ (pair_contains p (by decide))).write
    (List.mem_singleton_self _) _ (pair_contains p (by decide))
end VG.Proof.MlDsa.AArch64.Sample.Rej4
