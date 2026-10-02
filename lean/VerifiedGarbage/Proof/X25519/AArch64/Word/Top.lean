import VerifiedGarbage.Proof.X25519.AArch64.Word.Output
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! The four-word implementation under the unchanged RFC 7748 signature. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

/-- The shared signature also supplies the non-wrapping scratch range. -/
def localContract : Contract isa :=
  { Proof.X25519.x25519AArch64 with
    pre := fun s => Proof.X25519.x25519AArch64.pre s ∧ (s.gpr .x3).toNat + 4096 ≤ 2^64 }

theorem savedIndices : ∀ rd ∈ saved, ∃ i < 6,
    rd.1 = VG.Impl.X25519.AArch64.saved.getD i .x19 ∧ rd.2 = 8*i := by decide

theorem saved_of_words {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19)) :
    Saved base g m := by
  intro rd hr
  obtain ⟨i,hi,h1,h2⟩ := savedIndices rd hr
  rw [h1,h2]; exact h i hi

theorem preservedCases : ∀ r ∈ preserved,
    (∃ rd ∈ saved, rd.1 = r) ∨ r ∉ clob ++ ([.x0,.x1,.x19] : List Reg) := by decide

theorem correct {s₀ : State} (hp : localContract.pre s₀) :
    WP isa VG.Impl.X25519.AArch64.Word.x25519 s₀ fun t =>
      (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ localContract.post s₀ t := by
  have pre := VG.Proof.X25519.AArch64.Pre.of s₀ hp.1
  let base := s₀.gpr .x3
  have hs : Sc base s₀ := ⟨rfl,by rw [pre.wr]; simp [base,VG.Proof.X25519.AArch64.scR]⟩
  rw [VG.Impl.X25519.AArch64.Word.x25519]
  refine WP.seq (WP.mono (setup_ok hs hp.2 rfl rfl
    (by rw [pre.rd]; simp) (by rw [pre.rd]; simp) pre.scalar_sc pre.point_sc)
    fun a ⟨ha,ga,wa,oa,ba,sva,ka⟩ => ?_)
  refine WP.seq (WP.mono (ladder_ok ha ga wa ba) fun b ⟨kb,gb,wb⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok (kb.scratch ha) gb (ladderAfter_swap_le _ _ (by decide)) wb)
    fun c ⟨kc,cx,cz⟩ => ?_)
  have kac := kb.trans kc
  refine WP.seq (WP.mono (VG.Proof.Ed25519.AArch64.invert_ok (kac.scratch ha)) fun d ⟨kd,di⟩ => ?_)
  have kad := kac.trans (LoopKeep.of_invert kd)
  have od : d.gpr .x1 = s₀.gpr .x0 := (kad.gpr _ (by decide) (by decide)).trans oa
  have svd : Saved base s₀.gpr d.mem := (saved_of_words sva).outside kad.mem (by decide)
  have dx : env d.mem base 1 = env c.mem base 1 := by
    exact congrArg toFe (kd.mem.fe (Or.inl (by decide : offset 1+32 ≤ 512)) (by decide))
  refine WP.mono (finish_ok (kad.scratch ha) od
    (by rw [kad.wr,ka.wr,pre.wr]; simp) pre.out_sc svd) fun t ⟨tg,kt,rt⟩ => ?_
  refine ⟨fun r hr => ?_,?_⟩
  · rcases preservedCases r hr with ⟨rd,hrd,er⟩ | hn
    · rw [← er]; exact tg rd hrd
    · have kk := (ka.trans kad.kp).trans kt
      exact kk.sub (by decide) |>.gpr r hn
  · change bytesAt t.mem (s₀.gpr .x0) 32 = Spec.X25519.x25519
      (bytesAt s₀.mem (s₀.gpr .x1) 32) (bytesAt s₀.mem (s₀.gpr .x2) 32)
    rw [rt,dx,di,cx,cz,x25519_eq]

theorem x25519_ok (s : State) (hs : localContract.pre s) :
    ∃ tr t, Exec isa VG.Impl.X25519.AArch64.Word.x25519 s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr,t,he,hg,hp⟩ := correct hs
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he⟩,hp⟩
end VG.Proof.X25519.AArch64.Word
