import VerifiedGarbage.Impl.X25519.AArch64.Small
import VerifiedGarbage.Proof.X25519.AArch64.Word.Slots

/-! The single-row constant multiplication shares the checked carry fold. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

theorem moveHigh_ok (s : State) :
    WP isa (.block [VG.Impl.Ed25519.AArch64.mov .x20 .x21, .movz .w .x11 38 0]) s fun t =>
      t.gpr .x20 = s.gpr .x21 ∧ t.gpr .x11 = 38 ∧ Keeps [.x20,.x11] s t := by
  change WP isa (.block (([.addImm .x .x20 .x21 0] : List Instr) ++ [.movz .w .x11 38 0])) s _
  rw [WP.block_append_iff]
  have hm : WP isa (.block [.addImm .x .x20 .x21 0]) s fun t =>
      t.gpr .x20 = s.gpr .x21 ∧ Keeps [.x20] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,exec_addImm_x (imm := 0) (by decide),
      read_x,BitVec.add_zero,Option.some.injEq,exists_eq_left']
    exact ⟨RegUpd.gpr_write_self _ _ _ _,⟨fun r hr =>
      RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),rfl,rfl,rfl,rfl⟩⟩
  refine WP.mono hm fun a ⟨av,ka⟩ => ?_
  refine WP.mono (movz38_ok a) fun t ⟨tv,kt⟩ => ?_
  exact ⟨(kt.gpr _ (by decide)).trans av,tv,(ka.mono (by decide)).trans (kt.mono (by decide))⟩

theorem mulA24_ok {s : State} {base : Addr} (hs : Scratch s base) (o a : Slot) :
    WP isa (.block (VG.Impl.X25519.AArch64.mulA24 (offset o) (offset a))) s fun t =>
      Keep base s t ∧ env t.mem base = Function.update (env s.mem base) o (env s.mem base a * 121665) := by
  rw [VG.Impl.X25519.AArch64.mulA24]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun b ⟨bz,kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const64_ok b .x3 121665) fun c ⟨cv,kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok ((hs.of_keeps kb (by decide)).of_keeps kc (by decide))
    (slot_rangeWith (large := false) a) (by decide)) fun d ⟨d12,d13,d14,d15,kd⟩ => ?_
  have dz : d.gpr .x10 = 0 := by rw [kd.gpr _ (by decide),kc.gpr _ (by decide),bz]
  rw [WP.block_append_iff]
  refine WP.mono (rowFirst_ok d dz) fun e ⟨ev,ke⟩ => ?_
  have ep : val4 (e.gpr .x4) (e.gpr .x5) (e.gpr .x6) (e.gpr .x7) + 2^256*(e.gpr .x21).toNat =
      121665 * fe s.mem base (offset a) := by
    rw [kd.gpr _ (by decide),cv,show (121665 : BitVec 64).toNat = 121665 from rfl,
      d12,d13,d14,d15,kc.mem,kb.mem] at ev
    exact ev
  have eh : (e.gpr .x21).toNat < 2^52 := by
    have hh := val4_lt (word s.mem base (offset a)) (word s.mem base (offset a+8))
      (word s.mem base (offset a+16)) (word s.mem base (offset a+24))
    change fe s.mem base (offset a) < 2^256 at hh
    omega_using [ep,hh]
  rw [WP.block_append_iff]
  refine WP.mono (moveHigh_ok e) fun f ⟨fh,f38,kf⟩ => ?_
  have fz : f.gpr .x10 = 0 := by rw [kf.gpr _ (by decide),ke.gpr _ (by decide),dz]
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok f fz f38 (by rw [fh]; exact eh)) fun g ⟨gv,kg⟩ => ?_
  have kk : Keeps clob s g := (((((kb.mono (by decide)).trans (kc.mono (by decide))).trans
    (kd.mono (by decide))).trans (ke.mono (by decide))).trans (kf.mono (by decide))).trans (kg.mono (by decide))
  refine WP.mono (store4_ok (hs.of_keeps kk (by decide)) (slot_rangeWith (large := false) o)) fun t ht => ?_
  subst t
  have om := st4_outside g.mem base (by simp only [offset]; omega : offset o+32<2^64)
    (g.gpr .x4) (g.gpr .x5) (g.gpr .x6) (g.gpr .x7)
  have ov : Outside base (offset o) 32 s.mem (st4 g.mem base (offset o) (g.gpr .x4) (g.gpr .x5) (g.gpr .x6) (g.gpr .x7)) := by
    rw [← kk.mem]; exact om
  refine ⟨⟨kk.gpr,kk.rd,kk.wr,kk.sp,ov.mono (by simp [offset]) (by simp only [offset]; omega)⟩,?_⟩
  rw [env_update o ov]
  apply congrArg (Function.update (env s.mem base) o)
  change toFe (fe _ _ _) = _
  rw [fe_st4 _ _ (by simp only [offset]; omega),gv,fh,kf.gpr _ (by decide),kf.gpr _ (by decide),
    kf.gpr _ (by decide),kf.gpr _ (by decide)]
  have ee : toFe (121665 * fe s.mem base (offset a)) =
      toFe (val4 (e.gpr .x4) (e.gpr .x5) (e.gpr .x6) (e.gpr .x7) + 38*(e.gpr .x21).toNat) := by
    rw [← ep]
    apply toFe_congr
    exact fold256 _ _
  rw [← ee]
  exact toFe_mul rfl |>.trans (by simp only [show toFe 121665 = (121665 : Fe) from rfl,env,F]; exact mul_comm _ _)
end VG.Proof.X25519.AArch64.Word
