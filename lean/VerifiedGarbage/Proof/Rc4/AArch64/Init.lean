import VerifiedGarbage.Proof.Rc4.AArch64.ScheduleLoop

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4 RegUpd

theorem init_finish (s : State) (hp : InRegions s.wr (s.gpr .x0) 258) :
    WP isa (.block [.movz .w .x4 0 0, .strb .x4 .x0 256, .strb .x4 .x0 257,
      .movz .w .x0 0 0]) s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x0) = { table := (contextAt s.mem (s.gpr .x0)).table, i := 0, j := 0 } := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [State.store, h256, h257]
  exact context_finish _ _ _ _

theorem init_valid (s : State)
    (hlen : 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat)
    (hs : Mem.Sep (s.gpr .x0) (s.gpr .x1).toNat (s.gpr .x2) 256) :
    WP isa initValid s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat), i := 0, j := 0 } := by
  have hstart : WP isa (.block [.addImm .x .x17 .x0 0, .addImm .x .x0 .x2 0,
      .movz .x .x12 0 0, .movz .x .x9 255 0]) s fun a =>
      a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.gpr .x0 = s.gpr .x2 ∧
      a.gpr .x1 = s.gpr .x1 ∧ a.gpr .x17 = s.gpr .x0 ∧
      a.gpr .x12 = 0#64 ∧ a.gpr .x9 = 255#64 := by rrun
  unfold initValid
  refine WP.seq (WP.mono hstart fun a ha => ?_)
  obtain ⟨ham, har, haw, ha0, ha1, ha17, ha12, ha9⟩ := ha
  have hpa : InRegions a.wr (a.gpr .x0) 256 := by
    rw [haw, ha0]
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  have hka : InRegions (a.rd ++ a.wr) (a.gpr .x17) (a.gpr .x1).toNat := by
    rw [har, haw, ha17, ha1]; exact hk
  have hsa : Mem.Sep (a.gpr .x17) (a.gpr .x1).toNat (a.gpr .x0) 256 := by
    rw [ha17, ha1, ha0]; exact hs
  have hla : 1 ≤ (a.gpr .x1).toNat ∧ (a.gpr .x1).toNat ≤ 256 := ha1 ▸ hlen
  have hia : IdentityInv a 0 a := by
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · funext x
      simp only [IdentityMem, Nat.not_lt_zero, ite_false]
    · exact ha12
  refine WP.seq (WP.mono (identity_loop a a 0 (by decide) hpa hia) fun b hb => ?_)
  obtain ⟨hbm, hbr, hbw, hb0, hb1, hb17, hb9, _⟩ := hb
  have hreset : WP isa (.block [.movz .x .x12 0 0, .movz .x .x13 0 0, .movz .x .x3 0 0]) b
      (ScheduleInv a 0) := by
    have hframe : TableFrame (a.gpr .x0) a.mem b.mem := by
      intro x hx
      rw [hbm]
      simp only [IdentityMem, hx, ite_false]
    have htable : (contextAt b.mem (a.gpr .x0)).table = (schedulePrefix (keyAt a) 0).1 := by
      rw [hbm, identity_table, schedule_zero]
    rrun
    constructor <;> simp [gpr_write, mem_write, rd_write, wr_write, hframe, htable,
      schedule_zero, hbr, hbw, hb0, hb1, hb17, hb9, ha9]
  refine WP.seq (WP.mono hreset fun c hc => ?_)
  refine WP.seq (WP.mono (schedule_loop a c 0 (by decide) hla hpa hka hsa hc) fun d hd => ?_)
  have hpd : InRegions d.wr (d.gpr .x0) 258 := by rw [hd.wr, hd.p, haw, ha0]; exact hp
  refine WP.mono (init_finish d hpd) fun t ht => ?_
  refine ⟨ht.1, ?_⟩
  have htable := hd.table
  rw [← keySchedule_eq] at htable
  have hctx := ht.2
  rw [hd.p, htable, ha0] at hctx
  simpa only [keyAt, ham, ha17, ha1] using hctx

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = 0#64 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat)
    (hs : Mem.Sep (s.gpr .x0) (s.gpr .x1).toNat (s.gpr .x2) 256) :
    WP isa VG.Impl.Rc4.AArch64.init s fun t =>
      match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
      | .ok ctx => t.gpr .x0 = 0#64 ∧ contextAt t.mem (s.gpr .x2) = ctx
      | .error .invalidKeyLength => t.gpr .x0 = 1#64 := by
  have hcheck : WP isa (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x4 = (s.gpr .x1 - 1#64) >>> 8 := by rrun
  unfold VG.Impl.Rc4.AArch64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, ht0, ht1, ht2, ht4⟩ := ht
  let good := 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256
  have hcond : isa.eval (.nonzero .x .x4) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht4, BitVec.ofNat_eq_ofNat, bne]
    apply congrArg some
    by_cases hg : good
    · have hz := (valid_length (s.gpr .x1)).mpr hg
      rw [hz, beq_self_eq_true]
      simp only [hg, not_true_eq_false, decide_false, Bool.not_true]
    · have hn : (s.gpr .x1 - 1#64) >>> 8 ≠ 0#64 := fun hz => hg ((valid_length _).mp hz)
      rw [beq_eq_false_iff_ne.mpr hn]
      simp only [hg, not_false_eq_true, decide_true, Bool.not_false]
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
  · have hg : good := by
      have hnn := of_decide_eq_false hy
      exact Classical.not_not.mp hnn
    change 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .x2) 258 := by rw [htw, ht2]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .x0) (t.gpr .x1).toNat := by
      rw [htr, htw, ht0, ht1]; exact hk
    have hst : Mem.Sep (t.gpr .x0) (t.gpr .x1).toNat (t.gpr .x2) 256 := by
      rw [ht0, ht1, ht2]; exact hs
    have hlt : 1 ≤ (t.gpr .x1).toNat ∧ (t.gpr .x1).toNat ≤ 256 := ht1 ▸ hg
    refine WP.mono (init_valid t hlt hpt hkt hst) fun u hu => ?_
    simpa only [htm, ht0, ht1, ht2] using hu

end VG.Proof.Rc4.AArch64
