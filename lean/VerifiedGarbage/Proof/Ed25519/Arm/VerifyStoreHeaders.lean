import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI

/-! Untrusted: preserve the three input pointers beyond the verification workspace. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyHeaders_ok {s : State} {b : BitVec 32} (hb : s.gpr .r3 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t => Ctx b t ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 8128, 12⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8128) 32 = s.gpr .r0 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8132) 32 = s.gpr .r1 ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 8136) 32 = s.gpr .r2 := by
  refine wp_movw fun a ha => wp_dp (op2_reg _ _) fun c hc => ?_
  have cp : c.gpr .r12 = b + BitVec.ofNat 32 8128 := by
    rw [hc.gpr]
    change a.gpr .r3 + a.gpr .r12 = _
    rw [ha.other _ (by decide), hb, ha.gpr]
    rfl
  have cr : Rest [.r12] s c := (ha.rest (by decide)).trans (hc.rest (by decide))
  have cm : c.mem = s.mem := hc.mem.trans ha.mem
  have ca (k : Nat) (hk : k + 8128 < 8192) :
      State.addr (c.gpr .r12 + BitVec.ofNat 32 k) = State.addr b + BitVec.ofNat 64 (8128 + k) := by
    rw [cp, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8128) (by decide)
    (by simpa only [Nat.add_zero] using ca 0 (by decide))
    (by rw [cr.wr]; exact in_base hw (by decide) (by decide)) fun d hd => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8132) (by decide)
    (by rw [hd.gpr]; exact ca 4 (by decide))
    (by rw [hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun e he => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 8136) (by decide)
    (by rw [he.gpr, hd.gpr]; exact ca 8 (by decide))
    (by rw [he.wr, hd.wr, cr.wr]; exact in_base hw (by decide) (by decide)) fun f hf => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (cr.mono (by decide)).trans
    ((hd.rest _).trans ((he.rest _).trans ((hf.rest _).trans (ht.rest (by decide)))))
  have mt : t.mem = ((s.mem.writeW (State.addr b + BitVec.ofNat 64 8128) (s.gpr .r0)).writeW
      (State.addr b + BitVec.ofNat 64 8132) (s.gpr .r1)).writeW
      (State.addr b + BitVec.ofNat 64 8136) (s.gpr .r2) := by
    rw [ht.mem, hf.mem, he.mem, hd.mem, cm, he.gpr, hd.gpr,
      cr.gpr .r2 (by decide), cr.gpr .r1 (by decide), cr.gpr .r0 (by decide)]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, kt, ?_, ?_, ?_, ?_⟩
  · rw [ht.gpr, hf.gpr, he.gpr, hd.gpr, cr.gpr .r3 (by decide), hb]
  · rw [mt]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  · rw [mt, Mem.readW_writeW_self32]

end VG.Proof.Ed25519.Arm
