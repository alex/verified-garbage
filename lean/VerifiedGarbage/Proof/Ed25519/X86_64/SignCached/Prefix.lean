import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Prune
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

/-! Save the expanded key's nonce prefix without changing its pruned scalar. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add decode_words)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem prefixRegs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block prefixRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = dw t L 4 ∧ t'.gpr .r9 = dw t L 5 ∧
      t'.gpr .r10 = dw t L 6 ∧ t'.gpr .r11 = dw t L 7 := by
  have h0 := hc.inFr (d := 176) (by omega) (by omega)
  have h1 := hc.inFr (d := 184) (by omega) (by omega)
  have h2 := hc.inFr (d := 192) (by omega) (by omega)
  have h3 := hc.inFr (d := 200) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixRegs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, Nat.reduceAdd,
    h0, h1, h2, h3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial⟩

theorem prefixStores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block prefixStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 56) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 64) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 72) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 48) (by omega) (by omega)
  have w1 := hc.inFrW (d := 56) (by omega) (by omega)
  have w2 := hc.inFrW (d := 64) (by omega) (by omega)
  have w3 := hc.inFrW (d := 72) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok (L.B + BitVec.ofNat 64 32) u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  simp only [add_add, Nat.reduceAdd] at hf h0 h1 h2 h3
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prefix_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (prefixRegs ++ prefixStores)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 =
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64).drop 32 := by
  rw [WP.block_append_iff]
  refine WP.mono (prefixRegs_ok hc) fun u ⟨hu, hm, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (prefixStores_ok hu) fun w ⟨hw, hf, _, h0, h1, h2, h3⟩ => ?_
  refine ⟨hw, hm ▸ hf, ?_⟩
  rw [Proof.Ed25519.signatureBytes_drop, add_add]
  rw [Proof.Ed25519.bytesAt_encodeLE w.mem, Proof.Ed25519.bytesAt_encodeLE t.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  simp only [decode_words, add_add, Nat.reduceAdd, h0, h1, h2, h3, h8, h9, h10, h11, dw,
    Nat.reduceMul]

end VG.Proof.Ed25519.X86_64.SignCached
