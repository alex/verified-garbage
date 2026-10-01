import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Layout
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-! Pruning and saving the expanded signing scalar. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (pkPruneStores stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add prune_words decode_words take_bytesAt)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Frame stores cannot overwrite the saved arguments. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) {d n : Nat}
    (_hd : 16 ≤ d) (hn : d + n ≤ 208)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 d, n⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ e, 216 ≤ e → e + 8 ≤ 264 →
      t'.mem.readW (L.B + BitVec.ofNat 64 e) 64 = t.mem.readW (L.B + BitVec.ofNat 64 e) 64 := by
    intro e h₁ h₂
    exact hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr h => (hg r hr).trans (hc.cs r hr h), by rw [hmx]; exact hc.mx,
    (keep 216 (by omega) (by omega)).trans hc.pScr,
    (keep 224 (by omega) (by omega)).trans hc.pLen,
    (keep 232 (by omega) (by omega)).trans hc.pMsg,
    (keep 240 (by omega) (by omega)).trans hc.pPk,
    (keep 248 (by omega) (by omega)).trans hc.pSeed,
    (keep 256 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf ?_)⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

abbrev dw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.B + BitVec.ofNat 64 (144 + 8 * k)) 64

theorem pruneRegs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pruneRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = dw t L 1 ∧
      t'.gpr .r10 = dw t L 2 ∧
      t'.gpr .r11 = ((dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  have s0 := hc.inFr (d := 144) (by omega) (by omega)
  have s1 := hc.inFr (d := 152) (by omega) (by omega)
  have s2 := hc.inFr (d := 160) (by omega) (by omega)
  have s3 := hc.inFr (d := 168) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pruneRegs, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk, hc.rsp, add_add, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, 
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-8)) = BitVec.ofNat 64 (2 ^ 64 - 8)),
    trivial, trivial, trivial⟩

theorem stores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega) (by omega)
  have w1 := hc.inFrW (d := 24) (by omega) (by omega)
  have w2 := hc.inFrW (d := 32) (by omega) (by omega)
  have w3 := hc.inFrW (d := 40) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store (by decide) (by decide) rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = h) :
    WP isa (.block (pruneRegs ++ pkPruneStores)) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (pruneRegs_ok hc) fun u ⟨hcu, hmu, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (stores_ok hcu) fun u' ⟨hcu', hf, _, r0, r1, r2, r3⟩ => ?_
  refine ⟨hcu', hmu ▸ hf, ?_⟩
  rw [Spec.Ed25519.prune, ← hh, take_bytesAt]
  simp only [decode_words, add_add, Nat.reduceAdd, r0, r1, r2, r3, h8, h9, h10, h11]
  exact (prune_words _ _ _ _).symm

end VG.Proof.Ed25519.X86_64.SignCached
