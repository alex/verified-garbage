import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (ctrs)

/-- The byte-order numeric counter word occupies the last memory dword;
the cached prefix has that dword zero. -/
def counterLane (c : BitVec 32) (pfx : BitVec 128) : BitVec 128 :=
  XBinOp.eval .por (XShiftOp.eval .pslldq ((0 : BitVec 96) ++ bswap c) 12) pfx

/-- Inserting the byte-swapped low word preserves all 96 prefix bits. -/
theorem counterLane_eq (c : BitVec 32) (pfx : BitVec 96) :
    counterLane c ((0 : BitVec 32) ++ pfx) = bswap c ++ pfx := by
  change ((((0 : BitVec 96) ++ bswap c) <<< 96) ||| ((0 : BitVec 32) ++ pfx)) = _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < 96 <;> simp [h, BitVec.ofNat_eq_ofNat]
  simp [show i - 96 < 32 by omega, show i < 128 by omega]

/-- The two byte shifts cache exactly the first twelve memory bytes. -/
theorem cache_prefix (v : BitVec 128) :
    XShiftOp.eval .psrldq (XShiftOp.eval .pslldq v 4) 4 =
      (0 : BitVec 32) ++ v.extractLsb' 0 96 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change ((v <<< 32) >>> 32).getLsbD i = _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split <;> simp_all <;> omega

theorem counter_one (b : XReg) (s : State) (hb : b ≠ .xmm7) :
    WP isa (.block (ctrs [b])) s fun s' =>
      s'.xmm b = counterLane (s.gpr .ebx) (s.xmm .xmm7) ∧
      s'.gpr .ebx = s.gpr .ebx + 1 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [ctrs, List.append_nil]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, execAlu, counterLane, gpr_setReg,
    gpr_setXmm, xmm_setReg, xmm_setXmm, xmm_arithFlags, mem_setReg, rd_setReg,
    wr_setReg, ite_true, ite_false, Ne.symm hb, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · intro r heax hebx
    simp only [hebx, ite_false, gpr_arithFlags, gpr_setXmm, gpr_setReg, heax]
  · simp only [mem_arithFlags, mem_setXmm, mem_setReg]
  · simp only [rd_arithFlags, rd_setXmm, rd_setReg]
  · simp only [wr_arithFlags, wr_setXmm, wr_setReg]
  · intro r hr
    simp only [hr, ite_false]

structure CounterFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem CounterFrame.refl (rs : List XReg) (s : State) : CounterFrame rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem CounterFrame.comp {rs rs' : List XReg} {s s' s'' : State}
    (h : CounterFrame rs s s') (h' : CounterFrame rs' s' s'') :
    CounterFrame (rs ++ rs') s s'' :=
  ⟨fun r h1 h2 => (h'.gpr r h1 h2).trans (h.gpr r h1 h2),
    h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem CounterFrame.mono {rs rs' : List XReg} {s s' : State}
    (h : CounterFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') : CounterFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

theorem add_one_index (c : BitVec 32) (k : Nat) :
    c + 1 + BitVec.ofNat 32 k = c + BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm (1 : BitVec 32)]
  rfl

theorem counters_ok (regs : List XReg) (s : State) (hnd : regs.Nodup)
    (h7 : .xmm7 ∉ regs) :
    WP isa (.block (ctrs regs)) s fun s' =>
      (∀ k (h : k < regs.length), s'.xmm regs[k] =
        counterLane (s.gpr .ebx + BitVec.ofNat 32 k) (s.xmm .xmm7)) ∧
      s'.gpr .ebx = s.gpr .ebx + BitVec.ofNat 32 regs.length ∧
      CounterFrame regs s s' := by
  induction regs generalizing s with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h (by simp),
      (BitVec.add_zero _).symm, CounterFrame.refl _ _⟩
  | cons b bs ih =>
    have hb7 : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self ..)
    have hb : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [ctrs, WP.block_append_iff]
    refine WP.mono (counter_one b s hb7) fun s₁ ⟨hv₁, hc₁, hg₁, hm₁, hr₁, hw₁, hx₁⟩ => ?_
    have hf₁ : CounterFrame [b] s s₁ :=
      ⟨hg₁, hm₁, hr₁, hw₁, fun r hr => hx₁ r (by simpa using hr)⟩
    refine WP.mono (ih s₁ (List.nodup_cons.mp hnd).2
      (fun h => h7 (List.mem_cons_of_mem _ h))) fun s' ⟨hv, hc, hf⟩ => ⟨?_, ?_, ?_⟩
    · intro k hk
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, BitVec.add_zero]
        rw [hf.xmm b hb, hv₁]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [hv k (by simpa using hk), hc₁, hx₁ .xmm7 (Ne.symm hb7), add_one_index]
    · rw [hc, hc₁, add_one_index, List.length_cons]
    · exact (hf₁.comp hf).mono (by simp)

end VG.Proof.Aes.X86.AesNi
