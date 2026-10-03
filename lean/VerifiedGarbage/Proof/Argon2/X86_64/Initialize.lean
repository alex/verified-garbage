import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.Words

/-! Merged from `Proof.Argon2.X86_64.Copy`. -/
section
/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

theorem initWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hx : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) (8 * i.val)) 8)
    (hy : InRegions (s.rd ++ s.wr) (off (s.gpr .rsi) (8 * i.val)) 8) :
    let v := s.mem.readW (off (s.gpr .rdi) (8 * i.val)) 64 ^^^
      s.mem.readW (off (s.gpr .rsi) (8 * i.val)) 64
    WP isa (.block (initWord i.val)) s fun t =>
      t.mem = (s.mem.writeW (off p (8 * i.val)) v).writeW (off p (1024 + 8 * i.val)) v ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 8 * i.val) (n := 8) (by omega)
  have w2 := hs.write (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [initWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.store64, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hx, hy, w1, w2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

theorem finishWord_ok (s : State) {p : Addr} (hs : Scratch s p) (i : Fin 128)
    (hout : InRegions s.wr (off (s.gpr .rdi) (8 * i.val)) 8) :
    WP isa (.block (finishWord i.val)) s fun t =>
      t.mem = s.mem.writeW (off (s.gpr .rdi) (8 * i.val))
        (word s.mem p i.val ^^^ s.mem.readW (off p (8 * i.val)) 64) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 8 * i.val) (n := 8) (by omega)
  have r2 := hs.read (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, State.store64, execAlu, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hout, r1, r2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

end VG.Proof.Argon2.X86_64
end

/-! # Copy X XOR Y into both scratch blocks -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- Copying loops change only rax, memory, and flags. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (h' : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : Scratch s p) (h : CopyKeeps s t) :
    Scratch t p := ⟨(h.1 .rcx (by decide)).trans hs.reg, h.2.2 ▸ hs.wr⟩

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .rdi = x
  yreg : s.gpr .rsi = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : CopyKeeps s t) :
    Inputs t x y p := ⟨(hk.1 .rdi (by decide)).trans h.xreg,
      (hk.1 .rsi (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2] using h.xread,
      by simpa only [hk.2.1, hk.2.2] using h.yread, h.xsep, h.ysep⟩

theorem input_read {s : State} {x : Addr} (h : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (i : Fin 128) : InRegions (s.rd ++ s.wr) (off x (8 * i.val)) 8 :=
  ⟨_, h, Offset.contains_base x (by omega) (by omega)⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} (hf : Frame [⟨p, 4096⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) (i : Fin 128) :
    m'.readW (off x (8 * i.val)) 64 = m.readW (off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem init_store_frame (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    Frame [⟨p, 4096⟩] m
      ((m.writeW (off p (8 * i.val)) v).writeW (off p (1024 + 8 * i.val)) v) :=
  ((Frame.refl [⟨p, 4096⟩] m).writeW (r := ⟨p, 4096⟩) (by simp) v (Offset.contains_base p (by omega) (by omega))).writeW (r := ⟨p, 4096⟩)
    (by simp) v (Offset.contains_base p (by omega) (by omega))

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : Initialized m p r n) :
    Initialized ((m.writeW (off p (8 * n)) r[n]).writeW
      (off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  have lower (v : Word) :
      ((m.writeW (off p (8 * n)) r[n]).writeW (off p (1024 + 8 * n)) v).readW
        (off p (8 * i.val)) 64 = (m.writeW (off p (8 * n)) r[n]).readW
        (off p (8 * i.val)) 64 :=
    Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)
  by_cases he : i.val = n
  · subst n
    simp only [word, lower, Mem.readW_writeW_self64]
    exact ⟨rfl, rfl⟩
  · have hi' : i.val < n := by omega
    have sep1 : Mem.Sep (off p (8 * i.val)) 8 (off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep2 : Mem.Sep (off p (1024 + 8 * i.val)) 8 (off p (1024 + 8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep3 : Mem.Sep (off p (1024 + 8 * i.val)) 8 (off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    simp only [word, lower, Mem.readW_writeW_sep (w := 64) (w' := 64) sep1 (by decide),
      Mem.readW_writeW_sep (w := 64) (w' := 64) sep2 (by decide), Mem.readW_writeW_sep (w := 64) (w' := 64) sep3 (by decide)]
    exact h i hi'

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- Initialize an arbitrary prefix, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : Scratch s p) (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.X86_64.initWord)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (off (t.gpr .rdi) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact input_read htIn.xread ⟨n, hn'⟩
    have ly : InRegions (t.rd ++ t.wr) (off (t.gpr .rsi) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact input_read htIn.yread ⟨n, hn'⟩
    refine (initWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ lx ly).mono ?_
    rintro u ⟨hm, hreg, hr, hw⟩
    have hv : t.mem.readW (off x (8 * n)) 64 ^^^ t.mem.readW (off y (8 * n)) 64 =
        (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [xorBlock_get, blockAt_get, blockAt_get,
        input_unchanged hf hin.xsep ⟨n, hn'⟩, input_unchanged hf hin.ysep ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw⟩⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact initialized_step hn' ht
    · rw [hm, htIn.xreg, htIn.yreg]
      exact hf.trans (init_store_frame t.mem p ⟨n, hn'⟩ _)

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : Initialized m p r 128) :
    blockAt m p = r ∧ working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← working_get m p ⟨i, hi⟩] at he
    exact he

end VG.Proof.Argon2.X86_64
