import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Groups
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress

/-!
# SHA-256 compression function on x86-64 with AVX2 and BMI

Untrusted: everything here is checked by Lean. `compress_verified` proves
`Impl.Sha256.X86_64.Avx2.compress` against the same contract as the scalar
`vg_sha256_compress`, reusing its precondition (`Pre`) and block lemmas.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha256.X86_64.ShaNi (quad load_quad)
open VG.Proof.Sha256.X86_64 (Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' sub_offset toNat_ofNat_lt ofInt_natCast stateAt_get stateAt_eq
  readW_writeW_save readW_writeW_word writeState stateAt_writeState frame_writeState)

/-! ## The prologue -/

/-- The callee-saved registers are saved in the scratch space. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((512 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((520 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((528 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((536 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((544 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((552 : Nat) : Int)) 64 = s₀.gpr .r15

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((512 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((520 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((528 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((536 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((544 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((552 : Nat) : Int)) (s₀.gpr .r15)

theorem out_save {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 8 ≤ 560) :
    InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ const mBswap bswapMask ++ const mBA maskBA ++ const mDC maskDC ++
      ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ Masks s₁ := by
  have o0 := out_save hp (d := 512) (by omega); have o1 := out_save hp (d := 520) (by omega)
  have o2 := out_save hp (d := 528) (by omega); have o3 := out_save hp (d := 536) (by omega)
  have o4 := out_save hp (d := 544) (by omega); have o5 := out_save hp (d := 552) (by omega)
  apply WP.of_runBlock
  simp only [save, saved, const, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at, VOp.exec, State.setV, State.lane,
    State.store64, State.setReg, arithFlags, State.setFlags, o0, o1, o2, o3, o4, o5, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], trivial, trivial, rfl, trivial, ?_⟩
  simp (config := {decide := true}) only [Masks, mBA, mDC, mBswap, ite_true, ite_false, VBinOp.sse,
    movq_const, and_self]

/-! ## Loading the blocks -/

theorem load_ok {i : Nat} (hi : i < 4) (s : State) {p₀ p₁ scr : Addr} {M₀ M₁ : Block}
    (hrsi : s.gpr .rsi = p₀) (hr15 : s.gpr .r15 = p₁) (hrcx : s.gpr .rcx = scr)
    (hin₀ : InRegions (s.rd ++ s.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hout : InRegions s.wr (wAddr scr i) 32)
    (hm : s.xmm mBswap = bswapMask) (hm' : s.ymmHi mBswap = bswapMask)
    (hb₀ : ∀ t : Nat, t < 16 → bswap32 (s.mem.readW (p₀ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₀ t)
    (hb₁ : ∀ t : Nat, t < 16 → bswap32 (s.mem.readW (p₁ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₁ t) :
    WP isa (.block (load i)) s fun s' =>
      s'.xmm (msg i) = quad M₀ i ∧ s'.ymmHi (msg i) = quad M₁ i ∧
      (∀ r, r ≠ msg i → r ≠ tmp → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem.writeW (wAddr scr i) (quad M₁ i ++ quad M₀ i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup i
  have hd' := VG.nodup_reverse hd
  have q₀ := load_quad M₀ s.mem p₀ hi hb₀
  have q₁ := load_quad M₁ s.mem p₁ hi hb₁
  have e : bswapMask = Impl.Sha256.X86_64.ShaNi.bswapMask := rfl
  rw [← e] at q₀ q₁
  apply WP.of_runBlock
  simp only [load, vb]
  generalize msg i = x at *
  simp only [T, t0, t1, t2, t3, mBA, mDC, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd' hm hm' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.lane, State.ymm, State.store256, State.load128, ea_at, hrsi, hr15, hrcx, hin₀,
    hin₁, hout, ite_true, ite_false, hd, hd', hm, hm', VBinOp.sse, q₀, q₁, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## The hash value -/

/-- The working variables `v` are in the registers of round 0. -/
def Vars8 (s : State) (v : HashValue) : Prop :=
  s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
  s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
  s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
  s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64

theorem Vars.vars8 {s : State} {v : HashValue} (h : Vars 64 s v) : Vars8 s v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem loadState_eq : loadState = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .rbx (.mem (at_ .rdi (4 * 1))),
    .mov32 .rbp (.mem (at_ .rdi (4 * 2))), .mov32 .r8 (.mem (at_ .rdi (4 * 3))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 4))), .mov32 .r10 (.mem (at_ .rdi (4 * 5))),
    .mov32 .r11 (.mem (at_ .rdi (4 * 6))), .mov32 .r12 (.mem (at_ .rdi (4 * 7)))] := by
  decide

theorem addState_eq : addState = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .rbx (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .rbp (.mem (at_ .rdi (4 * 2))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 3))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 4))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 5))),
    .alu32 .add .r11 (.mem (at_ .rdi (4 * 6))), .alu32 .add .r12 (.mem (at_ .rdi (4 * 7))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .rbx,
    .store32 (at_ .rdi (4 * 2)) .rbp, .store32 (at_ .rdi (4 * 3)) .r8,
    .store32 (at_ .rdi (4 * 4)) .r9, .store32 (at_ .rdi (4 * 5)) .r10,
    .store32 (at_ .rdi (4 * 6)) .r11, .store32 (at_ .rdi (4 * 7)) .r12] := by
  decide

theorem initCarry_eq : initCarry = [.mov32 .r13 (.reg .rbx), .alu32 .xor .r13 (.reg .rbp)] := rfl

set_option simprocs false in
theorem loadState_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block loadState) s fun s₁ => Vars8 s₁ (stateAt s.mem (st s₀)) ∧ Keeps s s₁ := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [loadState_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp (config := {decide := true}) only [Vars8, Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, State.setReg, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
    s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
    s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
    s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64 ∧
    s.gpr .r13 = (v[1] ^^^ v[2]).setWidth 64 := Iff.rfl

theorem initCarry_ok {s : State} {v : HashValue} (hv : Vars8 s v) :
    WP isa (.block initCarry) s fun s₁ => Vars 0 s₁ v ∧ Keeps s s₁ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  rw [initCarry_eq]
  simp (config := {decide := true}) only [vars0, Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32, isa, State.setReg32, State.setReg, arithFlags, State.setFlags,
    h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r hr => by
    simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl, trivial⟩

set_option simprocs false in
theorem addState_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars8 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block addState) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      Vars8 s' (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [addState_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32,
    isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg, arithFlags,
    State.setFlags, hrdi, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, trivial⟩
  · simp only [writeState, Vector.getElem_zipWith]
  · simp (config := {decide := true}) only [Vars8, Vector.getElem_zipWith, ite_true, ite_false, and_self]
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After loading words `0 … 4n-1` of both blocks, from the state `sL`. -/
structure LdInv (M₀ M₁ : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = sL.gpr
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  masks : Masks s
  frame : Frame [wRegion scr] sL.mem s.mem
  wmem : ∀ k < n, WMem s.mem scr M₀ M₁ k
  msgs : ∀ k < n, s.xmm (msg k) = quad M₀ k ∧ s.ymmHi (msg k) = quad M₁ k

theorem load_step {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p₀) (hr15 : sL.gpr .r15 = p₁) (hrcx : sL.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 4 → InRegions (sL.rd ++ sL.wr) (p₀ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (sL.rd ++ sL.wr) (p₁ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [wRegion scr] sL.mem m →
      (∀ t : Nat, t < 16 → bswap32 (m.readW (p₀ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₀ t) ∧
      (∀ t : Nat, t < 16 → bswap32 (m.readW (p₁ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₁ t))
    {n : Nat} (hn : n < 4) {s : State} (h : LdInv M₀ M₁ scr sL n s) :
    WP isa (.block (load n)) s (LdInv M₀ M₁ scr sL (n + 1)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h.masks
  have hb := hblk _ h.frame
  refine WP.mono (load_ok (p₀ := p₀) (p₁ := p₁) (scr := scr) (M₀ := M₀) (M₁ := M₁) hn s (by rw [h.gpr]; exact hrsi) (by rw [h.gpr]; exact hr15)
    (by rw [h.gpr]; exact hrcx) (by rw [h.rd, h.wr]; exact (hin n hn).1) (by rw [h.rd, h.wr]; exact (hin n hn).2)
    (by rw [h.wr]; exact in_scr hR (by omega)) k5 k6 hb.1 hb.2)
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ⟨hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
  · have o := fun r (hr : r = mBA ∨ r = mDC ∨ r = mBswap) =>
      hx r (sched_other n r (by rcases hr with h | h | h <;> simp [h])).1 (by rcases hr with rfl | rfl | rfl <;> decide)
    rw [Masks, (o mBA (by simp)).1, (o mBA (by simp)).2, (o mDC (by simp)).1, (o mDC (by simp)).2,
      (o mBswap (by simp)).1, (o mBswap (by simp)).2]
    exact ⟨k1, k2, k3, k4, k5, k6⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (wAddr_contains scr (by omega))
  · intro k hk
    rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact wmem_self _ _ _ _ _
    · exact wmem_write (by omega) (by omega) hkn _ (h.wmem k (by omega))
  · intro k hk
    by_cases hkn : k = n
    · subst hkn; exact ⟨ex, ey⟩
    · have o₁ := (msg_ne k n (by omega) (by omega)).1
      have o₂ := (sched_other k tmp (by simp)).1
      rw [(hx _ (Ne.symm o₁) (Ne.symm o₂)).1, (hx _ (Ne.symm o₁) (Ne.symm o₂)).2]
      exact h.msgs k (by omega)

/-! ## Counting the blocks -/

theorem e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem e2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide
theorem e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
theorem e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide

theorem pub_ne15 {r : Reg} (hr : r ∈ pubRegs) : r ≠ .r15 := by
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem setup_ok (s : State) :
    WP isa (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr .r15 = s.gpr .rsi ∧
      (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [T, Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, e1, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r hr => by simp [hr], trivial, trivial, trivial,
    fun r hr => by simp [pub_ne15 hr], trivial⟩

theorem next_ok (s : State) :
    WP isa (.block [.alu .add T (.imm 64)]) s fun s' =>
      s'.gpr .r15 = s.gpr .r15 + 64 ∧ (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [T, Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, e64, ite_true, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, fun r hr => by simp [pub_ne15 hr], trivial⟩

theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr = s.gpr ∧ Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, arithFlags, State.setFlags, e1, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial⟩

theorem adv_ok (s : State) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## Regions -/

theorem wsub (p : Addr) : Region.Sub (wRegion p) ⟨p, 560⟩ := Region.sub_prefix (by omega)

theorem slot_sub (p : Addr) {d n : Nat} (hd : d + n ≤ 560) :
    Region.Sub ⟨p + BitVec.ofInt 64 (d : Int), n⟩ ⟨p, 560⟩ := by
  rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)

theorem saveSlot_w (p : Addr) {d : Nat} (hd : 512 ≤ d) (hd' : d + 8 ≤ 560) :
    Region.Disjoint ⟨p + BitVec.ofInt 64 (d : Int), 8⟩ (wRegion p) := by
  intro a h₁ h₂
  simp only [Region.Contains, ofInt_natCast, Offset.sub_add_eq, Offset.toNat_sub_ofNat] at h₁ h₂
  have := (a - p).isLt
  omega

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame [wRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' := by
  have key : ∀ d : Nat, 512 ≤ d → d + 8 ≤ 560 →
      m'.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 = m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
    intro d hd hd'
    rcases hf with hf | hf
    · exact hf.readW (Region.contains_self _ _) (by simpa using saveSlot_w (scr s₀) hd hd') (by decide)
    · exact hf.readW (Region.contains_self _ _)
        (by simpa using Region.Disjoint.sub_left hp.st_scr.symm (slot_sub (scr s₀) hd')) (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 512 (by omega) (by omega)).trans h1, (key 520 (by omega) (by omega)).trans h2,
    (key 528 (by omega) (by omega)).trans h3, (key 536 (by omega) (by omega)).trans h4,
    (key 544 (by omega) (by omega)).trans h5, (key 552 (by omega) (by omega)).trans h6⟩

theorem wmem_frame_st {s₀ : State} (hp : Pre s₀) {m m' : Mem} {M₀ M₁ : Block} {k : Nat} (hk : k < 16)
    (h : WMem m (scr s₀) M₀ M₁ k) (hf : Frame [stR s₀] m m') : WMem m' (scr s₀) M₀ M₁ k := by
  simp only [WMem] at h ⊢
  rw [← h]
  have hd := Region.Disjoint.sub_left hp.st_scr.symm (slot_sub (scr s₀) (d := 32 * k) (n := 32) (by omega))
  exact hf.readW (Region.contains_self _ _) (by simp only [List.mem_singleton, forall_eq]; exact hd)
    (by decide)

theorem state_frame_w {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [wRegion (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  apply stateAt_eq
  intro k hk
  rw [hf.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
    (by simpa using Region.Disjoint.sub_right hp.st_scr (wsub _)) (by decide), ← stateAt_get _ _ hk]

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : Saved s₀ s.mem
  masks : Masks s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-- The block in lane 1: the next one if there is one, else block `i` again. -/
abbrev nxt (s₀ : State) (i : Nat) : Nat := if nb s₀ - i = 1 then i else i + 1

/-- After the first block of an iteration. -/
structure Mid (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ (i + 1) s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  vars : Vars8 s (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))
  wmem : ∀ k < 16, WMem s.mem (scr s₀) (blk s₀ i) (blk s₀ (nxt s₀ i)) k
  e : eval .e s = some (nb s₀ - i == 1)

theorem sub_one_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (BitVec.ofNat 64 (nb s₀ - i) - 1 == 0) = (nb s₀ - i == 1) := by
  have := hp.nb_lt
  have hn : nb s₀ - i < 2 ^ 64 := by omega
  have h1 : 1 ≤ nb s₀ - i := by omega
  generalize nb s₀ - i = n at *
  by_cases h : n = 1
  · subst h; decide
  · have h' : BitVec.ofNat 64 n - 1 ≠ 0 := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat h1]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h (by have h2 : n - 1 = 0 := this; omega)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

theorem blk_read {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {m m' : Mem}
    (hf : Frame [stR s₀, scrR s₀] s₀.mem m) (hf' : Frame [wRegion (scr s₀)] m m') :
    ∀ t : Nat, t < 16 → bswap32 (m'.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) =
      W (blk s₀ i) t := by
  intro t ht
  rw [hf'.readW (hp.blk_contains hi ht) (by simpa using Region.Disjoint.sub_right hp.blk_scr (wsub _)) (by decide),
    hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
  exact blk_word i t ht

/-- The first block of an iteration, up to the choice of whether there is a second. -/
theorem first_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s)
    {G : Prog isa} {Q : State → Prop} (hG : ∀ s', Mid s₀ i s' → WP isa G s' Q) :
    WP isa (.seq (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)])
      (.seq (.ite .e (.block []) (.block [.alu .add T (.imm 64)]))
      (.seq (.block (load 0 ++ load 1 ++ load 2 ++ load 3 ++ loadState ++ initCarry))
      (.seq (groups 16)
      (.seq (.block addState)
      (.seq (.block [.alu .cmp .rdx (.imm 1)]) G)))))) s Q := by
  have := hp.nb_lt
  have hscr : (⟨scr s₀, 560⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  have hj : nxt s₀ i < nb s₀ := by simp only [nxt]; split <;> omega
  have hb : (s.gpr .rdx - 1 == 0) = (nb s₀ - i == 1) := by rw [hL.rdx]; exact sub_one_eq hp hi
  refine WP.seq (WP.mono (setup_ok s) fun s₁ ⟨he₁, h15₁, hg₁, hk₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r15 = blkAddr s₀ (nxt s₀ i) ∧
    (∀ r, r ≠ .r15 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂) ?_ fun s₂ ⟨h15₂, hg₂, hk₂⟩ => ?_)
  · refine WP.ite _ he₁ (fun h => ?_) (fun h => ?_)
    · rw [hb, beq_iff_eq] at h
      refine WP.block_nil ⟨?_, hg₁, hk₁⟩
      simp only [nxt, h, ↓reduceIte, h15₁, hL.rsi]
    · refine WP.mono (next_ok s₁) fun s₂ ⟨e15, eg, ek⟩ =>
        ⟨?_, fun r hr => (eg r hr).trans (hg₁ r hr), hk₁.trans ek⟩
      rw [hb, beq_eq_false_iff_ne] at h
      rw [e15, h15₁, hL.rsi]
      simp only [nxt, h, ↓reduceIte, blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 1) = 64 * i + 64 by omega]
  obtain ⟨hm₂, hrd₂, hwr₂, -, hx₂, hy₂⟩ := hk₂
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => hg₂ r (pub_ne15 hr)
  have hrsi₂ : s₂.gpr .rsi = blkAddr s₀ i := (pub₂ .rsi (by decide)).trans hL.rsi
  have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hL.rcx
  have hrdi₂ : s₂.gpr .rdi = st s₀ := (pub₂ .rdi (by decide)).trans hL.rdi
  have hR₂ : (⟨scr s₀, 560⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hL.wr]; exact hscr
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem := hm₂ ▸ hL.frame
  have hin : ∀ n : Nat, n < 4 →
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ (nxt s₀ i) + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 :=
    fun n hn => by rw [hrd₂, hwr₂, hL.rd, hL.wr]; exact ⟨ShaNi.Pre.in_blk16 hp hi hn, ShaNi.Pre.in_blk16 hp hj hn⟩
  have hblk := fun m (hm : Frame [wRegion (scr s₀)] s₂.mem m) =>
    And.intro (blk_read hp hi hf₂ hm) (blk_read hp hj hf₂ hm)
  have step := fun {n : Nat} (hn : n < 4) {x : State} (h : LdInv (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ n x) =>
    load_step hrsi₂ h15₂ hrcx₂ hR₂ hin hblk hn h
  have h₀ : LdInv (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₂ 0 s₂ :=
    ⟨rfl, rfl, rfl, by rw [Masks, hx₂, hy₂]; exact hL.masks, Frame.refl _ _, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (step (by omega) h₀) fun x₁ h₁ => ?_
  refine WP.mono (step (by omega) h₁) fun x₂ h₂ => ?_
  refine WP.mono (step (by omega) h₂) fun x₃ h₃ => ?_
  refine WP.mono (step (by omega) h₃) fun s₃ ld => ?_
  refine WP.mono (loadState_ok hp (by rw [ld.gpr]; exact hrdi₂) (by rw [ld.rd, hrd₂, hL.rd])
    (by rw [ld.wr, hwr₂, hL.wr])) fun s₄ ⟨hv₄, hk₄⟩ => ?_
  refine WP.mono (initCarry_ok hv₄) fun s₅ ⟨hv₅, hk₅⟩ => ?_
  have hk₃₅ := hk₄.trans hk₅
  obtain ⟨hm₅, hrd₅, hwr₅, pub₅, hx₅, hy₅⟩ := hk₃₅
  have hrcx₅ : s₅.gpr .rcx = scr s₀ := by rw [pub₅ .rcx (by decide), ld.gpr]; exact hrcx₂
  have hR₅ : (⟨scr s₀, 560⟩ : Region) ∈ s₅.wr := by rw [hwr₅, ld.wr]; exact hR₂
  have hS : Sched (blk s₀ i) (blk s₀ (nxt s₀ i)) (scr s₀) s₅ 0 s₅ :=
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Masks, hx₅, hy₅]; exact ld.masks, Frame.refl _ _,
      fun k _ hk => by rw [hm₅]; exact ld.wmem k (by omega),
      fun k _ hk _ => by rw [hx₅, hy₅]; exact ld.msgs k (by omega)⟩
  refine WP.seq (WP.mono (groups_ok _ _ _ _ s₅ hrcx₅ hR₅ ⟨hv₅, hS⟩ 16 (Nat.le_refl _)) fun s₆ ⟨hv₆, hS₆⟩ => ?_)
  have hHi : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i := by
    rw [state_frame_w hp ld.frame, hm₂]; exact hL.state
  have pub₆ : ∀ r ∈ pubRegs, s₆.gpr r = s.gpr r := fun r hr => by
    rw [hS₆.pub r hr, pub₅ r hr, ld.gpr, pub₂ r hr]
  have hrd₆ : s₆.rd = s₀.rd := by rw [hS₆.rd, hrd₅, ld.rd, hrd₂, hL.rd]
  have hwr₆ : s₆.wr = s₀.wr := by rw [hS₆.wr, hwr₅, ld.wr, hwr₂, hL.wr]
  have hH₆ : ∀ k : Nat, (hk : k < 8) →
      s₆.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = (stateAt s₃.mem (st s₀))[k] :=
    fun k hk => by rw [← stateAt_get _ _ hk, state_frame_w hp hS₆.frame, hm₅]
  refine WP.seq (WP.mono (addState_ok hp _ _ (Vars.vars8 hv₆) ((pub₆ .rdi (by decide)).trans hL.rdi) hrd₆ hwr₆
    hH₆) fun s₇ ⟨hm₇, hv₇, pub₇, hrd₇, hwr₇, hx₇, hy₇⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₇) fun s₈ ⟨he₈, hg₈, hk₈⟩ => hG s₈ ?_)
  obtain ⟨hm₈, hrd₈, hwr₈, -, hx₈, hy₈⟩ := hk₈
  have pub₈ : ∀ r ∈ pubRegs, s₈.gpr r = s.gpr r := fun r hr => by rw [hg₈, pub₇ r hr, pub₆ r hr]
  have hc : Vector.zipWith (· + ·) (Spec.Sha256.rounds (stateAt s₃.mem (st s₀)) (blk s₀ i) (4 * 16))
      (stateAt s₃.mem (st s₀)) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hHi]; rfl
  have hfw : Frame [stR s₀] s₆.mem s₇.mem := by
    rw [hm₇]; exact frame_writeState (Frame.refl _ _) _
  have hsub : ∀ r ∈ [wRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact wsub _⟩
  have hsub' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pub₈ .rdi (by decide)]; exact hL.rdi
  · rw [pub₈ .rcx (by decide)]; exact hL.rcx
  · rw [pub₈ .rsp (by decide)]; exact hL.rsp
  · rw [hrd₈, hrd₇]; exact hrd₆
  · rw [hwr₈, hwr₇]; exact hwr₆
  · rw [hm₈]
    refine hf₂.trans ((ld.frame.sub hsub).trans ?_)
    rw [← hm₅]
    exact (hS₆.frame.sub hsub).trans (hfw.sub hsub')
  · rw [hm₈, hm₇, stateAt_writeState]; exact hc
  · rw [hm₈]
    refine saved_frame hp ?_ (.inr hfw)
    refine saved_frame hp ?_ (.inl hS₆.frame)
    rw [hm₅]
    refine saved_frame hp ?_ (.inl ld.frame)
    rw [hm₂]; exact hL.saved
  · rw [Masks, hx₈, hy₈, hx₇, hy₇]; exact hS₆.masks
  · rw [pub₈ .rsi (by decide)]; exact hL.rsi
  · rw [pub₈ .rdx (by decide)]; exact hL.rdx
  · simp only [Vars8, hg₈]; rw [← hc]; exact hv₇
  · intro k hk
    rw [hm₈]
    exact wmem_frame_st hp hk (hS₆.wmem k hk (by omega)) hfw
  · rw [he₈, pub₇ .rdx (by decide), pub₆ .rdx (by decide), hb]

/-! ## The end of an iteration -/

theorem adv_common {s₀ : State} {k : Nat} {s : State} (hc : Common s₀ k s) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      Common s₀ k s' ∧ eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 := by
  refine WP.mono (adv_ok s a b) fun s' ⟨he, hrsi, hrdx, hg, hm, hrd, hwr, hx, hy⟩ => ⟨?_, he, hrsi, hrdx⟩
  refine ⟨by rw [hg _ (by decide) (by decide)]; exact hc.rdi, by rw [hg _ (by decide) (by decide)]; exact hc.rcx,
    by rw [hg _ (by decide) (by decide)]; exact hc.rsp, hrd.trans hc.rd, hwr.trans hc.wr, hm ▸ hc.frame,
    hm ▸ hc.state, hm ▸ hc.saved, ?_⟩
  rw [Masks, hx, hy]; exact hc.masks

/-- The loop exits after the last block, or goes on with block `k`. -/
theorem exit_or_next {s₀ : State} (hp : Pre s₀) {i k : Nat} (hk : i < k) (hk' : k ≤ nb s₀) {s : State}
    (hc : Common s₀ k s) (hrsi : s.gpr .rsi = blkAddr s₀ k) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - k))
    (he : eval .ne s = some (!(BitVec.ofNat 64 (nb s₀ - k) == 0))) :
    (eval .ne s = some false ∧ Common s₀ (nb s₀) s) ∨
      (eval .ne s = some true ∧ ∃ i', i < i' ∧ i' < nb s₀ ∧ LInv s₀ i' s) := by
  by_cases hlast : k = nb s₀
  · left
    subst hlast
    refine ⟨by rw [he]; simp, hc⟩
  · right
    have := hp.nb_lt
    have h0 : BitVec.ofNat 64 (nb s₀ - k) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      simp at h'
      omega
    refine ⟨by rw [he]; simpa using h0, k, hk, by omega, { hc with rsi := hrsi, rdx := hrdx }⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ i', i < i' ∧ i' < nb s₀ ∧ LInv s₀ i' s') := by
  have := hp.nb_lt
  have hn := (s₀.gpr .rdx).isLt
  refine first_ok hp hi hL fun s₁ hM => WP.ite _ hM.e (fun h => ?_) (fun h => ?_)
  · rw [beq_iff_eq] at h
    refine WP.mono (adv_common hM.toCommon 64 1) fun s₂ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₁.gpr .rdx - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
      rw [hM.rdx, e1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    refine exit_or_next hp (by omega) (by omega) hc ?_ hrdx he
    rw [hrsi, hM.rsi, e64]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 1) = 64 * i + 64 by omega]
  · rw [beq_eq_false_iff_ne] at h
    have hnx : nxt s₀ i = i + 1 := by simp only [nxt, h, ↓reduceIte]
    have hw := hM.wmem
    rw [hnx] at hw
    refine WP.seq (WP.mono (initCarry_ok hM.vars) fun s₂ ⟨hv₂, hk₂⟩ => ?_)
    obtain ⟨hm₂, hrd₂, hwr₂, pub₂, hx₂, hy₂⟩ := hk₂
    have hR₂ : (⟨scr s₀, 560⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hM.wr, hp.wr]; simp
    have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hM.rcx
    refine WP.seq (WP.mono (rounds2_ok _ (blk s₀ (i + 1)) s₂ hv₂ (fun t ht =>
      (wok_of_wmem ht hrcx₂ hR₂ (by rw [hm₂]; exact hw (t / 4) (by omega))).2) 64 (Nat.le_refl _))
      fun s₃ ⟨hv₃, hk₃⟩ => ?_)
    obtain ⟨hm₃, hrd₃, hwr₃, pub₃, hx₃, hy₃⟩ := hk₃
    rw [WP.block_append_iff]
    have hH : ∀ k : Nat, (hk : k < 8) → s₃.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))[k] :=
      fun k hk => by rw [← hM.state, stateAt_get _ _ hk, hm₃, hm₂]
    have hrdi₃ : s₃.gpr .rdi = st s₀ := by rw [pub₃ .rdi (by decide), pub₂ .rdi (by decide)]; exact hM.rdi
    have hrd₃' : s₃.rd = s₀.rd := by rw [hrd₃, hrd₂]; exact hM.rd
    have hwr₃' : s₃.wr = s₀.wr := by rw [hwr₃, hwr₂]; exact hM.wr
    refine WP.mono (addState_ok hp _ _ (Vars.vars8 hv₃) hrdi₃ hrd₃' hwr₃' hH)
      fun s₄ ⟨hm₄, _, pub₄, hrd₄, hwr₄, hx₄, hy₄⟩ => ?_
    have pub₄' : ∀ r ∈ pubRegs, s₄.gpr r = s₁.gpr r := fun r hr => by rw [pub₄ r hr, pub₃ r hr, pub₂ r hr]
    have hfw : Frame [stR s₀] s₃.mem s₄.mem := by
      rw [hm₄]; exact frame_writeState (Frame.refl _ _) _
    have hc₄ : Common s₀ (i + 2) s₄ := by
      refine ⟨by rw [pub₄' .rdi (by decide)]; exact hM.rdi, by rw [pub₄' .rcx (by decide)]; exact hM.rcx,
        by rw [pub₄' .rsp (by decide)]; exact hM.rsp, by rw [hrd₄, hrd₃, hrd₂]; exact hM.rd,
        by rw [hwr₄, hwr₃, hwr₂]; exact hM.wr, ?_, ?_, ?_, ?_⟩
      · refine hM.frame.trans ?_
        rw [← hm₂, ← hm₃]
        exact hfw.sub fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
      · rw [hm₄, stateAt_writeState, show i + 2 = i + 1 + 1 by omega, compressBlocks_succ _ _ _ (i + 1)]; rfl
      · refine saved_frame hp ?_ (.inr hfw)
        rw [hm₃, hm₂]; exact hM.saved
      · rw [Masks, hx₄, hy₄, hx₃, hy₃, hx₂, hy₂]; exact hM.masks
    refine WP.mono (adv_common hc₄ 128 2) fun s₅ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₄.gpr .rdx - BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 2)) := by
      rw [pub₄' .rdx (by decide), hM.rdx, e2, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    refine exit_or_next hp (by omega) (by omega) hc ?_ hrdx he
    rw [hrsi, pub₄' .rsi (by decide), hM.rsi, e128]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 2) = 64 * i + 128 by omega]

/-! ## The prologue and the epilogue -/

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 560 →
      (scrR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' (by omega) (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 512 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 520 (by omega))).writeW (List.mem_singleton_self _) _
    (c 528 (by omega))).writeW (List.mem_singleton_self _) _ (c 536 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 544 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 552 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) (hk : Masks s₁) :
    Common s₀ 0 s₁ := by
  refine ⟨hg _ (by decide), hg _ (by decide), hg _ (by decide), hrd, hwr, ?_, ?_,
    by rw [hm]; exact saveMem_saved, hk⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_eq : restore ++ ([.vop .vzeroupper] : List Instr) = [
    .mov .rbx (.mem (at_ .rcx 512)), .mov .rbp (.mem (at_ .rcx 520)), .mov .r12 (.mem (at_ .rcx 528)),
    .mov .r13 (.mem (at_ .rcx 536)), .mov .r14 (.mem (at_ .rcx 544)), .mov .r15 (.mem (at_ .rcx 552)),
    .vop .vzeroupper] := rfl

theorem in_save {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 8 ≤ 560) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block (restore ++ ([.vop .vzeroupper] : List Instr))) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  have i0 := in_save hp (d := 512) (by omega); have i1 := in_save hp (d := 520) (by omega)
  have i2 := in_save hp (d := 528) (by omega); have i3 := in_save hp (d := 536) (by omega)
  have i4 := in_save hp (d := 544) (by omega); have i5 := in_save hp (d := 552) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hc.saved
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  have hrsp := hc.rsp
  have hstate := hc.state
  have hrcx := hc.rcx
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64, VOp.exec,
    State.setReg, hrcx, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · exact hret
  · exact hstate

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf, hk⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm hk
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, i', hii, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - i', by omega, i', rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg _ (by decide)]; simp [blkAddr]
        rdx := by rw [hg _ (by decide)]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem compress_verified :
    Verified X86_64.target Impl.Sha256.X86_64.Avx2.compress Proof.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, (Proof.Sha256.X86_64.compress_verified).2.2⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.Sha256.X86_64.Avx2
