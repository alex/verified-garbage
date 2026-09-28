import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Md5.X86_64.Rounds
import VerifiedGarbage.Proof.Md5.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# MD5 compression function on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Md5.X86_64

open VG VG.X86_64 VG.Impl.Md5.X86_64
open VG.Spec.Md5 (HashValue Word Block stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [ofInt_natCast]; exact contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 4) (hk : k < 4) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 4 (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 4) (hk : k < 4)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 =
    m.readW (p + BitVec.ofInt 64 ((4 * j : Nat) : Int)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

/-- Distinct 8-byte slots (where the streaming functions save registers). -/
theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 4) → m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← ofInt_natCast]; exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 4) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast]

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- A 32-bit load reads four bytes, low-order byte first. -/
theorem readW_bytes (m : Mem) (a : Addr) :
    m.readW a 32 = (m (a + 1 + 1 + 1) ++ m (a + 1 + 1) ++ m (a + 1) ++ m a : BitVec 32) := by
  show (0#0 ++ m (a + 1 + 1 + 1) ++ m (a + 1 + 1) ++ m (a + 1) ++ m a).setWidth 32 = _
  simp only [BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero_length]
  split_ifs <;> first | omega | rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev bp : Addr := s₀.gpr .rsi
abbrev nb : Nat := (s₀.gpr .rdx).toNat
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨st s₀, 16⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 64⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Md5.compressX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from the state). -/
theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 4) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 4) :
    InRegions s₀.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset' (by omega) (by omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 := by
  have := h.nb_lt
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .r8 (.mem (at_ .rdi (4 * 1))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 2))), .mov32 .r10 (.mem (at_ .rdi (4 * 3)))] := by
  decide

theorem update_eq : update ++ advance = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 2))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 3))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .r8,
    .store32 (at_ .rdi (4 * 2)) .r9, .store32 (at_ .rdi (4 * 3)) .r10,
    .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .r8 = v[1].setWidth 64 ∧
    s.gpr .r9 = v[2].setWidth 64 ∧ s.gpr .r10 = v[3].setWidth 64 := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [load_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide)
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at,
    State.load32, State.setReg32, State.setReg, hrdi, h0, h1, h2, h3, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 4 by decide), stateAt_get _ _ (show 1 < 4 by decide),
    stateAt_get _ _ (show 2 < 4 by decide), stateAt_get _ _ (show 3 < 4 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Four 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((m.writeW (p + BitVec.ofInt 64 ((4 * 0 : Nat) : Int)) v[0]).writeW
    (p + BitVec.ofInt 64 ((4 * 1 : Nat) : Int)) v[1]).writeW
    (p + BitVec.ofInt 64 ((4 * 2 : Nat) : Int)) v[2]).writeW
    (p + BitVec.ofInt 64 ((4 * 3 : Nat) : Int)) v[3])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 4 → (stR s₀).Contains (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
    fun k hk => contains_offset' (by omega) (by omega)
  simp only [writeState]
  refine (((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _ (c 3 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 4) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rdx = s.gpr .rdx - 1 ∧
      s'.zf = some (s.gpr .rdx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 4 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 4 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execAlu, readSrc32, readSrc,
    isa, ea_at, State.load32, State.store32, State.setReg32, State.setReg, arithFlags,
    State.setFlags, hrdi, i0, i1, i2, i3, o0, o1, o2, o3,
    m0, m1, m2, m3, v0, v1, v2, v3, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨?_, by rw [e64], by rw [e1], by rw [e1], trivial⟩
  simp only [writeState, Vector.getElem_zipWith]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i k : Nat) (hk : k < 16) :
    s₀.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = blk s₀ i ⟨k, hk⟩ := by
  rw [readW_bytes, ofInt_natCast]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * k) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 1) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 2) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * k + 3) by
      bv_omega]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.rdi hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hX : ∀ k (hk : k < 16),
      s₁.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = blk s₀ i ⟨k, hk⟩ := by
    intro k hk
    rw [hm₁, hL.frame.readW (hp.blk_contains hi hk) (by simpa using hp.blk_st) (by decide)]
    exact blk_word i k hk
  have hrsi₁ : s₁.gpr .rsi = blkAddr s₀ i := (hpub₁ .rsi (by decide)).trans hL.rsi
  refine WP.seq (WP.mono (steps_ok _ (blk s₀ i) _ s₁ hrsi₁
    (fun k hk => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi hk) hX hv₁ 64 le_rfl)
    fun s₂ hR => ?_)
  have hrdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [hR.pub .rdi (by decide), hpub₁ .rdi (by decide), hL.rdi]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hrdi₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.mem, hm₁, stateAt_get _ _ hk]
  obtain ⟨hm₃, hrsi₃, hrdx₃, hzf₃, hrdi₃, hrd₃, hwr₃⟩ := h₃
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .rdx (by decide), hL.rdx]
    have := (s₀.gpr .rdx).isLt
    bv_omega
  have hframe : Frame [stR s₀] s₀.mem s₃.mem := by
    rw [hm₃, hR.mem, hm₁]
    exact frame_writeState hL.frame _
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hrdi₃, hrdi₂], by rw [hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, hzf₃]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon _ rfl with rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrsi₃, pub₂ .rsi (by decide), hL.rsi]
      simp only [blkAddr]
      bv_omega
    · rw [hrdx₃, hrdx]

/-! ## The whole function -/

set_option simprocs false in
theorem test_ok {s₀ : State} :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = s₀.mem ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, isa, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => Common s₀ (nb s₀) s' := by
  refine WP.seq (WP.mono test_ok fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  have hc₀ : Common s₀ 0 s₁ :=
    ⟨by rw [hg], hrd, hwr, by rw [hm]; exact Frame.refl _ _, by rw [hm]; rfl⟩
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
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg]; simp [blkAddr]
        rdx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- The registers no instruction writes: the callee-saved ones, `rdi` and `rcx`. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r12, .r13, .r14, .r15, .rdi, .rcx]

theorem compress_keeps : ((instrs compress).all fun i => kept.all fun r => Taint.dstOf i != some r) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem compress_keeps_reg {r : Reg} (hr : r ∈ kept) : ∀ i ∈ instrs compress, Taint.dstOf i ≠ some r := by
  intro i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp compress_keeps i hi) r hr
  simpa using this

/-- `compress` meets the calling convention and its postcondition. -/
theorem correct' {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Md5.compressX86_64.post s₀ s' := by
  obtain ⟨t, s', he, hc⟩ := correct hp
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (compress_keeps_reg ?_) he, ?_⟩, hc.state⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hc.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 16⟩, ⟨0x3000, 64⟩]

theorem compress_verified :
    Verified X86_64.target Impl.Md5.X86_64.compress Proof.Md5.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct' (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Md5.X86_64
