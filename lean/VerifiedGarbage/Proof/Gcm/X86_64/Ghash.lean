import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Gcm.X86_64.Step
import VerifiedGarbage.Proof.Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# GHASH on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

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

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .rdi
abbrev yp : Addr := s₀.gpr .rsi
abbrev dp : Addr := s₀.gpr .rdx
abbrev nb : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  ret_y : (retR s₀).Disjoint (yR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashX86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨hR s₀, by simp [h.rd], contains_offset' hd (by omega)⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem in_save {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem out_save {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset' hd (by omega)⟩

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) := by
  have := h.nb_lt
  exact sub_offset (by omega) (by omega)

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 (d : Int)) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 d = dp s₀ + BitVec.ofNat 64 (16 * i + d) by
    simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) 64 = s₀.gpr .r15

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = hA s₀
  rsi : s.gpr .rsi = yp s₀
  r8 : s.gpr .r8 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀, scrR s₀] s₀.mem s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  rdx : s.gpr .rdx = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem blockAt_bswap' (m : Mem) (p : Addr) :
    X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
      X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) = blockAt m p := by
  rw [ofInt_natCast, ofInt_natCast]; exact blockAt_bswap m p

set_option simprocs false in
theorem load_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8)
    (hd : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofInt 64 (d : Int)) 8) :
    WP isa (.block load) s fun s₁ =>
      Inner (blockAt s.mem (s.gpr .rsi) ^^^ blockAt s.mem (s.gpr .rdx)) (blockAt s.mem (s.gpr .rdi))
        s 0 s₁ ∧ s₁.gpr CNT = BitVec.ofNat 64 (128 / unroll) := by
  have h0 := hh 0 (by omega); have h8 := hh 8 (by omega)
  have y0 := hy 0 (by omega); have y8 := hy 8 (by omega)
  have d0 := hd 0 (by omega); have d8 := hd 8 (by omega)
  apply WP.of_runBlock
  simp only [load, XH, XL, ZH, ZL, VH, VL, T, RH, CNT]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at, State.load64,
    State.setReg, arithFlags, State.setFlags, h0, h8, y0, y8, d0, d8, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp (config := {decide := true}) only [XH, XL, ite_true, ite_false]
    rw [BitVec.shiftLeft_zero, ← BitVec.xor_append, blockAt_bswap', blockAt_bswap']
  · simp (config := {decide := true}) only [ZH, ZL, VH, VL, ite_true, ite_false]
    rw [mulSteps_zero, blockAt_bswap',
      show BitVec.signExtend 64 (0 : BitVec 32) ++ BitVec.signExtend 64 (0 : BitVec 32) = (0 : Block)
        by decide]
  · simp (config := {decide := true}) only [RH, ite_true, ite_false]
  · simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_false]
  · trivial

/-- The memory after storing `Z` at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) (bswap64 zh)).writeW
    (p + BitVec.ofInt 64 ((8 : Nat) : Int)) (bswap64 zl)

theorem half_sep (p : Addr) :
    Mem.Sep (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 8 (p + BitVec.ofInt 64 ((8 : Nat) : Int)) 8 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) :
    blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_bswap', storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (half_sep p) (by decide), Mem.readW_writeW_self64, bswap64_bswap64,
    bswap64_bswap64]

set_option simprocs false in
theorem store_ok (s : State)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = storeMem s.mem (s.gpr .rsi) (s.gpr ZH) (s.gpr ZL) ∧
      s'.gpr .rdx = s.gpr .rdx + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have y0 := hy 0 (by omega); have y8 := hy 8 (by omega)
  apply WP.of_runBlock
  simp only [store, ZH, ZL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at, State.store64,
    State.setReg, arithFlags, State.setFlags, y0, y8, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨rfl, by rw [e16], by rw [e1], by rw [e1], trivial⟩

theorem storeMem_frame {s₀ : State} {m m' : Mem} (h : Frame [yR s₀, scrR s₀] m m') (zh zl : BitVec 64) :
    Frame [yR s₀, scrR s₀] m (storeMem m' (yp s₀) zh zl) :=
  (h.writeW (List.mem_cons_self ..) _ (contains_offset' (by omega) (by omega))).writeW
    (List.mem_cons_self ..) _ (contains_offset' (by omega) (by omega))

theorem saved_storeMem {s₀ : State} (hp : Pre s₀) {m : Mem} (h : Saved s₀ m) (zh zl : BitVec 64) :
    Saved s₀ (storeMem m (yp s₀) zh zl) := by
  have key : ∀ d : Nat, d + 8 ≤ 256 →
      (storeMem m (yp s₀) zh zl).readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 =
        m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
    intro d hd
    have sep : ∀ e : Nat, e + 8 ≤ 16 →
        Mem.Sep (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) (yp s₀ + BitVec.ofInt 64 (e : Int)) (64 / 8) :=
      fun e he => hp.y_scr.symm.sep (contains_offset' hd (by omega)) (contains_offset' he (by omega))
    rw [storeMem, Mem.readW_writeW_sep (sep 8 (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 0 (by omega)) (by decide)]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(key 0 (by omega)).trans h1, (key 8 (by omega)).trans h2, (key 16 (by omega)).trans h3,
    (key 24 (by omega)).trans h4, (key 32 (by omega)).trans h5, (key 40 (by omega)).trans h6⟩

/-- Memory outside `y` and `scratch` is as on entry. -/
theorem blockAt_frame {s₀ : State} {m : Mem} (h : Frame [yR s₀, scrR s₀] s₀.mem m) {p : Addr}
    (hd : ∀ r ∈ [yR s₀, scrR s₀], Region.Disjoint ⟨p, 16⟩ r) : blockAt m p = blockAt s₀.mem p :=
  blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok s
    (fun d hd => by rw [hL.rd, hL.wr, hL.rdi]; exact hp.in_h hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.rsi]; exact hp.in_y hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.rdx]; exact hp.in_blk hi hd)) fun s₁ ⟨hI₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hI₁ hc₁) fun s₂ hI₂ => ?_)
  have hrsi₂ : s₂.gpr .rsi = yp s₀ := (hI₂.keep .rsi (by decide)).trans hL.rsi
  refine WP.mono (store_ok s₂ fun d hd => by rw [hI₂.wr, hL.wr, hrsi₂]; exact hp.out_y hd)
    fun s₃ ⟨hm₃, hrdx₃, hrcx₃, hzf₃, hrdi₃, hrsi₃, hr8₃, hrsp₃, hrd₃, hwr₃⟩ => ?_
  have hk : ∀ r ∈ keepRegs, s₂.gpr r = s.gpr r := hI₂.keep
  have hrcx : s₂.gpr .rcx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hk .rcx (by decide), hL.rcx]
    have := (s₀.gpr .rcx).isLt
    bv_omega
  have hy : blockAt s₃.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hz1 := congrArg Prod.fst hI₂.zv
    simp only at hz1
    rw [hm₃, hrsi₂, blockAt_storeMem, ghashFrom_blocksAt_succ, ← hL.y, mul_eq, hz1, hL.rsi, hL.rdx, hL.rdi,
      blockAt_frame (p := hA s₀) hL.frame (by simpa using ⟨hp.h_y, hp.h_scr⟩),
      blockAt_frame (p := blkAddr s₀ i) hL.frame (by simpa using
        ⟨(hp.y_d.symm.sub_left (hp.blk_sub hi)), hp.d_scr.sub_left (hp.blk_sub hi)⟩)]
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hrdi₃, hk .rdi (by decide), hL.rdi], by rw [hrsi₃, hrsi₂],
      by rw [hr8₃, hk .r8 (by decide), hL.r8], by rw [hrsp₃, hk .rsp (by decide), hL.rsp],
      by rw [hrd₃, hI₂.rd, hL.rd], by rw [hwr₃, hI₂.wr, hL.wr], ?_, hy, ?_⟩
    · rw [hm₃, hrsi₂, hI₂.mem]; exact storeMem_frame hL.frame _ _
    · rw [hm₃, hrsi₂, hI₂.mem]; exact saved_storeMem hp hL.saved _ _
  have hev : eval .ne s₃ = some (!(BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hzf₃, hrcx, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨by rw [hev]; decide, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with rdx := ?_, rcx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrdx₃, hk .rdx (by decide), hL.rdx]
      simp only [blkAddr]
      bv_omega
    · rw [hrcx₃, hrcx]

/-! ## Prologue and epilogue -/

theorem save_eq : save ++ [.alu .test .rcx (.reg .rcx)] = [
    .store (at_ .r8 0) .rbx, .store (at_ .r8 8) .rbp, .store (at_ .r8 16) .r12,
    .store (at_ .r8 24) .r13, .store (at_ .r8 32) .r14, .store (at_ .r8 40) .r15,
    .alu .test .rcx (.reg .rcx)] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .r8 0)), .mov .rbp (.mem (at_ .r8 8)), .mov .r12 (.mem (at_ .r8 16)),
    .mov .r13 (.mem (at_ .r8 24)), .mov .r14 (.mem (at_ .r8 32)), .mov .r15 (.mem (at_ .r8 40))] := rfl

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) (s₀.gpr .r15)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ [.alu .test .rcx (.reg .rcx)])) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) := by
  have o0 := hp.out_save (d := 0) (by omega); have o1 := hp.out_save (d := 8) (by omega)
  have o2 := hp.out_save (d := 16) (by omega); have o3 := hp.out_save (d := 24) (by omega)
  have o4 := hp.out_save (d := 32) (by omega); have o5 := hp.out_save (d := 40) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, ea_at,
    State.store64, arithFlags, State.setFlags, o0, o1, o2, o3, o4, o5, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (save_sep p hd he h) (by decide)

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_save]

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 8 ≤ 256 →
      (scrR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => contains_offset' hd (by omega)
  simp only [saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 8 (by omega))).writeW (List.mem_singleton_self _) _
    (c 16 (by omega))).writeW (List.mem_singleton_self _) _ (c 24 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 32 (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c 40 (by omega))

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = saveMem s₀) : Common s₀ 0 s₁ := by
  refine ⟨by rw [hg], by rw [hg], by rw [hg], by rw [hg], hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved⟩
  · rw [hm]; exact saveMem_frame.mono fun r hr => by simp at hr; simp [hr]
  · rw [hm, ghashFrom_blocksAt_zero]
    exact blockAt_congr fun _ hk =>
      saveMem_frame.bytes (R := yR s₀) (by simpa using hp.y_scr) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Gcm.ghashX86_64.post s₀ s' := by
  have i0 := hp.in_save (d := 0) (by omega); have i1 := hp.in_save (d := 8) (by omega)
  have i2 := hp.in_save (d := 16) (by omega); have i3 := hp.in_save (d := 24) (by omega)
  have i4 := hp.in_save (d := 32) (by omega); have i5 := hp.in_save (d := 40) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hc.saved
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_y, hp.ret_scr⟩) (by decide)
  have hrsp := hc.rsp
  have hy := hc.y
  have hr8 := hc.r8
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr8, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · exact hret
  · exact hy

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Gcm.ghashX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => restore_ok hp hc)
  have hc₀ := common_zero hp hg hrd hwr hm
  refine WP.ite (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
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
        rdx := by rw [hg]; simp [blkAddr]
        rcx := by rw [hg]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .r8 => 0x4000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_verified :
    Verified X86_64.target Impl.Gcm.X86_64.ghash Proof.Gcm.ghashX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Gcm.X86_64
