import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Gcm.X86_64.Parts
import VerifiedGarbage.Proof.Gcm.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# GHASH on x86-64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm VG.Proof.Gcm.X86_64.Ctmul VG.Proof.Gcm.Poly
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


/-! ## Separation in `y` and `scratch` -/

theorem off_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) (64 / 8) (p + BitVec.ofInt 64 (e : Int)) (64 / 8) := by
  intro x hx hy
  simp only [ofInt_natCast] at hx hy
  bv_omega

theorem readW_writeW_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (off_sep p hd he h) (by decide)

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem sep_ys {d e : Nat} (hd : d + 8 ≤ 16) (he : e + 8 ≤ 256) :
    Mem.Sep (yp s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) (scr s₀ + BitVec.ofInt 64 (e : Int)) (64 / 8) :=
  h.y_scr.sep (contains_offset' hd (by omega)) (contains_offset' he (by omega))

theorem sep_sy {d e : Nat} (hd : d + 8 ≤ 256) (he : e + 8 ≤ 16) :
    Mem.Sep (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) (yp s₀ + BitVec.ofInt 64 (e : Int)) (64 / 8) :=
  h.y_scr.symm.sep (contains_offset' hd (by omega)) (contains_offset' he (by omega))

theorem readW_y_s (m : Mem) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 16) (he : e + 8 ≤ 256) :
    (m.writeW (scr s₀ + BitVec.ofInt 64 (e : Int)) v).readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (h.sep_ys hd he) (by decide)

theorem readW_s_y (m : Mem) (v : BitVec 64) {d e : Nat} (hd : d + 8 ≤ 256) (he : e + 8 ≤ 16) :
    (m.writeW (yp s₀ + BitVec.ofInt 64 (e : Int)) v).readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (h.sep_sy hd he) (by decide)

end Pre

/-! ## Memory while hashing -/

/-- Where `Y_A ⊕ Y_B` and `W₃` are kept. -/
abbrev slotR (s₀ : State) : Region := ⟨scr s₀ + BitVec.ofNat 64 240, 16⟩

theorem slot_contains (s₀ : State) {d : Nat} (hd : 240 ≤ d) (hd' : d + 8 ≤ 256) :
    (slotR s₀).Contains (scr s₀ + BitVec.ofInt 64 (d : Int)) (64 / 8) := by
  simp only [Region.Contains, ofInt_natCast]
  rw [show scr s₀ + BitVec.ofNat 64 d - (scr s₀ + BitVec.ofNat 64 240) = BitVec.ofNat 64 (d - 240) by
    bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem slot_disjoint (s₀ : State) {d : Nat} (hd : d + 8 ≤ 240) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 64 / 8⟩ (slotR s₀) := by
  intro x h1 h2
  simp only [Region.Contains, ofInt_natCast] at h1 h2
  bv_omega

/-- Memory outside `y` and `scratch` is as on entry, and memory outside `y`
and the slots as after the set-up (`mS`). -/
structure MemInv (s₀ : State) (mS m : Mem) : Prop where
  f1 : Frame [yR s₀, scrR s₀] s₀.mem m
  f2 : Frame [yR s₀, slotR s₀] mS m

theorem MemInv.write_y {s₀ : State} {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat} (hd : d + 8 ≤ 16)
    (v : BitVec 64) : MemInv s₀ mS (m.writeW (yp s₀ + BitVec.ofInt 64 (d : Int)) v) :=
  ⟨h.f1.writeW (List.mem_cons_self ..) _ (contains_offset' hd (by omega)),
    h.f2.writeW (List.mem_cons_self ..) _ (contains_offset' hd (by omega))⟩

theorem MemInv.write_slot {s₀ : State} {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat} (hd : 240 ≤ d)
    (hd' : d + 8 ≤ 256) (v : BitVec 64) : MemInv s₀ mS (m.writeW (scr s₀ + BitVec.ofInt 64 (d : Int)) v) :=
  ⟨h.f1.writeW (by simp) _ (contains_offset' hd' (by omega)),
    h.f2.writeW (by simp) _ (slot_contains s₀ hd hd')⟩

/-- `scratch` below the slots is as after the set-up. -/
theorem MemInv.readW_low {s₀ : State} (hp : Pre s₀) {mS m : Mem} (h : MemInv s₀ mS m) {d : Nat}
    (hd : d + 8 ≤ 240) :
    m.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 = mS.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
  refine h.f2.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine hp.y_scr.symm.sub_left ?_
    rw [ofInt_natCast]
    exact sub_offset (by omega) (by omega)
  · exact slot_disjoint s₀ hd

/-- The words of the three tables. -/
def hword (ka kb : BitVec 64) : Nat → BitVec 64
  | 0 => ka
  | 1 => kb
  | _ => ka ^^^ kb

/-- The tables of `H' = ka ‖ kb` are in `m` at `p`. -/
def TblMem (p : Addr) (ka kb : BitVec 64) (m : Mem) : Prop :=
  ∀ u < 24, m.readW (p + BitVec.ofInt 64 ((off u : Nat) : Int)) 64 = part (hword ka kb (u / 8)) (u % 8)

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 = s₀.gpr .rbx ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) 64 = s₀.gpr .rbp ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) 64 = s₀.gpr .r12 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) 64 = s₀.gpr .r13 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) 64 = s₀.gpr .r14 ∧
  m.readW (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) 64 = s₀.gpr .r15

/-- What the set-up leaves in memory. -/
structure SetupMem (s₀ : State) (ka kb : BitVec 64) (mS : Mem) : Prop where
  saved : Saved s₀ mS
  tbl : TblMem (scr s₀) ka kb mS
  frame : Frame [scrR s₀] s₀.mem mS

theorem tbl_of {s₀ : State} (hp : Pre s₀) {ka kb : BitVec 64} {mS : Mem} (hS : SetupMem s₀ ka kb mS)
    {s : State} (hr8 : s.gpr .r8 = scr s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : MemInv s₀ mS s.mem) {q : Nat} (hq : q < 3) : Tbl s q (hword ka kb q) := by
  intro t ht
  have e1 : (8 * q + t) / 8 = q := by omega
  have e2 : (8 * q + t) % 8 = t := by omega
  have := hS.tbl (8 * q + t) (by omega)
  rw [e1, e2] at this
  simp only [readSrc, State.load64, ea_at, hr8, hrd, hwr]
  rw [ite_eq_left (hp.in_save (by simp only [off]; omega)), hm.readW_low hp (by simp only [off]; omega),
    this]

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (mS : Mem) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = yp s₀
  r8 : s.gpr .r8 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : MemInv s₀ mS s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (mS : Mem) (i : Nat) (s : State) : Prop extends Common s₀ mS i s where
  rdi : s.gpr .rdi = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)

/-- The registers a block changes, besides `rdi` and `rcx` at its end. -/
abbrev bigClob : List Reg := [.rax, .rdx, .rbx, .rbp, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The pointers during block `i`. -/
structure Ptrs (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = yp s₀
  r8 : s.gpr .r8 = scr s₀
  rdi : s.gpr .rdi = blkAddr s₀ i
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ - i)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem LInv.ptrs {s₀ : State} {mS : Mem} {i : Nat} {s : State} (h : LInv s₀ mS i s) : Ptrs s₀ i s :=
  ⟨h.rsi, h.r8, h.rdi, h.rcx, h.rsp, h.rd, h.wr⟩

namespace Ptrs
variable {s₀ : State} {i : Nat} {s : State} (h : Ptrs s₀ i s)
include h

theorem of_regs {s' : State} (hr : Regs bigClob s s') : Ptrs s₀ i s' :=
  ⟨(hr.1 _ (by decide)).trans h.rsi, (hr.1 _ (by decide)).trans h.r8, (hr.1 _ (by decide)).trans h.rdi,
    (hr.1 _ (by decide)).trans h.rcx, (hr.1 _ (by decide)).trans h.rsp, hr.2.1.trans h.rd,
    hr.2.2.trans h.wr⟩

variable (hp : Pre s₀)
include hp

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.rsi]; exact hp.in_y hd

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.wr, h.rsi]; exact hp.out_y hd

theorem in_s {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.r8]; exact hp.in_save hd

theorem out_s {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.wr, h.r8]; exact hp.out_save hd

theorem in_x (hi : i < nb s₀) {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8 := by
  rw [h.rd, h.wr, h.rdi]; exact hp.in_blk hi hd

/-- A load of `y` or `scratch`. -/
theorem load_y {d : Nat} (hd : d + 8 ≤ 16) :
    readSrc s (.mem (at_ .rsi d)) = some (s.mem.readW (yp s₀ + BitVec.ofInt 64 (d : Int)) 64) := by
  simp only [readSrc, State.load64, ea_at, h.in_y hp hd, ite_true]
  rw [h.rsi]

theorem load_s {d : Nat} (hd : d + 8 ≤ 256) :
    readSrc s (.mem (at_ .r8 d)) = some (s.mem.readW (scr s₀ + BitVec.ofInt 64 (d : Int)) 64) := by
  simp only [readSrc, State.load64, ea_at, h.in_s hp hd, ite_true]
  rw [h.r8]

end Ptrs

/-! ## One block -/

theorem blockAt_bswap' (m : Mem) (p : Addr) :
    X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
      X86_64.bswap64 (m.readW (p + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) = blockAt m p := by
  rw [ofInt_natCast, ofInt_natCast]; exact blockAt_bswap m p

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

/-- Memory outside `y` and `scratch` is as on entry. -/
theorem blockAt_frame {s₀ : State} {m : Mem} (h : Frame [yR s₀, scrR s₀] s₀.mem m) {p : Addr}
    (hd : ∀ r ∈ [yR s₀, scrR s₀], Region.Disjoint ⟨p, 16⟩ r) : blockAt m p = blockAt s₀.mem p :=
  blockAt_congr fun _ hk => h.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem blkAddr_succ (s₀ : State) (i : Nat) : blkAddr s₀ i + 16 = blkAddr s₀ (i + 1) := by
  simp only [blkAddr]; bv_omega

theorem ofNat_sub_succ {n i : Nat} (hi : i < n) :
    BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  bv_omega

theorem body_ok {s₀ : State} (hp : Pre s₀) {ka kb : BitVec 64} {mS : Mem}
    (hS : SetupMem s₀ ka kb mS) (hH : x * φ (ka ++ kb) = φ (H₀ s₀)) {i : Nat} (hi : i < nb s₀)
    {s : State} (hL : LInv s₀ mS i s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ mS (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ mS (i + 1) s') := by
  rw [body]
  repeat rw [WP.block_append_iff]
  have P₀ := hL.ptrs
  -- load `Y ⊕ X`
  refine WP.mono (load_ok s (P₀.in_y hp (d := 0) (by omega)) (P₀.in_y hp (d := 8) (by omega))
    (P₀.in_x hp hi (d := 0) (by omega)) (P₀.in_x hp hi (d := 8) (by omega)) (P₀.out_y hp (d := 8) (by omega))
    (P₀.out_s hp (d := 240) (by omega)))
    fun s₁ ⟨hW₁, hm₁, hr₁⟩ => ?_
  rw [P₀.rsi, P₀.rdi] at hW₁
  rw [P₀.rsi, P₀.rdi, P₀.r8] at hm₁
  generalize hyB : bswap64 (s.mem.readW (yp s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
    bswap64 (s.mem.readW (blkAddr s₀ i + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) = yB at hm₁
  have P₁ := P₀.of_regs (hr₁.mono (by decide))
  have M₁ : MemInv s₀ mS s₁.mem := by
    rw [hm₁]; exact (hL.mem.write_y (by omega) _).write_slot (by omega) (by omega) _
  -- `A = Y_A · H'_A`
  refine WP.mono (product_ok (.reg W0) 0 (yv := s₁.gpr W0)
    (tbl_of hp hS P₁.r8 P₁.rd P₁.wr M₁ (by omega))
    (fun s' hk => by simp only [readSrc]; rw [hk.1 W0 (by decide)])) fun s₂ ⟨hP₂, hk₂⟩ => ?_
  have P₂ := P₁.of_regs (hk₂.regs.mono (by decide))
  -- keep `A`
  refine WP.mono (keepA_ok s₂ (P₂.out_y hp (d := 0) (by omega))) fun s₃ ⟨hW₃, hm₃, hr₃⟩ => ?_
  rw [P₂.rsi, hk₂.2.1] at hm₃
  have P₃ := P₂.of_regs (hr₃.mono (by decide))
  have M₃ : MemInv s₀ mS s₃.mem := by rw [hm₃]; exact M₁.write_y (by omega) _
  -- `B = Y_B · H'_B`
  refine WP.mono (product_ok (.mem (at_ .rsi 8)) 1 (yv := yB)
    (tbl_of hp hS P₃.r8 P₃.rd P₃.wr M₃ (by omega))
    (fun s' hk => by
      rw [hk.readSrc_mem (by decide), P₃.load_y hp (d := 8) (by omega), hm₃,
        readW_writeW_off _ _ _ (by omega) (by omega) (by omega), hm₁, hp.readW_y_s _ _ (by omega) (by omega),
        Mem.readW_writeW_self64])) fun s₄ ⟨hP₄, hk₄⟩ => ?_
  have P₄ := P₃.of_regs (hk₄.regs.mono (by decide))
  -- keep `A ⊕ B`
  refine WP.mono (keepB_ok s₄ (P₄.in_y hp (d := 0) (by omega)) (P₄.out_y hp (d := 0) (by omega))
    (P₄.out_y hp (d := 8) (by omega)) (P₄.out_s hp (d := 248) (by omega))) fun s₅ ⟨hm₅, hr₅⟩ => ?_
  have ha : s₃.mem.readW (yp s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 = s₂.gpr PL := by
    rw [hm₃, Mem.readW_writeW_self64]
  rw [P₄.rsi, P₄.r8, hk₄.2.1, ha] at hm₅
  have P₅ := P₄.of_regs (hr₅.mono (by decide))
  have M₅ : MemInv s₀ mS s₅.mem := by
    rw [hm₅]; exact ((M₃.write_y (by omega) _).write_y (by omega) _).write_slot (by omega) (by omega) _
  -- `M = (Y_A ⊕ Y_B) · (H'_A ⊕ H'_B)`
  refine WP.mono (product_ok (.mem (at_ .r8 slotM)) 2 (yv := yB ^^^ s₁.gpr W0)
    (tbl_of hp hS P₅.r8 P₅.rd P₅.wr M₅ (by omega))
    (fun s' hk => by
      rw [hk.readSrc_mem (by decide), slotM, P₅.load_s hp (d := 240) (by omega), hm₅,
        readW_writeW_off _ _ _ (by omega) (by omega) (by omega), hp.readW_s_y _ _ (by omega) (by omega),
        hp.readW_s_y _ _ (by omega) (by omega), hm₃, hp.readW_s_y _ _ (by omega) (by omega),
        hm₁, Mem.readW_writeW_self64, hW₁])) fun s₆ ⟨hP₆, hk₆⟩ => ?_
  have P₆ := P₅.of_regs (hk₆.regs.mono (by decide))
  -- `W₁, W₂, W₃`
  refine WP.mono (keepM_ok s₆ (P₆.in_y hp (d := 0) (by omega)) (P₆.in_y hp (d := 8) (by omega))
    (P₆.in_s hp (d := 248) (by omega)))
    fun s₇ ⟨hAL₇, hAH₇, hPL₇, hk₇⟩ => ?_
  rw [P₆.rsi, hk₆.2.1, hm₅, hp.readW_y_s _ _ (by omega) (by omega),
    readW_writeW_off _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64] at hAL₇
  rw [P₆.rsi, hk₆.2.1, hm₅, hp.readW_y_s _ _ (by omega) (by omega), Mem.readW_writeW_self64] at hAH₇
  rw [P₆.r8, hk₆.2.1, hm₅, Mem.readW_writeW_self64] at hPL₇
  -- the reduction
  refine WP.mono (fold_ok PL AL AH (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s₇) fun s₈ ⟨hAL₈, hAH₈, hk₈⟩ => ?_
  refine WP.mono (fold_ok AH W0 AL (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) s₈) fun s₉ ⟨hW₉, hAL₉, hk₉⟩ => ?_
  have P₉ := P₆.of_regs (((hk₇.regs.mono (c' := bigClob) (by decide)).trans
    (hk₈.regs.mono (by decide))).trans (hk₉.regs.mono (by decide)))
  -- store `Y`
  refine WP.mono (store_ok s₉ (P₉.out_y hp (d := 0) (by omega)) (P₉.out_y hp (d := 8) (by omega)))
    fun s₁₀ ⟨hm₁₀, hrdi₁₀, hrcx₁₀, hzf₁₀, hr₁₀⟩ => ?_
  rw [P₉.rsi] at hm₁₀
  -- the memory after the block
  have hmem₉ : s₉.mem = s₅.mem := hk₉.2.1.trans (hk₈.2.1.trans (hk₇.2.1.trans hk₆.2.1))
  have M₁₀ : MemInv s₀ mS s₁₀.mem := by
    rw [hm₁₀, hmem₉]; exact (M₅.write_y (by omega) _).write_y (by omega) _
  -- the new `Y`
  have hW0₈ : s₈.gpr W0 = s₂.gpr PH := by
    rw [hk₈.1 W0 (by decide), hk₇.1 W0 (by decide), hk₆.1 W0 (by decide), hr₅.1 W0 (by decide),
      hk₄.1 W0 (by decide), hW₃]
  have hW0₄ : s₄.gpr W0 = s₂.gpr PH := by rw [hk₄.1 W0 (by decide), hW₃]
  rw [hW0₄] at hAL₇
  have hy : blockAt s₁₀.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hX : blockAt s.mem (yp s₀) ^^^ blockAt s.mem (blkAddr s₀ i) = s₁.gpr W0 ++ yB := by
      rw [← blockAt_bswap', ← blockAt_bswap', BitVec.xor_append, ← hW₁, hyB]
    have hA' : s₂.gpr PH ++ s₂.gpr PL = prodVal ka (s₁.gpr W0) := hP₂
    have hB' : s₄.gpr PH ++ s₄.gpr PL = prodVal kb yB := hP₄
    have hM' : s₆.gpr PH ++ s₆.gpr PL = prodVal (ka ^^^ kb) (s₁.gpr W0 ^^^ yB) := by
      rw [hP₆, BitVec.xor_comm yB]; rfl
    rw [ghashFrom_blocksAt_succ, ← hL.y,
      ← blockAt_frame (p := blkAddr s₀ i) hL.mem.f1 (by simpa using
        ⟨(hp.y_d.symm.sub_left (hp.blk_sub hi)), hp.d_scr.sub_left (hp.blk_sub hi)⟩),
      hX, ← reduce_eq_mul hH hA' hB' hM', hm₁₀]
    show blockAt (storeMem s₉.mem (yp s₀) (s₉.gpr W0) (s₉.gpr AL)) (yp s₀) = _
    rw [blockAt_storeMem, hW₉, hAL₉, hAL₈, hAH₈, hW0₈, hAL₇, hAH₇, hPL₇]
    rfl
  have hk : ∀ r ∈ [Reg.rsi, .r8, .rsp], s₁₀.gpr r = s₉.gpr r := fun r hr => hr₁₀.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)
  have hrcx : s₉.gpr .rcx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [P₉.rcx]; exact ofNat_sub_succ hi
  have hcommon : Common s₀ mS (i + 1) s₁₀ :=
    ⟨(hk .rsi (by simp)).trans P₉.rsi, (hk .r8 (by simp)).trans P₉.r8, (hk .rsp (by simp)).trans P₉.rsp,
      hr₁₀.2.1.trans P₉.rd, hr₁₀.2.2.trans P₉.wr, M₁₀, hy⟩
  have hev : eval .ne s₁₀ = some (!(BitVec.ofNat 64 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hzf₁₀, hrcx, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨by rw [hev]; decide, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with rdi := ?_, rcx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [hrdi₁₀, P₉.rdi, blkAddr_succ]
    · rw [hrcx₁₀, hrcx]

/-! ## The set-up -/

theorem save_eq : save = [
    .store (at_ .r8 0) .rbx, .store (at_ .r8 8) .rbp, .store (at_ .r8 16) .r12,
    .store (at_ .r8 24) .r13, .store (at_ .r8 32) .r14, .store (at_ .r8 40) .r15] := rfl

theorem restore_eq : restore = [
    .mov .rbx (.mem (at_ .r8 0)), .mov .rbp (.mem (at_ .r8 8)), .mov .r12 (.mem (at_ .r8 16)),
    .mov .r13 (.mem (at_ .r8 24)), .mov .r14 (.mem (at_ .r8 32)), .mov .r15 (.mem (at_ .r8 40))] := rfl

/-- The memory after saving the registers. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (scr s₀ + BitVec.ofInt 64 ((0 : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (scr s₀ + BitVec.ofInt 64 ((8 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (scr s₀ + BitVec.ofInt 64 ((16 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (scr s₀ + BitVec.ofInt 64 ((24 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (scr s₀ + BitVec.ofInt 64 ((32 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (scr s₀ + BitVec.ofInt 64 ((40 : Nat) : Int)) (s₀.gpr .r15)

set_option simprocs false in
theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block save) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = saveMem s₀ := by
  have o0 := hp.out_save (d := 0) (by omega); have o1 := hp.out_save (d := 8) (by omega)
  have o2 := hp.out_save (d := 16) (by omega); have o3 := hp.out_save (d := 24) (by omega)
  have o4 := hp.out_save (d := 32) (by omega); have o5 := hp.out_save (d := 40) (by omega)
  apply WP.of_runBlock
  rw [save_eq]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem saveMem_saved {s₀ : State} : Saved s₀ (saveMem s₀) := by
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_off]

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

theorem Saved.write {s₀ : State} {m : Mem} (h : Saved s₀ m) {e : Nat} (he : 48 ≤ e) (he' : e < 2 ^ 32)
    (v : BitVec 64) : Saved s₀ (m.writeW (scr s₀ + BitVec.ofInt 64 (e : Int)) v) := by
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := h
  exact ⟨(readW_writeW_off _ _ _ (d := 0) (by omega) he' (by omega)).trans g0,
    (readW_writeW_off _ _ _ (d := 8) (by omega) he' (by omega)).trans g1,
    (readW_writeW_off _ _ _ (d := 16) (by omega) he' (by omega)).trans g2,
    (readW_writeW_off _ _ _ (d := 24) (by omega) he' (by omega)).trans g3,
    (readW_writeW_off _ _ _ (d := 32) (by omega) he' (by omega)).trans g4,
    (readW_writeW_off _ _ _ (d := 40) (by omega) he' (by omega)).trans g5⟩

theorem tbl_word {s : State} {ka kb : BitVec 64} (hAL : s.gpr AL = ka) (hAH : s.gpr AH = kb)
    (hPH : s.gpr PH = ka ^^^ kb) (q : Nat) : s.gpr (tblReg q) = hword ka kb q := by
  rcases q with _ | _ | q
  · exact hAL
  · exact hAH
  · exact hPH

/-- While the tables are written: `k` parts done. -/
def EInv (s₀ s₂ : State) (k : Nat) (s : State) : Prop :=
  Regs [.rax] s₂ s ∧ Frame [scrR s₀] s₀.mem s.mem ∧ Saved s₀ s.mem ∧
  ∀ u < k, s.mem.readW (scr s₀ + BitVec.ofInt 64 ((off u : Nat) : Int)) 64 =
    part (hword (s₂.gpr AL) (s₂.gpr AH) (u / 8)) (u % 8)

theorem entry_step {s₀ s₂ : State} (hp : Pre s₀) (hr8 : s₂.gpr .r8 = scr s₀) (hwr : s₂.wr = s₀.wr)
    (hPH : s₂.gpr PH = s₂.gpr AL ^^^ s₂.gpr AH) (k : Nat) (s : State) (hk : k < 24)
    (hI : EInv s₀ s₂ k s) : WP isa (.block (entry k)) s (EInv s₀ s₂ (k + 1)) := by
  obtain ⟨hr, hf, hsv, ht⟩ := hI
  have hr8' : s.gpr .r8 = scr s₀ := (hr.1 _ (by decide)).trans hr8
  have ho : off k + 8 ≤ 240 := by simp only [off]; omega
  refine WP.mono (entry_ok k s (by rw [hr.2.2, hwr, hr8']; exact hp.out_save (by omega)))
    fun s' ⟨hm, hr'⟩ => ?_
  rw [hr8', hr.1 _ (by simpa using tblReg_ne (k / 8)), tbl_word rfl rfl hPH] at hm
  refine ⟨hr.trans hr', ?_, ?_, fun u hu => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
  · rw [hm]; exact hsv.write (by simp only [off]; omega) (by omega) _
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
    · rw [readW_writeW_off _ _ _ (by simp only [off]; omega) (by omega) (by simp only [off]; omega)]
      exact ht u hu
    · rw [Mem.readW_writeW_self64, part, show u % 8 % 2 = u % 2 by omega]

/-- The registers the set-up changes. -/
abbrev setupClob : List Reg := [AL, AH, .rax, PL, PH, .rdi]

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s₁ => ∃ ka kb, x * φ (ka ++ kb) = φ (H₀ s₀) ∧
      SetupMem s₀ ka kb s₁.mem ∧ s₁.zf = some (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) ∧
      s₁.gpr .rdi = dp s₀ ∧ Regs setupClob s₀ s₁ := by
  rw [setup]
  repeat rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun s₁ ⟨hg, hrd, hwr, hm⟩ => ?_
  have hh : ∀ d : Nat, d + 8 ≤ 16 → s₁.mem.readW (s₁.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64 =
      s₀.mem.readW (hA s₀ + BitVec.ofInt 64 (d : Int)) 64 := fun d hd => by
    rw [hg, hm]
    exact saveMem_frame.readW (contains_offset' (base := hA s₀) hd (by omega))
      (by simpa using hp.h_scr) (by decide)
  refine WP.mono (hInv_ok s₁ (by rw [hrd, hwr, hg]; exact hp.in_h (by omega))
    (by rw [hrd, hwr, hg]; exact hp.in_h (by omega))) fun s₂ ⟨hK, hPH, hk₂⟩ => ?_
  rw [hh 0 (by omega), hh 8 (by omega), blockAt_bswap'] at hK
  have hH : x * φ (s₂.gpr AL ++ s₂.gpr AH) = φ (H₀ s₀) := by rw [hK]; exact x_φ_hInv _
  have hr8₂ : s₂.gpr .r8 = scr s₀ := by rw [hk₂.1 _ (by decide), hg]
  have hwr₂ : s₂.wr = s₀.wr := hk₂.2.2.2.trans hwr
  refine WP.mono (wp_range_flatMap (EInv s₀ s₂) (entry_step hp hr8₂ hwr₂ hPH) 24 (Nat.le_refl _) s₂
    ⟨⟨fun _ _ => rfl, rfl, rfl⟩, by rw [hk₂.2.1, hm]; exact saveMem_frame,
      by rw [hk₂.2.1, hm]; exact saveMem_saved, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s₃ ⟨hr₃, hf₃, hsv₃, ht₃⟩ => ?_
  refine WP.mono (tail_ok s₃) fun s₄ ⟨hrdi, hzf, hk₄⟩ => ?_
  have hr : Regs setupClob s₀ s₃ :=
    ((show Regs setupClob s₀ s₁ from ⟨fun r _ => by rw [hg], hrd, hwr⟩).trans
      (hk₂.regs.mono (by decide))).trans (hr₃.mono (by decide))
  refine ⟨s₂.gpr AL, s₂.gpr AH, hH, ⟨?_, ?_, ?_⟩, ?_, ?_, hr.trans (hk₄.regs.mono (by decide))⟩
  · rw [hk₄.2.1]; exact hsv₃
  · rw [hk₄.2.1]; exact ht₃
  · rw [hk₄.2.1]; exact hf₃
  · rw [hzf, hr.1 _ (by decide)]
  · rw [hrdi, hr.1 _ (by decide)]

/-! ## The end -/

set_option simprocs false in
theorem restore_ok {s₀ : State} (hp : Pre s₀) {mS : Mem} (hsv : Saved s₀ mS) {s : State}
    (hc : Common s₀ mS (nb s₀) s) :
    WP isa (.block restore) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Gcm.ghashX86_64.post s₀ s' := by
  have i0 := hp.in_save (d := 0) (by omega); have i1 := hp.in_save (d := 8) (by omega)
  have i2 := hp.in_save (d := 16) (by omega); have i3 := hp.in_save (d := 24) (by omega)
  have i4 := hp.in_save (d := 32) (by omega); have i5 := hp.in_save (d := 40) (by omega)
  rw [← hc.rd, ← hc.wr] at i0 i1 i2 i3 i4 i5
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hsv
  rw [← hc.mem.readW_low hp (by omega)] at g0 g1 g2 g3 g4 g5
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.mem.f1.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_y, hp.ret_scr⟩) (by decide)
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
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨ka, kb, hH, hS, hzf, hrdi, hr⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ s₁.mem (nb s₀)) ?_ fun s₂ hc => restore_ok hp hS.saved hc)
  have hc₀ : Common s₀ s₁.mem 0 s₁ := by
    refine ⟨hr.1 _ (by decide), hr.1 _ (by decide), hr.1 _ (by decide), hr.2.1, hr.2.2,
      ⟨hS.frame.mono fun r hr => by simp at hr; simp [hr], Frame.refl _ _⟩, ?_⟩
    rw [ghashFrom_blocksAt_zero]
    exact blockAt_congr fun _ hk =>
      hS.frame.bytes (R := yR s₀) (by simpa using hp.y_scr) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  refine WP.ite (s₀.gpr .rcx &&& s₀.gpr .rcx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ s₁.mem i s
    have hstep : ∀ m s, Inv m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ s₁.mem (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hS hH hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ s₁.mem 0 s₁ :=
      { hc₀ with
        rdi := by rw [hrdi]; simp [blkAddr]
        rcx := by rw [hr.1 _ (by decide)]; simp [nb] }
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
