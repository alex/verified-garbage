import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.AArch64.Step
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# GHASH on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Gcm

open Spec.Gcm

open VG.AArch64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`:
replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over the `n`
blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other or the other
buffers. The pointers and `n` are public; `H`, `Y` and the data are
secret. -/
def ghashAArch64 : Contract AArch64.isa where
  pre s :=
    let h : Region := ⟨s.gpr .x0, 16⟩
    let y : Region := ⟨s.gpr .x1, 16⟩
    let data : Region := ⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch
  post s s' :=
    blockAt s'.mem (s.gpr .x1) =
      ghashFrom (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
        (blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Gcm

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## Big-endian halves -/

/-- `rev` is `byteRev64`, an involution. -/
theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := byteRev64_byteRev64 a

/-- The 16 bytes as 8 bytes. -/
theorem bytesAt_16 (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] := rfl

/-- Two 8-byte loads and `rev`s read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    rev64 (m.readW (p + BitVec.ofNat 64 0) 64) ++ rev64 (m.readW (p + BitVec.ofNat 64 8) 64) =
      blockAt m p := by
  have e : ∀ j : Nat, j < 15 → p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) :=
    fun j hj => by bv_omega
  rw [rev64_readW, rev64_readW, e 0 (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 8 (by omega), e 9 (by omega),
    e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega),
    Spec.Gcm.blockAt, bytesAt_16, ofBytes_16]

theorem read_8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

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

abbrev hA : Addr := s₀.gpr .x0
abbrev yp : Addr := s₀.gpr .x1
abbrev dp : Addr := s₀.gpr .x2
abbrev nb : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashAArch64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

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
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨hR s₀, by simp [h.rd], contains_offset hd (by omega)⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], contains_offset hd (by omega)⟩

theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) := by
  have := h.nb_lt
  exact sub_offset (by omega) (by omega)

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 d = dp s₀ + BitVec.ofNat 64 (16 * i + d) by
    simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = hA s₀
  x1 : s.gpr .x1 = yp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x2 : s.gpr .x2 = blkAddr s₀ i
  x3 : s.gpr .x3 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

set_option simprocs false in
theorem load_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8)
    (hd : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 d) 8) :
    WP isa (.block load) s fun s₁ =>
      Inner (blockAt s.mem (s.gpr .x1) ^^^ blockAt s.mem (s.gpr .x2)) (blockAt s.mem (s.gpr .x0))
        s 0 s₁ ∧ s₁.gpr CNT = BitVec.ofNat 64 (128 / unroll) := by
  have h0 := hh 0 (by omega); have h8 := hh 8 (by omega)
  have y0 := hy 0 (by omega); have y8 := hy 8 (by omega)
  have d0 := hd 0 (by omega); have d8 := hd 8 (by omega)
  apply WP.of_runBlock
  simp only [load, XH, XL, ZH, ZL, VH, VL, T, RH, CNT, ZERO]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.load, Size.bytes, h0, h8, y0, y8, d0, d8, State.read, State.write,
    BitVec.setWidth_eq, Size.bits, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩, trivial⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [BitVec.shiftLeft_zero, ← BitVec.xor_append, read_8, read_8, read_8, read_8, blockAt_rev,
      blockAt_rev]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [mulSteps_zero, read_8, read_8, blockAt_rev]
    rfl
  · simp (config := {decide := true}) only [ite_true, ite_false, RH]
  · simp (config := {decide := true}) only [ite_true, ite_false, ZERO]
  · simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_false]

theorem write_8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW]; exact congrArg (m.write a 8) (BitVec.setWidth_eq _).symm

/-- The memory after storing `Z` at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 0) (rev64 zh)).writeW (p + BitVec.ofNat 64 8) (rev64 zl)

theorem half_sep (p : Addr) : Mem.Sep (p + BitVec.ofNat 64 0) 8 (p + BitVec.ofNat 64 8) 8 := by
  intro x hx hy
  bv_omega

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) :
    blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_rev, storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (half_sep p) (by decide), Mem.readW_writeW_self64, rev64_rev64,
    rev64_rev64]

set_option simprocs false in
theorem store_ok (s : State)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 d) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = storeMem s.mem (s.gpr .x1) (s.gpr ZH) (s.gpr ZL) ∧
      s'.gpr .x2 = s.gpr .x2 + 16 ∧ s'.gpr .x3 = s.gpr .x3 - 1 ∧
      (∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ ZH → r ≠ ZL → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have y0 := hy 0 (by omega); have y8 := hy 8 (by omega)
  apply WP.of_runBlock
  simp only [store, ZH, ZL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, State.store, Size.bytes, y0, y8, State.read, State.write,
    BitVec.setWidth_eq, Size.bits, ite_true, ite_false, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by rw [storeMem, write_8, write_8], rfl, rfl, fun r h2 h3 h7 h8 => ?_, trivial⟩
  simp only [h2, h3, h7, h8, ite_false]

theorem storeMem_frame {s₀ : State} {m m' : Mem} (h : Frame [yR s₀] m m') (zh zl : BitVec 64) :
    Frame [yR s₀] m (storeMem m' (yp s₀) zh zl) :=
  (h.writeW (List.mem_cons_self ..) _ (contains_offset (by omega) (by omega))).writeW
    (List.mem_cons_self ..) _ (contains_offset (by omega) (by omega))

/-- Memory outside `y` is as on entry. -/
theorem blockAt_frame {s₀ : State} {m : Mem} (h : Frame [yR s₀] s₀.mem m) {p : Addr}
    (hd : Region.Disjoint ⟨p, 16⟩ (yR s₀)) : blockAt m p = blockAt s₀.mem p :=
  blockAt_congr fun _ hk =>
    h.bytes (R := ⟨p, 16⟩) (by simpa using hd) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x3) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x3) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok s
    (fun d hd => by rw [hL.rd, hL.wr, hL.x0]; exact hp.in_h hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.x1]; exact hp.in_y hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.x2]; exact hp.in_blk hi hd)) fun s₁ ⟨hI₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hI₁ hc₁) fun s₂ hI₂ => ?_)
  have hx1₂ : s₂.gpr .x1 = yp s₀ := (hI₂.keep .x1 (by decide)).trans hL.x1
  refine WP.mono (store_ok s₂ fun d hd => by rw [hI₂.wr, hL.wr, hx1₂]; exact hp.out_y hd)
    fun s₃ ⟨hm₃, hx2₃, hx3₃, hk₃, hrd₃, hwr₃⟩ => ?_
  have hk : ∀ r ∈ keepRegs, s₂.gpr r = s.gpr r := hI₂.keep
  have hx3 : s₂.gpr .x3 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hk .x3 (by decide), hL.x3]
    have := (s₀.gpr .x3).isLt
    bv_omega
  have hy : blockAt s₃.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hz1 := congrArg Prod.fst hI₂.zv
    simp only at hz1
    rw [hm₃, hx1₂, blockAt_storeMem, ghashFrom_blocksAt_succ, ← hL.y, mul_eq, hz1, hL.x1, hL.x2,
      hL.x0, blockAt_frame (p := hA s₀) hL.frame hp.h_y,
      blockAt_frame (p := blkAddr s₀ i) hL.frame (hp.y_d.symm.sub_left (hp.blk_sub hi))]
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hk₃ _ (by decide) (by decide) (by decide) (by decide), hk .x0 (by decide), hL.x0],
      by rw [hk₃ _ (by decide) (by decide) (by decide) (by decide), hx1₂],
      by rw [hrd₃, hI₂.rd, hL.rd], by rw [hwr₃, hI₂.wr, hL.wr], ?_, hy⟩
    rw [hm₃, hx1₂, hI₂.mem]; exact storeMem_frame hL.frame _ _
  have hev : eval (.nonzero .x .x3) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx3₃, hx3]
  by_cases hlast : i + 1 = nb s₀
  · left
    rw [hlast, Nat.sub_self] at hev
    exact ⟨hev.trans (by decide), hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with x2 := ?_, x3 := ?_ }⟩
    · have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      exact hev.trans (by simpa using h0)
    · rw [hx2₃, hk .x2 (by decide), hL.x2]
      simp only [blkAddr]
      bv_omega
    · rw [hx3₃, hx3]

/-! ## The whole function -/

theorem common_zero (s₀ : State) : Common s₀ 0 s₀ :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, (ghashFrom_blocksAt_zero _ _ _ _).symm⟩

theorem loops_ok {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => Proof.Gcm.ghashAArch64.post s₀ s' := by
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => hc.y
  have hev : eval (.zero .x .x3) s₀ = some (s₀.gpr .x3 == 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite (s₀.gpr .x3 == 0) hev (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ common_zero s₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x3) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x3) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { common_zero s₀ with
        x2 := by simp [blkAddr]
        x3 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashAArch64.post s₀ s' :=
  WP.mono (WP.gprs (rs := preserved) (loops_ok hp) (by decide +kernel) (by decide +kernel))
    fun _ ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x4 => 0x4000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashAArch64.pre s) :
    ∃ t s', Exec isa Impl.Gcm.AArch64.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub
    Impl.Gcm.AArch64.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem ghash_verified :
    Verified AArch64.target Impl.Gcm.AArch64.ghash (Spec.Gcm.ghashContract AArch64.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Gcm.AArch64.satState] using Proof.Gcm.AArch64.satState)

end VG.Proof.Gcm.AArch64
