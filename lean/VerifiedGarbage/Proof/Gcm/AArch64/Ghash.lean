import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Gcm.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Step`.
section

/-!
# GHASH on AArch64: one step of Algorithm 1

Untrusted: everything here is checked by Lean. What the instructions of a
step (`Impl.Gcm.AArch64.step`) compute on the two halves of a 128-bit value,
stated on the whole value, and the 128 steps.
-/

open VG.PowLit

namespace VG.Proof.Gcm.AArch64

open VG VG.AArch64 VG.Impl.Gcm.AArch64 VG.Proof.Gcm
open VG.Spec.Gcm (Block)

/-! ## The bit manipulations -/

/-- `lsl hi, hi, 1; lsr t, lo, 63; orr hi, hi, t; lsl lo, lo, 1` shifts
`hi ++ lo` left by one bit. -/
theorem shl1 (a b : BitVec 64) : (a <<< 1 ||| b >>> 63) ++ b <<< 1 = (a ++ b) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 64
  · by_cases h0 : i = 0
    · subst h0; simp
    · simp [h1, h0, hi, show i - 1 < 64 by omega_using [hi, h1]]
  · by_cases h64 : i = 64
    · subst h64; simp
    · simp [h1, hi, show i - 64 < 64 by omega_using [hi, h1], show ¬ i - 1 < 64 by omega_using [hi, h1, h64]]
      rw [BitVec.getLsbD_of_ge b (63 + (i - 64)) (by omega_using [hi, h1, h64]), Bool.or_false,
        decide_eq_false (show i - 64 ≠ 0 by omega_using [hi, h1, h64]), decide_eq_false (show i ≠ 0 by omega_using [hi, h1])]
      simp only [Bool.not_false, Bool.true_and]
      congr 1

/-- `0 − (x >>> 63)` is all ones if the top bit of `x` is set, and zero otherwise. -/
theorem neg_msb (x : BitVec 64) :
    (0 : BitVec 64) - x >>> 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  have h : x >>> 63 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega_using [hi] : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (64 - 1) <;> simp
    · simp only [show 63 + i ≥ 64 by omega_using [hi, h], BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega_using [hi, h]]
  rw [h]; split <;> decide

/-- `lsl t, lo, 63; lsr t, t, 63` isolates the lowest bit. -/
theorem neg_lsb (x : BitVec 64) :
    (0 : BitVec 64) - x <<< 63 >>> 63 = if x.getLsbD 0 then BitVec.allOnes 64 else 0 := by
  rw [neg_msb]
  have : (x <<< 63).msb = x.getLsbD 0 := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]; simp
  rw [this]

theorem mask_z (zh zl vh vl : BitVec 64) (c : Bool) :
    (zh ^^^ (vh &&& if c then BitVec.allOnes 64 else 0)) ++
      (zl ^^^ (vl &&& if c then BitVec.allOnes 64 else 0)) =
      if c then (zh ++ zl) ^^^ (vh ++ vl) else zh ++ zl := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_append]

theorem R_eq : Spec.Gcm.R = rHigh ++ 0#64 := by decide

/-- `lsr lo, lo, 1; lsl t, hi, 63; orr lo, lo, t; lsr hi, hi, 1` shifts
`hi ++ lo` right by one bit. -/
theorem shr1 (a b : BitVec 64) : a >>> 1 ++ (b >>> 1 ||| a <<< 63) = (a ++ b) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rcases (by omega_using [hi] : i < 63 ∨ i = 63 ∨ 64 ≤ i) with h | h | h
  · simp [h, show 1 + i < 64 by omega_using [hi, h], show i < 64 by omega_using [hi, h]]
  · subst h; simp
  · simp only [show ¬ 1 + i < 64 by omega_using [hi, h], show ¬ i < 64 by omega_using [hi, h], ite_false]
    congr 1; omega_using [hi, h]

theorem update_v (vh vl : BitVec 64) :
    (vh >>> 1 ^^^ ((0 : BitVec 64) - vl <<< 63 >>> 63 &&& rHigh)) ++ (vl >>> 1 ||| vh <<< 63) =
      if (vh ++ vl).getLsbD 0 then ((vh ++ vl) >>> 1) ^^^ Spec.Gcm.R else (vh ++ vl) >>> 1 := by
  rw [neg_lsb, R_eq, BitVec.getLsbD_append, ← shr1]
  simp only [show (0 : Nat) < 64 by decide, ite_true]
  cases vl.getLsbD 0
  · simp
  · simp only [ite_true, BitVec.allOnes_and]
    rw [BitVec.xor_append, BitVec.xor_zero]

theorem msb_shiftLeft (x : Block) (k : Nat) : (x <<< k).msb = x.getMsbD k := by
  rw [BitVec.msb_eq_getMsbD_zero, BitVec.getMsbD_shiftLeft, Nat.zero_add]

/-! ## One step -/

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.x0, .x1, .x2, .x3, .x4, RH, CNT, ZERO]

set_option simprocs false in
theorem step_ok (x : Block) (zv : Block × Block) (k : Nat) (s : State)
    (hx : s.gpr XH ++ s.gpr XL = x <<< k)
    (hzv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = zv)
    (hr : s.gpr RH = rHigh) (hz : s.gpr ZERO = 0) :
    WP isa (.block step) s fun s' =>
      s'.gpr XH ++ s'.gpr XL = x <<< (k + 1) ∧
      (s'.gpr ZH ++ s'.gpr ZL, s'.gpr VH ++ s'.gpr VL) = mulStep x zv k ∧
      (∀ r ∈ stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hzv
  simp only [XH, XL, ZH, ZL, VH, VL, RH, ZERO] at hx hr hz ⊢
  apply WP.of_runBlock
  simp only [step, XH, XL, ZH, ZL, VH, VL, M, T, RH, ZERO]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, State.write, BitVec.setWidth_eq, Size.bits,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  and_intros
  · rw [shl1, hx, BitVec.shiftLeft_add]
  · have hmsb : (s.gpr .x5).msb = x.getMsbD k := by
      rw [← msb_shiftLeft, ← hx, BitVec.msb_append]; rfl
    rw [hz, neg_msb, hmsb, mask_z, hr, update_v]
    rfl
  · intro r hr
    simp only [stepKeep, RH, CNT, ZERO, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) only [ite_false]
  all_goals trivial

/-! ## The 128 steps -/

/-- The registers the multiplication does not write. -/
def keepRegs : List Reg := [.x0, .x1, .x2, .x3, .x4]

theorem keep_sub {r : Reg} (h : r ∈ keepRegs) : r ∈ stepKeep := by
  simp only [keepRegs, stepKeep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- After `k` steps of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (sB : State) (k : Nat) (s : State) : Prop where
  xr : s.gpr XH ++ s.gpr XL = x <<< k
  zv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = mulSteps x h k
  rh : s.gpr RH = rHigh
  zero : s.gpr ZERO = 0
  keep : ∀ r ∈ keepRegs, s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem inner_step {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s) :
    WP isa (.block step) s fun s' => Inner x h sB (k + 1) s' ∧ s'.gpr CNT = s.gpr CNT := by
  refine WP.mono (step_ok x _ k s hs.xr hs.zv hs.rh hs.zero)
    fun s' ⟨hx, hzv, hk, hm, hrd, hwr⟩ => ?_
  refine ⟨⟨hx, by rw [hzv, mulSteps_succ], by rw [hk _ (by simp [stepKeep]), hs.rh],
    by rw [hk _ (by simp [stepKeep]), hs.zero],
    fun r hr => by rw [hk r (keep_sub hr), hs.keep r hr], by rw [hm, hs.mem], by rw [hrd, hs.rd],
    by rw [hwr, hs.wr]⟩, hk _ (by simp [stepKeep])⟩

theorem Inner.of_gpr {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s)
    {s' : State} (hg : ∀ r, r ≠ CNT → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inner x h sB k s' where
  xr := by rw [hg XH (by decide), hg XL (by decide)]; exact hs.xr
  zv := by rw [hg ZH (by decide), hg ZL (by decide), hg VH (by decide), hg VL (by decide)]; exact hs.zv
  rh := by rw [hg RH (by decide)]; exact hs.rh
  zero := by rw [hg ZERO (by decide)]; exact hs.zero
  keep r hr := by
    have : r ≠ CNT := by
      simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hg r this]; exact hs.keep r hr
  mem := hm.trans hs.mem
  rd := hrd.trans hs.rd
  wr := hwr.trans hs.wr

set_option simprocs false in
theorem steps_ok {x h : Block} {sB : State} {j : Nat} (hj : j < 128 / unroll) {s : State}
    (hs : Inner x h sB (unroll * j) s) (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)) :
    WP isa (.block steps) s fun s' => Inner x h sB (unroll * (j + 1)) s' ∧
      s'.gpr CNT = BitVec.ofNat 64 (128 / unroll - (j + 1)) := by
  rw [steps, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h sB (unroll * j + k) s' ∧ s'.gpr CNT = s.gpr CNT)
    (fun k s' _ ⟨hs', hc'⟩ => WP.mono (inner_step hs') fun s'' ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll (Nat.le_refl _) s ⟨hs, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  have e : 128 / unroll - j = (128 / unroll - (j + 1)) + 1 := by
    simp only [unroll] at hj ⊢; omega_using [hj]
  rw [e] at hc
  apply WP.of_runBlock
  simp only [CNT] at hc hc₁ ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, State.write, BitVec.setWidth_eq, Size.bits,
    ite_true, hc₁, hc, Option.some.injEq, exists_eq_left']
  have hlt : 128 / unroll - (j + 1) < 2 ^ 64 := by simp only [unroll]; omega_using []
  generalize 128 / unroll - (j + 1) = c at hlt ⊢
  have e2 : BitVec.ofNat 64 (c + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 c :=
    Offset.ofNat_sub_ofNat (Nat.le_add_left 1 c)
  rw [e2]
  refine ⟨?_, rfl⟩
  rw [Nat.mul_succ]
  exact hs₁.of_gpr (fun r hr => ite_eq_right hr) rfl rfl rfl

/-- The loop of `128 / unroll` iterations: all 128 steps. -/
theorem mul_ok {x h : Block} {sB s : State} (hs : Inner x h sB 0 s)
    (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll)) :
    WP isa (.loop (.block steps) (.nonzero .x CNT)) s (Inner x h sB 128) := by
  let Inv : Nat → State → Prop := fun m s =>
    ∃ j, m = 128 / unroll - j ∧ j < 128 / unroll ∧ Inner x h sB (unroll * j) s ∧
      s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)
  refine WP.loop (M := isa) Inv (fun m s ⟨j, hm, hj, hs, hc⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs, hc⟩
  subst hm
  refine WP.mono (steps_ok hj hs hc) fun s' ⟨hs', hc'⟩ => ?_
  have hev : eval (.nonzero .x CNT) s' = some (BitVec.ofNat 64 (128 / unroll - (j + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hc']
  by_cases hlast : j + 1 = 128 / unroll
  · left
    rw [hlast, Nat.sub_self] at hev
    refine ⟨hev.trans (by decide), ?_⟩
    rw [hlast] at hs'
    exact hs'
  · right
    have hne : BitVec.ofNat 64 (128 / unroll - (j + 1)) ≠ 0 := by
      simp only [unroll] at hlast hj ⊢
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, this])] at this
      simp at this; omega_using [hj, hlast, this]
    refine ⟨hev.trans (by simpa using hne), _, by omega_using [hj, hlast], j + 1, rfl, by omega_using [hj, hlast], hs', hc'⟩

end VG.Proof.Gcm.AArch64

end

-- Formerly the module `VerifiedGarbage.Proof.Gcm.AArch64.Ghash`.
section

/-!
# GHASH on AArch64: the whole function

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

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
    fun j _ => Offset.add_add p j 1
  rw [rev64_readW, rev64_readW, e 0 (by decide), e 1 (by decide), e 2 (by decide),
    e 3 (by decide), e 4 (by decide), e 5 (by decide), e 6 (by decide), e 8 (by decide), e 9 (by decide),
    e 10 (by decide), e 11 (by decide), e 12 (by decide), e 13 (by decide), e 14 (by decide),
    Spec.Gcm.blockAt, bytesAt_16, ofBytes_16]

theorem read_8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW]; exact (BitVec.setWidth_eq _).symm

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

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
  rw [blkAddr, Offset.add_add]
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
  have h0 := hh 0 (by decide); have h8 := hh 8 (by decide)
  have y0 := hy 0 (by decide); have y8 := hy 8 (by decide)
  have d0 := hd 0 (by decide); have d8 := hd 8 (by decide)
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

theorem half_sep (p : Addr) : Mem.Sep (p + BitVec.ofNat 64 0) 8 (p + BitVec.ofNat 64 8) 8 :=
  Offset.sep p (by decide) (by decide) (by decide)

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
  have y0 := hy 0 (by decide); have y8 := hy 8 (by decide)
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
  (h.writeW (List.mem_cons_self ..) _ (contains_offset (by decide) (by decide))).writeW
    (List.mem_cons_self ..) _ (contains_offset (by decide) (by decide))

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
    rw [hk .x3 (by decide), hL.x3, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
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
    · rw [hx2₃, hk .x2 (by decide), hL.x2, blkAddr, blkAddr,
        show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, Nat.mul_succ]
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
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩

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

end
