import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Impl.MdStream.X86
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Dims`, `Shape`) and of its compression function
(`CalleeOk`), the call of the compression function (`compressAt_ok`),
weakest-precondition rules for the instructions used that expose only what
changes, and arithmetic on 32-bit values.
-/

namespace VG.Proof.MdStream.X86

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Regions -/

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by
        rw [VG.Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.mod_le _ _
  omega

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [VG.Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem addr_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- `[x + d]`, for a word within a region at `x` inside the 32-bit address space. -/
theorem contains_addr {x : BitVec 32} {d n len : Nat} (h : d + n ≤ len) (hn : 0 < n)
    (hx : x.toNat + len ≤ 2 ^ 32) :
    (⟨x.setWidth 64, len⟩ : Region).Contains (addr x d) n := by
  rw [addr_eq (by omega)]
  exact contains_offset h (by omega)

/-- `[(x + k) + d]`, where nothing wraps around the 32-bit address space. -/
theorem addr_add_ofNat {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- Two accesses `[x + d]` and `[x + e]` of `n` and `k` bytes that do not overlap. -/
theorem addr_sep {x : BitVec 32} {d e n k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32) (he : x.toNat + e + k ≤ 2 ^ 32)
    (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (addr x d) n (addr x e) k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun _ h₁ => absurd h₁ (Nat.not_lt_zero _)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact fun _ _ h₂ => absurd h₂ (Nat.not_lt_zero _)
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_addr (m : Mem) {x : BitVec 32} (v : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr x e) v).readW (addr x d) 32 = m.readW (addr x d) 32 :=
  Mem.readW_writeW_sep (addr_sep hd he h) (by decide)

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- A region within one of `rs'`, at offset `o`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-! ## Arithmetic -/

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem ofNat_succ (k : Nat) : BitVec.ofNat 32 (k + 1) = BitVec.ofNat 32 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_add_add (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem lit32 (n : Nat) : (OfNat.ofNat n : BitVec 32) = BitVec.ofNat 32 n := rfl

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (v : BitVec 32) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (v : BitVec 32) :
    Upd s ((s.setFlags c o z n).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load32, ha, hin]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ha, hout]

theorem wp_addi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v) → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_andi {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_bswap {d : Reg} (k : ∀ s', Upd s s' d (bswap (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ha, hout]

end

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem eval_e (s : State) : eval .e s = s.zf := rfl
theorem eval_ne (s : State) : eval .ne s = s.zf.map (!·) := rfl
theorem eval_b (s : State) : eval .b s = s.cf := rfl
theorem eval_ae (s : State) : eval .ae s = s.cf.map (!·) := rfl

theorem seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

/-! ## Sizes -/

/-- The sizes the generic proofs support, for blocks of `B` bytes, a hash
value of `N` bytes, a length field of `L` bytes, a compression function using
`so` bytes of scratch space, and `S` bytes of scratch space in all: checked for
each hash function by `decide`. -/
structure Dims (P : Params) (S : Nat) : Prop where
  B : P.B = 64 ∨ P.B = 128
  N : 0 < P.N ∧ P.N ≤ 64
  L : 0 < P.L ∧ P.L ≤ 16
  so : P.so + 28 ≤ S
  S : S ≤ 4096

section
variable {P : Params} {S : Nat} (hd : Dims P S)
include hd

theorem Dims.pos : 0 < P.B := by rcases hd.B with h | h <;> omega

theorem Dims.le : P.B ≤ 128 := by rcases hd.B with h | h <;> omega

theorem Dims.ge : 64 ≤ P.B := by rcases hd.B with h | h <;> omega

theorem Dims.mod (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

/-- A byte count modulo `B`, from its low word. -/
theorem Dims.mod_append (hi lo : BitVec 32) : (hi ++ lo).toNat % P.B = lo.toNat % P.B := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  rcases hd.B with h | h <;> rw [h] <;> omega

/-- `x mod B`, as `direct`, `update` and `finalize` compute it. -/
theorem Dims.and (x : BitVec 32) : x &&& BitVec.ofNat 32 (P.B - 1) = BitVec.ofNat 32 (x.toNat % P.B) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- The shift count of `direct`. -/
theorem Dims.lg : 1 ≤ Nat.log2 P.B ∧ Nat.log2 P.B ≤ 31 := by
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- `a / B`, as `direct` computes it. -/
theorem Dims.shr {a : Nat} (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> Nat.log2 P.B = BitVec.ofNat 32 (a / P.B) := by
  have e : 2 ^ Nat.log2 P.B = P.B := by
    rcases hd.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, e, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

end

theorem restore_eq (P : Params) (b : Reg) : restore P b = [
    .mov .ebx (.mem (at_ b P.so)), .mov .esi (.mem (at_ b (P.so + 4))),
    .mov .edi (.mem (at_ b (P.so + 8))), .mov .ebp (.mem (at_ b (P.so + 12)))] :=
  rfl

theorem save_eq (P : Params) (b : Reg) : save P b = [
    .store (at_ b P.so) .ebx, .store (at_ b (P.so + 4)) .esi, .store (at_ b (P.so + 8)) .edi,
    .store (at_ b (P.so + 12)) .ebp] :=
  rfl

/-- The saved registers are outside the part of the scratch space the
compression function uses, before `count` and `out`. -/
theorem saved_offset {P : Params} {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 4 ≤ P.so + 16 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def count (s : State) : BitVec 64 := arg s 2 ++ arg s 1

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function
`compress(state, blocks, n, scratch)`: updates the hash value at `state`
with the `n` blocks at `blocks`, with `so` bytes of scratch space. -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, P.N⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, P.B * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, P.so⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + P.N ≤ 2 ^ 32 ∧ (arg s 1).toNat + P.B * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + P.so ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem ((arg s 0).setWidth 64) =
      H.compressBlocks (H.stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64) (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

variable (S : Nat)

/-- The contract of `update(state, count, data, len, scratch)`: if the state
represents a message of `count` bytes (modulo 2⁶⁴) from any initial hash
value, it then represents that message followed by the `len` bytes at
`data`. The arguments are only read (the taint analysis follows them in
memory only while nothing that may alias them is written). -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, P.N + P.B⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem ((arg s 0).setWidth 64) m → count s = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem ((arg s 0).setWidth 64) (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- The contract of `finalize(state, count, out, scratch)`: if the state
represents a message of `count` bytes, writes its final hash value to `out`
(`N` bytes). The arguments are only read. -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, P.N + P.B⟩
    let out : Region := ⟨(arg s 3).setWidth 64, P.N⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (arg s 3).toNat + P.N ≤ 2 ^ 32 ∧
    (arg s 4).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem ((arg s 0).setWidth 64) m → H.lenOk m.length →
    count s = BitVec.ofNat 64 m.length → bytesAt s'.mem ((arg s 3).setWidth 64) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `finK`, but letting `finalize` write its arguments (as the contracts of the
hash functions whose `finalize` is only verified against this say). -/
def finKw : Contract isa :=
  { finK H S with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, P.N + P.B⟩
      let out : Region := ⟨(arg s 3).setWidth 64, P.N⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, S⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (arg s 3).toNat + P.N ≤ 2 ^ 32 ∧
      (arg s 4).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `[ebp + so + 16]` (low word) and `[ebp + so + 20]` (high word)
at `ebx + N + B - L`, writing only `eax`, `ecx` and `edx`, and `P.out` writes
the digest of the hash value at `ebx` to `eax`, writing only `ecx`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  len : ∀ s : State, (s.gpr .ebx).toNat + (P.N + P.B) ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (P.so + 16)) 4 →
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (P.so + 20)) 4 →
    (∀ d, P.N + P.B - P.L ≤ d → d + 4 ≤ P.N + P.B → InRegions s.wr (addr (s.gpr .ebx) d) 4) →
    WP isa (.block P.len) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (P.N + P.B - P.L))
        (H.lenOf (s.mem.readW (addr (s.gpr .ebp) (P.so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (P.so + 16)) 32))
  out : ∀ s : State, (s.gpr .ebx).toNat + P.N ≤ 2 ^ 32 → (s.gpr .eax).toNat + P.N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) P.N → InRegions s.wr ((s.gpr .eax).setWidth 64) P.N →
    Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, P.N⟩ ⟨(s.gpr .eax).setWidth 64, P.N⟩ →
    WP isa (.block P.out) s fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))

/-! ## The compression function -/

/-- What `compressAt` needs of the compression function it calls: that it is
correct, does not touch `esp` but to call, and calls nothing that uses the
stack. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (compressK H).post s s'
  nosp : NoSp code
  stack : stackUse code = 0

/-- The 20 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

section
variable {P : Params} {H : Md P.B P.N P.L}

/-- Compressing the `k` blocks at `eax` (`blk`, their number in `ecx`) into
the hash value at `st` (in register `sr`), with the scratch space at `scr`
(in register `cr`): a call of `compress(st, blk, k, scr)` in a frame of its
arguments, which uses the 20 bytes below `esp` (`E`) and writes only there,
the hash value and the first `so` bytes of the scratch space. -/
theorem compressFrame_ok {name : String} {code : Prog isa} (hf : CalleeOk H code) {sr cr : Reg}
    (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) {s : State} {st scr blk E : BitVec 32} {k : Nat}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hk : (s.gpr .ecx).toNat = k)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : blk.toNat + P.B * k ≤ 2 ^ 32)
    (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, P.N⟩ ⟨scr.setWidth 64, P.so⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, P.B * k⟩ ⟨st.setWidth 64, P.N⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, P.B * k⟩ ⟨scr.setWidth 64, P.so⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, P.N⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, P.so⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, P.B * k⟩)
    (hc : Covers [⟨blk.setWidth 64, P.B * k⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩, below E 20] s.mem s'.mem →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k → Q s') :
    WP isa (.frame (.push [cr, .ecx, .eax, sr]) (.call name code) (.pop .eax 4)) s Q := by
  have fit : 4 * [cr, Reg.ecx, .eax, sr].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [cr, Reg.ecx, .eax, sr] := by simp [Ne.symm hsr, Ne.symm hcr]
  set sE := (pushed [cr, Reg.ecx, .eax, sr] s).callEntry with hsE
  have a0 : arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hS]
  have a1 : arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [heax]
  have a2 : (arg sE 2).toNat = k := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hk]
  have a3 : arg sE 3 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', hesp]; rfl
  have b16 : Region.Sub (below E 16) (below E 20) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below E 20) := by
    have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) hE
    rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  refine WP.callWith (k := compressK H) hf.verified hf.nosp (by simp) hrs
    (by rw [hf.stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, P.B * k⟩, ⟨argAddr sE 0, 16⟩])
    (wr := [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b16, dC.sub_left b16,
      dS.sub_left r4, dC.sub_left r4, f₀, f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hc a n ⟨_, List.mem_singleton_self _, by simpa using hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      simp only [Region.Contains] at hcn ⊢
      simpa using hcn
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [hf.stack, hesp] at f'
    have hsE' : Frame [below E 20] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    rw [← hsE] at post
    simp only [compressK, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    have e₁ : H.stateAt sE.mem (st.setWidth 64) = H.stateAt s.mem (st.setWidth 64) :=
      H.stateAt_congr fun i hi =>
        hsE'.bytes (R := ⟨st.setWidth 64, P.N⟩) (by simpa using dS.symm) (by simp; omega) hi
    have e₂ : H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) sE.mem (blk.setWidth 64) k =
        H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k :=
      H.compressBlocks_congr fun j hj =>
        hsE'.bytes (R := ⟨blk.setWidth 64, P.B * k⟩) (by simpa using dB.symm) (by simp; omega) hj
    rw [post, e₁, e₂]

/-- Compressing the block at `eax` (`blk`) into the hash value at `st` (in
register `sr`), with the scratch space at `scr` (in register `cr`): a call of
`compress(st, blk, 1, scr)` in a frame of its arguments, which uses the 20
bytes below `esp` (`E`) and writes only there, the hash value and the first
`so` bytes of the scratch space. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : CalleeOk H code) {sr cr : Reg}
    (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) (hsr' : sr ≠ .ecx)
    (hcr' : cr ≠ .ecx) {s : State} {st scr blk E : BitVec 32}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : blk.toNat + P.B ≤ 2 ^ 32)
    (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, P.N⟩ ⟨scr.setWidth 64, P.so⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, P.B⟩ ⟨st.setWidth 64, P.N⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, P.B⟩ ⟨scr.setWidth 64, P.so⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, P.N⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, P.so⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, P.B⟩)
    (hc : Covers [⟨blk.setWidth 64, P.B⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩, below E 20] s.mem s'.mem →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (blk.setWidth 64)) → Q s') :
    WP isa (compressAt name code sr cr) s Q := by
  rw [← Nat.mul_one P.B] at f₁ d₂ d₃ dB hc
  unfold compressAt compressWith
  refine WP.seq (WP.cons (s' := s.setReg .ecx 1) rfl (WP.block_nil ?_))
  set s₁ := s.setReg .ecx 1 with hs₁
  have g₁ : ∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
  refine compressFrame_ok (k := 1) hf hsr hcr (by rw [g₁ _ (by decide), hesp])
    (by rw [g₁ _ hsr', hS]) (by rw [g₁ _ hcr', hC]) (by rw [g₁ _ (by decide), heax])
    (by simp [hs₁, State.setReg]) hE f₀ f₁ f₃ d₁ d₂ d₃ dS dC dB (by rw [hs₁]; exact hc)
    (by rw [hs₁]; exact hw) fun s' rd' wr' cs' f' post => ?_
  have m₁ : s₁.mem = s.mem := by rw [hs₁]; rfl
  rw [m₁, Md.compressBlocks_one] at post
  rw [m₁] at f'
  refine hQ s' (by rw [rd']; rfl) (by rw [wr']; rfl) (fun r hr => ?_) f' post
  rw [cs' r hr, g₁ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]

end

end VG.Proof.MdStream.X86
