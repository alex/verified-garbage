import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# Poly1305 on x86-64: one instruction at a time

Weakest-precondition rules for the instruction forms of the byte loops and the
counts of `update` and `finalize`, exposing only what changes, and facts about
the counters.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    Upd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  Upd.withFlags _ _ _ _ _ _ _

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : Upd s₁ s₂ d v)
    (h₂ : Upd s₂ s₃ d w) : Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

end

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: the buffer

Bytes stored into the buffer (bytes 56–71 of the state), absorbing the buffer
as a block, and a message with its last bytes buffered (`Buffered`) as its
whole blocks and the rest.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## Bytes in memory -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := by rw [off_eq]; rfl

/-! ## The buffer -/

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address `[rdi + i + 56]`, for `i = j`. -/
theorem ea_bufAt (s : State) (i : Reg) {j : Nat} (h : s.gpr i = BitVec.ofNat 64 j) :
    s.ea (bufAt i) = bufB (s.gpr .rdi) j := by
  simp only [State.ea, bufAt, h]
  rw [BitVec.mul_one, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 by decide, bufB,
    Offset.add_add, Nat.add_comm]

theorem bfR_contains (st : Addr) {d n : Nat} (h : d + n ≤ 16) :
    (bfR st).Contains (off st 56 + BitVec.ofNat 64 d) n := by
  exact Offset.contains_base _ h (by omega_using [h])

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [bufB] using he)
  rw [toNat_ofNat_lt (by omega_using [hj]), toNat_ofNat_lt (by omega_using [hk])] at this
  omega_using [h, this]

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} (hw : sR (s.gpr .rdi) ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB (s.gpr .rdi) k) 1 :=
  ⟨_, hw, by rw [bufB, ← ofInt_natCast]; exact contains_off (by omega_using [hk]) (by omega_using [hk])⟩

/-- The saved registers are not in the buffer. -/
theorem Saved.of_frame {st : Addr} {s₀ : State} {m m' : Mem} (h : Saved st s₀ m) (hf : Frame [bfR st] m m') :
    Saved st s₀ m' := by
  have e : ∀ d, 72 ≤ d → d + 8 ≤ 128 → m'.readW (off st d) 64 = m.readW (off st d) 64 := by
    intro d h₁ h₂
    refine hf.readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq, bfR, off, ofInt_natCast]
    exact Offset.disjoint st (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂]) (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(e 72 (by decide) (by decide)).trans h1, (e 80 (by decide) (by decide)).trans h2,
    (e 88 (by decide) (by decide)).trans h3, (e 96 (by decide) (by decide)).trans h4,
    (e 104 (by decide) (by decide)).trans h5, (e 112 (by decide) (by decide)).trans h6⟩

theorem bfR_disjoint_svR (st : Addr) : (bfR st).Disjoint (svR st) := by
  simp only [bfR, svR, off, ofInt_natCast]
  exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The first `n` bytes of the buffer are not where the registers are saved. -/
theorem buf_disjoint_svR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (svR st) :=
  (bfR_disjoint_svR st).sub_left (Region.sub_prefix hn)

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) := by
  simp only [bfR, wR, off, ofInt_natCast]
  exact Offset.sub st (by decide) (by decide)

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1)
    (hw : sR (s.gpr .rdi) ∈ s.wr) {q : Nat} (hr0 : (s.gpr .r8).toNat < 2 ^ 60)
    (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58) (hs1 : (s.gpr .r10).toNat = 5 * q) :
    WP isa (.block (absorbAt .rdi 56 pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        hval s' % P = ((hval s + (leNum (bytesAt s.mem (off (s.gpr .rdi) 56) 16) + 2 ^ 128 * pad.toNat)) *
          ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d : Nat, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  refine WP.mono (absorbAt_ok s (b := .rdi) (d := 56) (by decide) hpad hr0 hr1 hq hs1 (hin 56 (by decide))
    (hin (56 + 8) (by decide))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv, hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv, leNum_key, off_off, off_off]

/-! ## Instructions -/

theorem and15 (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.signExtend 64 (15 : BitVec 32)).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

theorem se16' : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide

/-! ## Copying bytes into the buffer -/

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .r13 (at_ .rsi 0), .store8 (bufAt .r12) .r13, .alu .add .rsi (.imm 1),
    .alu .add .r12 (.imm 1), .alu .sub .rax (.imm 1)]

theorem copyIn_eq : copyIn = .loop (.block copyBody) .ne := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
from byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (m₀ : Mem) (src : Addr) (j0 n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  rsi : s.gpr .rsi = src + BitVec.ofNat 64 j
  r12 : s.gpr .r12 = BitVec.ofNat 64 (j0 + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = writeBytes sI.mem (bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (m₀ : Mem) (src : Addr) (n : Nat) : Prop :=
  ∀ i < n, InRegions (sI.rd ++ sI.wr) (src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bfR (sI.gpr .rdi)).Contains (src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (src + BitVec.ofNat 64 i) = m₀ (src + BitVec.ofNat 64 i)

theorem ofNat_add_one (a : Addr) (j : Nat) :
    a + BitVec.ofNat 64 j + BitVec.signExtend 64 (1 : BitVec 32) = a + BitVec.ofNat 64 (j + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ofNat_succ, BitVec.add_assoc]

theorem copy_step {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : SrcOk sI m₀ src n) {j : Nat} (hj : j < n) {s : State}
    (h : CopyInv sI m₀ src j0 n j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI m₀ src j0 n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0)) := by
  obtain ⟨hin, hnb, hm₀⟩ := hs j hj
  have hrdi : s.gpr .rdi = sI.gpr .rdi := h.keep _ (by decide) (by decide) (by decide) (by decide)
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR (sI.gpr .rdi)).Contains (bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j).length := by
    rw [bufB_eq, List.length_take]; exact bfR_contains _ (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_movzx8 (d := .r13) (a := src + BitVec.ofNat 64 j)
    (by rw [ea_at, h.rsi, ofInt_natCast, BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin)
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .r13) (a := bufB (sI.gpr .rdi) (j0 + j))
    (by rw [ea_bufAt s₁ .r12 (by rw [u₁.other _ (by decide), h.r12]), u₁.other _ (by decide), hrdi])
    (by rw [u₁.wr, h.wr]; exact bufB_in hw (by omega_using [hj0, hj, hxs])) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rsi → r ≠ .r13 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrax : s₅.gpr .rax = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      e1, ofNat_pred (by omega_using [hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, hrax, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other .rsi (by decide), u₄.other .rsi (by decide), u₃.gpr, g₂, u₁.other .rsi (by decide), h.rsi,
      ofNat_add_one]
  · rw [u₅.other .r12 (by decide), u₄.gpr, u₃.other .r12 (by decide), g₂, u₁.other .r12 (by decide), h.r12,
      e1, ← Nat.add_assoc, ofNat_succ]
  · rw [g r h3 h2 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : bufB (sI.gpr .rdi) (j0 + j) =
        bufB (sI.gpr .rdi) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (BitVec.setWidth 64 (s.mem (src + BitVec.ofNat 64 j))).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hv, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]
  · rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax, e1,
      ofNat_pred (by omega_using [hj, hxs]), ofNat_beq_zero (by omega_using [hj0, hj, hxs]), show n - j - 1 = n - (j + 1) by omega_using []]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : SrcOk sI m₀ src n) (hrsi : sI.gpr .rsi = src)
    (hr12 : sI.gpr .r12 = BitVec.ofNat 64 j0) (hrax : sI.gpr .rax = BitVec.ofNat 64 n) :
    WP isa copyIn sI (CopyInv sI m₀ src j0 n n) := by
  have h₀ : CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hrsi]; simp, by rw [hr12]; simp, by rw [hrax]; simp, fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hj0 hw hs hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .rdi) 56) (j0 + n) = bytesAt sI.mem (off (sI.gpr .rdi) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .rdi) 56) j0 (bytesAt m₀ src n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs]), bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .rdi)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine writeBytes_frame _ _ _ ?_
  rw [bufB_eq, hxs]; exact bfR_contains _ hj0

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.X86_64
