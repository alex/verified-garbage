import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Impl.Sha256.X86_64.Stream

/-!
# Streaming SHA-256 on x86-64: common lemmas

Untrusted: everything here is checked by Lean. The inlined compression
function (`compressAt`), and memory written byte by byte.
-/

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset contains_offset' toNat_ofNat_lt compress_verified)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## The inlined compression function -/

theorem compress_keeps : ((instrs Impl.Sha256.X86_64.compress).all fun i =>
    Taint.dstOf i != some .rdi && Taint.dstOf i != some .rcx) = true := by decide +kernel

theorem compress_keeps_rdi : ∀ i ∈ instrs Impl.Sha256.X86_64.compress, Taint.dstOf i ≠ some .rdi := by
  intro i hi
  have := List.all_eq_true.mp compress_keeps i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.1

theorem compress_keeps_rcx : ∀ i ∈ instrs Impl.Sha256.X86_64.compress, Taint.dstOf i ≠ some .rcx := by
  intro i hi
  have := List.all_eq_true.mp compress_keeps i hi
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this.2

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

/-- Compressing the block at `rsi` into the hash value at `rbx`, with scratch
space at `r15`. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (hrbx : s.gpr .rbx = st) (hr15 : s.gpr .r15 = scr) (hrsi : s.gpr .rsi = src)
    (d₁ : Region.Disjoint ⟨st, 32⟩ ⟨scr, 112⟩) (d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, 32⟩)
    (d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 112⟩) (d₄ : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨st, 32⟩)
    (d₅ : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨scr, 112⟩)
    (hc : Covers [⟨src, 64⟩, ⟨st, 32⟩, ⟨scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 32⟩, ⟨scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  have h₁ : WP isa (.block [.mov .rdi (.reg .rbx), .mov32 .rdx (.imm 1), .mov .rcx (.reg .r15)]) s
      fun s₁ => s₁.gpr .rdi = st ∧ s₁.gpr .rdx = 1 ∧ s₁.gpr .rcx = scr ∧ s₁.gpr .rsi = src ∧
        (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
    apply WP.of_runBlock
    simp only [runBlock, exec, readSrc, readSrc32, isa, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp [State.setReg, State.setReg32, hrbx], by simp [State.setReg, State.setReg32],
      by simp [State.setReg, State.setReg32, hr15], by simp [State.setReg, State.setReg32, hrsi],
      fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg, State.setReg32]
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ => ?_)
  have hsp : s₁.gpr .rsp = s.gpr .rsp := e₅ _ (by simp [calleeSaved])
  refine WP.seq (WP.inline (k := Proof.Sha256.compressX86_64) compress_verified.1
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨scr, 112⟩]) ?_ ?_ ?_ ?_)
  · simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, e₁, e₂, e₃, e₄, hsp]
    exact ⟨by simp, by simp, d₁, d₂, d₃, d₄, d₅⟩
  · rw [e₆, e₇]; simpa using hc
  · rw [e₇]; exact hw
  · intro s₂ hrd hwr habi hf hkeep hpost
    have k₁ := hkeep .rdi compress_keeps_rdi
    have k₃ := hkeep .rcx compress_keeps_rcx
    simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_mem, e₁, e₂, e₄,
      e₈] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, compressBlocks_one] at hpost
    apply WP.of_runBlock
    simp only [runBlock, exec, readSrc, isa, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine hQ _ (hrd.trans e₆) (hwr.trans e₇) (fun r hr => ?_) (e₈ ▸ hf) hpost
      (by simp [State.setReg, k₁, e₁]) (by simp [State.setReg, k₃, e₃])
    have h₂ := habi.1 r hr
    simp only [State.setReg]
    by_cases h15 : r = .r15
    · subst h15; simp [k₃, e₃, hr15]
    · by_cases hbx : r = .rbx
      · subst hbx; simp [k₁, e₁, hrbx]
      · simp [h15, hbx, h₂, e₅ r hr]

/-! ## One instruction at a time

Weakest-precondition rules for the instruction forms used here, exposing
only what changes, so that proofs about a block stay small. -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.zf = s.zf → s'.cf = s.cf →
    WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.zf = s.zf →
    s'.cf = s.cf → WP isa (.block is) s' Q) : WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_add {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_bswap32 {d : Reg}
    (k : ∀ s', Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

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

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_bswap {d : Reg}
    (k : ∀ s', Upd s s' d (bswap64 (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-! ## Byte order -/

theorem bswap32_bytes' (w : BitVec 32) :
    (List.range 4).map (fun j => (bswap32 w).extractLsb' (8 * j) 8) = Spec.Sha256.wordBytes w := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Sha256.wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

theorem bswap64_bytes (x : BitVec 64) :
    (List.range 8).map (fun j => (bswap64 x).extractLsb' (8 * j) 8) =
      (List.range 8).reverse.map (fun i => x.extractLsb' (8 * i) 8) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap64, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

end VG.Proof.Sha256.X86_64.Stream
