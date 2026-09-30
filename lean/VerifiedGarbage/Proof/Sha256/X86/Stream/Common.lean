import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.X86.Stream
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming SHA-256 on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. Per-instruction WP rules that
expose only what changes, the call of the compression function (`compressAt`),
and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (compress_verified contains_offset)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## Regions -/

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

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

/-! ## The call of the compression function -/

/-- The 20 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

theorem compress_nosp : NoSp Impl.Sha256.X86.compress := NoSp.of_all (by lit_decide)

theorem compress_stack : stackUse Impl.Sha256.X86.compress = 0 := by lit_decide

/-- A region within one of `rs'`, at offset `o`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-- Compressing the block at `eax` (`blk`) into the hash value at `st` (in
register `sr`), with the scratch space at `scr` (in register `cr`): a call of
`vg_sha256_compress(st, blk, 1, scr)` in a frame of its arguments, which
uses the 20 bytes below `esp` (`E`) and writes only there, the hash value
and the first 112 bytes of the scratch space. -/
theorem compressAt_ok {sr cr : Reg} (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) (hsr' : sr ≠ .ecx)
    (hcr' : cr ≠ .ecx) {s : State} {st scr blk E : BitVec 32}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : blk.toNat + 64 ≤ 2 ^ 32)
    (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, 32⟩ ⟨scr.setWidth 64, 112⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨st.setWidth 64, 32⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨scr.setWidth 64, 112⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, 32⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, 112⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, 64⟩)
    (hc : Covers [⟨blk.setWidth 64, 64⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, below E 20] s.mem s'.mem →
      stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (blk.setWidth 64)) → Q s') :
    WP isa (compressAt sr cr) s Q := by
  unfold compressAt
  refine WP.seq (WP.cons (s' := s.setReg .ecx 1) rfl (WP.block_nil ?_))
  set s₁ := s.setReg .ecx 1 with hs₁
  have g₁ : ∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
  have fit : 4 * [cr, Reg.ecx, .eax, sr].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [g₁ _ (by decide), hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [cr, Reg.ecx, .eax, sr] := by simp [Ne.symm hsr, Ne.symm hcr]
  set sE := (pushed [cr, Reg.ecx, .eax, sr] s₁).callEntry with hsE
  have a0 : arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ _ hsr', hS]
  have a1 : arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ Reg.eax (by decide), heax]
  have a2 : arg sE 2 = 1 := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hs₁, State.setReg]
  have a3 : arg sE 3 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ _ hcr', hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, g₁ _ (by decide), hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', g₁ _ (by decide), hesp]; rfl
  have b16 : Region.Sub (below E 16) (below E 20) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below E 20) := by
    have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) hE
    rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have hesp₁ : s₁.gpr .esp = E := by rw [g₁ _ (by decide), hesp]
  refine WP.callWith (k := Proof.Sha256.compressX86) compress_verified.1 compress_nosp (by simp) hrs
    (by rw [compress_stack, hesp₁]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, 64 * (1 : BitVec 32).toNat⟩, ⟨argAddr sE 0, 16⟩])
    (wr := [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [Proof.Sha256.compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b16, dC.sub_left b16,
      dS.sub_left r4, dC.sub_left r4, f₀, by simpa using f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp₁]
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
  · rw [hesp₁]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [compress_stack, hesp₁] at f'
    have hsE' : Frame [below E 20] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp₁] at this; exact this
    rw [← hsE] at post
    simp only [Proof.Sha256.compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂,
      show (1 : BitVec 32).toNat = 1 from rfl, compressBlocks_one] at post
    rw [hs₁] at f'
    refine hQ s' rd' wr' (fun r hr => ?_) (by simpa [State.setReg] using f') ?_
    · rw [cs' r hr, g₁ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    · have e₁ : stateAt sE.mem (st.setWidth 64) = stateAt s.mem (st.setWidth 64) :=
        Proof.Sha256.Stream.stateAt_congr fun i hi =>
          hsE'.bytes (R := ⟨st.setWidth 64, 32⟩) (by simpa using dS.symm) (by simp) hi
      have e₂ : blockAt sE.mem (blk.setWidth 64) = blockAt s.mem (blk.setWidth 64) := by
        simp only [blockAt]
        exact Proof.Sha256.Stream.parseBlock_congr fun k hk =>
          hsE'.bytes (R := ⟨blk.setWidth 64, 64⟩) (by simpa using dB.symm) (by simp) hk
      rw [post, e₁, e₂]

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

theorem and63 (x : BitVec 32) : x &&& 63 = BitVec.ofNat 32 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : BitVec 32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## Byte order -/

theorem bswap_bytes (w : BitVec 32) :
    (List.range 4).map (fun j => (bswap w).extractLsb' (8 * j) 8) = Spec.Sha256.wordBytes w := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Sha256.wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp (disch := decide) only [bswap, Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

end VG.Proof.Sha256.X86.Stream
