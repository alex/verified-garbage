import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Impl.Sha256.X86.Stream

/-!
# Streaming SHA-256 on x86 (32-bit): common lemmas

Untrusted: everything here is checked by Lean. Per-instruction WP rules that
expose only what changes, the inlined compression function (`compressAt`),
and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (compress_verified contains_offset)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## Regions -/

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.mod_le _ _
  omega

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
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
  intro a ha hb
  rw [addr_eq (by omega)] at ha hb
  have := x.isLt
  generalize x.setWidth 64 = b at *
  bv_omega

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

/-! ## The inlined compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

/-- Compressing the block at `eax` into the hash value at `[esp + 4]`, with
scratch space at `[esp + 16]`. -/
theorem compressAt_ok {s : State} {st scr blk : BitVec 32}
    (h4 : s.mem.readW (addr (s.gpr .esp) 4) 32 = st) (h16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = scr)
    (heax : s.gpr .eax = blk) (fsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32)
    (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : blk.toNat + 64 ≤ 2 ^ 32) (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, 32⟩ ⟨scr.setWidth 64, 112⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨st.setWidth 64, 32⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨scr.setWidth 64, 112⟩)
    (d₄ : Region.Disjoint ⟨addr (s.gpr .esp) 4, 16⟩ ⟨st.setWidth 64, 32⟩)
    (d₅ : Region.Disjoint ⟨addr (s.gpr .esp) 4, 16⟩ ⟨scr.setWidth 64, 112⟩)
    (d₆ : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨st.setWidth 64, 32⟩)
    (d₇ : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨scr.setWidth 64, 112⟩)
    (d₈ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨addr (s.gpr .esp) 4, 16⟩)
    (hc : Covers [⟨blk.setWidth 64, 64⟩, ⟨addr (s.gpr .esp) 4, 16⟩, ⟨st.setWidth 64, 32⟩,
      ⟨scr.setWidth 64, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, ⟨addr (s.gpr .esp) 4, 16⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, ⟨addr (s.gpr .esp) 4, 16⟩] s.mem s'.mem →
      s'.mem.readW (addr (s.gpr .esp) 4) 32 = st → s'.mem.readW (addr (s.gpr .esp) 16) 32 = scr →
      stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (blk.setWidth 64)) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  set esp := s.gpr .esp with hesp
  have hA : ∀ d, d + 4 ≤ 16 → (⟨addr esp 4, 16⟩ : Region).Contains (addr esp (4 + d)) 4 := by
    intro d hd
    simp only [Region.Contains]
    rw [addr_eq (by omega), addr_eq (by omega),
      show esp.setWidth 64 + BitVec.ofNat 64 (4 + d) - (esp.setWidth 64 + BitVec.ofNat 64 4) =
        BitVec.ofNat 64 d by rw [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hout : ∀ d, d + 4 ≤ 16 → InRegions s.wr (addr esp (4 + d)) 4 :=
    fun d hd => hw _ _ ⟨_, by simp, hA d hd⟩
  refine WP.seq (wp_store (a := addr esp 8) (ea_at _ _ _) (hout 4 (by omega)) fun s₁ u₁ => ?_)
  refine wp_movi fun s₂ u₂ => wp_store (a := addr esp 12) (by rw [ea_at, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₂.wr, u₁.wr]; exact hout 8 (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h => by rw [u₃.gpr, u₂.other r h, u₁.gpr]
  have hm₃ : s₃.mem = (s.mem.writeW (addr esp 8) blk).writeW (addr esp 12) (1 : BitVec 32) := by
    rw [u₃.mem, u₂.gpr, u₂.mem, u₁.mem, heax]
  have hesp₃ : s₃.gpr .esp = esp := g₃ _ (by decide)
  -- The arguments of the inlined code.
  have rd : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ 20 → e + 4 ≤ 20 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr esp e) v).readW (addr esp d) 32 = m.readW (addr esp d) 32 :=
    fun m d e v h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  have a0 : arg s₃ 0 = st := by
    rw [arg_eq, hesp₃, hm₃, rd _ 4 12 _ (by omega) (by omega) (by omega),
      rd _ 4 8 _ (by omega) (by omega) (by omega), h4]
  have a1 : arg s₃ 1 = blk := by
    rw [arg_eq, hesp₃, hm₃, rd _ 8 12 _ (by omega) (by omega) (by omega)]
    exact Mem.readW_writeW_self32 _ _ _
  have a2 : arg s₃ 2 = 1 := by
    rw [arg_eq, hesp₃, hm₃]
    exact Mem.readW_writeW_self32 _ _ _
  have a3 : arg s₃ 3 = scr := by
    rw [arg_eq, hesp₃, hm₃, rd _ 16 12 _ (by omega) (by omega) (by omega),
      rd _ 16 8 _ (by omega) (by omega) (by omega), h16]
  have e₀ : argAddr s₃ 0 = addr esp 4 := by rw [argAddr, hesp₃]; rfl
  -- The memory the stores changed.
  have fr₃ : Frame [⟨addr esp 4, 16⟩] s.mem s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hA 4 (by omega))).writeW
      (List.mem_singleton_self _) _ (hA 8 (by omega))
  have hst₃ : stateAt s₃.mem (st.setWidth 64) = stateAt s.mem (st.setWidth 64) :=
    Proof.Sha256.Stream.stateAt_congr fun i hi =>
      frame_bytes fr₃ (R := ⟨st.setWidth 64, 32⟩) (by simpa using d₄.symm) (by simp) hi
  have hblk₃ : blockAt s₃.mem (blk.setWidth 64) = blockAt s.mem (blk.setWidth 64) := by
    simp only [blockAt]
    apply Proof.Sha256.Stream.parseBlock_congr
    intro k hk
    exact frame_bytes fr₃ (R := ⟨blk.setWidth 64, 64⟩) (by simpa using d₈) (by simp) hk
  refine WP.inline (k := Proof.Sha256.compressX86) compress_verified.1
    (rd := [⟨blk.setWidth 64, 64 * (1 : BitVec 32).toNat⟩, ⟨addr esp 4, 16⟩])
    (wr := [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩]) ?_ ?_ ?_ ?_
  · have ha : ∀ rd wr, arg (s₃.withRegions rd wr) = arg s₃ := fun _ _ => rfl
    have hb : ∀ rd wr, argAddr (s₃.withRegions rd wr) 0 = addr esp 4 := fun _ _ => e₀
    simp only [Proof.Sha256.compressX86, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      hesp₃, ha, hb, a0, a1, a2, a3]
    exact ⟨trivial, trivial, d₁, d₂, d₃, d₄, d₅, d₆, d₇, f₀, by simpa using f₁, f₃, by omega⟩
  · rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
    intro a n hin
    obtain ⟨r, hr, hc'⟩ := hin
    refine hc a n ⟨r, ?_, hc'⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (rfl | rfl) | rfl | rfl
    · left; simp
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; rfl
  · rw [u₃.wr, u₂.wr, u₁.wr]
    intro a n ⟨r, hr, hc'⟩
    refine hw a n ⟨r, ?_, hc'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro s' hrd hwr habi hf hg hpost
    simp only [Proof.Sha256.compressX86, State.withRegions_mem] at hpost
    have : ∀ t : State, arg (t.withRegions [⟨blk.setWidth 64, 64 * (1 : BitVec 32).toNat⟩, ⟨addr esp 4, 16⟩]
        [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩]) = arg t := fun _ => rfl
    rw [this, a0, a1, a2, show (1 : BitVec 32).toNat = 1 from rfl, compressBlocks_one, hst₃, hblk₃] at hpost
    have hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := fun r hr => by
      rw [habi.1 r hr, g₃ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    have hesp' : s'.gpr .esp = esp := hcs _ (by simp [calleeSaved])
    have hf' : Frame [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, ⟨addr esp 4, 16⟩] s.mem s'.mem :=
      (fr₃.mono (by simp)).trans (hf.mono (by simp))
    have keep : ∀ d, d + 4 ≤ 16 → d + 4 ≤ 4 ∨ 12 ≤ d → s'.mem.readW (addr esp (4 + d)) 32 = s.mem.readW (addr esp (4 + d)) 32 := by
      intro d hd hd'
      rw [hf.readW (r := ⟨addr esp (4 + d), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · rw [hm₃, rd _ _ 12 _ (by omega) (by omega) (by omega), rd _ _ 8 _ (by omega) (by omega) (by omega)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact d₄.sub_left (fun a ha => by
            simp only [Region.Contains] at ha ⊢
            rw [addr_eq (by omega), addr_eq (by omega)] at *
            generalize esp.setWidth 64 = b at *
            bv_omega)
        · exact d₅.sub_left (fun a ha => by
            simp only [Region.Contains] at ha ⊢
            rw [addr_eq (by omega), addr_eq (by omega)] at *
            generalize esp.setWidth 64 = b at *
            bv_omega)
    refine hQ s' (hrd.trans (by rw [u₃.rd, u₂.rd, u₁.rd])) (hwr.trans (by rw [u₃.wr, u₂.wr, u₁.wr])) hcs hf'
      ?_ ?_ hpost
    · rw [← h4]; exact keep 0 (by omega) (by omega)
    · rw [← h16]; exact keep 12 (by omega) (by omega)

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
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [bswap, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

end VG.Proof.Sha256.X86.Stream
