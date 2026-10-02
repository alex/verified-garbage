import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `init`

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacInit.lean`): HMAC's `init`
(`Impl/Pbkdf2/Md/AArch64.lean`) saves our caller's registers and our return
address (`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`), compresses each buffer into
its state's hash value (`cmp_ok`), and loads our caller's registers back.
A state whose initial hash value has absorbed the block in its buffer
represents that block (`Md.repr_of_block`). No instruction of `init` or of
the functions it calls writes a SIMD register (`HashOK.hmacInit_keepsV`), so
it keeps their low halves. Constant time: the taint analysis checks the
pieces between the calls (`Checks`); the calls are constant time by the
callees' own proofs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacInit

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat Upd Mupd wp_mov wp_movz wp_addImm wp_add wp_sub wp_ldrb wp_strb
  wp_ldr32 wp_str32 eval_zero ofNat_succ toNat_ofNat_lt)
open VG.Impl.MdStream.AArch64 (compressAt mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (CallOk compressAt_ok compressAt_rel)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok savedRegs count_loop wp_eor movz_ofNat sub_ofNat' ofNat_ne_zero repr_keep PubEq args untouched)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_sep)
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set fill_mem
  xorOpad_mem xorOpad_ipad)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## Constants -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem movzk_val (lo hi : BitVec 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 lo))) &&&
        BitVec.setWidth 64 (~~~((65535 : BitVec 32) <<< 16)) |||
      BitVec.setWidth 64 (BitVec.setWidth 32 hi <<< 16) = BitVec.setWidth 64 (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h1 : i < 16
  · simp [h1, show i < 32 by omega, hi']
  · by_cases h2 : i < 32
    · simp [h1, h2, hi']
      rw [BitVec.getLsbD_of_ge lo i (by omega)]
      simp [show i - 16 < 32 by omega]
    · simp [h1, h2, hi']
      exact BitVec.getLsbD_of_ge hi (i - 16) (by omega)

/-- `movz wd, #lo; movk wd, #hi, lsl #16`: the word `hi ++ lo`. -/
theorem wp_movzk {d : Reg} {lo hi : BitVec 16}
    (k : ∀ s', Upd s s' d ((hi ++ lo).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .w d lo 0 :: .movk .w d hi 1 :: is)) s Q := by
  refine Proof.MdStream.AArch64.WP.cons (s' := s.write .w d (lo.setWidth 32)) (by simp [exec]) ?_
  refine Proof.MdStream.AArch64.WP.cons (s' := (s.write .w d (lo.setWidth 32)).write .w d (hi ++ lo)) ?_
    (k _ ?_)
  · simp only [exec, State.read, State.write, Size.bits]
    simp only [show 16 * 1 < 32 by decide, ↓reduceIte, Option.some.injEq]
    congr 1
    funext r'
    by_cases h : r' = d
    · simp only [h, ↓reduceIte]; exact movzk_val lo hi
    · simp [h]
  · exact ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

end

/-- `ipad` in every byte of a word. -/
abbrev c36 : BitVec 64 := ((0x3636 : BitVec 16) ++ (0x3636 : BitVec 16)).setWidth 64

/-- `ipad ⊕ opad` in every byte of a word. -/
abbrev c6a : BitVec 64 := ((0x6a6a : BitVec 16) ++ (0x6a6a : BitVec 16)).setWidth 64

theorem c36_32 : c36.setWidth 32 = (0x36363636 : BitVec 32) := by decide

theorem c36_8 : c36.setWidth 8 = ipad := by decide

theorem c6a_32 : c6a.setWidth 32 = (0x6a6a6a6a : BitVec 32) := by decide

theorem xor_byte (b : Byte) (c : BitVec 64) : (b.setWidth 64 ^^^ c).setWidth 8 = b ^^^ c.setWidth 8 := by
  ext i hi; simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

theorem xor_word (x : BitVec 32) (c : BitVec 64) : (x.setWidth 64 ^^^ c).setWidth 32 = x ^^^ c.setWidth 32 := by
  ext i hi; simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev kp : Addr := s₀.gpr .x2
abbrev kl : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev stkR : Region := below s₀.sp 16
/-- The compression function's working space. -/
abbrev calR : Region := ⟨scr s₀, H.P.so⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := saveR H.stream (scr s₀)
/-- The buffer of the state at `p`. -/
abbrev bufOf (p : Addr) : Addr := p + BitVec.ofNat 64 H.P.N
/-- The key, padded to a block. -/
abbrev k0 : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.P.B

end

abbrev scR (sc : Nat) (s₀ : State) : Region := ⟨scr s₀, 8 * sc⟩

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.P.B
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_s : (outR H s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (inR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 56 ∧ H.stream.W ≤ 64 ∧
    8 * H.stream.W + 56 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.sizes.N4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.sizes.dims.so
  have := hp.nw; have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 56 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have hmd : H.P.md.so = H.P.so := rfl
  have : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega
  omega

/-! ## The parts of the regions -/

theorem save_sub : Region.Sub (svR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sizes hH hp
  exact Offset.sub_base _ h

theorem cal_sub : Region.Sub (calR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', -⟩ := sizes hH hp
  exact Region.sub_prefix (by omega)

theorem cal_save : (calR H s₀).Disjoint (svR H s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', h''⟩ := sizes hH hp
  have := hp.nw
  exact Offset.base_disjoint _ (by omega) (by omega)

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (scR sc s₀)
  stk : (stkR s₀).Disjoint ⟨p, H.S⟩
  key : (keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : StOk (H := H) (sc := sc) (s₀ := s₀) (inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.k_i⟩

omit hH in
theorem stOk_out : StOk (H := H) (sc := sc) (s₀ := s₀) (out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.k_o⟩

/-- A region the code may write while our caller's registers and the key
stay put. -/
structure Away (r : Region) : Prop where
  sv : (svR H s₀).Disjoint r
  key : (keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (save_sub hH hp)).sub_right h, hs.key.sub_right h⟩

theorem away_cal : Away (H := H) (s₀ := s₀) (calR H s₀) :=
  ⟨(cal_save hH hp).symm, hp.k_s.sub_right (cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (stkR s₀)) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (save_sub hH hp)).sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `x19 = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = b
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = out s₀
  x22 : s.gpr .x22 = kp s₀
  x23 : s.gpr .x23 = scr s₀
  x24 : s.gpr .x24 = s₀.gpr .x3
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  key : ∀ i < kl s₀, s.mem (kp s₀ + BitVec.ofNat 64 i) = s₀.mem (kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-- Those the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (ha : ∀ r ∈ rs, Away (H := H) (s₀ := s₀) r) : KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19, (hg _ (by simp)).trans h.x20,
    (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x22, (hg _ (by simp)).trans h.x23,
    (hg _ (by simp)).trans h.x24, fun r hr => (hg r (by revert r; decide)).trans (h.cs r hr),
    h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    fun i hi => (hf.bytes (R := keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .x3).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hsp hg (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem KR.upd {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR H s₀ b s' :=
  h.regs u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (KR H s₀ (inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := scr s₀) rfl (by omega) (by rw [hp.wr]; simp) hL
    fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ =>
    wp_mov fun s₇ u₇ => WP.block_nil ?_
  have hm : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other r hr.2.2.2.2.2, u₆.other r hr.2.2.2.2.1, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have hk : ∀ r ∈ [svR H s₀], (keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.k_s.sub_right (save_sub hH hp)
  exact ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.other, g₁],
    by simp (disch := decide) only [u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, u₂.other, g₁],
    fun r hr => g r (by revert r; decide),
    hm ▸ sv₁,
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := keyR s₀) hk (Nat.le_of_lt (s₀.gpr .x3).isLt) hi⟩

/-! ## The calls of the streaming `init` -/

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', KR H s₀ b s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : KR H s₀ b s₁ := hk.upd (by decide) u₁
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.sp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2)
      (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact away_st hH hp hst (fun _ h => h)
  · exact away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- Stores of `ipad` words (the low half of `x14`) at `x19 + o + 4 k`, for
`k < n`, which write `4 n` bytes of `ipad` from `p = x19 + o`. -/
theorem fill_ok {o : Nat} {p : Addr} (ho : o % 4 = 0) : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    o + 4 * n ≤ 4096 * 4 → s.gpr .x19 + BitVec.ofNat 64 o = p → s.gpr .x14 = c36 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) → 4 * n + 4 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem p (List.replicate (4 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .w .x14 .x19 (o + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hb hp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q (by omega) hp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str32 (a := p + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁, ← hp, add_ofNat]) (by rw [wr₁]; exact hout n (by omega)) fun s₂ m₂ =>
        k s₂ (by rw [m₂.gpr, g₁]) (by rw [m₂.rd, rd₁]) (by rw [m₂.wr, wr₁]) (by rw [m₂.sp, sp₁]) ?_
    rw [m₂.mem, g₁, hax, c36_32, m₁, fill_mem _ _ _ (by omega), Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loop starts in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ [Reg.x9, .x10, .x11, .x12, .x13], t.gpr r = s.gpr r
  x10 : t.gpr .x10 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes m P (ipadBlk mk K B j)

/-- Where the key loop reads and writes. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B ≤ 128
  hN : H.P.N ≤ 64
  x22 : s.gpr .x22 = K
  x19 : s.gpr .x19 + BitVec.ofNat 64 H.P.N = P
  x24 : s.gpr .x24 = BitVec.ofNat 64 kl
  x14 : s.gpr .x14 = c36
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1
  bout : ∀ i < H.P.B, InRegions s.wr (P + BitVec.ofNat 64 i) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.add .x .x13 .x22 .x10, .ldrb .x9 .x13 0, .logic .eor .x .x9 .x9 .x14,
      .add .x .x12 .x19 .x10, .strb .x9 .x12 H.P.N, .addImm .x .x10 .x10 1, .sub .x .x11 .x24 .x10]) t
      fun t' => KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.gpr .x11 = BitVec.ofNat 64 (kl - (j + 1)) := by
  have hkl := hr.kl_le
  have hB := hr.hB
  have hN := hr.hN
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hr.key j hj]
    refine (writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega) hj
    simp only [List.mem_singleton]; rintro r rfl; exact hr.disj
  have o : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13] → t.gpr r = s.gpr r := h.other
  refine wp_add fun t₁ u₁ => ?_
  refine wp_ldrb (a := K + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.gpr, o _ (by decide), hr.x22, h.x10, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hr.kin j hj) fun t₂ u₂ => ?_
  refine wp_eor fun t₃ u₃ => wp_add fun t₄ u₄ => ?_
  refine wp_strb (a := P + BitVec.ofNat 64 j) (by omega)
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), o _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.x10, ← hr.x19]; ac_rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hr.bout j (by omega)) fun t₅ m₅ => ?_
  refine wp_addImm (by decide) fun t₆ u₆ => wp_sub fun t₇ u₇ => WP.block_nil ?_
  have h10 : t₆.gpr .x10 = BitVec.ofNat 64 (j + 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.x10]
    exact (ofNat_succ j).symm
  refine ⟨⟨by rw [u₇.rd, u₆.rd, m₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, m₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [u₇.sp, u₆.sp, m₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      rw [u₇.other r hr'.2.2.1, u₆.other r hr'.2.1, m₅.gpr, u₄.other r hr'.2.2.2.1, u₃.other r hr'.1,
        u₂.other r hr'.1, u₁.other r hr'.2.2.2.2, h.other r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1,
          hr'.2.2.2.2])],
    by rw [u₇.other _ (by decide), h10], ?_⟩, ?_⟩
  · have v : (t₄.gpr .x9).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        o _ (by decide), hr.x14, xor_byte, c36_8, u₁.mem, hbyte]
    rw [u₇.mem, u₆.mem, m₅.mem, v, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem,
      writeBytes_set _ _ _ (by rw [hl]; omega) (by rw [hl]; omega), ipadBlk_succ]
  · rw [u₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), o _ (by decide), hr.x24, h10,
      sub_ofNat' (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 0) (hm : s.mem = writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite (.zero .x .x24) (.block []) H.keyLoop) s (KeyInv s m mk P K H.P.B kl) := by
  have i0 : KeyInv s m mk P K H.P.B 0 s := ⟨rfl, rfl, rfl, fun _ _ => rfl, h10, hm⟩
  have hkl := hr.kl_le
  have hB := hr.hB
  have hz : isa.eval (.zero .x .x24) s = some (decide (kl = 0)) := by
    show VG.AArch64.eval (.zero .x .x24) s = _
    rw [eval_zero, hr.x24]
    congr 1
    by_cases hk : kl = 0
    · simp [hk]
    · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact hk this
  refine WP.ite (decide (kl = 0)) hz (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (by omega) (KeyInv s m mk P K H.P.B) (fun j hj t h => key_step hr hj h) i0

/-- The words of the outer buffer: `n` words of the inner buffer at
`x19 + N`, XORed with `ipad ⊕ opad` (`x15`), to `x21 + N`. -/
theorem opad_ok (hN : H.P.N % 4 = 0) : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    H.P.N + 4 * n ≤ 4096 * 4 → s.gpr .x15 = c6a →
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr .x19 + BitVec.ofNat 64 H.P.N) (4 * n) (s.gpr .x21 + BitVec.ofNat 64 H.P.N) (4 * n) →
    (∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (s.gpr .x21 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .x19 + BitVec.ofNat 64 H.P.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hb h15 hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (by omega) h15 (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_ldr32 (a := s.gpr .x19 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ (by decide), add_ofNat]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_eor fun s₃ u₃ => ?_
    refine wp_str32 (a := s.gpr .x21 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n)) ⟨by omega, by omega⟩
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), add_ofNat])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ m₄ => k s₄ (fun r hr => by rw [m₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [m₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [m₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [m₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    rw [m₄.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h15, xor_word, c6a_32, u₃.mem,
      u₂.mem, m₁, Nat.mul_succ, xorOpad_mem _ _ _ _ (by rwa [← Nat.mul_succ]) (by omega)]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `x1`. -/
theorem keys_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa H.initKeys s fun t => KR H s₀ (inn s₀) t ∧ t.gpr .x1 = bufOf H (inn s₀) ∧
      Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad ∧
      bytesAt t.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have eB : 4 * (H.P.B / 4) = H.P.B := by omega
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have hS : H.S = H.P.N + H.P.B := rfl
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ ⟨inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ ⟨out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dIO : Region.Disjoint ⟨bufOf H (inn s₀), H.P.B⟩ ⟨bufOf H (out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_movzk fun s₁ u₁ => ?_)
  refine fill_ok (o := H.P.N) (p := bufOf H (inn s₀)) (by omega) (H.P.B / 4) _ s₁ _ (by omega)
    (by rw [u₁.other _ (by decide), hk.x19]) u₁.gpr (fun k hk' => by rw [u₁.wr, hk.wr]; exact inI _ 4 (by omega))
    (by omega) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_movz fun s₃ u₃ => WP.block_nil ?_
  have G₃ : ∀ r, r ≠ .x14 → r ≠ .x10 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, g₂, u₁.other r h1]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hk.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hk.wr]
  have hr : KeyRegs H s₃ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) (kl s₀) :=
    { kl_le := hkl, hB := hB, hN := hN
      x22 := by rw [G₃ _ (by decide) (by decide), hk.x22]
      x19 := by rw [G₃ _ (by decide) (by decide), hk.x19]
      x24 := by rw [G₃ _ (by decide) (by decide), hk.x24, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      x14 := by rw [u₃.other _ (by decide), g₂, u₁.gpr]
      key := hk.key
      kin := fun i hi => by
        rw [rd₃, wr₃, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩
      bout := fun i hi => by rw [wr₃]; exact inI i 1 (by omega)
      disj := hp.k_i.sub_right bI }
  have h10 : s₃.gpr .x10 = BitVec.ofNat 64 0 := by rw [u₃.gpr]; rfl
  have hm : s₃.mem = writeBytes s.mem (bufOf H (inn s₀)) (ipadBlk s₀.mem (kp s₀) H.P.B 0) := by
    rw [u₃.mem, m₂, u₁.mem, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (key_ok hr h10 hm) fun t ht => ?_)
  have Gt : ∀ r, r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14] → t.gpr r = s.gpr r := fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ht.other r (by simp [hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1]),
      G₃ r hr'.2.2.2.2.2 hr'.2.1]
  have bxt : t.gpr .x19 = inn s₀ := by rw [Gt _ (by decide), hk.x19]
  have x21t : t.gpr .x21 = out s₀ := by rw [Gt _ (by decide), hk.x21]
  have rdt : t.rd = s₀.rd := by rw [ht.rd, rd₃]
  have wrt : t.wr = s₀.wr := by rw [ht.wr, wr₃]
  unfold Hash.opadFill
  simp only [List.cons_append, List.nil_append]
  refine wp_movzk fun t₁ v₁ => ?_
  have bxt₁ : t₁.gpr .x19 = inn s₀ := by rw [v₁.other _ (by decide), bxt]
  have x21t₁ : t₁.gpr .x21 = out s₀ := by rw [v₁.other _ (by decide), x21t]
  refine opad_ok hN4 (H.P.B / 4) _ t₁ _ (by omega) v₁.gpr
    (fun k hk' => by rw [bxt₁, v₁.rd, v₁.wr, rdt, wrt]; exact InRegions.right' (inI _ 4 (by omega)))
    (fun k hk' => by rw [x21t₁, v₁.wr, wrt]; exact inO _ 4 (by omega))
    (by rw [bxt₁, x21t₁, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  refine wp_addImm (by omega) fun s₆ u₆ => WP.block_nil ?_
  rw [bxt₁, x21t₁, eB, v₁.mem] at m₅
  have G : ∀ r, r ∉ [Reg.x1, .x9, .x10, .x11, .x12, .x13, .x14, .x15] → s₆.gpr r = s.gpr r := fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [u₆.other r hr'.1, g₅ r hr'.2.1, v₁.other r hr'.2.2.2.2.2.2.2,
      Gt r (by simp [hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2.1])]
  have hm₆ : s₆.mem = s₅.mem := u₆.mem
  have lI : (ipadBlk s₀.mem (kp s₀) H.P.B (kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  have bt : bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega), ipadBlk_eq _ _ hkl]
  have lO : ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  have fT : Frame [⟨bufOf H (inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  have f₅ : Frame [⟨bufOf H (out s₀), H.P.B⟩] t.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  have f : Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem s₆.mem := by
    rw [hm₆]; exact (fT.mono (by simp)).trans (f₅.mono (by simp))
  refine ⟨hk.keep (by rw [u₆.rd, rd₅, v₁.rd, ht.rd, rd₃, ← hk.rd])
      (by rw [u₆.wr, wr₅, v₁.wr, ht.wr, wr₃, ← hk.wr]) (by rw [u₆.sp, sp₅, v₁.sp, ht.sp, u₃.sp, sp₂, u₁.sp])
      (fun r hr' => G r (by revert hr'; revert r; decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact away_st hH hp si bI
        · exact away_st hH hp so bO),
    by rw [u₆.gpr, g₅ _ (by decide), bxt₁], f, ?_, ?_⟩
  · have sIO : Mem.Sep (bufOf H (inn s₀)) H.P.B (bufOf H (out s₀))
        ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm₆, m₅, bytesAt_writeBytes_sep _ _ sIO (by omega), bt]
  · rw [hm₆, m₅, bytesAt_writeBytes_self' lO (by omega), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hx1 : t.gpr .x1 = bufOf H p) : CallOk t H.P.N H.P.B H.P.so p (scr s₀) (bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := sizes hH hp
  have sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hb : Region.Sub ⟨bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hc : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := cal_sub hH hp
  refine ⟨hk.x19, hk.x20, hx1, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hs.sc.sub_left hb).sub_right hc, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hs.mem, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ hs.mem, 0, (BitVec.add_zero _).symm,
        by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hs.mem, 0, (BitVec.add_zero _).symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block in the buffer of the state at `p` into its
hash value. -/
theorem cmp_ok {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hx1 : t.gpr .x1 = bufOf H p) {Q : State → Prop}
    (k : ∀ s', KR H s₀ p s' → Frame [⟨p, H.P.N⟩, calR H s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  refine compressAt_ok hH.comp (callOk hH hp hs hk hx1) fun s' hrd hwr hcs hsp hfr hst =>
    k s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hfr ?_) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega))
  · exact away_cal hH hp

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => KR H s₀ (out s₀) t ∧ t.gpr .x1 = bufOf H (out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ => wp_addImm (by omega) fun s₂ u₂ => WP.block_nil ?_
  have G : ∀ r, r ≠ .x19 → r ≠ .x1 → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₂.other r h2, u₁.other r h1]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₂.rd, u₁.rd, hk.rd], by rw [u₂.wr, u₁.wr, hk.wr], by rw [u₂.sp, u₁.sp, hk.sp],
    by rw [u₂.other _ (by decide), u₁.gpr, hk.x21],
    by rw [G _ (by decide) (by decide), hk.x20], by rw [G _ (by decide) (by decide), hk.x21],
    by rw [G _ (by decide) (by decide), hk.x22], by rw [G _ (by decide) (by decide), hk.x23],
    by rw [G _ (by decide) (by decide), hk.x24],
    fun r hr => by rw [G r (by revert hr; revert r; decide) (by revert hr; revert r; decide), hk.cs r hr],
    by rw [hm]; exact hk.saved, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₂.gpr, u₁.other _ (by decide), hk.x21], hm⟩

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, k0, K0, bytesAt_length, hH.hB, show ¬ (H.P.B < kl s₀) by omega, ↓reduceIte]

theorem correct : WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.withPreservedV ?_ hH.hmacInit_keepsV
  refine WP.seq (WP.mono (pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (callInit_ok hH hp k₁ (st := .x19) k₁.x19 si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (callInit_ok hH hp k₂ (st := .x21) k₂.x21 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (cmp_ok hH hp si k₄ si₄ fun s₅ k₅ f₅ e₅ => ?_)
  refine WP.seq (WP.mono (mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
  refine WP.seq (cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => ?_)
  refine WP.mono (restore_ok H.stream k₇.x23 (by omega) k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hsp, k₇.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hg _ (by decide)
      | exact (ho _ (by decide)).trans (k₇.cs _ (by decide))
  -- What each piece keeps: the hash values and the buffers it does not write.
  have keepS : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) → hH.md.stateAt m' p = hH.md.stateAt m p :=
    fun hf hd => hH.md.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega) hi
  have hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have nb : ∀ p : Addr, Region.Disjoint ⟨p, H.P.N⟩ ⟨bufOf H p, H.P.B⟩ := fun p =>
    Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  have iv : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := ((hH.repr _ _ _).1 h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  -- The inner state.
  have iv₄ : hH.md.stateAt s₄.mem (inn s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact nb _
        · exact (hp.i_o.sub_left hvI).sub_right bO),
      keepS f₃ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.i_o.sub_left hvI
        · exact hp.stk_i.symm.sub_left hvI), iv r₂]
  have hl : (xorPad (k0 H s₀) ipad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rI₅ := Md.repr_of_block hH.md hB0 hl iv₄ bI₄ e₅
  -- The outer state.
  have iv₆ : hH.md.stateAt s₆.mem (out s₀) = hH.iv := by
    rw [m₆, keepS f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
        · exact (so.sc.sub_left hvO).sub_right (cal_sub hH hp)),
      keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  have bO₆ : bytesAt s₆.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
    rw [m₆, bytes_keep f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left bO).sub_right hvI
        · exact (so.sc.sub_left bO).sub_right (cal_sub hH hp)) (by omega), bO₄]
  have hl' : (xorPad (k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rO₇ := Md.repr_of_block hH.md hB0 hl' iv₆ bO₆ e₇
  -- The inner state, kept by the outer compression.
  have rI₇ : hH.SH.Repr s₇.mem (inn s₀) (xorPad (k0 H s₀) ipad) :=
    repr_keep hH.stream f₇ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_right hvO
      · exact hp.i_s.sub_right (cal_sub hH hp)) (m₆ ▸ (hH.repr _ _ _).2 rI₅)
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₇, (hH.repr _ _ _).2 rO₇⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.x19, .x21], ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block [mov .x0 st])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : PubEq s₀ s₀') {b : Addr} {s s' : State} (h : KR H s₀ b s) (h' : KR H s₀' b s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19]
  · rw [h.x20, h'.x20, scr, scr, hq.x4]
  · rw [h.x21, h'.x21, out, out, hq.x1]
  · rw [h.x22, h'.x22, kp, kp, hq.x2]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]
  · rw [h.x24, h'.x24, hq.x3]

omit hH in
theorem callOk_congr {t : State} {N B so : Nat} {a b c a' b' c' : Addr} (h : CallOk t N B so a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : CallOk t N B so a' b' c' := by
  subst ha hb hc; exact h

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.x19, .x21]) {p : Addr}
    (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (H.stream.callInit st)
      fun s s' => KR H s₀ b s ∧ KR H s₀' b s' := by
  have ha : RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (.block [mov .x0 st])
      fun s s' => (KR H s₀ b s ∧ s.gpr .x0 = p) ∧ (KR H s₀' b s' ∧ s'.gpr .x0 = p) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u => WP.block_nil ⟨h.upd (by decide) u, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u => WP.block_nil ⟨h.upd (by decide) u, by rw [u.gpr, hr' h]⟩)
  have call : ∀ {t₀ : State}, Pre H sc t₀ → StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, KR H t₀ b t →
      t.gpr .x0 = p → WP isa (.call H.stream.initN H.stream.initC) t (KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.sp] at f
    refine k.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact away_st hH hpt hst (fun _ h => h)
    · exact away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => KR H s₀ b s ∧ s.gpr .x0 = p)
    (F' := fun s => KR H s₀' b s ∧ s.gpr .x0 = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.sp, k'.sp, hq.sp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (KR H s₀ p s ∧ s.gpr .x1 = bufOf H p) ∧ (KR H s₀' p s' ∧ s'.gpr .x1 = bufOf H p))
      (compressAt H.compN H.compC) fun s s' => KR H s₀ p s ∧ KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.comp fun s s' ⟨⟨k, x1⟩, ⟨k', x1'⟩⟩ =>
      ⟨callOk hH hp hs k x1, callOk_congr (callOk hH hp' hs' k' x1') rfl hq.x4.symm rfl,
        by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun s ⟨k, x1⟩ => cmp_ok hH hp hs k x1 fun s' k' _ _ => k')
    (fun s ⟨k, x1⟩ => cmp_ok hH hp' hs' k x1 fun s' k' _ _ => k')

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : inn s₀' = inn s₀ := hq.x0.symm
  have eo : out s₀' = out s₀ := hq.x1.symm
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
  have so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s' :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact pro_ok hH hp')
  have c₁ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .x19) (by simp) si si'
    (fun k => k.x19) (fun k => k.x19)
  have c₂ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .x21) (by simp) so so'
    (fun k => k.x21) (fun k => by rw [k.x21, eo])
  have keys : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') H.initKeys
      fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .x1 = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .x1 = bufOf H (inn s₀)) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  have mid : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') (.block H.initOuter)
      fun s s' => (KR H s₀ (out s₀) s ∧ s.gpr .x1 = bufOf H (out s₀)) ∧
        (KR H s₀' (out s₀) s' ∧ s'.gpr .x1 = bufOf H (out s₀)) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun _ h => WP.mono (mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR H s₀ (out s₀) s ∧ KR H s₀' (out s₀) s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((cmp_rel hH hp hp' hq si si').seq (mid.seq
    ((cmp_rel hH hp hp' hq so so').seq restore))))))

end

/-- HMAC's `init` is verified against `initG`, given the taint checks. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf ≤ 8 * sc) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified AArch64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.HmacInit
