import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
import VerifiedGarbage.Proof.Pbkdf2.MdKeys

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `init`

HMAC's `init` (`Impl/Pbkdf2/Md/X86_64.lean`) saves our caller's registers
(`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`: `ipad` a word at a time, the
key's bytes XORed in, then the outer buffer from the inner one a word at a
time), compresses each buffer into its state's hash value (`cmp_ok`), and
loads our caller's registers back. A state whose initial hash value has
absorbed the block in its buffer represents that block
(`Md.repr_block`). Constant time: the taint analysis checks the pieces
between the calls (`Checks`); the calls are constant time by the callees'
own proofs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacInit

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat zx_ofNat wp_mov wp_mov32i wp_addi wp_mov32m wp_store32
  wp_store8 wp_movzx8 wp_cmp wp_test Upd CallOk compressAt_ok compressAt_rel ea_at ofInt_natCast setWidth32
  ofNat_succ sub_beq)
open VG.Impl.MdStream.X86_64 (compressAt at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash byteAt)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok count_loop ea_byteAt sx_one wp_xor32i xor_byte PubEq args repr_keep)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' bytesAt_writeBytes_sep)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set fill_mem
  xorOpad_mem xorOpad_ipad)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
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
  ret_i : (retR s₀).Disjoint (inR H s₀)
  ret_o : (retR s₀).Disjoint (outR H s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 48 ∧ H.stream.W ≤ 256 ∧
    8 * H.stream.W + 48 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.hN4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.hso; have := hp.nw
  have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 48 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega
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

omit hH hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega)

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (scR sc s₀)
  stk : (stkR s₀).Disjoint ⟨p, H.S⟩
  ret : (retR s₀).Disjoint ⟨p, H.S⟩
  key : (keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : StOk (H := H) (sc := sc) (s₀ := s₀) (inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.ret_i, hp.k_i⟩

omit hH in
theorem stOk_out : StOk (H := H) (sc := sc) (s₀ := s₀) (out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.ret_o, hp.k_o⟩

/-- A region the code may write while our caller's registers, the return
address and the key stay put. -/
structure Away (r : Region) : Prop where
  sv : (svR H s₀).Disjoint r
  ret : (retR s₀).Disjoint r
  key : (keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (save_sub hH hp)).sub_right h, hs.ret.sub_right h, hs.key.sub_right h⟩

theorem away_cal : Away (H := H) (s₀ := s₀) (calR H s₀) :=
  ⟨(cal_save hH hp).symm, hp.ret_s.sub_right (cal_sub hH hp), hp.k_s.sub_right (cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (stkR s₀)) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (save_sub hH hp)).sub_right h, stk_ret.symm.sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `rbx = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = b
  rbp : s.gpr .rbp = kp s₀
  r12 : s.gpr .r12 = out s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  key : ∀ i < kl s₀, s.mem (kp s₀ + BitVec.ofNat 64 i) = s₀.mem (kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Away (H := H) (s₀ := s₀) r) : KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13,
    (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (ha r hr).ret) (by decide)).trans h.ret,
    fun i hi => (hf.bytes (R := keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hg (by rw [hm]; exact Frame.refl _ _) (by simp)

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (KR H s₀ (inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := scr s₀) rfl hW (by rw [hp.wr]; simp) hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2.2.2.2, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1, u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have hs : ∀ r ∈ [svR H s₀], (retR s₀).Disjoint r ∧ (keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨hp.ret_s.sub_right (save_sub hH hp), hp.k_s.sub_right (save_sub hH hp)⟩
  exact ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    g _ (by decide),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    hm ▸ sv₁,
    by rw [hm]; exact f₁.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (hs r hr).1) (by decide),
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := keyR s₀) (fun r hr => (hs r hr).2) (Nat.le_of_lt (s₀.gpr .rcx).isLt) hi⟩

end

/-! ## The calls of the streaming `init` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', KR H s₀ b s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  have k₁ : KR H s₀ b s₁ := hk.regs u₁.rd u₁.wr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    (by rw [k₁.rsp]; exact hst.stk) fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.rsp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact away_st hH hp hst (fun _ h => h)
  · exact away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- Stores of `ipad` words (the low 32 bits of `rax`) at `rbx + o + 4 k`, for
`k < n`, which write `4 n` bytes of `ipad` from `p = rbx + o`. -/
theorem fill_ok {o : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbx + BitVec.ofNat 64 o = p → (s.gpr .rax).setWidth 32 = 0x36363636 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (4 * k)) 4) → 4 * n + 4 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem p (List.replicate (4 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store32 (at_ .rbx (o + 4 * k)) .rax) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hp hax hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hp hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store32 (a := p + BitVec.ofNat 64 (4 * n)) (by rw [ea_off, g₁, hp])
      (by rw [wr₁]; exact hout n (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_
    rw [m₂, g₁, hax, m₁, fill_mem _ _ _ (by omega), Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loop starts in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes m P (ipadBlk mk K B j)

/-- Where the key loop reads and writes. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B ≤ 128
  rbp : s.gpr .rbp = K
  rbx : s.gpr .rbx + BitVec.ofNat 64 H.P.N = P
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i < kl, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) 1
  bout : ∀ i < H.P.B, InRegions s.wr (P + BitVec.ofNat 64 i) 1
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .alu32 .xor .rax (.imm 0x36),
      .store8 (byteAt .rbx H.P.N) .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) t
      fun t' => KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hr.kl_le
  have hB := hr.hB
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hr.key j hj]
    refine (writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega) hj
    simp only [List.mem_singleton]; rintro r rfl; exact hr.disj
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide), hr.rbp, BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin j hj) fun t₁ u₁ => ?_
  refine wp_xor32i fun t₂ u₂ => ?_
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ j (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r14]),
      u₂.other _ (by decide), u₁.other _ (by decide), h.other _ (by decide) (by decide), hr.rbx])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hr.bout j (by omega)) fun t₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_cmp fun t₅ g₅ m₅ rd₅ wr₅ _ z₅ => WP.block_nil ?_
  have h14 : t₄.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₄.gpr, g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₅, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₅, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 => by rw [g₅, u₄.other r h2, g₃, u₂.other r h1, u₁.other r h1, h.other r h1 h2],
    by rw [g₅, h14], ?_⟩, ?_⟩
  · have v : (t₂.gpr .rax).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₂.gpr, u₁.gpr, xor_byte, hbyte]; rfl
    rw [m₅, u₄.mem, m₃, v, u₂.mem, u₁.mem, h.mem, writeBytes_set _ _ _ (by rw [hl]; omega) (by rw [hl]; omega),
      ipadBlk_succ]
  · rw [z₅, h14, show t₄.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide),
        h.other _ (by decide) (by decide), hr.r13], sub_beq (by omega) (by omega)]

/-- The key loop, skipped for an empty key. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hz : s.zf = some (decide (kl = 0)))
    (hm : s.mem = writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite .e (.block []) H.keyLoop) s (KeyInv s m mk P K H.P.B kl) := by
  have i0 : KeyInv s m mk P K H.P.B 0 s := ⟨rfl, rfl, fun _ _ _ => rfl, h14, hm⟩
  refine WP.ite (decide (kl = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl = 0 := by simpa using h0
    subst this; exact i0
  · have : 0 < kl := by simp at h0; omega
    exact count_loop this (KeyInv s m mk P K H.P.B) (fun j hj t h => key_step hr hj h) i0

/-- The words of the outer buffer: `n` words of the inner buffer at
`rbx + N`, XORed with `ipad ⊕ opad`, to `r12 + N`. -/
theorem opad_ok : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (4 * n) (s.gpr .r12 + BitVec.ofNat 64 H.P.N) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr .r12 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ (by decide)]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_xor32i fun s₃ u₃ => ?_
    refine wp_store32 (a := s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    rw [m₄, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, setWidth32, setWidth32, m₁, Nat.mul_succ,
      xorOpad_mem _ _ _ _ (by rwa [← Nat.mul_succ]) (by omega)]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `rsi`. -/
theorem keys_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa H.initKeys s fun t => KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀) ∧
      Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad ∧
      bytesAt t.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have eB : 4 * (H.P.B / 4) = H.P.B := by omega
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ ⟨inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ ⟨out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hS : H.S = H.P.N + H.P.B := rfl
  have inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have dIO : Region.Disjoint ⟨bufOf H (inn s₀), H.P.B⟩ ⟨bufOf H (out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  simp only [List.cons_append]
  refine WP.seq (wp_mov32i fun s₁ u₁ _ _ => ?_)
  refine fill_ok (o := H.P.N) (p := bufOf H (inn s₀)) (H.P.B / 4) _ s₁ _ (by rw [u₁.other _ (by decide), hk.rbx])
    (by rw [u₁.gpr, setWidth32]) (fun k hk' => by rw [u₁.wr, hk.wr]; exact inI _ 4 (by omega)) (by omega)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => wp_test fun s₄ g₄ m₄ rd₄ wr₄ z₄ => WP.block_nil ?_
  have G₄ : ∀ r, r ≠ .rax → r ≠ .r14 → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₄, u₃.other r h2, g₂, u₁.other r h1]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, u₃.rd, rd₂, u₁.rd, hk.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, u₃.wr, wr₂, u₁.wr, hk.wr]
  have hr : KeyRegs H s₄ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) (kl s₀) :=
    { kl_le := hkl, hB := hB
      rbp := by rw [G₄ _ (by decide) (by decide), hk.rbp]
      rbx := by rw [G₄ _ (by decide) (by decide), hk.rbx]
      r13 := by rw [G₄ _ (by decide) (by decide), hk.r13, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      key := hk.key
      kin := fun i hi => by
        rw [rd₄', wr₄', hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩
      bout := fun i hi => by rw [wr₄']; exact inI i 1 (by omega)
      disj := hp.k_i.sub_right bI }
  have h14 : s₄.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₄, u₃.gpr]; rfl
  have hz : s₄.zf = some (decide (kl s₀ = 0)) := by
    rw [z₄, u₃.other _ (by decide), g₂, u₁.other _ (by decide), hk.r13, BitVec.and_self]
    congr 1
    by_cases h : kl s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (show (s₀.gpr .rcx).toNat = (0 : BitVec 64).toNat from h)]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'; exact h (by show (s₀.gpr .rcx).toNat = 0; rw [h']; rfl)
  have hm : s₄.mem = writeBytes s.mem (bufOf H (inn s₀)) (ipadBlk s₀.mem (kp s₀) H.P.B 0) := by
    rw [m₄, u₃.mem, m₂, u₁.mem, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (key_ok hr h14 hz hm) fun t ht => ?_)
  have Gt : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ht.other r h1 h2, G₄ r h1 h2]
  have bxt : t.gpr .rbx = inn s₀ := by rw [Gt _ (by decide) (by decide), hk.rbx]
  have r12t : t.gpr .r12 = out s₀ := by rw [Gt _ (by decide) (by decide), hk.r12]
  have rdt : t.rd = s₀.rd := by rw [ht.rd, rd₄']
  have wrt : t.wr = s₀.wr := by rw [ht.wr, wr₄']
  unfold Hash.opadFill
  refine opad_ok (H.P.B / 4) _ t _
    (fun k hk' => by rw [bxt, rdt, wrt]; exact InRegions.right' (inI _ 4 (by omega)))
    (fun k hk' => by rw [r12t, wrt]; exact inO _ 4 (by omega))
    (by rw [bxt, r12t, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega)
    fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => WP.block_nil ?_
  rw [bxt, r12t, eB] at m₅
  have G : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .rsi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₇.other r h3, u₆.other r h3, g₅ r h1, Gt r h1 h2]
  have hm₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  have lI : (ipadBlk s₀.mem (kp s₀) H.P.B (kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  have bt : bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega), ipadBlk_eq _ _ hkl]
  have lO : ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  have fT : Frame [⟨bufOf H (inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  have f₅ : Frame [⟨bufOf H (out s₀), H.P.B⟩] t.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  have f : Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem s₇.mem := by
    rw [hm₇]; exact (fT.mono (by simp)).trans (f₅.mono (by simp))
  refine ⟨hk.keep (by rw [u₇.rd, u₆.rd, rd₅, ht.rd, rd₄, u₃.rd, rd₂, u₁.rd])
      (by rw [u₇.wr, u₆.wr, wr₅, ht.wr, wr₄, u₃.wr, wr₂, u₁.wr]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact G _ (by decide) (by decide) (by decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact away_st hH hp si bI
        · exact away_st hH hp so bO),
    by rw [u₇.gpr, u₆.gpr, g₅ _ (by decide), bxt, sx_ofNat (by omega)], f, ?_, ?_⟩
  · have sIO : Mem.Sep (bufOf H (inn s₀)) H.P.B (bufOf H (out s₀))
        ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm₇, m₅, bytesAt_writeBytes_sep _ _ sIO (by omega), bt]
  · rw [hm₇, m₅, bytesAt_writeBytes_self' lO (by omega), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hsi : t.gpr .rsi = bufOf H p) : CallOk H.P t p (scr s₀) (bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := sizes hH hp
  have sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega)
  have hb : Region.Sub ⟨bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hc : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := cal_sub hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hk.rbx, hk.r15, hsi, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hs.sc.sub_left hb).sub_right hc,
    (hs.stk.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hc,
    (hs.stk.sub_left b8).sub_right hb, ?_, ?_⟩
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
    (hsi : t.gpr .rsi = bufOf H p) {Q : State → Prop}
    (k : ∀ s', KR H s₀ p s' → Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine compressAt_ok hH.md hH.comp (callOk hH hp hs hk hsi) (by omega) (by omega)
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  have f : Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem := hfr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨calR H s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, b8⟩
  refine k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_) f hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega))
  · exact away_cal hH hp
  · exact away_stk hH hp (fun _ h => h)

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => KR H s₀ (out s₀) t ∧ t.gpr .rsi = bufOf H (out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rbx → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, hk.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hk.wr],
    by rw [G _ (by decide) (by decide), hk.rsp],
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r12],
    by rw [G _ (by decide) (by decide), hk.rbp], by rw [G _ (by decide) (by decide), hk.r12],
    by rw [G _ (by decide) (by decide), hk.r13], by rw [G _ (by decide) (by decide), hk.r15],
    by rw [hm]; exact hk.saved, by rw [hm]; exact hk.ret, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r12, sx_ofNat (by omega)], hm⟩

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, k0, K0, bytesAt_length, hH.hB, show ¬ (H.P.B < kl s₀) by omega, ↓reduceIte]

theorem correct : WP isa H.hmacInit s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (callInit_ok hH hp k₁ (st := .rbx) k₁.rbx si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (callInit_ok hH hp k₂ (st := .r12) k₂.r12 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (cmp_ok hH hp si k₄ si₄ fun s₅ k₅ f₅ e₅ => ?_)
  refine WP.seq (WP.mono (mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
  refine WP.seq (cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => ?_)
  refine WP.mono (restore_ok H.stream k₇.r15 hW k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₇.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₇.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
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
  have rI₅ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl bI₄ (e₅.trans (congrArg (hH.md.compress · _) iv₄))
  -- The outer state.
  have iv₆ : hH.md.stateAt s₆.mem (out s₀) = hH.iv := by
    rw [m₆, keepS f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
        · exact (so.sc.sub_left hvO).sub_right (cal_sub hH hp)
        · exact so.stk.symm.sub_left hvO),
      keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  have bO₆ : bytesAt s₆.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
    rw [m₆, bytes_keep f₅ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl | rfl)
        · exact (hp.i_o.symm.sub_left bO).sub_right hvI
        · exact (so.sc.sub_left bO).sub_right (cal_sub hH hp)
        · exact so.stk.symm.sub_left bO) (by omega), bO₄]
  have hl' : (xorPad (k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rO₇ := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl' bO₆ (e₇.trans (congrArg (hH.md.compress · _) iv₆))
  -- The inner state, kept by the outer compression.
  have rI₇ : hH.SH.Repr s₇.mem (inn s₀) (xorPad (k0 H s₀) ipad) :=
    repr_keep hH.stream f₇ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.i_o.sub_right hvO
      · exact hp.i_s.sub_right (cal_sub hH hp)
      · exact hp.stk_i.symm) (m₆ ▸ (hH.repr _ _ _).2 rI₅)
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₇, (hH.repr _ _ _).2 rO₇⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.rbx, .r12], ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.mov .rdi (.reg st)])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : PubEq s₀ s₀') {b : Addr} {s s' : State} (h : KR H s₀ b s) (h' : KR H s₀' b s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, kp, kp, hq.rdx]
  · rw [h.r12, h'.r12, out, out, hq.rsi]
  · rw [h.r13, h'.r13, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.rbx, .r12]) {p : Addr}
    (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (H.stream.callInit st)
      fun s s' => KR H s₀ b s ∧ KR H s₀' b s' := by
  have ha : RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (.block [.mov .rdi (.reg st)])
      fun s s' => (KR H s₀ b s ∧ s.gpr .rdi = p) ∧ (KR H s₀' b s' ∧ s'.gpr .rdi = p) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr' h]⟩)
  have call : ∀ {t₀ : State}, Pre H sc t₀ → StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, KR H t₀ b t →
      t.gpr .rdi = p → WP isa (.call H.stream.initN H.stream.initC) t (KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem)
      (by rw [k.rsp]; exact hst.stk) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.rsp] at f
    refine k.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact away_st hH hpt hst (fun _ h => h)
    · exact away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => KR H s₀ b s ∧ s.gpr .rdi = p)
    (F' := fun s => KR H s₀' b s ∧ s.gpr .rdi = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.rsp]; exact hs.stk, by rw [k'.rsp]; exact hs'.stk, by rw [k.rsp, k'.rsp, hq.rsp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (KR H s₀ p s ∧ s.gpr .rsi = bufOf H p) ∧ (KR H s₀' p s' ∧ s'.gpr .rsi = bufOf H p))
      (compressAt H.compN H.compC) fun s s' => KR H s₀ p s ∧ KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, si⟩, ⟨k', si'⟩⟩ =>
      ⟨⟨_, _, _, callOk hH hp hs k si⟩, ⟨_, _, _, callOk hH hp' hs' k' si'⟩,
        by rw [k.rbx, k'.rbx], by rw [k.r15, k'.r15, scr, scr, hq.r8], by rw [si, si'],
        by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun s ⟨k, si⟩ => cmp_ok hH hp hs k si fun s' k' _ _ => k')
    (fun s ⟨k, si⟩ => cmp_ok hH hp' hs' k si fun s' k' _ _ => k')

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : inn s₀' = inn s₀ := hq.rdi.symm
  have eo : out s₀' = out s₀ := hq.rsi.symm
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
  have so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s' :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact pro_ok hH hp')
  have c₁ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .rbx) (by simp) si si'
    (fun k => k.rbx) (fun k => k.rbx)
  have c₂ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .r12) (by simp) so so'
    (fun k => k.r12) (fun k => by rw [k.r12, eo])
  have keys : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') H.initKeys
      fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀)) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  have mid : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') (.block H.initOuter)
      fun s s' => (KR H s₀ (out s₀) s ∧ s.gpr .rsi = bufOf H (out s₀)) ∧
        (KR H s₀' (out s₀) s' ∧ s'.gpr .rsi = bufOf H (out s₀)) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun _ h => WP.mono (mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR H s₀ (out s₀) s ∧ KR H s₀' (out s₀) s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((cmp_rel hH hp hp' hq si si').seq (mid.seq
    ((cmp_rel hH hp hp' hq so so').seq restore))))))

end

/-- HMAC's `init` is verified against `initG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf ≤ 8 * sc)
    (hmx : H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacInit
