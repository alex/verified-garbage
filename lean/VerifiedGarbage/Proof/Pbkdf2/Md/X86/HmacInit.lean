import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Pbkdf2.MdInit

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, correct

HMAC's `init` (`Impl/Pbkdf2/Md/X86.lean`): the prologue (`pro_ok`), the
streaming `init` of both states (`callInit_ok`), `ipad` in every byte of the
inner state's buffer (`fill_ok`) and the key XORed into its start
(`key_ok`), the outer buffer from the inner one, word by word
(`opadW_ok`), and one compression of each buffer into its state's hash
value (`cmpI_ok`, `cmpO_ok`): each state then represents its block
(`Md.repr_block`).
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  wp_movzx8 wp_store8 ofNat_beq_zero ofNat_pred ofNat_succ addr_add_ofNat)
open VG.Proof.Pbkdf2.Stream.X86 (ea_at wp_xori count_loop)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep extractLsb'_read)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `ecx` stored at `[y + o]`, `[y + o + 4]`, … -/
theorem fillW_ok {dst : Reg} {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ecx = b ++ b ++ b ++ b →
    s.gpr dst = y → y.toNat + o + 4 * n ≤ 2 ^ 32 → (∀ k < n, InRegions s.wr (addr y (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store (at_ dst (o + 4 * k)) .ecx) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hc hy (by omega) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_store (a := addr y (o + 4 * n)) (by rw [ea_at, g₁, hy]) (by rw [wr₁]; exact hout n (by omega))
      fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, addr_word fy (by omega : n < n + 1), MdInit.writeW_rep,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega), List.replicate_append_replicate,
      show 4 * n + 4 = 4 * (n + 1) by omega]

/-- The outer state's buffer, from the inner one's: `n` words of
`[ebx + N + 4 k]`, XORed with `0x6a` in every byte, into `[esi + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .esi = y →
    x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr y (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (y.setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx hy (by omega) (by omega) (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_movm (a := addr x (H.N + 4 * n)) (by rw [ea_at, g₁ _ (by decide), hx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => wp_xori fun s₃ u₃ => ?_
    refine wp_store (a := addr y (H.N + 4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : ((bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    have f₁ : Frame [⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    have dX : ∀ r ∈ [(⟨y.setWidth 64 + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    rw [u₄.mem, u₃.gpr, u₂.gpr, u₃.mem, u₂.mem, addr_word fx (by omega : n < n + 1),
      addr_word fy (by omega : n < n + 1),
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdInit.c6a, MdInit.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `K`, its `kl`
bytes, XORed with `ipad`, written at `P`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r
  edi : t.gpr .edi = kp + BitVec.ofNat 32 j
  edx : t.gpr .edx = p + BitVec.ofNat 32 j
  ecx : t.gpr .ecx = BitVec.ofNat 32 (kl - j)
  mem : t.mem = writeBytes s.mem (p.setWidth 64) ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩) {j : Nat} (hj : j < kl) {t : State}
    (h : KeyInv s kp p kl j t) :
    WP isa (.block [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (at_ .edx 0) .al,
      .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun t' => KeyInv s kp p kl (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hl : ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  have hbyte : t.mem (kp.setWidth 64 + BitVec.ofNat 64 j) = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨kp.setWidth 64, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega))) (by show kl ≤ 2 ^ 64; omega) hj
  refine wp_movzx8 (a := kp.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [ea_at, h.edi, addr_add_ofNat (by omega), Nat.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => wp_xori fun t₂ u₂ => ?_
  refine wp_store8 (a := p.setWidth 64 + BitVec.ofNat 64 j)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.edx, addr_add_ofNat (by omega), Nat.add_zero])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_subi fun t₆ u₆ z₆ => WP.block_nil ?_
  have ecx₅ : t₅.gpr .ecx = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.ecx]
  have v : (t₂.gpr Reg8.al.reg).setWidth 8 = s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    show (t₂.gpr .eax).setWidth 8 = _
    rw [u₂.gpr, u₁.gpr, MdInit.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [u₆.other r h2, u₅.other r h3, u₄.other r h4, u₃.gpr, u₂.other r h1, u₁.other r h1, h.other r h1 h2 h3 h4],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edi, ofNat_succ, BitVec.add_assoc],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.edx, ofNat_succ, BitVec.add_assoc],
    by rw [u₆.gpr, ecx₅, ofNat_pred (by omega), show kl - j - 1 = kl - (j + 1) by omega], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    have e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (p.setWidth 64)
      ((bytesAt s.mem (kp.setWidth 64) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (kp.setWidth 64 + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega)
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, ecx₅, ofNat_pred (by omega), ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (kp.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (p.setWidth 64 + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨kp.setWidth 64, kl⟩ ⟨p.setWidth 64, kl⟩)
    (h0 : KeyInv s kp p kl 0 s) (hz : s.zf = some (decide (kl = 0))) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s (KeyInv s kp p kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz])
    (fun e => WP.block_nil ?_) fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega) _ (fun j hj t h => key_step hkp hp hkl hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK initG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After stk_args stk_ret arg_keep arg_contains arg_sub argAddr_eq init_frame setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one InRegions.right' bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi wp_test sub_offset ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev out : BitVec 32 := arg s₀ 1
abbrev kp : BitVec 32 := arg s₀ 2
abbrev kl : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.N + H.B⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, H.N + H.B⟩
abbrev keyR : Region := ⟨(kp s₀).setWidth 64, kl s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(scr s₀).setWidth 64, H.so⟩

end

/-- The precondition. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_o : (retR s₀).Disjoint (outR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of (hO : MdOk H) {s₀ : State} (h : (initG hO.hH.SH sc).pre s₀) (hfit : H.st.buf ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  have hS : hO.hH.SH.stateBytes = H.N + H.B := hO.hH.hS.trans hO.sizes.S
  have hB := hO.hH.hB
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, hB, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ 8 * H.st.W + 16 ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (kp s₀).toNat + kl s₀ ≤ 2 ^ 32 ∧ kl s₀ ≤ H.B := by
  have := hz.B4
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.N.2.2, this.1, this.2.1, this.2.2, hp.ni, hp.no,
    hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  have := bounds hz hp; exact sub_offset (by omega) (by omega)

theorem cmp_sub : Region.Sub (cmpR (H := H) s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR (H := H) s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨p.setWidth 64 + BitVec.ofNat 64 a, n⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below `esp`, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p.setWidth 64, H.N + H.B⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧
      (saveR H.st (scr s₀)).Disjoint ⟨p.setWidth 64, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨p.setWidth 64, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  esi : s.gpr .esi = out s₀
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .esi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.esi, h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega)

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, by rw [hp.rd]; simp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) : arg s i = arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega)

theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := hk.argEq hp hi
  simp only [arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hk : KR (H := H) sc s₀ s) :
    bytesAt s.mem ((kp s₀).setWidth 64) (kl s₀) = bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (arg s₀ 3).isLt (by decide)))

end

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀ := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := bounds hz hp
  have sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have dA : ∀ r ∈ [saveR H.st (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hz hp)
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at]; rfl) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega) (by have := hp.spf; omega))) (by decide)
  have i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)],
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hz hp⟩⟩,
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)]⟩

end

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

/-- `KR` after a call that writes `rs`, parts of our buffers. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hz hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hsub r hr
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- What a call of the streaming `init` on the state at `p`, in `st`, needs. -/
theorem initArgs {s : State} (hk : KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) (hsr : s.gpr st = p) :
    VG.Proof.Pbkdf2.Stream.X86.InitArgs (H := H.st) s st p := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, dK, _, np, hin⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  exact
    { hst := hsr
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by rw [hk.wr, hS]; exact covers_one hin
      b_st := by rw [stk_eq hk, hS]; exact dK
      nst := by rw [hS]; exact np }

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hO : MdOk H) {s : State} (hk : KR (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) (hsr : s.gpr st = p) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .ebx = s.gpr .ebx →
      Frame [⟨p.setWidth 64, H.N + H.B⟩, stkR s₀] s.mem s'.mem → hO.hH.SH.Repr s'.mem (p.setWidth 64) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, dV, _, _⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_frame hO.hH (initArgs hz hp hk hst hsr) fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [stk_eq hk] at f
  exact hQ s' (KR.call hz hp hk ha (by simp only [List.mem_singleton]; rintro r rfl; exact dV)
    (by
      simp only [List.mem_singleton]; rintro r rfl
      rcases hpR with rfl | rfl
      · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
      · exact ⟨outR (H := H) s₀, by simp, fun _ h => h⟩)) (ha.cs .ebx (by decide)) f hr

/-- What the compression of the buffer of the state at `p`, in `ebx`, with
`eax` at the buffer, needs. -/
theorem cmpArgs {s : State} (hk : KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s p (scr s₀) := by
  obtain ⟨hb, hf, nw, hso, hW, -⟩ := bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := st_facts hz hp hpR
  exact
    { ebx := hbx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := by rw [hk.wr]; exact covers_one hin
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, by rw [hp.wr]; simp, 0, by simp, by simp only; omega⟩
      st_sc := dS.sub_right (cmp_sub hz hp)
      b_st := by rw [stk_eq hk]; exact dK
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hz hp)
      nst := np
      nsc := by omega }

/-- The compression of the buffer of the state at `p`, in `ebx`, with `eax`
at the buffer. -/
theorem cmpS_ok (hO : MdOk H) {s : State} (hk : KR (H := H) sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (hbx : s.gpr .ebx = p) (hax : s.gpr .eax = p + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .ebx = p →
      Frame [⟨p.setWidth 64, H.N⟩, cmpR (H := H) s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem (p.setWidth 64) = hO.md.compress (hO.md.stateAt s.mem (p.setWidth 64))
        (hO.md.blockAt s.mem (p.setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, -, -, hB64, -⟩ := bounds hz hp
  obtain ⟨dS, dK, dV, np, hin⟩ := st_facts hz hp hpR
  refine cmp_ok hO.comp (by omega) (cmpArgs hz hp hk hpR hbx hax) fun s' ha e => ?_
  have f := ha.frame
  rw [stk_eq hk] at f
  have sN : Region.Sub ⟨p.setWidth 64, H.N⟩ ⟨p.setWidth 64, H.N + H.B⟩ := Region.sub_prefix (by omega)
  refine hQ s' (KR.call hz hp hk ha ?_ ?_) (ha.cs .ebx (by decide) |>.trans hbx) (f.mono (by simp)) e
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR (H := H) s₀, by simp, sN⟩
      · exact ⟨outR (H := H) s₀, by simp, sN⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩

end

/-! ## The blocks -/

section
variable {sc : Nat} {s₀ : State} (hz : Sizes H) (hp : Pre (H := H) sc s₀)
include hz hp

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (addr p (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, -⟩ := bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := st_facts hz hp hpR
  rw [addr_eq (by omega)]
  exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩

/-- `ipad` in every byte of the inner buffer, then the key's arguments. -/
theorem fill_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa (.block H.fillIpad) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧ t.gpr .edi = kp s₀ ∧
      t.gpr .edx = inn s₀ + BitVec.ofNat 32 H.N ∧ t.gpr .ecx = BitVec.ofNat 32 (kl s₀) ∧
      t.zf = some (decide (kl s₀ = 0)) ∧
      t.mem = writeBytes s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  simp only [Hash.fillIpad, List.cons_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine fillW_ok (H.B / 4) _ s₁ _ (b := 0x36) (u₁.gpr.trans (by decide)) (by rw [u₁.other _ (by decide), hbx])
    (by omega) (fun j hj => by rw [u₁.wr, hk.wr]; exact buf_word hz hp (.inl rfl) hj) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [h4] at m₂
  have f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem]; exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  have sB : Region.Sub ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (inR (H := H) s₀) := st_sub _ (by omega)
  have k₂ : KR (H := H) sc s₀ s₂ := hk.keep (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr])
    (fun r hr => by rw [g₂, u₁.other r (by revert hr; decide +revert)]) f₂
    (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
    (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩)
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, k₂.esp]; rfl) (argIn hp k₂.rd k₂.wr (by decide))
    fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, u₃.other _ (by decide), k₂.esp]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact argIn hp k₂.rd k₂.wr (by decide)) fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  have hcx : s₇.gpr .ecx = arg s₀ 3 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, k₂.readArg hp (by decide)]
  have bx₂ : s₂.gpr .ebx = inn s₀ := by rw [g₂, u₁.other _ (by decide), hbx]
  have bx : s₇.gpr .ebx = inn s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  have k₇ : KR (H := H) sc s₀ s₇ :=
    ((((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).keep f₇.rd f₇.wr
      (fun r _ => by rw [f₇.gpr]) (rs := []) (by rw [f₇.mem]; exact Frame.refl _ _) (by simp) (by simp)
  refine ⟨k₇, bx, ?_, ?_, ?_, ?_, by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      k₂.readArg hp (by decide)]
  · rw [f₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), bx₂]
  · rw [hcx, kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [z₇, ← f₇.gpr, hcx, VG.Proof.Pbkdf2.Stream.X86.test_z]


/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) (hdi : s.gpr .edi = kp s₀)
    (hdx : s.gpr .edx = inn s₀ + BitVec.ofNat 32 H.N) (hcx : s.gpr .ecx = BitVec.ofNat 32 (kl s₀))
    (hzf : s.zf = some (decide (kl s₀ = 0)))
    (hm : bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .e (.block []) Hash.keyLoop) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := bounds hz hp
  have kl32 : kl s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have ap : (inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
    setWidth_add (by omega)
  have tp : (inn s₀ + BitVec.ofNat 32 H.N).toNat = (inn s₀).toNat + H.N := toNat_add_ofNat (by omega)
  have hin : ∀ j < kl s₀, InRegions (s.rd ++ s.wr) ((kp s₀).setWidth 64 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : ∀ j < kl s₀, InRegions s.wr ((inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, ap, Memory.add_ofNat]
      exact ⟨inR (H := H) s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : Region.Disjoint ⟨(kp s₀).setWidth 64, kl s₀⟩ ⟨(inn s₀ + BitVec.ofNat 32 H.N).setWidth 64, kl s₀⟩ := by
    rw [ap]; exact hp.k_i.sub_right (st_sub _ (by omega))
  have h0 : KeyInv s (kp s₀) (inn s₀ + BitVec.ofNat 32 H.N) (kl s₀) 0 s :=
    ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [hdi]; exact (BitVec.add_zero _).symm,
      by rw [hdx]; exact (BitVec.add_zero _).symm, by rw [hcx, Nat.sub_zero],
      by rw [show bytesAt s.mem ((kp s₀).setWidth 64) 0 = [] from rfl, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (key_ok (by omega) (by rw [tp]; omega) kl32 hin hout hsep h0 hzf) fun t ht => ?_
  have hl : ((bytesAt s.mem ((kp s₀).setWidth 64) (kl s₀)).map (· ^^^ ipad)).length = kl s₀ := by
    simp [bytesAt_length]
  have sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have ft : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem, ap]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr (fun r hr => ht.other r (by revert hr; decide +revert) (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), hbx], ft, ?_⟩
  rw [ht.mem, ap, MdInit.bytes_over (by rw [hl]; omega) (by omega) hm, hl, hk.key hp]
  rfl


/-- The outer buffer from the inner one, and `eax` at the inner one. -/
theorem opad_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa (.block H.fillOpad) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  have sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (by omega)
  unfold Hash.fillOpad
  refine opadW_ok H (H.B / 4) _ s _ hbx hk.esi (by omega) (by omega)
    (fun j hj => by rw [hk.wr, hk.rd]; exact InRegions.right' (buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [hk.wr]; exact buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [h4] at m₁
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have hl : ((bytesAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₂.mem := by
    rw [m₂, m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
      (fun r hr => by rw [g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [g₂ _ (by decide), g₁ _ (by decide), hbx], by rw [e₂, g₁ _ (by decide), hbx], by rw [m₂, m₁]⟩


/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : KR (H := H) sc s₀ s) (hbx : s.gpr .ebx = inn s₀) :
    WP isa H.blocks s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = inn s₀ ∧
      t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N := by
  have := (bounds hz hp).2.2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (fill_ok hz hp hk hbx) fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)])) fun s₅ ⟨k₅, b₅, _⟩ => ?_)
  exact WP.mono (opad_ok hz hp k₅ b₅) fun _ ⟨k₆, b₆, a₆, _⟩ => ⟨k₆, b₆, a₆⟩

omit hz hp in
/-- `ebx` at the outer state, and `eax` at its buffer. -/
theorem toOuter_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block H.toOuter) s fun t => KR (H := H) sc s₀ t ∧ t.gpr .ebx = out s₀ ∧
      t.gpr .eax = out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  unfold Hash.toOuter
  refine wp_mov fun s₁ u₁ => ?_
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  have k₁ := hk.upd (by decide) u₁
  exact ⟨k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by revert hr; decide +revert)) (rs := [])
      (by rw [m₂]; exact Frame.refl _ _) (by simp) (by simp),
    by rw [g₂ _ (by decide), u₁.gpr, hk.esi], by rw [e₂, u₁.gpr, hk.esi], by rw [m₂, u₁.mem]⟩

end


/-! ## Correctness -/

section
variable {sc : Nat} {s₀ : State} (hO : MdOk H) (hp : Pre (H := H) sc s₀)
include hO hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hO.md.stateAt m' p = hO.md.stateAt m p :=
  hO.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hO.sizes.N; show H.N ≤ 2 ^ 64; omega) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hO.md.Repr hO.iv m p x) :
    hO.md.Repr hO.iv m' p x :=
  hO.md.repr_congr (by have := hO.sizes.B4; omega) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have := hO.sizes.B4; have := hO.sizes.N; show H.N + H.B ≤ 2 ^ 64; omega) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN0, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := bounds hz hp
  have hl := hO.link
  -- Where things are.
  have sNI := st_sub (H := H) (inn s₀) (a := 0) (n := H.N) (by omega)
  have sNO := st_sub (H := H) (out s₀) (a := 0) (n := H.N) (by omega)
  rw [BitVec.add_zero] at sNI sNO
  have sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (by omega)
  have nb : ∀ (x : BitVec 32), Region.Disjoint ⟨x.setWidth 64, H.N⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  have iv0 : ∀ {m : Mem} {p : Addr}, hO.hH.SH.Repr m p [] → hO.md.stateAt m p = hO.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (pro_ok hz hp) fun s₁ ⟨k₁, b₁⟩ => ?_)
  refine WP.seq (callInit_ok hz hp hO k₁ (.inl ⟨rfl, rfl⟩) b₁ fun s₂ k₂ b₂ _ r₂ => ?_)
  refine WP.seq (callInit_ok hz hp hO k₂ (.inr ⟨rfl, rfl⟩) k₂.esi fun s₃ k₃ b₃ f₃ r₃ => ?_)
  have vI₃ : hO.md.stateAt s₃.mem ((inn s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  have vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (fill_ok hz hp k₃ (b₃.trans (b₂.trans b₁)))
    fun s₄ ⟨k₄, b₄, d₄, x₄, c₄, z₄, m₄⟩ => ?_))
  have rep₄ : bytesAt s₄.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)]
  have f₄ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ b₄ d₄ x₄ c₄ z₄ rep₄) fun s₅ ⟨k₅, b₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (opad_ok hz hp k₅ b₅) fun s₆ ⟨k₆, b₆, a₆, m₆⟩ => ?_
  have hl6 : ((bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f₆ : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  have bO₆ : bytesAt s₆.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (by omega)]
  have bI₆ : bytesAt s₆.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega)
  -- The hash values are those `init` left.
  have vI₆ : hO.md.stateAt s₆.mem ((inn s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      keep_st hO f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hO f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  have vO₆ : hO.md.stateAt s₆.mem ((out s₀).setWidth 64) = hO.iv := by
    rw [keep_st hO f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hO f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      keep_st hO f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (cmpS_ok hz hp hO k₆ (.inl rfl) b₆ a₆ fun s₇ k₇ _ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (toOuter_ok k₇) fun s₈ ⟨k₈, b₈, a₈, m₈⟩ => ?_)
  refine WP.seq (cmpS_ok hz hp hO k₈ (.inr rfl) b₈ a₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  have hK : xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) ipad =
      bytesAt s₅.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdInit.blockKey_short _ (by rw [bytesAt_length, hO.hH.hB]; exact hkl), MdInit.xorPad_short,
      bytesAt_length, hO.hH.hB]
  have hKl : (xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  have rI₇ := Md.repr_block (H := hO.md) (iv := hO.iv) (by omega) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  have dI₉ : ∀ r ∈ [(⟨(out s₀).setWidth 64, H.N⟩ : Region), cmpR (H := H) s₀, stkR s₀],
      Region.Disjoint ⟨(inn s₀).setWidth 64, H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (cmp_sub hz hp)
    · exact hp.b_i.symm
  have rI₉ := keep_repr hO f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  have d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨(inn s₀).setWidth 64, H.N⟩ : Region), cmpR (H := H) s₀,
      stkR s₀], Region.Disjoint ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_o.symm.sub_left (st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (st_sub _ h)).sub_right (cmp_sub hz hp)
    · exact hp.b_o.symm.sub_left (st_sub _ h)
  have vO₈ : hO.md.stateAt s₈.mem ((out s₀).setWidth 64) = hO.iv := by
    rw [m₈, keep_st hO f₇ (by have := d₇ (a := 0) (n := H.N) (by omega); rwa [BitVec.add_zero] at this), vO₆]
  have bO₈ : bytesAt s₈.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hO.hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (by omega)) (by omega), bO₆, ← hK, MdInit.xorPad_6a]
  have rO₉ := Md.repr_block (H := hO.md) (iv := hO.iv) (by omega) (by rw [xorPad_length, ← xorPad_length _ ipad, hKl])
    bO₈ (by rw [e₉, vO₈])
  -- The end.
  have hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (restore_ok H.st k₉.ebp k₉.saved hsc (by omega) nw) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hm]; exact k₉.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₉.esp]
    · exact hg r (callee_saved r hr he)
  · show hO.hH.SH.Repr s'.mem ((inn s₀).setWidth 64) _ ∧ hO.hH.SH.Repr s'.mem ((out s₀).setWidth 64) _
    rw [hm]
    exact ⟨hO.back _ _ _ rI₉, hO.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.X86.HmacInit
