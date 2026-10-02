import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
import VerifiedGarbage.Proof.Pbkdf2.MdInit

/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: correct

As on x86 (`Proof/Pbkdf2/Md/X86/HmacInit.lean`): HMAC's `init`
(`Impl/Pbkdf2/Md/Arm.lean`) saves our caller's registers (`pro_ok`), calls
the streaming `init` on both states (`callInit_ok`), writes `ipad` in every
byte of the inner state's buffer (`fill_ok`) and the key XORed into its
start (`keys_ok`), the outer buffer from the inner one, word by word
(`opad_ok`), and compresses each buffer into its state's hash value
(`compressBlock_ok`): each state then represents its block
(`Md.repr_block`). The contract is `initG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_ldr wp_str wp_ldrb wp_strb wp_subs wp_cmp op2_imm
  op2_reg eval_eq)
open VG.Proof.Pbkdf2.Stream.Arm (count_loop addr3 left_z left_val)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `r1` stored at `[r4 + o]`, `[r4 + o + 4]`, … -/
theorem fillW_ok {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) (ho : o + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = b ++ b ++ b ++ b →
    s.gpr .r4 = y → y.toNat + o + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr y + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .r1 .r4 (o + 4 * k)) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hc hy (by omega) (fun j hj => hout j (by omega)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (o + 4 * n)) (by omega)
      (by rw [g₁, hy, addr_add (by omega)]) (by rw [wr₁]; exact hout n (by omega)) fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) (by rw [u₂.sp, sp₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, MdInit.writeW_rep, ← Memory.add_ofNat,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega),
      List.replicate_append_replicate, show 4 * n + 4 = 4 * (n + 1) by omega]

/-- The outer state's buffer, from the inner one's: `n` words of
`[r4 + N + 4 k]`, XORed with `r1 = 0x6a6a6a6a`, into `[r5 + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) (ho : H.N + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = 0x6a6a6a6a → s.gpr .r4 = x →
    s.gpr .r5 = y → x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr y + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q h1 hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q h1 hx hy (by omega) (by omega) (fun j hj => hin j (by omega))
      (fun j hj => hout j (by omega))
      ((hsep.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega)))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) (by omega)
      (by rw [g₁ _ (by decide), hx, addr_add (by omega)]) (by rw [rd₁, wr₁]; exact hin n (by omega))
      fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (H.N + 4 * n)) (by omega)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy, addr_add (by omega)])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    have f₁ : Frame [⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    have dX : ∀ r ∈ [(⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    have v : s₃.gpr .r12 = s₁.mem.readW (State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) 32 ^^^ 0x6a6a6a6a := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h1]
    rw [u₄.mem, v, u₃.mem, u₂.mem, ← Memory.add_ofNat, ← Memory.add_ofNat,
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdInit.c6a, MdInit.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `kp`, its bytes,
XORed with `ipad`, written at `p + N`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (N kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r
  r6 : t.gpr .r6 = kp + BitVec.ofNat 32 j
  r8 : t.gpr .r8 = p + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = BitVec.ofNat 32 (kl - j)
  mem : t.mem = writeBytes s.mem (State.addr p + BitVec.ofNat 64 N)
    ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩) {j : Nat} (hj : j < kl)
    {t : State} (h : KeyInv s kp p H.N kl j t) :
    WP isa (.block [.ldrb .r12 .r6 0, .dp .eor .r12 .r12 (.imm 0x36), .strb .r12 .r8 H.N,
      .dp .add .r6 .r6 (.imm 1), .dp .add .r8 .r8 (.imm 1), .subs .r7 .r7 (.imm 1)]) t
      fun t' => KeyInv s kp p H.N kl (j + 1) t' ∧ t'.z = decide (kl - (j + 1) = 0) := by
  have hl : ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  have hbyte : t.mem (State.addr kp + BitVec.ofNat 64 j) = s.mem (State.addr kp + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨State.addr kp, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega))) (by show kl ≤ 2 ^ 64; omega) hj
  refine wp_ldrb (a := State.addr kp + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, addr3 (by omega), BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => wp_eor (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_strb (a := State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) hN
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8, addr3 (by omega)])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine wp_add (op2_imm (by decide)) fun t₄ u₄ => wp_add (op2_imm (by decide)) fun t₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ => WP.block_nil ?_
  have r7₅ : t₅.gpr .r7 = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r7]
  have v : (t₂.gpr .r12).setWidth 8 = s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    rw [u₂.gpr, u₁.gpr, MdInit.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h6 h7 h8 h12 => by
      rw [u₆.other r h7, u₅.other r h8, u₄.other r h6, u₃.gpr, u₂.other r h12, u₁.other r h12,
        h.other r h6 h7 h8 h12],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r6, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.gpr, r7₅, left_val hj], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    have e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (State.addr p + BitVec.ofNat 64 H.N)
      ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega)
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, r7₅, left_z hj hkl]

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩)
    (h0 : KeyInv s kp p H.N kl 0 s) (hz : s.z = decide (kl = 0)) :
    WP isa (.ite .eq (.block []) H.keyLoop) s (KeyInv s kp p H.N kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show eval .eq s = _; rw [eval_eq, hz]) (fun e => WP.block_nil ?_)
    fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega) _ (fun j hj t h => key_step H hkp hp hkl hN hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (initG below SavedRegs saveR savedRegs preserved_saved After below_eq covers_one
  init_call save_ok restore_ok)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_cmp wp_ldrSp op2_imm op2_reg cmp0)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev keyR : Region := ⟨State.addr (kp s₀), kl s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev inR : Region := ⟨State.addr (inn s₀), H.N + H.B⟩
abbrev outR : Region := ⟨State.addr (out s₀), H.N + H.B⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨State.addr (scr s₀), H.so⟩

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_s : (outR H s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR H s₀)
  a_o : (argR s₀).Disjoint (outR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_i : (below s₀).Disjoint (inR H s₀)
  b_o : (below s₀).Disjoint (outR H s₀)
  b_k : (below s₀).Disjoint (keyR s₀)
  b_s : (below s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀)
    (hfit : H.st.buf ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS : hH.SH.stateBytes = H.N + H.B := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 36 ∧ 8 * H.st.W + 36 ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (kp s₀).toNat + kl s₀ ≤ 2 ^ 32 ∧ kl s₀ ≤ H.B := by
  have hB : H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> rw [h] <;> decide
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N64, hz.N4, hB.1, hB.2.1, hB.2.2, hp.ni, hp.no, hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  have := bounds hz hp; exact Offset.sub_base _ (by omega)

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨State.addr p + BitVec.ofNat 64 a, n⟩ ⟨State.addr p, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below the stack pointer, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨State.addr p, H.N + H.B⟩ (scR sc s₀) ∧ (below s₀).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧
      (saveR H.st (scr s₀)).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨State.addr p, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below the stack pointer. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [inR H s₀, outR H s₀, scR sc s₀, below s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = out s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR H sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs H sc s₀, Region.Sub r r') : KR H sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r11, h.saved.frame H.st hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s s' : State} (h : KR H sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR H sc s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hp : Pre H sc s₀) (hk : KR H sc s₀ s) :
    bytesAt s.mem (State.addr (kp s₀)) (kl s₀) = bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (s₀.gpr .r3).isLt (by decide)))

end

/-! ## The pieces -/

/-- The offsets of the buffers in a state can be added as immediates. -/
theorem enc_small : ∀ n < 65, encodable (BitVec.ofNat 32 n) = true := by decide

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => KR H sc s₀ s ∧ s.gpr .r6 = kp s₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (kl s₀) := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := bounds hz hp
  have hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  unfold Hash.initPrologue
  simp only [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (by rw [hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (L := 8 * sc) (by omega) nw
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have hm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    hm ▸ f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR sc s₀, by simp, save_sub hz hp⟩⟩,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- A call of the streaming `init` on the state at `p`, in `r0`. -/
theorem initCall_ok (hH : HashOK H) {t : State} (hk : KR H sc s₀ t) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (h0 : t.gpr .r0 = p) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = t.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (.call H.st.initN H.st.initC) t Q := by
  obtain ⟨_, _, dV, np, hin⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_call hH.stream (st := p) h0 (by rw [hS]; exact np) (by rw [hk.wr, hS]; exact covers_one hin)
    fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [below_eq hk.sp] at f
  have f' : Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem := f
  refine hQ s' (hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f' ?_ ?_)
    (fun r hr => ?_) f' hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV
    · exact hp.b_s.symm.sub_left (save_sub hz hp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨outR H s₀, by simp, fun _ h => h⟩
    · exact ⟨below s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.cs .r6 (by decide) (by decide)
    · exact ha.cs .r7 (by decide) (by decide)

omit hz hp in
/-- `r0` at the state in `st`. -/
theorem initArg_ok {s : State} (hk : KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) :
    WP isa (.block [.mov .r0 (.reg st)]) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = p ∧
      (∀ r ∈ [Reg.r6, .r7], t.gpr r = s.gpr r) ∧ t.mem = s.mem :=
  wp_mov (op2_reg _ _) fun _ u₁ => WP.block_nil ⟨hk.upd (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide) u₁,
    by rw [u₁.gpr]; rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hk.r4, hk.r5],
    fun r hr => u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                               rcases hr with rfl | rfl <;> decide), u₁.mem⟩

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hH : HashOK H) {s : State} (hk : KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = s.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] s.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  unfold Impl.Pbkdf2.Stream.Arm.Hash.callInit
  exact WP.seq (WP.mono (initArg_ok hk hst) fun t ⟨k, d, g, m⟩ =>
    initCall_ok hz hp hH k hpR d fun s' k' g' f r => hQ s' k' (fun r hr => (g' r hr).trans (g r hr)) (m ▸ f) r)

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (State.addr p + BitVec.ofNat 64 (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, -⟩ := bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := st_facts hz hp hpR
  exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩

/-- `ipad` in every byte of the inner buffer, and the flags of `key_len = 0`. -/
theorem fill_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀)) :
    WP isa (.block H.fillIpad) s fun t => KR H sc s₀ t ∧ t.gpr .r6 = kp s₀ ∧
      t.gpr .r7 = BitVec.ofNat 32 (kl s₀) ∧ t.gpr .r8 = inn s₀ ∧ t.z = decide (kl s₀ = 0) ∧
      t.mem = writeBytes s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  simp only [Hash.fillIpad, List.cons_append, List.append_assoc]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  have c₂ : s₂.gpr .r1 = (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) := by
    rw [u₂.gpr, u₁.gpr]; decide
  have hr4 : s₂.gpr .r4 = inn s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4]
  refine fillW_ok (H.B / 4) (by omega) _ s₂ _ c₂ hr4 (by omega)
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact buf_word hz hp (.inl rfl) hj) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r8 → s₅.gpr r = s.gpr r := fun r h1 h8 => by
    rw [f₅.gpr, u₄.other r h8, g₃, u₂.other r h1, u₁.other r h1]
  have sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have f : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₅.mem := by
    rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
    exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [f₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [f₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [f₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp]) (fun r hr => g r (by revert hr; decide +revert)
        (by revert hr; decide +revert)) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [g _ (by decide) (by decide), h6], by rw [g _ (by decide) (by decide), h7],
    by rw [f₅.gpr, u₄.gpr, g₃, hr4], ?_, by rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]⟩
  rw [z₅, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide), h7,
    cmp0 (s₀.gpr .r3).isLt]

/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀) (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀))
    (h8 : s.gpr .r8 = inn s₀) (hzf : s.z = decide (kl s₀ = 0))
    (hm : bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .eq (.block []) H.keyLoop) s fun t => KR H sc s₀ t ∧
      Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := bounds hz hp
  have kl32 : kl s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  have hin : ∀ j < kl s₀, InRegions (s.rd ++ s.wr) (State.addr (kp s₀) + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : ∀ j < kl s₀, InRegions s.wr (State.addr (inn s₀) + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, Memory.add_ofNat]
      exact ⟨inR H s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hsep : Region.Disjoint ⟨State.addr (kp s₀), kl s₀⟩ ⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, kl s₀⟩ :=
    hp.k_i.sub_right (st_sub _ (by omega))
  have h0 : KeyInv s (kp s₀) (inn s₀) H.N (kl s₀) 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [h6]; exact (BitVec.add_zero _).symm,
      by rw [h8]; exact (BitVec.add_zero _).symm, by rw [h7, Nat.sub_zero],
      by rw [show bytesAt s.mem (State.addr (kp s₀)) 0 = [] from rfl, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (key_ok H (by omega) (by omega) kl32 (by omega) hin hout hsep h0 hzf) fun t ht => ?_
  have hl : ((bytesAt s.mem (State.addr (kp s₀)) (kl s₀)).map (· ^^^ ipad)).length = kl s₀ := by
    simp [bytesAt_length]
  have sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have ft : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr ht.sp (fun r hr => ht.other r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩), ft, ?_⟩
  rw [ht.mem, MdInit.bytes_over (by rw [hl]; omega) (by omega) hm, hl, hk.key hp]
  rfl

/-- What the compression of the buffer of the state at `p` needs. -/
theorem callOk {s : State} (hk : KR H sc s₀ s) {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀)
    (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = scr s₀) (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) :
    CallOk s H.N H.B H.so p (scr s₀) (p + BitVec.ofNat 32 H.N) := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := bounds hz hp
  obtain ⟨dS, _, _, np, hin⟩ := st_facts hz hp hpR
  have ap : State.addr (p + BitVec.ofNat 32 H.N) = State.addr p + BitVec.ofNat 64 H.N := addr_add (by omega)
  have tp : (p + BitVec.ofNat 32 H.N).toNat = p.toNat + H.N := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := H.N) (by omega), Nat.mod_eq_of_lt (by omega)]
  have sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (by omega)
  have sB := st_sub (H := H) p (a := H.N) (n := H.B) (by omega)
  have sS : scR sc s₀ ∈ s.wr := by rw [hk.wr, hp.wr]; simp
  have hin' : ⟨State.addr p, H.N + H.B⟩ ∈ s.wr := by rw [hk.wr]; exact hin
  refine ⟨h0, h3, h6, by omega, by rw [tp]; omega, by omega, dS.sub_left sN |>.sub_right (cmp_sub hz hp),
    by rw [ap]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega),
    by rw [ap]; exact dS.sub_left sB |>.sub_right (cmp_sub hz hp), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ap]; exact ⟨_, List.mem_append_right _ hin', H.N, rfl, by simp only; omega⟩
    · exact ⟨_, List.mem_append_right _ hin', 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨_, List.mem_append_right _ sS, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hin', 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨_, sS, 0, (BitVec.add_zero _).symm, by simp only; omega⟩

/-- The outer buffer from the inner one, and the inner state's compression set up. -/
theorem opad_ok {s : State} (hk : KR H sc s₀ s) :
    WP isa (.block H.fillOpad) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = inn s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = writeBytes s.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := bounds hz hp
  have h4 : 4 * (H.B / 4) = H.B := by omega
  have sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (by omega)
  simp only [Hash.fillOpad, List.cons_append, List.append_assoc]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  have c₂ : s₂.gpr .r1 = 0x6a6a6a6a := by rw [u₂.gpr, u₁.gpr]; decide
  refine opadW_ok H (H.B / 4) (by omega) _ s₂ _ c₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r5]) (by omega) (by omega)
    (fun j hj => by rw [u₂.wr, u₂.rd, u₁.wr, u₁.rd, hk.wr, hk.rd]
                    exact Hmac.Generic.Common.InRegions.right' (buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4, u₂.mem, u₁.mem] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm (enc_small _ (by omega))) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h12 => by
    rw [g₃ r h12, u₂.other r h1, u₁.other r h1]
  have hl : ((bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₆.mem := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp])
      (fun r hr => by
        rw [u₆.other r (by revert hr; decide +revert), u₅.other r (by revert hr; decide +revert),
          u₄.other r (by revert hr; decide +revert), g r (by revert hr; decide +revert) (by revert hr; decide +revert)])
      f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g _ (by decide) (by decide), hk.r4],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g _ (by decide) (by decide), hk.r11],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g _ (by decide) (by decide), hk.r4],
    by rw [u₆.mem, u₅.mem, u₄.mem, m₃]⟩

/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀)) :
    WP isa H.blocks s fun t => KR H sc s₀ t ∧ t.gpr .r0 = inn s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N := by
  have := (bounds hz hp).2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (fill_ok hz hp hk h6 h7) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ d₄ c₄ e₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)])) fun s₅ ⟨k₅, _⟩ => ?_)
  exact WP.mono (opad_ok hz hp k₅) fun _ ⟨k₆, a, b, c, _⟩ => ⟨k₆, a, b, c⟩

/-- The compression of the buffer of the state at `p`, at `r0`, with its
buffer at `r6` and `scratch` at `r3`. -/
theorem cmpS_ok (hH : HashOK H) {s : State} (hk : KR H sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = scr s₀)
    (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → s'.gpr .r3 = scr s₀ →
      Frame [⟨State.addr p, H.N⟩, cmpR H s₀] s.mem s'.mem →
      hH.md.stateAt s'.mem (State.addr p) = hH.md.compress (hH.md.stateAt s.mem (State.addr p))
        (hH.md.blockAt s.mem (State.addr p + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.compressBlock s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := bounds hz hp
  obtain ⟨_, _, dV, np, _⟩ := st_facts hz hp hpR
  have sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (by omega)
  refine compressBlock_ok hH.comp (callOk hz hp hk hpR h0 h3 h6) fun s' hrd hwr hcs h0' h3' hsp hfr hst => ?_
  rw [addr_add (by omega)] at hst
  refine hQ s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hfr ?_ ?_) h3' hfr hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR H s₀, by simp, sN⟩
      · exact ⟨outR H s₀, by simp, sN⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩

omit hp in
/-- The outer state's compression set up. -/
theorem toOuter_ok {s : State} (hk : KR H sc s₀ s) (h3 : s.gpr .r3 = scr s₀) :
    WP isa (.block H.toOuter) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = out s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  have := hz.N64
  unfold Hash.toOuter
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (enc_small _ (by omega))) fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(hk.upd (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr, hk.r5],
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h3], by rw [u₂.gpr, u₁.other _ (by decide), hk.r5],
    by rw [u₂.mem, u₁.mem]⟩

end

/-! ## Correctness -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hH : HashOK H) (hp : Pre H sc s₀)
include hH hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hH.md.stateAt m' p = hH.md.stateAt m p :=
  hH.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hH.sizes.N64; show H.N ≤ 2 ^ 64; omega) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hH.md.Repr hH.iv m p x) :
    hH.md.Repr hH.iv m' p x :=
  hH.md.repr_congr (by have := hH.B_ge; omega) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have := hH.B_le; have := hH.sizes.N64; show H.N + H.B ≤ 2 ^ 64; omega) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  have hz := hH.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := bounds hz hp
  have hl := hH.link
  -- Where things are.
  have sNI := st_sub (H := H) (inn s₀) (a := 0) (n := H.N) (by omega)
  have sNO := st_sub (H := H) (out s₀) (a := 0) (n := H.N) (by omega)
  rw [BitVec.add_zero] at sNI sNO
  have sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (by omega)
  have sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (by omega)
  have nb : ∀ (x : BitVec 32), Region.Disjoint ⟨State.addr x, H.N⟩ ⟨State.addr x + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  have iv0 : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (pro_ok hz hp) fun s₁ ⟨k₁, r6₁, r7₁⟩ => ?_)
  refine WP.seq (callInit_ok hz hp hH k₁ (.inl ⟨rfl, rfl⟩) fun s₂ k₂ g₂ _ r₂ => ?_)
  refine WP.seq (callInit_ok hz hp hH k₂ (.inr ⟨rfl, rfl⟩) fun s₃ k₃ g₃ f₃ r₃ => ?_)
  have r6₃ : s₃.gpr .r6 = kp s₀ := by rw [g₃ _ (by simp), g₂ _ (by simp), r6₁]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 (kl s₀) := by rw [g₃ _ (by simp), g₂ _ (by simp), r7₁]
  have vI₃ : hH.md.stateAt s₃.mem (State.addr (inn s₀)) = hH.iv := by
    rw [keep_st hH f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  have vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (fill_ok hz hp k₃ r6₃ r7₃) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_))
  have rep₄ : bytesAt s₄.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (by omega)]
  have f₄ : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ d₄ c₄ e₄ z₄ rep₄) fun s₅ ⟨k₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (opad_ok hz hp k₅) fun s₆ ⟨k₆, a₆, b₆, c₆, m₆⟩ => ?_
  have hl6 : ((bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  have f₆ : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  have bO₆ : bytesAt s₆.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (by omega)]
  have bI₆ : bytesAt s₆.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega)
  -- The hash values are those `init` left.
  have vI₆ : hH.md.stateAt s₆.mem (State.addr (inn s₀)) = hH.iv := by
    rw [keep_st hH f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      keep_st hH f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hH f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  have vO₆ : hH.md.stateAt s₆.mem (State.addr (out s₀)) = hH.iv := by
    rw [keep_st hH f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hH f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      keep_st hH f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (cmpS_ok hz hp hH k₆ (.inl rfl) a₆ b₆ c₆ fun s₇ k₇ r3₇ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (toOuter_ok hz k₇ r3₇) fun s₈ ⟨k₈, a₈, b₈, c₈, m₈⟩ => ?_)
  refine WP.seq (cmpS_ok hz hp hH k₈ (.inr rfl) a₈ b₈ c₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  have hK : xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ipad =
      bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdInit.blockKey_short _ (by rw [bytesAt_length, hH.hB]; exact hkl), MdInit.xorPad_short,
      bytesAt_length, hH.hB]
  have hKl : (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  have rI₇ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  have dI₉ : ∀ r ∈ [(⟨State.addr (out s₀), H.N⟩ : Region), cmpR H s₀],
      Region.Disjoint ⟨State.addr (inn s₀), H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (cmp_sub hz hp)
  have rI₉ := keep_repr hH f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  have d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨State.addr (inn s₀), H.N⟩ : Region), cmpR H s₀],
      Region.Disjoint ⟨State.addr (out s₀) + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_o.symm.sub_left (st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (st_sub _ h)).sub_right (cmp_sub hz hp)
  have vO₈ : hH.md.stateAt s₈.mem (State.addr (out s₀)) = hH.iv := by
    rw [m₈, keep_st hH f₇ (by have := d₇ (a := 0) (n := H.N) (by omega); rwa [BitVec.add_zero] at this), vO₆]
  have bO₈ : bytesAt s₈.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (by omega)) (by omega), bO₆, ← hK, MdInit.xorPad_6a]
  have rO₉ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega)
    (by rw [xorPad_length, ← xorPad_length _ ipad, hKl]) bO₈ (by rw [e₉, vO₈])
  -- The end.
  have hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (restore_ok H.st k₉.r11 hW k₉.saved hsc (by omega) nw) fun s' ⟨hm, _, _, hsp, hg, _⟩ => ?_
  refine ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, k₉.sp]⟩, ?_⟩
  show hH.SH.Repr s'.mem (State.addr (inn s₀)) _ ∧ hH.SH.Repr s'.mem (State.addr (out s₀)) _
  rw [hm]
  exact ⟨hH.back _ _ _ rI₉, hH.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.Arm.HmacInit
