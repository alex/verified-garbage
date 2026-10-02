import VerifiedGarbage.Impl.Pbkdf2.Md.Arm
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.MdStep
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC and PBKDF2-HMAC over a Merkle–Damgård hash function on ARMv7: words

What the straight-line pieces of `Impl/Pbkdf2/Md/Arm.lean` write, in one run:
copies of 32-bit words (`copyW`), the padding (`padFrom`, then the constant
words `constW` of the length field), `T ← T ⊕ U` (`xorW`), and `scratch` plus
an offset in a register (`scrAt`); and what the code writing a hash function's
digest must do (`OutOk`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (cp copyW padFrom constW xorW)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.MdStream (Md bytes32)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_ldr wp_str op2_imm op2_reg writeW_le)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero bytesAt_add bytesAt_length bytesAt_writeBytes_sep
  extractLsb'_read bytesAt_getD')
open VG.Proof.Pbkdf2.Memory (writeW_bytes writeBytes_append' xorBytes_length sep_after off_contains)
open VG.Spec.Sha256 (bytesAt)

/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (Upd.setReg _ _ _))

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

end

theorem add_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 (o + j) = p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem movw_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `d ← scratch + o`, with `scratch` in `r11`. -/
theorem scrAt_ok {d : Reg} {o : Nat} (ho : o < 2 ^ 16) {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.gpr d = s.gpr .r11 + BitVec.ofNat 32 o →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => k s₂ (fun r h₁ h₂ => ?_) ?_
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · rw [u₂.other r h₁, u₁.other r h₂]
  · rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), movw_ofNat ho]

/-! ## Copies -/

/-- Copying `n` words from `[src + o₁]` to `[dst + o₂]`, through `r12`. -/
theorem copyW_ok {src dst : Reg} (hs : src ≠ .r12) (hd : dst ≠ .r12) (o₁ o₂ : Nat) (n : Nat)
    (hb : o₁ + 4 * n ≤ 4096 ∧ o₂ + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (s.gpr src).toNat + o₁ + 4 * n ≤ 2 ^ 32 → (s.gpr dst).toNat + o₂ + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)
      (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂) (4 * n) →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (State.addr (s.gpr src) + BitVec.ofNat 64 o₁) (4 * n)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (copyW src dst o₁ o₂ n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q fs fd hin hout hsep k
    rw [copyW, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih ⟨by omega_nat, by omega_nat⟩ _ s Q (by omega_nat) (by omega_nat) (fun j hj => hin j (by omega_nat))
      (fun j hj => hout j (by omega_nat)) (fun x hx hy => hsep x (by omega_nat) (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [cp, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr (s.gpr src) + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [g₁ _ hs, addr_add (by omega_nat), add_off])
      (by rw [rd₁, wr₁]; exact hin n (by omega_nat)) fun s₂ u₂ => ?_
    refine wp_str (a := State.addr (s.gpr dst) + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by omega_nat) (by rw [u₂.other _ hd, g₁ _ hd, addr_add (by omega_nat), add_off])
      (by rw [u₂.wr, wr₁]; exact hout n (by omega_nat))
      fun s₃ u₃ => k s₃ (fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr])
        (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁]) (by rw [u₃.sp, u₂.sp, sp₁]) ?_
    rw [u₃.mem, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega_nat)

/-! ## The padding -/

/-- Stores of zero (`r12`) at `r6 + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : BitVec 32} : ∀ n, a + 4 + 4 * n ≤ 4096 → p.toNat + a + 4 + 4 * n ≤ 2 ^ 32 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .r6 = p → s.gpr .r12 = 0 →
    (∀ k < n, InRegions s.wr (State.addr p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .r12 .r6 (a + 4 + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ _ rest s Q _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro ha hf rest s Q h6 h12 hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega_nat) (by omega_nat) _ s Q h6 h12 (fun j hj => hout j (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str (a := State.addr p + BitVec.ofNat 64 (a + 4 + 4 * n)) (by omega_nat)
      (by rw [g₁, h6, addr_add (by omega_nat)]) (by rw [wr₁]; exact hout n (by omega_nat)) fun s₂ g₂ =>
        k s₂ (by rw [g₂.gpr, g₁]) (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    rw [g₂.mem, g₁, h12, m₁, writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      writeBytes_append' _ _ _ (by rw [List.length_replicate, Memory.add_ofNat])
        (by simp; omega_nat), Nat.mul_succ, ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `r6`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (hb : b ≤ 4096) {s : State} {p : BitVec 32}
    (h6 : s.gpr .r6 = p) (hf : p.toNat + b ≤ 2 ^ 32)
    (hout : ∀ k < (b - a) / 4, InRegions s.wr (State.addr p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr p + BitVec.ofNat 64 a) (by omega_nat)
    (by rw [u₁.other _ (by decide), h6, addr_add (by omega_nat)])
    (by rw [u₁.wr]; simpa using hout 0 (by omega_nat)) fun s₂ g₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine zeros_ok (a := a) (p := p) ((b - a) / 4 - 1) (by omega_nat) (by omega_nat) rest s₃ Q
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h6]) u₃.gpr
    (fun j hj => by
      rw [u₃.wr, g₂.wr, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega_nat]; exact hout (j + 1) (by omega_nat))
    fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂.gpr, u₁.other r hr]) (by rw [rd₄, u₃.rd, g₂.rd, u₁.rd])
      (by rw [wr₄, u₃.wr, g₂.wr, u₁.wr]) (by rw [sp₄, u₃.sp, g₂.sp, u₁.sp]) ?_
  rw [m₄, u₃.mem, g₂.mem, u₁.gpr, u₁.mem,
    writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, Memory.add_ofNat]) (by simp; omega_nat),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega_nat, ← List.replicate_append_replicate]
  rfl

/-- The bytes of words, each stored little-endian. -/
def wordsBytes (ws : List (BitVec 32)) : List Byte := ws.flatMap (bytes32 false)

theorem wordsBytes_length (ws : List (BitVec 32)) : (wordsBytes ws).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wordsBytes, List.flatMap_cons, List.length_append, MdStream.bytes32_length] at ih ⊢
    rw [ih, List.length_cons]; omega

theorem movw_movt' (x : BitVec 32) :
    (x.extractLsb' 16 16 ++ ((x.extractLsb' 0 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = x :=
  movw_movt x

/-- `constW o ws` stores the words `ws` from `r6 + o` on. -/
theorem constW_ok {p : BitVec 32} : ∀ (ws : List (BitVec 32)) (o : Nat), o + 4 * ws.length ≤ 4096 →
    p.toNat + o + 4 * ws.length ≤ 2 ^ 32 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r6 = p →
    (∀ k < ws.length, InRegions s.wr (State.addr p + BitVec.ofNat 64 (o + 4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr p + BitVec.ofNat 64 o) (wordsBytes ws) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (constW o ws ++ rest)) s Q
  | [], o, _, _, rest, s, Q, _, _, k => k s (fun _ _ => rfl) rfl rfl rfl (by rw [wordsBytes, List.flatMap_nil,
      writeBytes_nil])
  | w :: ws, o, ho, hf, rest, s, Q, h6, hout, k => by
    simp only [List.length_cons] at ho hf
    simp only [constW, List.cons_append, List.nil_append]
    refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
    have e6 : s₂.gpr .r6 = p := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h6]
    refine wp_str (a := State.addr p + BitVec.ofNat 64 o) (by omega_nat) (by rw [e6, addr_add (by omega_nat)])
      (by rw [u₂.wr, u₁.wr]; simpa using hout 0 (by simp)) fun s₃ g₃ => ?_
    refine constW_ok (p := p) ws (o + 4) (by omega_nat) (by omega_nat) rest s₃ Q (by rw [g₃.gpr, e6])
      (fun j hj => by
        rw [g₃.wr, u₂.wr, u₁.wr, show o + 4 + 4 * j = o + 4 * (j + 1) by omega_nat]
        exact hout (j + 1) (by simp; omega_nat)) fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
    refine k s₄ (fun r hr => by rw [g₄ r hr, g₃.gpr, u₂.other r hr, u₁.other r hr])
      (by rw [rd₄, g₃.rd, u₂.rd, u₁.rd]) (by rw [wr₄, g₃.wr, u₂.wr, u₁.wr]) (by rw [sp₄, g₃.sp, u₂.sp, u₁.sp]) ?_
    have v : s₂.gpr .r12 = w := by rw [u₂.gpr, u₁.gpr, movw_movt']
    rw [m₄, g₃.mem, v, u₂.mem, u₁.mem, writeW_le,
      writeBytes_append' _ _ _ (by rw [MdStream.bytes32_length, Memory.add_ofNat]) (by
        rw [MdStream.bytes32_length, wordsBytes_length]; omega_nat)]
    rfl

/-! ## `T ← T ⊕ U` -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

/-- `T ← T ⊕ U` for the first `n` words of `T` at `r7` (`tp`) and `U` at `r6` (`bp`). -/
theorem xor_ok {tp bp : BitVec 32} {D : Nat} (hd : Region.Disjoint ⟨State.addr tp, D⟩ ⟨State.addr bp, D⟩)
    (hD : D ≤ 4096) (ft : tp.toNat + D ≤ 2 ^ 32) (fb : bp.toNat + D ≤ 2 ^ 32) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r6 = bp → s.gpr .r7 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (State.addr bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r12 → r ≠ .r1 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr tp)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp) (4 * n)) (bytesAt s.mem (State.addr bp) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q h6 h7 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_nat) _ s Q h6 h7 (fun j hj => hin j (by omega_nat)) (fun j hj => hout j (by omega_nat))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (by omega_nat)
    refine wp_ldr (a := State.addr bp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [g₁ _ (by decide) (by decide), h6, addr_add (by omega_nat)]) (by rw [rd₁, wr₁]; exact hin n (by omega_nat))
      fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr tp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h7, addr_add (by omega_nat)])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_str (a := State.addr tp + BitVec.ofNat 64 (4 * n)) (by omega_nat)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h7, addr_add (by omega_nat)])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h12 h1 => by
          rw [g₅.gpr, u₄.other r h12, u₃.other r h1, u₂.other r h12, g₁ r h12 h1])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp) (4 * n))
        (bytesAt s.mem (State.addr bp) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have v : s₄.gpr .r12 = s₁.mem.readW (State.addr bp + BitVec.ofNat 64 (4 * n)) 32 ^^^
        s₁.mem.readW (State.addr tp + BitVec.ofNat 64 (4 * n)) 32 := by
      rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem]
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, v, writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := State.addr tp + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := State.addr bp + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem (State.addr tp) _
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr tp + BitVec.ofNat 64 (4 * n)) 4)
          (bytesAt s.mem (State.addr bp + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_nat)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega_nat) (off_contains h₁ (by omega_nat) (by omega_nat))
    · omega_nat
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega_nat)
    · omega_nat

/-! ## Digests -/

/-- What the code writing a hash function's digest must do: write the digest
of the hash value at `r0` to `r6`, writing only `r9` and `r10`. -/
def OutOk {B N L : Nat} (H : Md B N L) (out : List Instr) : Prop :=
  ∀ s : State, (s.gpr .r0).toNat + N ≤ 2 ^ 32 → (s.gpr .r6).toNat + N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) N → InRegions s.wr (State.addr (s.gpr .r6)) N →
    Region.Disjoint ⟨State.addr (s.gpr .r0), N⟩ ⟨State.addr (s.gpr .r6), N⟩ →
    WP isa (.block out) s fun s' => (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6)) (H.digest (H.stateAt s.mem (State.addr (s.gpr .r0))))

/-- The streaming proofs' digest code. -/
theorem OutOk.ofShape {P : Impl.MdStream.Arm.Params} {H : Md P.B P.N P.L} (h : MdStream.Arm.Shape H) :
    OutOk H P.out := fun s f₀ f₆ hin hout hd =>
  h.out s f₀ f₆ hin hout hd

/-! ## Blocks -/

/-- The block, of `D` bytes of message and the padding after them. -/
theorem blockAt_eq {B N L D : Nat} {md : Md B N L} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : bytesAt m (p + BitVec.ofNat 64 D) (B - D) = md.tailPad D) :
    md.blockAt m p = md.tailBlock D (bytesAt m p D) := by
  simp only [Md.blockAt, Md.tailBlock]
  refine md.parse_congr fun k hk => ?_
  have e := bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, bytesAt_getD' _ _ hk]

end VG.Proof.Pbkdf2.Md.Arm
