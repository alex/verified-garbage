import VerifiedGarbage.Proof.CmacAes.Arm.Call
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.MdStream.Arm.Common

/-!
# AES-CMAC on ARMv7: blocks formed a word at a time

Weakest preconditions of the instruction sequences the functions build blocks
with: the XOR of the blocks at `pb + pd` and `qb + qd` stored at `cb + cd`
through two temporaries (`xorBlk`, which leaves `Cmac.xor4Mem`), and four
stores of a zero register (`zeroBlk`, which leaves `Cmac.zero4`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd WP.cons op2_reg wp_ldr wp_str)

/-- The words of the blocks at `pb + pd` and `qb + qd`, XORed through `t₁`
and `t₂` and stored at `cb + cd`. -/
def xorBlk (t₁ t₂ pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr t₁ pb pd, .ldr t₂ qb qd, .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb cd,
   .ldr t₁ pb (pd + 4), .ldr t₂ qb (qd + 4), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 4),
   .ldr t₁ pb (pd + 8), .ldr t₂ qb (qd + 8), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 8),
   .ldr t₁ pb (pd + 12), .ldr t₂ qb (qd + 12), .dp .eor t₁ t₁ (.reg t₂), .str t₁ cb (cd + 12)]

/-- `z` stored in the four words at `b + d`. -/
def zeroBlk (z b : Reg) (d : Nat) : List Instr :=
  [.str z b d, .str z b (d + 4), .str z b (d + 8), .str z b (d + 12)]

/-- `s'` is `s` with memory `m`, and `t₁` and `t₂` clobbered. -/
structure Step (s s' : State) (t₁ t₂ : Reg) (m : Mem) : Prop where
  gpr : ∀ r, r ≠ t₁ → r ≠ t₂ → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2} {y : BitVec 32}
    (ho : o.eval s = some y) (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

/-- One word. -/
theorem xw_ok {t₁ t₂ pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    {P Q' C : Addr} (h12 : t₁ ≠ t₂) (hq : qb ≠ t₁) (hc₁ : cb ≠ t₁) (hc₂ : cb ≠ t₂)
    (hpd : pd < 4096) (hqd : qd < 4096) (hcd : cd < 4096)
    (hP : State.addr (s.gpr pb + BitVec.ofNat 32 pd) = P) (hQ : State.addr (s.gpr qb + BitVec.ofNat 32 qd) = Q')
    (hC : State.addr (s.gpr cb + BitVec.ofNat 32 cd) = C)
    (rP : InRegions (s.rd ++ s.wr) P 4) (rQ : InRegions (s.rd ++ s.wr) Q' 4) (wC : InRegions s.wr C 4)
    (k : ∀ s', Step s s' t₁ t₂ (s.mem.writeW C (s.mem.readW P 32 ^^^ s.mem.readW Q' 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t₁ pb pd :: .ldr t₂ qb qd :: .dp .eor t₁ t₁ (.reg t₂) :: .str t₁ cb cd :: is)) s Q := by
  subst hQ hC
  refine wp_ldr hpd hP rP fun s₁ u₁ => ?_
  refine wp_ldr hqd (by rw [u₁.other _ hq]) (by rw [u₁.rd, u₁.wr]; exact rQ) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_str hcd (by rw [u₃.other _ hc₁, u₂.other _ hc₂, u₁.other _ hc₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wC) fun s₄ u₄ => k s₄ ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₄.mem, u₃.gpr, u₂.other _ h12, u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- Word `i` of a block that does not wrap the 32-bit space. -/
theorem addr_word {b : BitVec 32} {d : Nat} (i : Nat) (h : b.toNat + d + 16 ≤ 2 ^ 32) (hi : i ≤ 12) :
    State.addr (b + BitVec.ofNat 32 (d + i)) = State.addr b + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  rw [addr_add (by omega), Offset.add_add]

theorem in_word {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) {i : Nat} (hi : i ≤ 12) :
    InRegions rs (P + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega) (by omega)⟩

theorem in_word0 {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) : InRegions rs P 4 := by
  have c := Offset.contains_base P (d := 0) (n := 4) (k := 16) (by decide) (by decide)
  rw [show P + BitVec.ofNat 64 0 = P from BitVec.add_zero P] at c
  exact h _ _ ⟨_, List.mem_singleton_self _, c⟩

/-- The XOR of the blocks at `pb + pd` and `qb + qd`, stored at `cb + cd`. -/
theorem xorBlk_ok {t₁ t₂ pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (h12 : t₁ ≠ t₂) (hp₁ : pb ≠ t₁) (hp₂ : pb ≠ t₂) (hq₁ : qb ≠ t₁) (hq₂ : qb ≠ t₂) (hc₁ : cb ≠ t₁)
    (hc₂ : cb ≠ t₂) (hpd : pd + 12 < 4096) (hqd : qd + 12 < 4096) (hcd : cd + 12 < 4096)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨State.addr (s.gpr pb) + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Step s s' t₁ t₂ (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr pb) + BitVec.ofNat 64 pd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (xorBlk t₁ t₂ pb qb cb pd qd cd ++ is)) s Q := by
  simp only [xorBlk, List.cons_append, List.nil_append]
  refine xw_ok h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega) (addr_add (by omega)) (addr_add (by omega))
    (addr_add (by omega)) (in_word0 rP) (in_word0 rQ) (in_word0 wC) fun s₁ g₁ => ?_
  have e₁ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₁.gpr r = s.gpr r := g₁.gpr
  refine xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 4)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 4)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 4) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₁ _ hp₁ hp₂]; exact addr_word 4 fp (by decide))
    (by rw [e₁ _ hq₁ hq₂]; exact addr_word 4 fq (by decide))
    (by rw [e₁ _ hc₁ hc₂]; exact addr_word 4 fc (by decide))
    (by rw [g₁.rd, g₁.wr]; exact in_word rP (by decide)) (by rw [g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₁.wr]; exact in_word wC (by decide)) fun s₂ g₂ => ?_
  have e₂ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₂.gpr r h₁ h₂, e₁ r h₁ h₂]
  refine xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 8)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 8)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 8) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₂ _ hp₁ hp₂]; exact addr_word 8 fp (by decide))
    (by rw [e₂ _ hq₁ hq₂]; exact addr_word 8 fq (by decide))
    (by rw [e₂ _ hc₁ hc₂]; exact addr_word 8 fc (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₃ g₃ => ?_
  have e₃ : ∀ r, r ≠ t₁ → r ≠ t₂ → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁ h₂]
  refine xw_ok (P := State.addr (s.gpr pb) + BitVec.ofNat 64 pd + BitVec.ofNat 64 12)
    (Q' := State.addr (s.gpr qb) + BitVec.ofNat 64 qd + BitVec.ofNat 64 12)
    (C := State.addr (s.gpr cb) + BitVec.ofNat 64 cd + BitVec.ofNat 64 12) h12 hq₁ hc₁ hc₂ (by omega) (by omega) (by omega)
    (by rw [e₃ _ hp₁ hp₂]; exact addr_word 12 fp (by decide))
    (by rw [e₃ _ hq₁ hq₂]; exact addr_word 12 fq (by decide))
    (by rw [e₃ _ hc₁ hc₂]; exact addr_word 12 fc (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₄ g₄ => k s₄ ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂; rw [g₄.gpr r h₁ h₂, e₃ r h₁ h₂]
  · rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem]; rfl
  · rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]
  · rw [g₄.sp, g₃.sp, g₂.sp, g₁.sp]

/-- The block at `b + d` zeroed, from a register `z` holding zero. -/
theorem zeroBlk_ok {z b : Reg} {d : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hz : s.gpr z = 0) (hd : d + 12 < 4096) (fb : (s.gpr b).toNat + d + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨State.addr (s.gpr b) + BitVec.ofNat 64 d, 16⟩] s.wr)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = Proof.Cmac.zero4 s.mem (State.addr (s.gpr b) + BitVec.ofNat 64 d) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (zeroBlk z b d ++ is)) s Q := by
  simp only [zeroBlk, List.cons_append, List.nil_append]
  refine wp_str (by omega) (addr_add (by omega)) (in_word0 wB) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
    (by rw [u₁.gpr]; exact addr_word 4 fb (by decide))
    (by rw [u₁.wr]; exact in_word wB (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (by omega)
    (by rw [u₂.gpr, u₁.gpr]; exact addr_word 8 fb (by decide))
    (by rw [u₂.wr, u₁.wr]; exact in_word wB (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := State.addr (s.gpr b) + BitVec.ofNat 64 d + BitVec.ofNat 64 12) (by omega)
    (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact addr_word 12 fb (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in_word wB (by decide)) fun s₄ u₄ => k s₄ ?_ ?_ ?_ ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, hz]; rfl
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

end VG.Proof.CmacAes.Arm
