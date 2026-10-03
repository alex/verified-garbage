import VerifiedGarbage.Proof.CmacAes.X86.Contract
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.MdStream.X86.Common

/-!
# AES-CMAC on x86: blocks formed a word at a time

Weakest preconditions of the instruction sequences the functions build blocks
with: the XOR of the blocks at `pb + pd` and `qb + qd` stored at `cb + cd`
through `eax` and `ecx` (`xor4`, which leaves `Cmac.xor4Mem`), and four stores
of a zeroed `eax` (`zero4`, which leaves `Cmac.zero4`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd WP.cons wp_movm wp_movi wp_store)

/-- The `xor4` instructions, written out. -/
def xorBlk (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.mov .eax (.mem (at_ pb pd)), .mov .ecx (.mem (at_ qb qd)), .alu .xor .eax (.reg .ecx), .store (at_ cb cd) .eax,
   .mov .eax (.mem (at_ pb (pd + 4))), .mov .ecx (.mem (at_ qb (qd + 4))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 4)) .eax,
   .mov .eax (.mem (at_ pb (pd + 8))), .mov .ecx (.mem (at_ qb (qd + 8))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 8)) .eax,
   .mov .eax (.mem (at_ pb (pd + 12))), .mov .ecx (.mem (at_ qb (qd + 12))), .alu .xor .eax (.reg .ecx),
   .store (at_ cb (cd + 12)) .eax]

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) : xor4 pb qb cb pd qd cd = xorBlk pb qb cb pd qd cd := rfl

theorem zero4_eq (b : Reg) (d : Nat) : zero4 b d =
    [.mov .eax (.imm 0), .store (at_ b d) .eax, .store (at_ b (d + 4)) .eax, .store (at_ b (d + 8)) .eax,
     .store (at_ b (d + 12)) .eax] := rfl

/-- `s'` is `s` with memory `m`, and `eax` and `ecx` (and the flags) clobbered. -/
structure Step (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (MdStream.X86.Upd.flags _ _ _ _ _ _))

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- One word. -/
theorem xw_ok {pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    {P Q' C : Addr} (hq : qb ≠ .eax) (hc₁ : cb ≠ .eax) (hc₂ : cb ≠ .ecx)
    (hP : addr (s.gpr pb) pd = P) (hQ : addr (s.gpr qb) qd = Q') (hC : addr (s.gpr cb) cd = C)
    (rP : InRegions (s.rd ++ s.wr) P 4) (rQ : InRegions (s.rd ++ s.wr) Q' 4) (wC : InRegions s.wr C 4)
    (k : ∀ s', Step s s' (s.mem.writeW C (s.mem.readW P 32 ^^^ s.mem.readW Q' 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .eax (.mem (at_ pb pd)) :: .mov .ecx (.mem (at_ qb qd)) :: .alu .xor .eax (.reg .ecx) ::
      .store (at_ cb cd) .eax :: is)) s Q := by
  subst hP hQ hC
  refine wp_movm (ea_at' _ _ _) rP fun s₁ u₁ => ?_
  refine wp_movm (by rw [ea_at', u₁.other _ hq]) (by rw [u₁.rd, u₁.wr]; exact rQ) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_store (by rw [ea_at', u₃.other _ hc₁, u₂.other _ hc₂, u₁.other _ hc₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact wC) fun s₄ u₄ => k s₄ ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.other _ h₁, u₂.other _ h₂, u₁.other _ h₁]
  · rw [u₄.mem, u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- Word `i` of a block that does not wrap the 32-bit space. -/
theorem addr_word {b : BitVec 32} {d : Nat} (i : Nat) (h : b.toNat + d + 16 ≤ 2 ^ 32) (hi : i ≤ 12) :
    addr b (d + i) = b.setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
  rw [addr_eq (by omega), Offset.add_add]

theorem in_word {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) {i : Nat} (hi : i ≤ 12) :
    InRegions rs (P + BitVec.ofNat 64 i) 4 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P (by omega) (by omega)⟩

theorem in_word0 {rs : List Region} {P : Addr} (h : Covers [⟨P, 16⟩] rs) : InRegions rs P 4 := by
  have c := Offset.contains_base P (d := 0) (n := 4) (k := 16) (by decide) (by decide)
  rw [show P + BitVec.ofNat 64 0 = P from BitVec.add_zero P] at c
  exact h _ _ ⟨_, List.mem_singleton_self _, c⟩

/-- The XOR of the blocks at `pb + pd` and `qb + qd`, stored at `cb + cd`. -/
theorem xor4_ok {pb qb cb : Reg} {pd qd cd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hp₁ : pb ≠ .eax) (hp₂ : pb ≠ .ecx) (hq₁ : qb ≠ .eax) (hq₂ : qb ≠ .ecx) (hc₁ : cb ≠ .eax)
    (hc₂ : cb ≠ .ecx)
    (fp : (s.gpr pb).toNat + pd + 16 ≤ 2 ^ 32) (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32)
    (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rP : Covers [⟨(s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd, 16⟩] (s.rd ++ s.wr))
    (rQ : Covers [⟨(s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨(s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Step s s' (Proof.Cmac.xor4Mem s.mem ((s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd)
        ((s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd) ((s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (xor4 pb qb cb pd qd cd ++ is)) s Q := by
  rw [xor4_eq]
  simp only [xorBlk, List.cons_append, List.nil_append]
  refine xw_ok hq₁ hc₁ hc₂ (addr_eq (by omega)) (addr_eq (by omega)) (addr_eq (by omega))
    (in_word0 rP) (in_word0 rQ) (in_word0 wC) fun s₁ g₁ => ?_
  have e₁ : ∀ r, r ≠ .eax → r ≠ .ecx → s₁.gpr r = s.gpr r := g₁.gpr
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 4)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 4)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 4) hq₁ hc₁ hc₂
    (by rw [e₁ _ hp₁ hp₂]; exact addr_word 4 fp (by decide))
    (by rw [e₁ _ hq₁ hq₂]; exact addr_word 4 fq (by decide))
    (by rw [e₁ _ hc₁ hc₂]; exact addr_word 4 fc (by decide))
    (by rw [g₁.rd, g₁.wr]; exact in_word rP (by decide)) (by rw [g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₁.wr]; exact in_word wC (by decide)) fun s₂ g₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₂.gpr r h₁ h₂, e₁ r h₁ h₂]
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 8)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 8)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 8) hq₁ hc₁ hc₂
    (by rw [e₂ _ hp₁ hp₂]; exact addr_word 8 fp (by decide))
    (by rw [e₂ _ hq₁ hq₂]; exact addr_word 8 fq (by decide))
    (by rw [e₂ _ hc₁ hc₂]; exact addr_word 8 fc (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₃ g₃ => ?_
  have e₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁ h₂]
  refine xw_ok (P := (s.gpr pb).setWidth 64 + BitVec.ofNat 64 pd + BitVec.ofNat 64 12)
    (Q' := (s.gpr qb).setWidth 64 + BitVec.ofNat 64 qd + BitVec.ofNat 64 12)
    (C := (s.gpr cb).setWidth 64 + BitVec.ofNat 64 cd + BitVec.ofNat 64 12) hq₁ hc₁ hc₂
    (by rw [e₃ _ hp₁ hp₂]; exact addr_word 12 fp (by decide))
    (by rw [e₃ _ hq₁ hq₂]; exact addr_word 12 fq (by decide))
    (by rw [e₃ _ hc₁ hc₂]; exact addr_word 12 fc (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rP (by decide))
    (by rw [g₃.rd, g₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]; exact in_word rQ (by decide))
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact in_word wC (by decide)) fun s₄ g₄ => k s₄ ⟨?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂; rw [g₄.gpr r h₁ h₂, e₃ r h₁ h₂]
  · rw [g₄.mem, g₃.mem, g₂.mem, g₁.mem]; rfl
  · rw [g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]

/-- The block at `b + d` zeroed (`b` not `eax`). -/
theorem zero4_ok {b : Reg} {d : Nat} {is : List Instr} {s : State} {Q : State → Prop} (hb : b ≠ .eax)
    (fb : (s.gpr b).toNat + d + 16 ≤ 2 ^ 32)
    (wB : Covers [⟨(s.gpr b).setWidth 64 + BitVec.ofNat 64 d, 16⟩] s.wr)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero4 s.mem ((s.gpr b).setWidth 64 + BitVec.ofNat 64 d) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (zero4 b d ++ is)) s Q := by
  rw [zero4_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₀ u₀ => ?_
  have b₀ : s₀.gpr b = s.gpr b := u₀.other _ hb
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d) (by rw [ea_at', b₀]; exact addr_eq (by omega))
    (by rw [u₀.wr]; exact in_word0 wB) fun s₁ u₁ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 4)
    (by rw [ea_at', u₁.gpr, b₀]; exact addr_word 4 fb (by decide))
    (by rw [u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₂ u₂ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 8)
    (by rw [ea_at', u₂.gpr, u₁.gpr, b₀]; exact addr_word 8 fb (by decide))
    (by rw [u₂.wr, u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₃ u₃ => ?_
  refine wp_store (a := (s.gpr b).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 12)
    (by rw [ea_at', u₃.gpr, u₂.gpr, u₁.gpr, b₀]; exact addr_word 12 fb (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact in_word wB (by decide)) fun s₄ u₄ => k s₄ ?_ ?_ ?_ ?_
  · intro r hr; rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₀.other _ hr]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.gpr, u₀.mem]; rfl
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]

end VG.Proof.CmacAes.X86
