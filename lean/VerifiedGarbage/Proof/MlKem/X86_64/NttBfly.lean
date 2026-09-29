import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Proof.MlKem.X86_64.Reduce
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub

/-!
# ML-KEM on x86-64: the butterflies of `NTT` and `NTT⁻¹`

Untrusted: everything here is checked by Lean. What one butterfly's code
stores (`bfly_ok`, `bflyInv_ok`), for any `len`, from the words it reads
and the zeta in `r9`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem (q)

/-! ## `NTT` -/

/-- The part of `bfly` after the product is reduced. -/
def bflyTail (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .rdx (.reg .rax), .alu32 .add .rdx (.imm qImm),
      .alu32 .sub .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi (4 * len)) .rdx, .alu32 .add .rax (.reg .r10)] ++ csubQ .rax .r11 ++
    [.store32 (at_ .rsi 0) .rax, .alu .add .rsi (.imm 4), .alu .sub .rcx (.imm 1)]

theorem bfly_eq (len : Nat) :
    bfly len = ([.mov32 .rax (.mem (at_ .rsi (4 * len))), .mul .r9] : List Instr) ++ (reduce ++ bflyTail len) := by
  simp only [bfly, bflyTail, List.append_assoc]

/-- The product of a loaded word and `r9`. -/
abbrev prodR9 (a : BitVec 32) (z : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * z.toNat)

theorem bflyHead_ok (len : Nat) (s : State)
    (h : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block ([.mov32 .rax (.mem (at_ .rsi (4 * len))), .mul .r9] : List Instr)) s fun s' =>
      (s'.gpr .rax = prodR9 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [h]

theorem bflyTail_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (bflyTail len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * len))
          (csub32 (s.mem.readW (s.gpr .rsi) 32 + qImm - BitVec.setWidth 32 (s.gpr .r10)))).writeW (s.gpr .rsi)
          (csub32 (s.mem.readW (s.gpr .rsi) 32 + BitVec.setWidth 32 (s.gpr .r10))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r11] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold bflyTail csubQ
  xrun [h0, w0, w1, List.cons_append, List.nil_append, csub32]

theorem bfly_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (bfly len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * len))
          (csub32 (s.mem.readW (s.gpr .rsi) 32 + qImm - BitVec.setWidth 32
            (redV (prodR9 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9)))))).writeW
          (s.gpr .rsi) (csub32 (s.mem.readW (s.gpr .rsi) 32 + BitVec.setWidth 32
            (redV (prodR9 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32) (s.gpr .r9))))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  rw [bfly_eq, WP.block_append_iff]
  refine WP.mono (bflyHead_ok len s h1) fun s1 ⟨⟨ha, hm1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi : s2.gpr .rsi = s.gpr .rsi := k12.gpr (by decide)
  have hrr : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [k12.2.1, k12.2.2]
  refine WP.mono (bflyTail_ok len s2 (by rw [hrr, hsi]; exact h0) (by rw [k12.2.2, hsi]; exact w0)
    (by rw [k12.2.2, hsi]; exact w1)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  have hcx : s2.gpr .rcx = s.gpr .rcx := k12.gpr (by decide)
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## `NTT⁻¹` -/

/-- The part of `bflyInv` up to the product. -/
def bflyInvHead (len : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .r10 (.mem (at_ .rsi (4 * len))), .mov32 .rdx (.reg .rax),
    .alu32 .add .rdx (.reg .r10)] ++ csubQ .rdx .r11 ++
    [.store32 (at_ .rsi 0) .rdx, .alu32 .add .r10 (.imm qImm), .alu32 .sub .r10 (.reg .rax)] ++
    csubQ .r10 .r11 ++ [.mov32 .rax (.reg .r10), .mul .r9]

theorem bflyInv_eq (len : Nat) :
    bflyInv len = bflyInvHead len ++ (reduce ++ ([.store32 (at_ .rsi (4 * len)) .r10, .alu .add .rsi (.imm 4),
      .alu .sub .rcx (.imm 1)] : List Instr)) := by
  simp only [bflyInv, bflyInvHead, List.append_assoc]

theorem bflyInvHead_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) :
    WP isa (.block (bflyInvHead len)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi) (csub32 (s.mem.readW (s.gpr .rsi) 32 +
          s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32)) ∧
        s'.gpr .rax = prodR9 (csub32 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32 + qImm -
          s.mem.readW (s.gpr .rsi) 32)) (s.gpr .r9)) ∧ Keep [.rax, .rdx, .r10, .r11] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold bflyInvHead csubQ
  xrun [h0, h1, w0, List.cons_append, List.nil_append, csub32]

theorem bflyInv_ok (len : Nat) (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 4)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4)
    (w0 : InRegions s.wr (s.gpr .rsi) 4) (w1 : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4) :
    WP isa (.block (bflyInv len)) s fun s' =>
      (s'.mem = (s.mem.writeW (s.gpr .rsi) (csub32 (s.mem.readW (s.gpr .rsi) 32 +
          s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32))).writeW
          (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) (BitVec.setWidth 32 (redV (prodR9
            (csub32 (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * len)) 32 + qImm - s.mem.readW (s.gpr .rsi) 32))
            (s.gpr .r9)))) ∧
        s'.gpr .rsi = s.gpr .rsi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdx, .rsi, .rcx, .r10, .r11] s s' := by
  rw [bflyInv_eq, WP.block_append_iff]
  refine WP.mono (bflyInvHead_ok len s h0 h1 w0) fun s1 ⟨⟨hm1, ha⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s1) fun s2 ⟨⟨hr, hm2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hsi : s2.gpr .rsi = s.gpr .rsi := k12.gpr (by decide)
  have hcx : s2.gpr .rcx = s.gpr .rcx := k12.gpr (by decide)
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun s' => s'.mem = s2.mem.writeW (s2.gpr .rsi + BitVec.ofNat 64 (4 * len))
      (BitVec.setWidth 32 (s2.gpr .r10)) ∧ s'.gpr .rsi = s2.gpr .rsi + 4 ∧ s'.gpr .rcx = s2.gpr .rcx - 1 ∧
      s'.zf = some (s2.gpr .rcx - 1 == 0)) (by
        xrun [show InRegions s2.wr (s2.gpr .rsi + BitVec.ofNat 64 (4 * len)) 4 by rw [k12.2.2, hsi]; exact w1])
      (by rfl)) fun s3 ⟨⟨hm3, h3si, h3cx, h3z⟩, k3⟩ => ⟨?_, (k12.trans k3).mono (by decide)⟩
  rw [hm3, h3si, h3cx, h3z, hcx, hsi, hr, hm2, hm1, ha]
  exact ⟨rfl, rfl, rfl, rfl⟩

end VG.Proof.MlKem.X86_64
