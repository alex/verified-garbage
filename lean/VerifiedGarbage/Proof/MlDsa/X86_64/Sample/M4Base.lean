import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes
import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask4

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4`, the layout

Untrusted: everything here is checked by Lean. The contract the proofs are
written against (`em4K`), what holds between the pieces of the functions
(`Env`, relative to the entry state `σ`), and the prologue, as for
`vg_mlkem_sample_ntt4` (`Proof/MlKem/X86_64/S4Base.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Mask4

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sample.Mask4
open VG.Proof.MlKem.X86_64 (Keep WP.keep retR)
open VG.Proof.MlDsa.X86_64.Sample (gOf)
open VG.Spec.MlDsa (H PolyIs toRq bitUnpack bitlen seed66)
open VG.Spec.Sha3 (bytesAt)

/-- The output polynomial `k` of four at `a`. -/
abbrev poly4 (a : Addr) (k : Nat) : Addr := a + BitVec.ofNat 64 (1024 * k)

/-- `vg_mldsa_expand_mask_poly4(seeds = rdi, gamma1 = esi, a = rdx, scratch = rcx)`,
with 24 bytes of stack below `rsp`. -/
def em4K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 264⟩] ∧ s.wr = [⟨s.gpr .rdx, 4096⟩, ⟨s.gpr .rcx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rdx, 4096⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 264⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 4096⟩ ⟨s.gpr .rcx, 8192⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (retR s).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 264⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 4096⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rcx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 4096 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64 ∧
    (gOf s = 2 ^ 17 ∨ gOf s = 2 ^ 19)
  post s s' := ∀ k < 4, PolyIs s'.mem (poly4 (s.gpr .rdx) k)
    (toRq (bitUnpack (H (seed66 s.mem (s.gpr .rdi) k) (32 * (1 + bitlen (gOf s - 1)))) (gOf s - 1) (gOf s)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rdx
abbrev scr : Addr := σ.gpr .rcx
/-- Seed `k`. -/
abbrev B (k : Nat) : List Byte := seed66 σ.mem (sd σ) k
abbrev sdR : Region := ⟨sd σ, 264⟩
abbrev aR : Region := ⟨aP σ, 4096⟩
abbrev scrR : Region := ⟨scr σ, 8192⟩
abbrev stkR : Region := below (σ.gpr .rsp) 24
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := scr σ + BitVec.ofNat 64 off
end

/-- The precondition, by name. -/
structure Pre (σ : State) : Prop where
  rd : σ.rd = [sdR σ]
  wr : σ.wr = [aR σ, scrR σ]
  sd_a : (sdR σ).Disjoint (aR σ)
  sd_scr : (sdR σ).Disjoint (scrR σ)
  a_scr : (aR σ).Disjoint (scrR σ)
  ret_sd : (retR σ).Disjoint (sdR σ)
  ret_a : (retR σ).Disjoint (aR σ)
  ret_scr : (retR σ).Disjoint (scrR σ)
  stk_sd : (stkR σ).Disjoint (sdR σ)
  stk_a : (stkR σ).Disjoint (aR σ)
  stk_scr : (stkR σ).Disjoint (scrR σ)
  a_lt : (aP σ).toNat + 4096 ≤ 2 ^ 64
  scr_lt : (scr σ).toNat + 8192 ≤ 2 ^ 64
  gamma : gOf σ = 2 ^ 17 ∨ gOf σ = 2 ^ 19

theorem pre_of {σ : State} (h : em4K.pre σ) : Pre σ :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = scr σ
  r12 : s.gpr .r12 = sd σ
  r13 : s.gpr .r13 = aP σ
  r14 : s.gpr .r14 = σ.gpr .rsi
  rsp : s.gpr .rsp = σ.gpr .rsp
  r15 : s.gpr .r15 = σ.gpr .r15
  saved : ∀ i < 5, s.mem.readW (at' σ (oSave + 8 * i)) 64 = σ.gpr (saved.getD i .rbx)
  frame : Frame [aR σ, scrR σ, stkR σ] σ.mem s.mem

section
variable {σ : State} (hp : Pre σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 8192) : Region.Sub ⟨at' σ a, n⟩ (scrR σ) := Offset.sub_base _ h

omit hp in
theorem sub_poly {k : Nat} (hk : k < 4) : Region.Sub ⟨poly4 (aP σ) k, 1024⟩ (aR σ) :=
  Offset.sub_base _ (by omega)

theorem in_scr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) : InRegions s.wr (at' σ a) n := by
  rw [hw, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_scr' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (at' σ a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_sd' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 264) :
    InRegions (s.rd ++ s.wr) (sd σ + BitVec.ofNat 64 a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨sdR σ, by simp, Offset.contains_base _ h (by omega)⟩

/-- The seeds are not written. -/
theorem seeds_frame {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {a : Nat} (ha : a < 264) :
    m (sd σ + BitVec.ofNat 64 a) = σ.mem (sd σ + BitVec.ofNat 64 a) :=
  hf.bytes (R := sdR σ) (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by simp) ha

/-- Byte `a` of seed `k`. -/
theorem seed_byte {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {k a : Nat} (hk : k < 4) (ha : a < 66) :
    m (sd σ + BitVec.ofNat 64 (66 * k + a)) = (B σ k).getD a 0 := by
  rw [seeds_frame hp hf (by omega), B, seed66, ← Offset.add_add]
  simp [bytesAt, ha]

end

/-! ## The prologue -/

/-- A read of 8 bytes at `scratch + d` after a write of 8 elsewhere. -/
theorem rd64_off {σ : State} {m : Mem} {d e : Nat} {v : BitVec 64} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : (m.writeW (at' σ e) v).readW (at' σ d) 64 = m.readW (at' σ d) 64 :=
  readW_writeW_off m _ v (n := 8) (by omega) (by omega) h

theorem pro_eq : pro = [.store (VG.Impl.MlKem.X86_64.at_ .rcx 5088) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5096) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5104) .r12, .store (VG.Impl.MlKem.X86_64.at_ .rcx 5112) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 5120) .r14, .mov .rbx (.reg .rcx), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rdx), .mov .r14 (.reg .rsi)] := rfl

theorem pro_ok {σ : State} (hp : Pre σ) : WP isa (.block pro) σ (Env σ) := by
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (at' σ 5088) (σ.gpr .rbx)).writeW (at' σ 5096) (σ.gpr .rbp)).writeW (at' σ 5104)
          (σ.gpr .r12)).writeW (at' σ 5112) (σ.gpr .r13)).writeW (at' σ 5120) (σ.gpr .r14) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .r12 = sd σ ∧ s.gpr .r13 = aP σ ∧ s.gpr .r14 = σ.gpr .rsi)
    (by xrun [in_scr hp rfl (a := 5088) (n := 8) (by omega), in_scr hp rfl (a := 5096) (n := 8) (by omega),
      in_scr hp rfl (a := 5104) (n := 8) (by omega), in_scr hp rfl (a := 5112) (n := 8) (by omega),
      in_scr hp rfl (a := 5120) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨k1.2.1, k1.2.2, hbx, h12, h13, h14,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩
  · rw [hm1]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oSave, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega) (by omega)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 5088 (by omega))).writeW (by simp) _
      (hin 5096 (by omega))).writeW (by simp) _ (hin 5104 (by omega))).writeW (by simp) _
      (hin 5112 (by omega))).writeW (by simp) _ (hin 5120 (by omega)))

end VG.Proof.MlDsa.X86_64.Mask4
