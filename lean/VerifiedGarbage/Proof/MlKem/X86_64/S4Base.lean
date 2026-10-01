import VerifiedGarbage.Proof.MlKem.X86_64.SampleNtt
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the layout

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`sample4K`), what holds between the pieces of the
function (`Env`, relative to the entry state `σ`), and the prologue.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem_sample_ntt4_avx2(seeds = rdi, a = rsi, scratch = rdx) -> eax`,
with 24 bytes of stack below `rsp`. -/
def sample4K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 136⟩] ∧ s.wr = [⟨s.gpr .rsi, 4096⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 136⟩ ⟨s.gpr .rsi, 4096⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 136⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 4096⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 136⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 136⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rsi, 4096⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rsi).toNat + 4096 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 4).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
          then 1 else 0) ∧
      ∀ k < 4, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
        PolyIs s'.mem (poly4 (s.gpr .rsi) k) f
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 136 = bytesAt s₂.mem (s₂.gpr .rdi) 136

namespace S4

open VG.Impl.MlKem.X86_64.Sample4

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rsi
abbrev scr : Addr := σ.gpr .rdx
/-- Seed `k`. -/
abbrev B (k : Nat) : List Byte := seed4 σ.mem (sd σ) k
abbrev sdR : Region := ⟨sd σ, 136⟩
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

theorem pre_of {σ : State} (h : sample4K.pre σ) : Pre σ :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = scr σ
  r12 : s.gpr .r12 = sd σ
  r13 : s.gpr .r13 = aP σ
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
theorem sub_a {a n : Nat} (h : a + n ≤ 4096) : Region.Sub ⟨aP σ + BitVec.ofNat 64 a, n⟩ (aR σ) :=
  Offset.sub_base _ h

theorem in_scr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) : InRegions s.wr (at' σ a) n := by
  rw [hw, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_scr' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (at' σ a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_sd' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 136) :
    InRegions (s.rd ++ s.wr) (sd σ + BitVec.ofNat 64 a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨sdR σ, by simp, Offset.contains_base _ h (by omega)⟩

/-- The seeds are not written. -/
theorem seeds_frame {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {a : Nat} (ha : a < 136) :
    m (sd σ + BitVec.ofNat 64 a) = σ.mem (sd σ + BitVec.ofNat 64 a) :=
  hf.bytes (R := sdR σ) (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by simp) ha

/-- Byte `a` of seed `k`. -/
theorem seed_byte {m : Mem} (hf : Frame [aR σ, scrR σ, stkR σ] σ.mem m) {k a : Nat} (hk : k < 4) (ha : a < 34) :
    m (sd σ + BitVec.ofNat 64 (34 * k + a)) = (B σ k).getD a 0 := by
  rw [seeds_frame hp hf (by omega), B, seed4, ← Offset.add_add]
  simp [bytesAt, ha]

end

/-! ## The prologue -/

/-- A read of 8 bytes at `scratch + d` after a write of 8 elsewhere. -/
theorem rd64_off {σ : State} {m : Mem} {d e : Nat} {v : BitVec 64} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : (m.writeW (at' σ e) v).readW (at' σ d) 64 = m.readW (at' σ d) 64 :=
  readW_writeW_off m _ v (n := 8) (by omega) (by omega) h

theorem pro_eq : pro = [.store (at_ .rdx 4384) .rbx, .store (at_ .rdx 4392) .rbp, .store (at_ .rdx 4400) .r12,
    .store (at_ .rdx 4408) .r13, .store (at_ .rdx 4416) .r14, .mov .rbx (.reg .rdx), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rsi), .mov32 .r14 (.imm 1)] := rfl

/-- After the prologue. -/
structure I0 (σ s : State) : Prop where
  env : Env σ s
  r14 : s.gpr .r14 = 1

theorem pro_ok {σ : State} (hp : Pre σ) : WP isa (.block pro) σ (I0 σ) := by
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (at' σ 4384) (σ.gpr .rbx)).writeW (at' σ 4392) (σ.gpr .rbp)).writeW (at' σ 4400)
          (σ.gpr .r12)).writeW (at' σ 4408) (σ.gpr .r13)).writeW (at' σ 4416) (σ.gpr .r14) ∧
        s.gpr .rbx = scr σ ∧ s.gpr .r12 = sd σ ∧ s.gpr .r13 = aP σ ∧ s.gpr .r14 = 1)
    (by xrun [in_scr hp rfl (a := 4384) (n := 8) (by omega), in_scr hp rfl (a := 4392) (n := 8) (by omega),
      in_scr hp rfl (a := 4400) (n := 8) (by omega), in_scr hp rfl (a := 4408) (n := 8) (by omega),
      in_scr hp rfl (a := 4416) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨⟨k1.2.1, k1.2.2, hbx, h12, h13,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩, h14⟩
  · rw [hm1]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oSave, Mem.readW_writeW_self64, rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (scrR σ).Contains (at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega) (by omega)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 4384 (by omega))).writeW (by simp) _
      (hin 4392 (by omega))).writeW (by simp) _ (hin 4400 (by omega))).writeW (by simp) _
      (hin 4408 (by omega))).writeW (by simp) _ (hin 4416 (by omega)))

end S4

end VG.Proof.MlKem.X86_64
