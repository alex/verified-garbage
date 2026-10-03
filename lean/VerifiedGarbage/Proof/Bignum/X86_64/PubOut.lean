import VerifiedGarbage.Proof.Bignum.X86_64.PubExp

/-!
# `vg_rsa_public` on x86-64: the result

The result, masked, to `out`; the mask's low bit returned; the saved
registers restored (`outPhase_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- The steps of the result. -/
def outSteps : List (Prog isa) := [
  .block [.mov .rbx (.mem (hdr (sArr aY))), .mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)),
    .mov .r15 (.mem (hdr sMask))],
  storeBE,
  .block ([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] ++ exit)]

theorem exit_eq : exit = [.mov .rbx (.mem (hdr 0)), .mov .rbp (.mem (hdr 1)), .mov .r12 (.mem (hdr 2)),
    .mov .r13 (.mem (hdr 3)), .mov .r14 (.mem (hdr 4)), .mov .r15 (.mem (hdr 5))] := rfl

theorem mask_and1 (c : Bool) : mask c &&& 1 = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- A byte of the working space is not one of `out`'s. -/
theorem scr_ne_out {B out : Addr} {Z k : Nat} (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    {d i : Nat} (hd : d + i < Z) (hZ : Z ≤ 2 ^ 64) :
    ∀ j < k, off B d + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro j hj he
  have h := hsep j hj
  rw [← he, ofs_off B (by omega)] at h
  omega

/-- The result: `i2osp (c ? Y : 0)` to `out`, `c` returned, and the saved
registers restored from the header. -/
theorem outPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs outSteps) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold outSteps
  refine WP.seq (WP.mono (WP.keep [.rbx, .rsi, .rcx, .r15] (Q := fun t =>
      t.gpr .rbx = off B (slot ((k + 7) / 8) aY) ∧ t.gpr .rsi = out ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.gpr .r15 = mask c ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) rfl)
    fun t₁ ⟨⟨hbx, hsi, hcx, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (storeBE_ok hs₁ hbx hsi hcx h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) (show aY < 8 by decide); omega)
    (fun j hj => by rw [k₁.2.2]; exact hout j hj) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (scr_ne_out hsep (d := 8 * i) (i := b) (by omega) (by omega)), hm₁]
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.2.1, k₁.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = BitVec.ofNat 64 c.toNat ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sMask (by decide), hw₂ sMask (by decide), hM, mask_and1,
      hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide), hl₂ 3 (by decide), hl₂ 4 (by decide),
      hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide), hw₂ 2 (by decide), hw₂ 3 (by decide),
      hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hax, ?_,
      fun x hx => by rw [hm, hf₂ x hx, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Bignum.X86_64
