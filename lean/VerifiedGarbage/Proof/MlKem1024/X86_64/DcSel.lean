import VerifiedGarbage.Proof.MlKem.X86_64.DcSel
import VerifiedGarbage.Proof.MlKem1024.X86_64.Frag
import VerifiedGarbage.Impl.MlKem1024.X86_64.Decaps

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_decaps`, the choice of the key

As for ML-KEM-768 (`Proof/MlKem/X86_64/DcSel.lean`, whose loop bodies, mask
and choice of the bytes of the key it shares), over the 1568 bytes of the
ciphertexts: the comparison (`cmp4_ok`) and the choice of the key
(`select4_ok`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

namespace Decaps4

open VG.Impl.MlKem.X86_64.Decaps VG.Impl.MlKem1024.X86_64.Decaps1024
open VG.Proof.MlKem.X86_64.Decaps

theorem cmp4_ok (s : State) {a b : Addr} (ha : InRegions (s.rd ++ s.wr) a 1568) (hb : InRegions (s.rd ++ s.wr) b 1568)
    (hsi : s.gpr .rsi = a) (hdi : s.gpr .rdi = b) (hdx : s.gpr .rdx = 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 1568) :
    WP isa (.loop cmpBody .ne) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdx = BitVec.setWidth 64 (accX (bytesAt s.mem a 1568) (bytesAt s.mem b 1568)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine wp_countdown (cnt := .rcx) (N := 1568) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = b + BitVec.ofNat 64 k ∧
      s'.gpr .rdx = BitVec.setWidth 64 (accX (bytesAt s.mem a k) (bytesAt s.mem b k)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', hdx', hm', hrd', hwr', kk⟩ _ => ?_) (fun _ ⟨_, _, h1, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, h1, h5⟩)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [hdx]; rfl, rfl, rfl, rfl, Keep.refl _ _⟩ hcx
  refine WP.mono (cmpBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte ha hk (by omega))
    (by rw [hrd', hwr', hdi']; exact inRegions_byte hb hk (by omega))) fun s'' ⟨⟨hm, hdx, hsi'', hdi'', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
        by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add], ?_, hm.trans hm',
        k'.2.1.trans hrd', k'.2.2.trans hwr', (kk.trans k').mono (by decide)⟩, hcx, hz⟩
  rw [hdx, hdx', hsi', hdi', hm', zx_or_xor, bytesAt_succ, bytesAt_succ,
    accX_snoc (by rw [bytesAt_length, bytesAt_length])]

abbrev setupB4 : List Instr := [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx),
  .alu .add .rdi (.imm (BitVec.ofNat 32 oCT4)), .mov32 .rcx (.imm 1568), .mov32 .rdx (.imm 0)]

theorem setup4_ok (s : State) :
    WP isa (.block setupB4) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rsi = pa s (.r14, 0) ∧ s'.gpr .rdi = pa s (sc oCT4) ∧
        s'.gpr .rcx = BitVec.ofNat 64 1568 ∧ s'.gpr .rdx = 0) ∧
      Keep [.rsi, .rdi, .rcx, .rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oCT4 < 2 ^ 31 by decide)]
  rw [pa, add_ofNat_zero]

theorem select4_ok {s : State} (hc : InRegions (s.rd ++ s.wr) (pa s (.r14, 0)) 1568)
    (hct : InRegions (s.rd ++ s.wr) (pa s (sc oCT4)) 1568) (hg : InRegions (s.rd ++ s.wr) (pa s (sc oG)) 32)
    (hkb : InRegions (s.rd ++ s.wr) (pa s (sc oKB)) 32) (hkey : InRegions s.wr (pa s (.r12, 0)) 32)
    (dg : Region.Disjoint ⟨pa s (sc oG), 32⟩ ⟨pa s (.r12, 0), 32⟩)
    (dkb : Region.Disjoint ⟨pa s (sc oKB), 32⟩ ⟨pa s (.r12, 0), 32⟩) :
    WP isa Decaps1024.select s fun s' => PPost s s' [((.r12, 0), 32)] ∧
      bytesAt s'.mem (pa s (.r12, 0)) 32 =
        if bytesAt s.mem (pa s (.r14, 0)) 1568 = bytesAt s.mem (pa s (sc oCT4)) 1568 then
          bytesAt s.mem (pa s (sc oG)) 32 else bytesAt s.mem (pa s (sc oKB)) 32 := by
  unfold Decaps1024.select
  refine WP.seq (WP.mono (setup4_ok s) fun s₁ ⟨⟨hm₁, hsi₁, hdi₁, hcx₁, hdx₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmp4_ok s₁ (by rw [k₁.2.1, k₁.2.2]; exact hc) (by rw [k₁.2.1, k₁.2.2]; exact hct) hsi₁ hdi₁
    hdx₁ hcx₁) fun s₂ ⟨hm₂, hrd₂, hwr₂, hdx₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok s₂) fun s₃ ⟨⟨hm₃, hax₃, hsi₃, hdi₃, h8₃, hcx₃⟩, k₃⟩ => ?_)
  have e12 : ∀ r ∈ [Reg.rbx, Reg.r12], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide),
      k₁.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have pG : pa s₂ (sc oG) = pa s (sc oG) := by rw [pa, pa, e12 .rbx (by simp)]
  have pKB : pa s₂ (sc oKB) = pa s (sc oKB) := by rw [pa, pa, e12 .rbx (by simp)]
  have pK : pa s₂ (.r12, 0) = pa s (.r12, 0) := by rw [pa, pa, e12 .r12 (by simp)]
  rw [pG] at hsi₃; rw [pKB] at hdi₃; rw [pK] at h8₃
  have hmem : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have hrd : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.2.1, k₃.2.2, hrd₂, hwr₂, k₁.2.1, k₁.2.2]
  have hwr : s₃.wr = s.wr := by rw [k₃.2.2, hwr₂, k₁.2.2]
  have hax : s₃.gpr .rax = if decide (bytesAt s.mem (pa s (.r14, 0)) 1568 = bytesAt s.mem (pa s (sc oCT4)) 1568) then
      BitVec.allOnes 64 else 0 := by
    rw [hax₃, hdx₂, hm₁, ← hsi₁, ← hdi₁, hsi₁, hdi₁]
    exact ite_congr (propext (zx_eq_zero.trans ((eq_iff_foldl_or_xor (by rw [bytesAt_length, bytesAt_length])).symm.trans
      decide_eq_true_iff.symm))) (fun _ => rfl) (fun _ => rfl)
  refine WP.mono (sel_ok s₃ _ (by rw [hrd]; exact hg) (by rw [hrd]; exact hkb) (by rw [hwr]; exact hkey) dg dkb hsi₃
    hdi₃ h8₃ hax hcx₃) fun s₄ ⟨hb, hf, k₄⟩ => ⟨?_, ?_⟩
  · refine post_of_keep ((((k₁.trans k₂).trans k₃).trans k₄).mono (rs' := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10])
      (by decide)) (by decide) ?_
    rw [← hmem]; exact hf
  · rw [hb, hmem]
    simp only [decide_eq_true_eq]

end Decaps4

end VG.Proof.MlKem1024.X86_64
