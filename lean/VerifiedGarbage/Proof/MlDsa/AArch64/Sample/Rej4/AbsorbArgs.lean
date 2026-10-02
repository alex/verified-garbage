import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Pro

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (Only wp_addImm)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbArgs)

theorem absorbArgs_ok {s : State} {p : Nat} (hp : p < 2) :
    WP isa (.block (absorbArgs p)) s fun t => Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2 = s.gpr .x19+BitVec.ofNat 64 (400*p) ∧
      t.gpr .x3 = s.gpr .x20+BitVec.ofNat 64 (68*p) ∧
      t.gpr .x4 = s.gpr .x20+BitVec.ofNat 64 (68*p+34) := by
  unfold absorbArgs
  refine wp_addImm (by omega) fun s1 h1 e1 => wp_addImm (by omega) fun s2 h2 e2 =>
    wp_addImm (by decide) fun t h3 e3 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((h1.trans h2).trans h3).mono (by simp)
  · rw [h3.get .x2,h2.get .x2,e1]
  · rw [h3.get .x3,e2,h1.get .x20]
  · rw [e3,e2,h1.get .x20,Offset.add_add]

/-- Initialize both pairs while retaining the saved ABI registers. -/
theorem zeroAll_ok {σ s : State} (hp : Pre σ) (he : Env σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => Env σ t ∧
      ∀ i < 50,t.mem.read (wordAddr (scr σ) i) 16 = 0 := by
  refine WP.mono (zeros_ok he.x19 (fun i hi => in_scr hp he.wr (by omega))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩
end VG.Proof.MlDsa.AArch64.Sample.Rej4
