import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Impl.MdStream.X86
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! The framed single-block compression proof, independent of backend. -/
namespace VG.Proof.Sha256.X86.Stream
open VG.X86
open VG.X86.RegUpd
open VG.Spec.Sha256 (stateAt compress blockAt)
variable {name : String} {code : Prog isa}
  (hv : Verified X86.target code Proof.Sha256.compressX86)
  (hnosp : NoSp code) (hstack : stackUse code = 0)
include hv hnosp hstack

theorem compressAt_of {sr cr : Reg} (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) (hsr' : sr ≠ .ecx)
    (hcr' : cr ≠ .ecx) {s : State} {st scr blk E : BitVec 32}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : blk.toNat + 64 ≤ 2 ^ 32)
    (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, 32⟩ ⟨scr.setWidth 64, 112⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨st.setWidth 64, 32⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, 64⟩ ⟨scr.setWidth 64, 112⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, 32⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, 112⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, 64⟩)
    (hc : Covers [⟨blk.setWidth 64, 64⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, below E 20] s.mem s'.mem →
      stateAt s'.mem (st.setWidth 64) =
        compress (stateAt s.mem (st.setWidth 64)) (blockAt s.mem (blk.setWidth 64)) → Q s') :
    WP isa (Impl.MdStream.X86.compressAt name code sr cr) s Q := by
  unfold Impl.MdStream.X86.compressAt Impl.MdStream.X86.compressWith
  refine WP.seq (WP.cons (s' := s.setReg .ecx 1) rfl (WP.block_nil ?_))
  set s₁ := s.setReg .ecx 1 with hs₁
  have g₁ : ∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h => by rw [hs₁, gpr_setReg_of_ne s 1 h]
  have fit : 4 * [cr, Reg.ecx, .eax, sr].length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [g₁ _ (by decide), hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [cr, Reg.ecx, .eax, sr] := by simp [Ne.symm hsr, Ne.symm hcr]
  set sE := (pushed [cr, Reg.ecx, .eax, sr] s₁).callEntry with hsE
  have a0 : arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ _ hsr', hS]
  have a1 : arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ Reg.eax (by decide), heax]
  have a2 : arg sE 2 = 1 := by rw [hsE, callEntry_arg fit hrs (by simp)]; change s₁.gpr .ecx = 1; rw [hs₁, gpr_setReg_self]
  have a3 : arg sE 3 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [g₁ _ hcr', hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, g₁ _ (by decide), hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', g₁ _ (by decide), hesp]; rfl
  have b16 : Region.Sub (below E 16) (below E 20) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below E 20) := by
    have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) hE
    rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have hesp₁ : s₁.gpr .esp = E := by rw [g₁ _ (by decide), hesp]
  refine WP.callWith (k := Proof.Sha256.compressX86) hv.1 hnosp (by simp) hrs
    (by rw [hstack, hesp₁]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, 64 * (1 : BitVec 32).toNat⟩, ⟨argAddr sE 0, 16⟩])
    (wr := [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [Proof.Sha256.compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b16, dC.sub_left b16,
      dS.sub_left r4, dC.sub_left r4, f₀, by simpa using f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp₁]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hc a n ⟨_, List.mem_singleton_self _, by simpa using hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      simp only [Region.Contains] at hcn ⊢
      simpa using hcn
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · rw [hesp₁]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [hstack, hesp₁] at f'
    have hsE' : Frame [below E 20] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp₁] at this; exact this
    rw [← hsE] at post
    simp only [Proof.Sha256.compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂,
      show (1 : BitVec 32).toNat = 1 from rfl, compressBlocks_one] at post
    rw [hs₁] at f'
    refine hQ s' rd' wr' (fun r hr => ?_) (by
      change Frame [⟨st.setWidth 64, 32⟩, ⟨scr.setWidth 64, 112⟩, below E 20] s.mem s'.mem at f'
      exact f') ?_
    · rw [cs' r hr, g₁ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    · have e₁ : stateAt sE.mem (st.setWidth 64) = stateAt s.mem (st.setWidth 64) :=
        Proof.Sha256.Stream.stateAt_congr fun i hi =>
          hsE'.bytes (R := ⟨st.setWidth 64, 32⟩) (by simpa using dS.symm) (by simp) hi
      have e₂ : blockAt sE.mem (blk.setWidth 64) = blockAt s.mem (blk.setWidth 64) := by
        simp only [blockAt]
        exact Proof.Sha256.Stream.parseBlock_congr fun k hk =>
          hsE'.bytes (R := ⟨blk.setWidth 64, 64⟩) (by simpa using dB.symm) (by simp) hk
      rw [post, e₁, e₂]


end VG.Proof.Sha256.X86.Stream
