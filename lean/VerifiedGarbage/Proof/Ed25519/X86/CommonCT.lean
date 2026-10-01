import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish
import VerifiedGarbage.Proof.Framework.X86.Taint

namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarTaint (scidx argc : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 8192], argLen := 4 + 4 * argc,
    argBases := [(4, 0), (4 + 4 * scidx, 1)] }

theorem scalarTaint_wf {s : State} {scidx argc : Nat} (hp : ScratchPre s scidx argc)
    (ho : OutputPre s scidx)
    (hw : s.wr = [⟨(arg s 0).setWidth 64, 32⟩, scR (arg s scidx)])
    (hao : (⟨argAddr s 0, 4 * argc⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 32⟩) :
    VG.X86.Taint.Wf (scalarTaint scidx argc) s := by
  have hf := hp.fit; have ofit := ho.fit; have spfit := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, scalarTaint], by simpa [hw] using ho.sep, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by change (s.gpr .esp).toNat + (4 + 4 * argc) ≤ 2 ^ 32; omega_using [spfit], ?_⟩, ?_⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hf, ofit]
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) ho.ret hao
    · exact VG.X86.Taint.frame_disjoint (n := 4 * argc) (by omega_using [spfit]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [scalarTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by dsimp only [scalarTaint]; have := hp.index; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]
    · refine ⟨by dsimp only [scalarTaint]; have := hp.index; omega_using [this], ?_⟩
      simp [VG.X86.Taint.region, hw, VG.X86.addr, arg, argAddr]

theorem scalarTaint_agree {s t : State} {scidx argc : Nat}
    (hs : VG.X86.Taint.Wf (scalarTaint scidx argc) s) (ht : VG.X86.Taint.Wf (scalarTaint scidx argc) t)
    (hsp : s.gpr .esp = t.gpr .esp) (ha : ∀ i < argc, arg s i = arg t i)
    (hi : scidx < argc)
    (hws : s.wr = [⟨(arg s 0).setWidth 64, 32⟩, scR (arg s scidx)])
    (hwt : t.wr = [⟨(arg t 0).setWidth 64, 32⟩, scR (arg t scidx)])
    (hss : (s.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32)
    (hst : (t.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32) :
    VG.X86.Taint.Agree (scalarTaint scidx argc) s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, hs, ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hsp,
    fun k h4 hk => ?_⟩
  · simp only [scalarTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hsp
  · rw [hws, hwt, ha 0 (by omega_using [hi]), ha scidx hi]
  · simp only [scalarTaint] at hk
    rw [show VG.X86.Taint.depth (scalarTaint scidx argc).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by omega_using [hss]) h4 hk,
      VG.X86.Taint.argByte_eq (by omega_using [hst]) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega_using [hk, h4]))
end VG.Proof.Ed25519.X86
