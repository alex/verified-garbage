import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# TDEA-CMAC on x86: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/X86/Taint.lean`) checks that only the stack arguments, which are
public, decide branches and addresses. The functions keep their pointers
and counts in the scratch buffer, the second writable region: the analysis
knows the stack argument holding it is that region's base, so `ebp`, loaded
from it, addresses public words there, and the block's counters and step
are stored and loaded through it.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

/-- `init`'s initial taint: the stack arguments are public; `out` and
`scratch` are the bases of the writable regions. -/
def initTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [400, 640], argLen := 20, argBases := [(12, 0), (16, 1)] }

/-- `update`'s and `finalize`'s: the stack arguments are public; `state` and
`scratch` are the bases of the writable regions. -/
def streamTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8, 640], argLen := 24, argBases := [(8, 0), (20, 1)] }

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

/-! ## `init` -/

theorem init_wf {s : State} (h : initX86.pre s) : VG.X86.Taint.Wf initTaint s := by
  have hp := IPre.of h
  have := hp.out_fit; have := hp.scr_fit; have := hp.esp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, initTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [initTaint]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_scr
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.args_scr
  · intro p hp'
    simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [initTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem init_ct : ConstantTime isa initX86.pre initX86.pub init := by
  refine VG.Taint.constantTime (A := taint) initTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have hp₁ := IPre.of h₁; have hp₂ := IPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, init_wf h₁, init_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 20) hp₁.esp_fit hp₂.esp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [outR, iscrR, O, Sc, ha 2 (by omega), ha 3 (by omega)]

/-! ## `update` and `finalize` -/

/-- The state and the scratch buffer, the writable regions of `update` and
`finalize`, from their stack arguments. -/
abbrev streamWr (s : State) : List Region := [⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 640⟩]

theorem streamTaint_wf {s : State} (hwr : s.wr = streamWr s)
    (st_scr : Region.Disjoint ⟨(arg s 1).setWidth 64, 8⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (ret_st : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 8⟩)
    (ret_scr : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (args_st : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 1).setWidth 64, 8⟩)
    (args_scr : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (st_fit : (arg s 1).toNat + 8 ≤ 2 ^ 32) (scr_fit : (arg s 4).toNat + 640 ≤ 2 ^ 32)
    (esp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) : VG.X86.Taint.Wf streamTaint s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hwr, streamTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [streamTaint]; omega, ?_⟩, ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact st_scr
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) ret_st args_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) ret_scr args_scr
  · intro p hp'
    simp only [streamTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [streamTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

/-- Two runs agree on `streamTaint` when they agree on the stack arguments. -/
theorem streamTaint_agree {s₁ s₂ : State} (w₁ : VG.X86.Taint.Wf streamTaint s₁)
    (w₂ : VG.X86.Taint.Wf streamTaint s₂) (hw₁ : s₁.wr = streamWr s₁) (hw₂ : s₂.wr = streamWr s₂)
    (f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32) (f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i < 5, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree streamTaint s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, w₁, w₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 24) f₁ f₂ (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [streamTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hw₁, hw₂]; simp only [streamWr, ha 1 (by omega), ha 4 (by omega)]

theorem update_ct : ConstantTime isa updateX86.pre updateX86.pub update := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := UPre.of h₁; have p₂ := UPre.of h₂
  exact streamTaint_agree
    (streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub finalize := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := FPre.of h₁; have p₂ := FPre.of h₂
  exact streamTaint_agree
    (streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

end VG.Proof.CmacTripleDes.X86
