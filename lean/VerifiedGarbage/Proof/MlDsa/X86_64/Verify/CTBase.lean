import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
import VerifiedGarbage.Proof.MlKem.X86_64.Rel

/-!
# ML-DSA verification on x86-64: constant time, the pieces without calls

Untrusted: everything here is checked by Lean. Two runs from inputs with
the same public data (`RV`) keep the same pointers (`T.lrel`). A block
that accesses no memory, followed by code that the taint analysis checks
from the registers it sets (`blockLoop_tr`), leaks the same in both: the
copy (`copy_tr`), the mask of a sampler's output (`mask_tr`) and the
comparison (`cmpAnd_tr`). The rest is checked by the taint analysis.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Spec.MlDsa

/-- Two runs from states satisfying `VPre p` with the same public data, each
satisfying `I` from its own initial state. -/
abbrev RV (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (VPre p) (verifyK p).pub I

theorem T.sameB {p : Params} {σ₁ σ₂ x y : State} (pub : (verifyK p).pub σ₁ σ₂) (h₁ : T p σ₁ x) (h₂ : T p σ₂ y) :
    SameB x y := by
  refine ⟨fun r hr => ?_, by rw [h₁.rsp, h₂.rsp, pub.2.2.2.2.1]⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]
  · rw [h₁.rbp, h₂.rbp, pub.1]
  · rw [h₁.r12, h₂.r12, pub.2.1]
  · rw [h₁.r13, h₂.r13, pub.2.2.1]

theorem RV.lrel {p : Params} (hp : p ∈ params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → T p σ s)
    {x y : State} (h : RV p I x y) : LRel (vR p) (vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩ := h
  exact ⟨(hI _ _ i₁).lay hp v₁, (hI _ _ i₂).lay hp v₂, T.sameB pub (hI _ _ i₁) (hI _ _ i₂)⟩

/-! ## A block without memory accesses, then code the taint analysis checks -/

theorem blockLoop_tr {B : List Instr} {L : Prog isa} {P : State → State → Prop}
    (hB : ∀ i ∈ B, ∀ s, isa.addrs i s = []) {F : State → State → Prop}
    (hw : ∀ x y, P x y → WP isa (.block B) x (F x) ∧ WP isa (.block B) y (F y)) (rs : List Reg)
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → ∀ r ∈ rs, x'.gpr r = y'.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T} (h : (taint.check (X86_64.Taint.ofRegs rs) L hc).isSome = true) :
    RelCT isa P (.seq (.block B) L) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (block_nomem_tr hB) hw hQ) (taintRel rs (fun _ _ h => h) h)

theorem SameB.arg {x y : State} (h : SameB x y) {p : Ptr} (hp : p.1 ∈ bases) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.pa hp

theorem copy_tr {dst src : Ptr} {n : Nat} (hok : ∀ a ∈ copyArgs dst src n, a.2.Ok ∧ a.1 ∈ argRegs)
    (hd : dst.1 ∈ bases) (hs : src.1 ∈ bases) {P : State → State → Prop} (hP : ∀ x y, P x y → SameB x y) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  have nd : ((copyArgs dst src n).map (·.1)).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  unfold copy
  refine blockLoop_tr (glue_nomem _) (fun x y _ => ⟨glue_ok' hok nd x, glue_ok' hok nd y⟩) [.rdi, .rsi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  have e := hP x y hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [hx.1.1 _ (List.mem_cons_self ..), hy.1.1 _ (List.mem_cons_self ..)]; exact e.arg hd
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]; exact e.arg hs
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))]; rfl

theorem maskPre_wp {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) (s : State) :
    WP isa (.block (([.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax)] : List Instr) ++
      glue [(.rdi, .ptr a), (.rcx, .imm 256)])) s
      fun s' => s'.gpr .rdi = (Arg.ptr a).val s ∧ s'.gpr .rcx = BitVec.ofNat 64 256 := by
  have hok' : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm 256)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨hok, by decide⟩, ⟨show 256 < 2 ^ 31 by decide, by decide⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (maskPre_ok s) fun s₀ ⟨_, k₀⟩ => ?_
  refine WP.mono (glue_ok _ hok' (by simp only [List.map_cons, List.map_nil]; decide) s₀) fun s1 ⟨⟨hv1, _⟩, _⟩ =>
    ⟨?_, hv1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  have nb : a.1 ∉ [Reg.rdx] := by
    simp only [List.mem_singleton]; intro h; rw [h] at hb; exact absurd hb (by decide)
  rw [hv1 _ (List.mem_cons_self ..)]
  simp only [Arg.val, pa]
  rw [k₀.gpr nb]

theorem mask_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) {P : State → State → Prop}
    (hP : ∀ x y, P x y → SameB x y) : RelCT isa P (mask a) fun _ _ => True := by
  unfold mask
  refine blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨maskPre_wp hok hb x, maskPre_wp hok hb y⟩) [.rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> rfl
    · exact glue_nomem _ i h s
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg hb
    · rw [hx.2, hy.2]

theorem cmpPre_wp {a b : Ptr} {n : Nat} (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ argRegs) (s : State) :
    WP isa (.block (glue [(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] ++ ([.mov32 .rdx (.imm 0)] : List Instr))) s
      fun s' => s'.gpr .rsi = (Arg.ptr a).val s ∧ s'.gpr .rdi = (Arg.ptr b).val s ∧
        s'.gpr .rcx = (Arg.imm n).val s := by
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (by decide)) fun s2 ⟨_, k2⟩ => ⟨?_, ?_, ?_⟩
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem cmpAnd_tr {a b : Ptr} {n : Nat}
    (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs)
    (ha : a.1 ∈ bases) (hb : b.1 ∈ bases) {P : State → State → Prop} (hP : ∀ x y, P x y → SameB x y) :
    RelCT isa P (cmpAnd a b n) fun _ _ => True := by
  unfold cmpAnd
  refine blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨cmpPre_wp hok x, cmpPre_wp hok y⟩) [.rsi, .rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · exact glue_nomem _ i h s
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg ha
    · rw [hx.2.1, hy.2.1]; exact (hP x y hp).arg hb
    · rw [hx.2.2, hy.2.2]; rfl

/-! ## Blocks the taint analysis checks -/

theorem setB2_tr {x y : Nat} {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rbx = s₂.gpr .rbx) :
    RelCT isa P (.block (setB (sc (oSB + 32)) x ++ setB (sc (oSB + 33)) y)) fun _ _ => True :=
  taintRel [.rbx] (fun s₁ s₂ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hP s₁ s₂ h)
    (hc := .block []) (by with_unfolding_all rfl)

theorem and15_tr {P : State → State → Prop} : RelCT isa P (.block and15) fun _ _ => True :=
  block_nomem_tr fun i hi s => by simp only [and15, List.mem_singleton] at hi; subst hi; rfl

theorem pro_tr {p : Params} : RelCT isa (RV p fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    subst h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [pub.2.2.2.1, pub.1, pub.2.1, pub.2.2.1]) (by taint_decide)

theorem epi_tr {p : Params} : RelCT isa (RV p (T p)) (.block epi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Verify
