import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on whole blocks, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `scratch`
from the stack gives both the same pointer (`rel_r11`), after which the taint
analysis checks the piece from it and `rsp`; the interleaved loops are checked
from the arguments in their registers; the branch on the blocks left agrees
(`tailHead_ok`); and the calls get the same public arguments (`ctr_rel`,
`gh_rel`), from what correctness says of each run (`rel_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `scratch`, loaded from the stack into `r11`. -/
theorem loadR11_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 8))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadR11_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 8))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `scratch` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_r11 {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 8))] : List Instr) ++ l) (rs rs' : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 8) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 8) 8)
    (hc : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).map fun τ' =>
      (RegSet.ofList rs').subset τ'.regs && (!false || τ'.flags)) = some true) :
    RelCT isa P (.block l₀) fun s₁ s₂ => ∀ r ∈ rs', s₁.gpr r = s₂.gpr r := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) loadR11_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨loadR11_ok (hS _ _ h).2.1, loadR11_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ ((rel_regs (.r11 :: rs) rs' false (fun s₁ s₂ h r hr => ?_) hc).mono
    (fun _ _ h => h) fun _ _ h => h.1))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

section
variable {s : State} (hp : BP s)
include hp

/-- `Ready` after `ctrCall`. -/
theorem ctrCall_ready (c : Ctr32Impl) {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (ctrCall ⟨c.callee.name, c.callee.code⟩) st (Ready s q) :=
  WP.seq (WP.mono (ctrArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (ctr_call c hc) fun st₃ g => by
    have f₃ := g.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (apart_kR' hp (q := q) (by omega)).ctr r hr) (fun r hr => (apart_a hp (q := q) (by omega)).ctr r hr)
      (g.saved _ (by decide)) g.rd g.wr)

/-- `Ready` after `ghCall`. -/
theorem ghCall_ready (g : GhashImpl) {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (ghCall g.fn) st (Ready s q) :=
  WP.seq (WP.mono (ghArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (gh_call g hc) fun st₃ g' => by
    have f₃ := g'.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (apart_kR' hp (q := q) (by omega)).gh r hr) (fun r hr => (apart_a hp (q := q) (by omega)).gh r hr)
      (g'.saved _ (by decide)) g'.rd g'.wr)

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : K s₀' = K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  c : C s₀' = C s₀
  y : Y s₀' = Y s₀
  d : D s₀' = D s₀
  r9 : s₀'.gpr .r9 = s₀.gpr .r9
  sp : SP s₀' = SP s₀
  sc : S s₀' = S s₀

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.blocksPub s₀ s₀') : Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.symm⟩

theorem Pub.en {s₀ s₀' : State} (pb : Pub s₀ s₀') : n s₀' = n s₀ := by simp only [n, pb.r9]
theorem Pub.eR {s₀ s₀' : State} (pb : Pub s₀ s₀') : R s₀' = R s₀ := by simp only [R, pb.rsi]
theorem Pub.edq {s₀ s₀' : State} (pb : Pub s₀ s₀') (q : Nat) : dq s₀' q = dq s₀ q := by simp only [dq, pb.d]
theorem Pub.es5 {s₀ s₀' : State} (pb : Pub s₀ s₀') : S5 s₀' = S5 s₀ := by simp only [S5, pb.sc]

theorem tailHead_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)]) hc).map fun τ' =>
      (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).map fun τ' =>
    (RegSet.ofList (.r11 :: args)).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem rest_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block rest.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem stitchE_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (stitchPart Impl.Gcm.X86_64.Stitch.enc) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem stitchD_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (stitchPart Impl.Gcm.X86_64.Stitch.dec) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ctrArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ctrArgs.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ghArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.r11, .rsp]) (.block ghArgs.tail) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hp : BP s₀) (hp' : BP s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- Loading `scratch` from the stack, in two runs that are `Ready`. -/
theorem ready_hS {q q' : Nat} {s₁ s₂ : State} (h₁ : Ready s₀ q s₁) (h₂ : Ready s₀' q' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 8) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 8) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 8) 8 := by
  refine ⟨by rw [h₁.rsp, h₂.rsp, h₁.arg, h₂.arg, pb.sc], ?_, ?_⟩
  · rw [h₁.rd, h₁.wr, h₁.rsp]; exact a_in hp
  · rw [h₂.rd, h₂.wr, h₂.rsp]; exact a_in hp'

omit hp hp' in
theorem ready_rsp {q q' : Nat} {s₁ s₂ : State} (h₁ : Ready s₀ q s₁) (h₂ : Ready s₀' q' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.sp]

/-- `ctrCall`, in two runs `Ready` for the same blocks left. -/
theorem ctrCall_rel (c : Ctr32Impl) {q : Nat} (hq : q < n s₀) :
    RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) (ctrCall ⟨c.callee.name, c.callee.code⟩)
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂ := by
  have hq' : q < n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (rel_r11 (l₀ := ctrArgs) (l := ctrArgs.tail) rfl (P := fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) [.rsp] [.rsp]
      (by simp) (fun _ _ h => ready_rsp pb h.1 h.2) (fun _ _ h => ready_hS hp hp' pb h.1 h.2) ctrArgs_check)
    (fun _ _ h => h) (G₁ := fun st' => CtrCall st' (K s₀) (C s₀) (dq s₀ q) (S5 s₀) (R s₀) (n s₀ - q) ∧ Ready s₀ q st')
    (G₂ := fun st' => CtrCall st' (K s₀') (C s₀') (dq s₀' q) (S5 s₀') (R s₀') (n s₀' - q) ∧ Ready s₀' q st')
    (fun _ h => WP.mono (ctrArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (ctrArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (ctr_rel c fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => ctrCall_ready hp c h hq)
    (fun _ h => ctrCall_ready hp' c h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨hr, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.c, pb.edq, pb.es5, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `ghCall`, in two runs `Ready` for the same blocks left. -/
theorem ghCall_rel (g : GhashImpl) {q : Nat} (hq : q < n s₀) :
    RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) (ghCall g.fn)
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂ := by
  have hq' : q < n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (rel_r11 (l₀ := ghArgs) (l := ghArgs.tail) rfl (P := fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) [.rsp] [.rsp]
      (by simp) (fun _ _ h => ready_rsp pb h.1 h.2) (fun _ _ h => ready_hS hp hp' pb h.1 h.2) ghArgs_check)
    (fun _ _ h => h) (G₁ := fun st' => GhCall st' (K s₀ + BitVec.ofNat 64 240) (Y s₀) (dq s₀ q) (S5 s₀) (n s₀ - q) ∧ Ready s₀ q st')
    (G₂ := fun st' => GhCall st' (K s₀' + BitVec.ofNat 64 240) (Y s₀') (dq s₀' q) (S5 s₀') (n s₀' - q) ∧
      Ready s₀' q st')
    (fun _ h => WP.mono (ghArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (ghArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (gh_rel g fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => ghCall_ready hp g h hq)
    (fun _ h => ghCall_ready hp' g h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨hr, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.y, pb.edq, pb.es5, pb.en] at c₂
  exact ⟨_, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel {first second : Prog isa}
    (h₁ : ∀ q, q < n s₀ → RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) first
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂)
    (h₂ : ∀ q, q < n s₀ → RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) second
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂)
    {q : Nat} {ys ys' : List Block} :
    RelCT isa (fun s₁ s₂ => Mid s₀ q q ys s₁ ∧ Mid s₀' q q ys' s₂) (tail first second) fun _ _ => True := by
  have a := rel_wp (rel_r11 (l₀ := [.mov .r11 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r11 argN)),
      .alu .test .r8 (.reg .r8)]) (l := [.mov .r8 (.mem (at_ .r11 argN)), .alu .test .r8 (.reg .r8)]) rfl
      (P := fun s₁ s₂ => Mid s₀ q q ys s₁ ∧ Mid s₀' q q ys' s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => ready_rsp pb (h.1.ready hp) (h.2.ready hp'))
      (fun _ _ h => ready_hS hp hp' pb (h.1.ready hp) (h.2.ready hp')) tailHead_check)
    (fun _ _ h => h) (fun _ h => tailHead_ok hp h) (fun _ h => tailHead_ok hp' h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) ⟨_, by taint_decide⟩).mono (fun _ _ h => h) fun _ _ h => h
  · by_cases hlt : q < n s₀
    · exact (RelCT.seq (h₁ q hlt) (h₂ q hlt)).mono (fun _ _ h => ⟨h.1.2.1.1.ready hp, h.1.2.2.1.ready hp'⟩)
        fun _ _ _ => trivial
    · intro s₁ s₂ _ _ _ _ h
      have e := h.1.2.1.2
      rw [h.2] at e
      simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at e
      exact absurd (by omega) e

/-- What the entry leaves. -/
def EntryPost (s₀ s₁ : State) : Prop :=
  s₁.gpr .r11 = S s₀ ∧ (∀ r, r ≠ .r11 → s₁.gpr r = s₀.gpr r) ∧ Kept s₀ 0 s₁.mem ∧ Frame [kR' s₀] s₀.mem s₁.mem ∧
    s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.c.symm, pb.y.symm, pb.d.symm, pb.r9.symm, pb.sp.symm]
  refine rel_wp (rel_r11 (l₀ := entry) (l := entry.tail) rfl args (.r11 :: args) (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [arg_eq, arg_eq, pb.sc], a_in hp, a_in hp'⟩) entry_check)
    (fun _ _ h => h) (fun s h => by subst h; exact entry_ok hp) (fun s h => by subst h; exact entry_ok hp')

/-- The interleaved part (or nothing) and `rest`, in two runs. -/
theorem part_rel (stitch : Bool) (piece : Prog isa) {ys : State → Nat → List Block}
    (hys : ∀ s, ys s 0 = [])
    (hc : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args)) (stitchPart piece) hc).map
      fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true)
    (hw : ∀ {s : State}, BP s → ∀ {s₁ : State}, EntryPost s s₁ →
      WP isa (stitchPart piece) s₁ (Mid s (n s - n s % 16) 0 (ys s (n s - n s % 16)))) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧ EntryPost s₀' s₂)
      (if stitch then .seq (stitchPart piece) (.block rest) else .block [])
      fun s₁ s₂ => ∃ q, Mid s₀ q q (ys s₀ q) s₁ ∧ Mid s₀' q q (ys s₀' q) s₂ := by
  cases stitch
  · refine ((rel_regs (.r11 :: args) [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := Mid s₀ 0 0 (ys s₀ 0)) (F₂ := Mid s₀' 0 0 (ys s₀' 0)) fun s₁ s₂ h => ⟨WP.block_nil ?_,
        WP.block_nil ?_⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
    · obtain ⟨-, ⟨-, b, c, d, e, f⟩, -⟩ := h; rw [hys]; exact mid_entry hp b c d e f
    · obtain ⟨-, -, ⟨-, b, c, d, e, f⟩⟩ := h; rw [hys]; exact mid_entry hp' b c d e f
  · have a := rel_wp (P := fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧
        EntryPost s₀' s₂) (rel_regs (.r11 :: args) [.rsp] false (fun _ _ h => h.1) hc) (fun _ _ h => h.2)
      (fun _ h => hw hp h) (fun _ h => hw hp' h)
    have b := rel_wp (rel_r11 (l₀ := rest) (l := rest.tail) rfl
      (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
        Mid s₀ (n s₀ - n s₀ % 16) 0 (ys s₀ (n s₀ - n s₀ % 16)) s₁ ∧
        Mid s₀' (n s₀' - n s₀' % 16) 0 (ys s₀' (n s₀' - n s₀' % 16)) s₂) [.rsp] [.rsp] (by simp)
      (fun _ _ h => h.1) (fun _ _ h => ready_hS hp hp' pb (h.2.1.ready hp) (h.2.2.ready hp')) rest_check)
      (fun _ _ h => h.2) (fun _ h => rest_ok hp rfl h) (fun _ h => rest_ok hp' rfl h)
    refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
      fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
    rw [← pb.en]; exact h.2.2

end

theorem encrypt_ct (v : GcmImpl) (stitch : Bool) :
    ConstantTime isa Proof.AesGcm.encryptBlocksX86_64.pre Proof.AesGcm.encryptBlocksX86_64.pub
      (encrypt v.callees.ctr v.callees.gh stitch) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb stitch Impl.Gcm.X86_64.Stitch.enc
    (ys := fun s q => ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) (fun _ => rfl) stitchE_check
    fun {_} hp {_} h => by obtain ⟨a, b, c, d, e, f⟩ := h; exact stitchE_ok hp a b c d e f) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb (fun q hq => ctrCall_rel hp hp' pb v.ctr hq) (fun q hq => ghCall_rel hp hp' pb v.gh hq)
    _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

theorem decrypt_ct (v : GcmImpl) (stitch : Bool) :
    ConstantTime isa Proof.AesGcm.decryptBlocksX86_64.pre Proof.AesGcm.decryptBlocksX86_64.pub
      (decrypt v.callees.ctr v.callees.gh stitch) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (part_rel hp hp' pb stitch Impl.Gcm.X86_64.Stitch.dec
    (ys := fun s q => blocksAt s.mem (D s) q) (fun _ => rfl) stitchD_check
    fun {_} hp {_} h => by obtain ⟨a, b, c, d, e, f⟩ := h; exact stitchD_ok hp a b c d e f) ?_)
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
  exact tail_rel hp hp' pb (fun q hq => ghCall_rel hp hp' pb v.gh hq) (fun q hq => ctrCall_rel hp hp' pb v.ctr hq)
    _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.Blocks
