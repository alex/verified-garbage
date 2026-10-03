import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM on whole blocks, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments load the same `scratch` from the stack (`load_ok`) and
push the same frame; in it, every address is `rsp` plus a constant or comes
from the arguments in their registers, which the taint analysis checks: the
interleaved loops from the arguments, the rest from `rsp`. The branch on the
blocks left agrees (`tailHead_ok`), and the calls get the same public
arguments (`ctr_rel`, `gh_rel`), from what correctness says of each run
(`rel_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Spec.Gcm (Block blockAt blocksAt ctr32)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

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
theorem Pub.eF {s₀ s₀' : State} (pb : Pub s₀ s₀') : F s₀' = F s₀ := by simp only [F, pb.sp]

/-- What the frame's push leaves, from `s`. -/
def PushPost (s p : State) : Prop :=
  p.gpr .rsp = F s ∧ p.gpr .r11 = S s ∧ (∀ r, r ≠ .r11 → r ≠ .rsp → p.gpr r = s.gpr r) ∧ Kept s 0 p.mem ∧
    Frame [fR s] s.mem p.mem ∧ p.rd = s.rd ∧ p.wr = fR s :: s.wr

/-- What the load of `scratch` leaves, from `s`. -/
def LoadPost (s s₁ : State) : Prop :=
  s₁.gpr .r11 = S s ∧ (∀ r, r ≠ .r11 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr

theorem pushPost_of {s s₁ : State} (hp : BP s) (h : LoadPost s s₁) : PushPost s (pushed frameRegs s₁) := by
  obtain ⟨h11, hg, hm, hrd, hwr⟩ := h
  obtain ⟨psp, pk, pf⟩ := pushed_kept hp h11 hg hm
  refine ⟨psp, by rw [pushed_gpr _ _ (by decide)]; exact h11, fun r h₁ h₂ => by rw [pushed_gpr _ _ h₂]; exact hg r h₁,
    pk, pf, by rw [pushed_rd, hrd], ?_⟩
  rw [pushed_wr, hg _ (by decide), hwr]; rfl

/-- The registers of the arguments, and `scratch` and `rsp`. -/
def args : List Reg := [.r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem rest_check : ∃ hc, ((taint.check (Taint.ofRegs [.rsp]) (.block rest) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem stitchE_check : ∃ hc, ((taint.check (Taint.ofRegs args) (stitchPart Impl.Gcm.X86_64.Stitch.enc) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem stitchD_check : ∃ hc, ((taint.check (Taint.ofRegs args) (stitchPart Impl.Gcm.X86_64.Stitch.dec) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem nil_check : ∃ hc, ((taint.check (Taint.ofRegs args) (.block []) hc).map
    fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem tailHead_check : ∃ hc, ((taint.check (Taint.ofRegs [.rsp])
    (.block [.mov .r8 (.mem (at_ .rsp argN)), .alu .test .r8 (.reg .r8)]) hc).map fun τ' =>
      (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ctrArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.rsp]) (.block ctrArgs) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem ghArgs_check : ∃ hc, ((taint.check (Taint.ofRegs [.rsp]) (.block ghArgs) hc).map fun τ' =>
    (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true := ⟨_, by taint_decide⟩

theorem load_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 8))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

section
variable {s : State} (hp : BP s)
include hp

/-- `Ready` after `ctrCall`. -/
theorem ctrCall_ready (c : Ctr32Impl) {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (ctrCall ⟨c.callee.name, c.callee.code⟩) st (Ready s q) :=
  WP.seq (WP.mono (ctrArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (ctr_call c hc) fun st₃ g => by
    have f₃ := g.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (apart_fR hp (q := q) (by omega)).ctr r hr) (g.saved _ (by decide)) g.rd g.wr)

/-- `Ready` after `ghCall`. -/
theorem ghCall_ready (g : GhashImpl) {q : Nat} {st : State} (h : Ready s q st) (hq : q < n s) :
    WP isa (ghCall g.fn) st (Ready s q) :=
  WP.seq (WP.mono (ghArgs_ok hp h hq) fun st₂ ⟨hc, R₂, _, _⟩ => WP.mono (gh_call g hc) fun st₃ g' => by
    have f₃ := g'.frame
    rw [R₂.rsp] at f₃
    exact R₂.frame f₃ (fun r hr => (apart_fR hp (q := q) (by omega)).gh r hr) (g'.saved _ (by decide)) g'.rd g'.wr)

end

section
variable {s₀ s₀' : State} (hp : BP s₀) (hp' : BP s₀') (pb : Pub s₀ s₀')
include hp hp' pb

omit hp hp' in
theorem ready_rsp {q q' : Nat} {s₁ s₂ : State} (h₁ : Ready s₀ q s₁) (h₂ : Ready s₀' q' s₂) :
    ∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rsp, h₂.rsp, pb.eF]

/-- `ctrCall`, in two runs `Ready` for the same blocks left. -/
theorem ctrCall_rel (c : Ctr32Impl) {q : Nat} (hq : q < n s₀) :
    RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) (ctrCall ⟨c.callee.name, c.callee.code⟩)
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂ := by
  have hq' : q < n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) [.rsp] [.rsp] false
      (fun _ _ h => ready_rsp pb h.1 h.2) ctrArgs_check) (fun _ _ h => h)
    (G₁ := fun st' => CtrCall st' (K s₀) (C s₀) (dq s₀ q) (S s₀) (R s₀) (n s₀ - q) ∧ Ready s₀ q st')
    (G₂ := fun st' => CtrCall st' (K s₀') (C s₀') (dq s₀' q) (S s₀') (R s₀') (n s₀' - q) ∧ Ready s₀' q st')
    (fun _ h => WP.mono (ctrArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (ctrArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (ctr_rel c fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => ctrCall_ready hp c h hq)
    (fun _ h => ctrCall_ready hp' c h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨⟨hr, -⟩, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.c, pb.edq, pb.sc, pb.eR, pb.en] at c₂
  exact ⟨_, _, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `ghCall`, in two runs `Ready` for the same blocks left. -/
theorem ghCall_rel (g : GhashImpl) {q : Nat} (hq : q < n s₀) :
    RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) (ghCall g.fn)
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂ := by
  have hq' : q < n s₀' := by rw [pb.en]; exact hq
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) [.rsp] [.rsp] false
      (fun _ _ h => ready_rsp pb h.1 h.2) ghArgs_check) (fun _ _ h => h)
    (G₁ := fun st' => GhCall st' (K s₀ + BitVec.ofNat 64 240) (Y s₀) (dq s₀ q) (S s₀) (n s₀ - q) ∧ Ready s₀ q st')
    (G₂ := fun st' => GhCall st' (K s₀' + BitVec.ofNat 64 240) (Y s₀') (dq s₀' q) (S s₀') (n s₀' - q) ∧
      Ready s₀' q st')
    (fun _ h => WP.mono (ghArgs_ok hp h hq) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (ghArgs_ok hp' h hq') fun _ h => ⟨h.1, h.2.1⟩)
  refine (rel_wp (RelCT.seq a (gh_rel g fun s₁ s₂ h => ?_)) (fun _ _ h => h) (fun _ h => ghCall_ready hp g h hq)
    (fun _ h => ghCall_ready hp' g h hq')).mono (fun _ _ h => h) fun _ _ h => h.2
  obtain ⟨⟨hr, -⟩, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
  rw [pb.k, pb.y, pb.edq, pb.sc, pb.en] at c₂
  exact ⟨_, _, _, _, _, c₁, c₂, hr _ (List.mem_singleton_self _)⟩

/-- `tail`, from two runs at the same point. -/
theorem tail_rel {first second : Prog isa}
    (h₁ : ∀ q, q < n s₀ → RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) first
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂)
    (h₂ : ∀ q, q < n s₀ → RelCT isa (fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂) second
      fun s₁ s₂ => Ready s₀ q s₁ ∧ Ready s₀' q s₂)
    {q : Nat} {ys ys' : List Block} :
    RelCT isa (fun s₁ s₂ => Mid s₀ q q ys s₁ ∧ Mid s₀' q q ys' s₂) (tail first second) fun _ _ => True := by
  have a := rel_wp (rel_regs (P := fun s₁ s₂ => Mid s₀ q q ys s₁ ∧ Mid s₀' q q ys' s₂) [.rsp] [.rsp] false
      (fun _ _ h => ready_rsp pb h.1.ready h.2.ready) tailHead_check)
    (fun _ _ h => h) (fun _ h => tailHead_ok hp h) (fun _ h => tailHead_ok hp' h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, pb.en]) ?_ ?_)
  · exact (rel_taint [] (fun _ _ _ r hr => by cases hr) ⟨_, by taint_decide⟩).mono (fun _ _ h => h) fun _ _ h => h
  · by_cases hlt : q < n s₀
    · exact (RelCT.seq (h₁ q hlt) (h₂ q hlt)).mono (fun _ _ h => ⟨h.1.2.1.1.ready, h.1.2.2.1.ready⟩)
        fun _ _ _ => trivial
    · intro s₁ s₂ _ _ _ _ h
      have e := h.1.2.1.2
      rw [h.2] at e
      simp only [Option.some.injEq, Bool.false_eq, decide_eq_false_iff_not] at e
      exact absurd (by omega) e

/-- The interleaved part (or nothing) and `rest`, in two runs from the frame's push. -/
theorem part_rel (stitch : Bool) (piece : Prog isa) {ys : State → Nat → List Block}
    (hys : ∀ s, ys s 0 = [])
    (hc : ∃ hc, ((taint.check (Taint.ofRegs args) (stitchPart piece) hc).map
      fun τ' => (RegSet.ofList [Reg.rsp]).subset τ'.regs && (!false || τ'.flags)) = some true)
    (hw : ∀ {s : State}, BP s → ∀ {p : State}, PushPost s p →
      WP isa (stitchPart piece) p (Mid s (n s - n s % 16) 0 (ys s (n s - n s % 16)))) :
    RelCT isa (fun a b => (∀ r ∈ args, a.gpr r = b.gpr r) ∧ PushPost s₀ a ∧ PushPost s₀' b)
      (if stitch then .seq (stitchPart piece) (.block rest) else .block [])
      fun s₁ s₂ => ∃ q, Mid s₀ q q (ys s₀ q) s₁ ∧ Mid s₀' q q (ys s₀' q) s₂ := by
  cases stitch
  · refine ((rel_regs args [.rsp] false (fun _ _ h => h.1) nil_check).wp
      (F₁ := Mid s₀ 0 0 (ys s₀ 0)) (F₂ := Mid s₀' 0 0 (ys s₀' 0)) fun s₁ s₂ h => ⟨WP.block_nil ?_,
        WP.block_nil ?_⟩).mono (fun _ _ h => h) fun _ _ h => ⟨0, h.2.1, h.2.2⟩
    · obtain ⟨-, ⟨a, -, b, c, d, e, f⟩, -⟩ := h; rw [hys]; exact mid_entry hp a b c d e f
    · obtain ⟨-, -, ⟨a, -, b, c, d, e, f⟩⟩ := h; rw [hys]; exact mid_entry hp' a b c d e f
  · have a := rel_wp (P := fun a b => (∀ r ∈ args, a.gpr r = b.gpr r) ∧ PushPost s₀ a ∧ PushPost s₀' b)
      (rel_regs args [.rsp] false (fun _ _ h => h.1) hc) (fun _ _ h => h.2)
      (fun _ h => hw hp h) (fun _ h => hw hp' h)
    have b := rel_wp (rel_regs
      (P := fun s₁ s₂ => (∀ r ∈ [Reg.rsp], s₁.gpr r = s₂.gpr r) ∧
        Mid s₀ (n s₀ - n s₀ % 16) 0 (ys s₀ (n s₀ - n s₀ % 16)) s₁ ∧
        Mid s₀' (n s₀' - n s₀' % 16) 0 (ys s₀' (n s₀' - n s₀' % 16)) s₂) [.rsp] [.rsp] false
      (fun _ _ h => h.1) rest_check)
      (fun _ _ h => h.2) (fun _ h => rest_ok hp rfl h) (fun _ h => rest_ok hp' rfl h)
    refine (RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2⟩) b).mono (fun _ _ h => h)
      fun _ _ h => ⟨n s₀ - n s₀ % 16, h.2.1, ?_⟩
    rw [← pb.en]; exact h.2.2

/-- The load of `scratch` and the frame, in two runs from the entry states. -/
theorem blocks_rel (stitch : Bool) (piece first second : Prog isa)
    (hbody : RelCT isa (fun a b => ∃ s₁ s₂, (True ∧ LoadPost s₀ s₁ ∧ LoadPost s₀' s₂) ∧
        a = pushed frameRegs s₁ ∧ b = pushed frameRegs s₂)
      (.seq (if stitch then .seq (stitchPart piece) (.block rest) else .block []) (tail first second))
      fun _ _ => True) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (blocks stitch piece first second) fun _ _ => True := by
  have l := rel_wp (rel_taint (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact pb.sp.symm) load_check)
    (fun _ _ h => h) (G₁ := LoadPost s₀) (G₂ := LoadPost s₀')
    (fun s h => by subst h; exact load_ok hp) (fun s h => by subst h; exact load_ok hp')
  refine RelCT.seq l (RelCT.frame (fun s₁ s₂ h => ?_) hbody)
  rw [h.2.1.2.1 _ (by decide), h.2.2.2.1 _ (by decide)]; exact pb.sp.symm

end

/-- Two runs' pushed states agree on the arguments. -/
theorem pushed_args {s₀ s₀' : State} (pb : Pub s₀ s₀') {s₁ s₂ : State} (h₁ : LoadPost s₀ s₁)
    (h₂ : LoadPost s₀' s₂) : ∀ r ∈ args, (pushed frameRegs s₁).gpr r = (pushed frameRegs s₂).gpr r := by
  intro r hr
  by_cases hsp : r = .rsp
  · subst hsp; rw [pushed_rsp, pushed_rsp, h₁.2.1 _ (by decide), h₂.2.1 _ (by decide),
      show s₀'.gpr .rsp = s₀.gpr .rsp from pb.sp]
  · rw [pushed_gpr _ _ hsp, pushed_gpr _ _ hsp]
    by_cases h11 : r = .r11
    · subst h11; rw [h₁.1, h₂.1, pb.sc]
    · rw [h₁.2.1 r h11, h₂.2.1 r h11]
      simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h11
      · exact pb.k.symm
      · exact pb.rsi.symm
      · exact pb.c.symm
      · exact pb.y.symm
      · exact pb.d.symm
      · exact pb.r9.symm
      · exact absurd rfl hsp

theorem encrypt_ct (v : GcmImpl) (stitch : Bool) :
    ConstantTime isa Proof.AesGcm.encryptBlocksX86_64.pre Proof.AesGcm.encryptBlocksX86_64.pub
      (encrypt v.callees.ctr v.callees.gh stitch) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine blocks_rel hp hp' pb stitch _ _ _ ?_
  refine RelCT.seq ((part_rel hp hp' pb stitch Impl.Gcm.X86_64.Stitch.enc
    (ys := fun s q => ctr32 (ciph s) (cb s) (blocksAt s.mem (D s) q)) (fun _ => rfl) stitchE_check
    fun {_} hp {_} h => by obtain ⟨a, b, c, d, e, f, g⟩ := h; exact stitchE_ok hp a b c d e f g).mono
    (fun _ _ h => ?_) fun _ _ h => h) ?_
  · obtain ⟨s₁, s₂, ⟨-, l₁, l₂⟩, rfl, rfl⟩ := h
    exact ⟨pushed_args pb l₁ l₂, pushPost_of hp l₁, pushPost_of hp' l₂⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
    exact tail_rel hp hp' pb (fun q hq => ctrCall_rel hp hp' pb v.ctr hq) (fun q hq => ghCall_rel hp hp' pb v.gh hq)
      _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

theorem decrypt_ct (v : GcmImpl) (stitch : Bool) :
    ConstantTime isa Proof.AesGcm.decryptBlocksX86_64.pre Proof.AesGcm.decryptBlocksX86_64.pub
      (decrypt v.callees.ctr v.callees.gh stitch) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  have hp := BP.of h
  have hp' := BP.of h'
  have pb := Pub.of hq
  refine blocks_rel hp hp' pb stitch _ _ _ ?_
  refine RelCT.seq ((part_rel hp hp' pb stitch Impl.Gcm.X86_64.Stitch.dec
    (ys := fun s q => blocksAt s.mem (D s) q) (fun _ => rfl) stitchD_check
    fun {_} hp {_} h => by obtain ⟨a, b, c, d, e, f, g⟩ := h; exact stitchD_ok hp a b c d e f g).mono
    (fun _ _ h => ?_) fun _ _ h => h) ?_
  · obtain ⟨s₁, s₂, ⟨-, l₁, l₂⟩, rfl, rfl⟩ := h
    exact ⟨pushed_args pb l₁ l₂, pushPost_of hp l₁, pushPost_of hp' l₂⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, M₁, M₂⟩ e₁ e₂
    exact tail_rel hp hp' pb (fun q hq => ghCall_rel hp hp' pb v.gh hq) (fun q hq => ctrCall_rel hp hp' pb v.ctr hq)
      _ _ _ _ _ _ ⟨M₁, M₂⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64.Blocks
