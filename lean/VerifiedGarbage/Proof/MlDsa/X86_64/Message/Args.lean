import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Layout

/-!
# ML-DSA on x86-64, `sign_message` and `verify_message`: the moves of a call's arguments

Untrusted: everything here is checked by Lean. `setArgs as` moves each
argument (a slot of the frame, a slot plus an offset, an immediate, `rsp`
or `rax`) into its register: afterwards each argument register holds the
argument's value in the state before the moves (`setArgs_ok`), and nothing
else changed but those registers and the flags.
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-- The value of an argument in the state `s`. -/
def _root_.VG.Impl.MlDsa.X86_64.Message.Arg.val (s : State) : Arg → BitVec 64
  | .slot f => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64
  | .slotOff f o => s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o
  | .imm v => BitVec.ofNat 64 v
  | .sp => s.gpr .rsp
  | .ret => s.gpr .rax

/-- A slot within the frame, an offset or an immediate of 31 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Message.Arg.ok : Arg → Bool
  | .slot f => decide (f + 8 ≤ 72)
  | .slotOff f o => decide (f + 8 ≤ 72) && decide (o < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 31)
  | .sp => true
  | .ret => true

/-- The slots of the frame are readable. -/
abbrev FrOk (s : State) : Prop := ∀ f, f + 8 ≤ 72 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 f) 8

theorem Arg.mov_ok (d : Reg) (a : Arg) (ha : a.ok = true) (hd : d ∈ argRegs6) (s : State) (hfr : FrOk s) :
    WP isa (.block (a.mov d)) s fun s1 =>
      (s1.gpr d = a.val s ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ Keep [d] s s1 := by
  refine WP.keep [d] ?_ (by cases a <;> cases d <;> rfl)
  have hsp : d ≠ .rsp := fun h => by subst h; revert hd; decide
  have hax : d ≠ .rax := fun h => by subst h; revert hd; decide
  cases a with
  | slot f =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [ea_stk, hfr f ha, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | slotOff f o =>
    simp only [Arg.ok, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [ea_stk, hfr f ha.1, sx32 ha.2, RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg, RegUpd.mxcsr_setFlags]
  | imm v =>
    simp only [Arg.ok, decide_eq_true_eq] at ha
    simp only [Arg.mov, Arg.val]
    xrun [zx32 (show v < 2 ^ 32 by omega), RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | sp =>
    simp only [Arg.mov, Arg.val]
    xrun [RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]
  | ret =>
    simp only [Arg.mov, Arg.val]
    xrun [RegUpd.gpr_setReg_self, RegUpd.mxcsr_setReg]

/-- The value of an argument is the same after moves into other argument registers. -/
theorem Arg.val_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (hm : s1.mem = s.mem) (k : Keep [d] s s1)
    (a : Arg) : a.val s1 = a.val s := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  have hax : Reg.rax ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  cases a <;> simp only [Arg.val, hm, k.gpr hsp, k.gpr hax]

theorem frOk_keep {d : Reg} (hd : d ∈ argRegs6) {s s1 : State} (k : Keep [d] s s1) (h : FrOk s) : FrOk s1 := by
  have hsp : Reg.rsp ∉ [d] := by
    simp only [List.mem_singleton]; intro h; subst h; revert hd; decide
  intro f hf
  rw [k.2.1, k.2.2, k.gpr hsp]
  exact h f hf

theorem setArgsGen_ok : ∀ (ds : List Reg) (as : List Arg), ds.Nodup → (∀ d ∈ ds, d ∈ argRegs6) →
    as.all Arg.ok = true → ∀ s : State, FrOk s →
    WP isa (.block ((ds.zip as).flatMap fun (d, a) => a.mov d)) s fun s1 =>
      ((∀ da ∈ ds.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧ Keep ds s s1
  | [], _, _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | _ :: _, [], _, _, _, s, _ => WP.block_nil ⟨⟨fun _ h => by simp at h, rfl, rfl⟩, Keep.refl _ _⟩
  | d :: ds, a :: as, hn, hd, ha, s, hfr => by
    rw [List.nodup_cons] at hn
    simp only [List.all_cons, Bool.and_eq_true] at ha
    simp only [List.zip_cons_cons, List.flatMap_cons]
    rw [WP.block_append_iff]
    have hd0 := hd d (List.mem_cons_self ..)
    refine WP.mono (Arg.mov_ok d a ha.1 hd0 s hfr) fun s1 ⟨⟨h1, hm1, hx1⟩, k1⟩ => ?_
    refine WP.mono (setArgsGen_ok ds as hn.2 (fun d' h => hd d' (List.mem_cons_of_mem _ h)) ha.2 s1
      (frOk_keep hd0 k1 hfr))
      fun s2 ⟨⟨h2, hm2, hx2⟩, k2⟩ => ⟨⟨fun da hda => ?_, hm2.trans hm1, hx2.trans hx1⟩,
        (k1.trans k2).mono fun r hr => by simpa using hr⟩
    rcases List.mem_cons.mp hda with rfl | hda
    · rw [k2.gpr hn.1, h1]
    · rw [h2 da hda, Arg.val_keep hd0 hm1 k1]

theorem argRegs6_nodup : argRegs6.Nodup := by decide

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ argRegs := by decide

/-- The moves of the arguments `as`. -/
theorem setArgs_ok (as : List Arg) (ha : as.all Arg.ok = true) (s : State) (hfr : FrOk s) :
    WP isa (.block (setArgs as)) s fun s1 =>
      ((∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s) ∧ s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr) ∧
        Keep argRegs s s1 := by
  refine WP.mono (setArgsGen_ok argRegs6 as argRegs6_nodup (fun _ h => h) ha s hfr) fun s1 ⟨h, k⟩ => ⟨h, ?_⟩
  refine ⟨fun r hr => k.gpr fun hm => hr ?_, k.2⟩
  simp only [argRegs6, argRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with h | h | h | h | h | h <;> simp [h]

/-- The arguments of `as`, in their registers after the moves. -/
abbrev ArgsIn (as : List Arg) (s s1 : State) : Prop := ∀ da ∈ argRegs6.zip as, s1.gpr da.1 = da.2.val s

theorem argsIn4 {a b c d : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6])⟩

theorem argsIn5 {a b c d e : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6])⟩

theorem argsIn6 {a b c d e f : Arg} {s s1 : State} (h : ArgsIn [a, b, c, d, e, f] s s1) :
    s1.gpr .rdi = a.val s ∧ s1.gpr .rsi = b.val s ∧ s1.gpr .rdx = c.val s ∧ s1.gpr .rcx = d.val s ∧
      s1.gpr .r8 = e.val s ∧ s1.gpr .r9 = f.val s :=
  ⟨h (.rdi, a) (by simp [argRegs6]), h (.rsi, b) (by simp [argRegs6]), h (.rdx, c) (by simp [argRegs6]),
    h (.rcx, d) (by simp [argRegs6]), h (.r8, e) (by simp [argRegs6]), h (.r9, f) (by simp [argRegs6])⟩

/-! ## The values of the arguments in the frame -/

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}

theorem Ctx.frOk (hc : Ctx L g mx m₀ t) : FrOk t := fun f hf => by
  rw [hc.rsp]; exact hc.inFr hf

theorem Ctx.slot (hc : Ctx L g mx m₀ t) (f : Nat) :
    (Arg.slot f).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 := by
  simp only [Arg.val, hc.rsp]

theorem Ctx.slotOff (hc : Ctx L g mx m₀ t) (f o : Nat) :
    (Arg.slotOff f o).val t = t.mem.readW (L.SP + BitVec.ofNat 64 f) 64 + BitVec.ofNat 64 o := by
  simp only [Arg.val, hc.rsp]

/-- The Keccak state, the sponge functions' working space and `μ`. -/
theorem Ctx.aSt (hc : Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (aSt p).val t = L.ST := by
  simp only [Impl.MlDsa.X86_64.Message.aSt, hc.slotOff, fScr, hc.pScr, hE]

theorem Ctx.aKs (hc : Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (aKs p).val t = L.KS := by
  simp only [Impl.MlDsa.X86_64.Message.aKs, hc.slotOff, fScr]
  rw [hc.pScr, hE, Lay.KS, Lay.X, add_add]

theorem Ctx.aMu (hc : Ctx L g mx m₀ t) (p : Spec.MlDsa.Params) (hE : oE p = L.E) :
    (aMu p).val t = L.MU := by
  simp only [Impl.MlDsa.X86_64.Message.aMu, hc.slotOff, fScr]
  rw [hc.pScr, hE, Lay.MU, Lay.X, add_add]

end

end VG.Proof.MlDsa.X86_64.Message
