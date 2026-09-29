import VerifiedGarbage.Proof.Hmac.Generic.Arm.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Arm.InitCT

/-!
# HMAC over any streaming hash function on 32-bit ARM: `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init` (`InitCT.lean`).
-/

namespace VG.Proof.Hmac.Generic.Arm.Finalize

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Hmac.Generic.Arm.Init (args)

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  [.mov .r0 (.reg .r4)] ++ [] ++ scrAt .r1 H.buf ++ [.mov .r12 (.reg .r11)]

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  [.mov .r0 (.reg .r4)] ++ [.movw .r2 (BitVec.ofNat 16 (H.B + H.D)), .mov .r3 (.imm 0)] ++
    scrAt .r1 H.buf ++ [.mov .r12 (.reg .r11)]

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  [.mov .r0 (.reg .r4)] ++ scrAt .r1 H.buf ++ [.movw .r7 (BitVec.ofNat 16 H.D), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint args 8) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r5 0 .r4 0 H.S) hc).isSome = true
  upd : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r11 H.buf .r6 0 H.D) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, outer, outer, hq.r1]
  · rw [h.r6, h'.r6, op, op, hq.a0]
  · rw [h.r11, h'.r11, scr, scr, hq.a1]

/-- The stack arguments lie outside the writable regions. -/
theorem args_wf {t : State} (h : Pre (H := H) sc t) :
    t.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 8⟩ r := by
  have e : (⟨State.addr t.sp, 8⟩ : Region) = argR t := by simp [stackArgAddr]
  refine ⟨h.spf, ?_⟩
  simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.a_i
  · exact h.a_p
  · exact h.a_s

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ tO (H := H) s₀' = tO (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.r0.symm, by rw [tO, tO, scr, scr, hq.a1], hq.a1.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧ count t = c)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (tO (H := H) s₀') (scr s₀') ∧ count t = c) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧
      count t = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧ count t = c)
    pubRegs hag hck (fun s h => hb s h)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (sp := s₀.sp) (st := inn s₀) (o := tO (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have hcnt : count s₀ = count s₀' := by rw [count, count, hq.r2, hq.r3]
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ count s = count s₀) ∧ (KR (H := H) s₀' s' ∧ count s' = count s₀') :=
    rel_agree (argTaint args 8) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_wf hp) (args_wf hp')
          (argMem_of (j := 2) hq.sp hp.spf fun i hi => by
            rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
            · exact hq.a0
            · exact hq.a1)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, _, x, _⟩ => ⟨k, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, _, x, _⟩ => ⟨k, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := count s₀)
    (F := fun s => KR (H := H) s₀ s ∧ count s = count s₀)
    (F' := fun s => KR (H := H) s₀' s ∧ count s = count s₀') hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, x⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1.trans x⟩)
    (fun s ⟨k, x⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1.trans (x.trans hcnt.symm)⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => WP.mono (fin2Args_ok hH hp k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s k => WP.mono (fin2Args_ok hH hp' k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [.mov .r0 (.reg .r4)] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
      pubRegs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
    exact ha.seq (rel_wp (upd_rel hH (sp := s₀.sp) (st := inn s₀) (d := tO (H := H) s₀) (sc := scr s₀)
      (len := H.D)
      fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h =>
      Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.Arm.Finalize

namespace VG.Proof.Hmac.Generic.Arm.Finalize

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified Arm.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6, h7⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.Arm.Finalize
