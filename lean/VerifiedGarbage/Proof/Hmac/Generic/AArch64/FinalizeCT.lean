import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.InitCT

/-!
# HMAC over any streaming hash function on AArch64: `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init` (`InitCT.lean`).
-/

namespace VG.Proof.Hmac.Generic.AArch64.Finalize

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.AArch64.Init (PubEq args)

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x23]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  [] ++ [mov .x1 .x2] ++ [.addImm .x .x2 .x23 H.buf, mov .x3 .x23]

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  [mov .x0 .x19] ++ [.movz .x .x1 (BitVec.ofNat 16 (H.B + H.D)) 0] ++ [.addImm .x .x2 .x23 H.buf, mov .x3 .x23]

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  [mov .x0 .x19] ++ [.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 H.buf,
    .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (copy .x20 0 .x19 0 H.S) hc).isSome = true
  upd : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (copy .x23 H.buf .x21 0 H.D) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, outer, outer, hq.x1]
  · rw [h.x21, h'.x21, op, op, hq.x3]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.x0.symm, by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .x1 = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .x1 = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c)
    pubRegs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2) ∧
        (KR (H := H) s₀' s' ∧ s'.gpr .x0 = inn s₀' ∧ s'.gpr .x2 = s₀'.gpr .x2) :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := s₀.gpr .x2)
    (F := fun s => KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .x0 = inn s₀' ∧ s.gpr .x2 = s₀'.gpr .x2) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH hp' k d x) fun _ ⟨k, a, x1, m⟩ => ⟨k, a, x1.trans hq.x2.symm, m⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => fin2Args_ok hH hp k) (fun s k => fin2Args_ok hH hp' k)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [mov .x0 .x19] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
      pubRegs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
    exact ha.seq (rel_wp (upd_rel hH (st := inn s₀) (d := T (H := H) s₀) (sc := scr s₀) (len := H.D)
      fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.AArch64.Finalize

namespace VG.Proof.Hmac.Generic.AArch64.Finalize

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified AArch64.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.AArch64.Finalize
