import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.InitCT

/-!
# HMAC over any streaming hash function on x86-64: `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init` (`InitCT.lean`).
-/

namespace VG.Proof.Hmac.Generic.X86_64.Finalize

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash copy)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Hmac.Generic.X86_64.Init (PubEq args)

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  [] ++ [.mov .rsi (.reg .rdx)] ++ VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ [.mov .rcx (.reg .r15)]

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  [.mov .rdi (.reg .rbx)] ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 (H.B + H.D)))] ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ [.mov .rcx (.reg .r15)]

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  [.mov .rdi (.reg .rbx)] ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 H.B))] ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D)), .mov .r8 (.reg .r15)]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (copy .r12 0 .rbx 0 H.S) hc).isSome = true
  upd : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (copy .r15 H.buf .r13 0 H.D) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.restore) hc).isSome = true

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.r12, h'.r12, outer, outer, hq.rsi]
  · rw [h.r13, h'.r13, op, op, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.rdi.symm, by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ kregs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .rsi = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .rsi = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c)
    kregs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx) ∧
        (KR (H := H) s₀' s' ∧ s'.gpr .rdi = inn s₀' ∧ s'.gpr .rdx = s₀'.gpr .rdx) :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := s₀.gpr .rdx)
    (F := fun s => KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .rdi = inn s₀' ∧ s.gpr .rdx = s₀'.gpr .rdx) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH hp' k d x) fun _ ⟨k, a, si, m⟩ => ⟨k, a, si.trans hq.rdx.symm, m⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => fin2Args_ok hH hp k) (fun s k => fin2Args_ok hH hp' k)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [.mov .rdi (.reg .rbx)] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
      kregs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
    exact ha.seq (rel_wp (upd_rel hH (st := inn s₀) (d := T (H := H) s₀) (sc := scr s₀) (len := H.D)
      fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.X86_64.Finalize

namespace VG.Proof.Hmac.Generic.X86_64.Finalize

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)

/-- `finalize` is verified against `finG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hmx : H.finalize.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86_64.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.X86_64.Finalize
