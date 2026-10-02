import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacFin
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# HMAC's `finalize` over a Merkle–Damgård hash function on ARMv7: constant time

Untrusted: everything here is checked by Lean. As for `iterate`
(`IterateCT.lean`): we relate two runs (`RelCT`). Correctness determines our
registers from the public arguments alone, so the taint analysis proves the
blocks between the calls constant time from them (`Checks`, evaluated for
each hash function); the call of the streaming `finalize` is constant time
by its own proof (`fin_rel`, `Proof/Hmac/Generic/Arm/Hash.lean`), and the
call of the compression function by its own (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Fin

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Impl.Hmac.Generic.Arm (scrAt)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Hmac.Generic.Arm (finG count FinArgs fin_rel)

/-- The registers the blocks after the outer hash value is set up use. -/
abbrev regsO : List Reg := [.r0, .r3, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `finalize` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (taint.check (Taint.ofRegs kregs)
    (.block (([] : List Instr) ++ [] ++ scrAt .r1 H.blkO ++ [.mov .r12 (.reg .r11)])) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (taint.check (Taint.ofRegs regsO) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR H sc s₀ s) (h' : KR H sc s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, outer, outer, hq.r1]
  · rw [h.r7, h'.r7, op, op, hq.a0]
  · rw [h.r11, h'.r11, scr, scr, hq.a1]

theorem kr'_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR' H sc s₀ s) (h' : KR' H sc s₀' s') :
    ∀ r ∈ regsO, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0, hv, hv, scr, scr, hq.a1]
  · rw [h.r3, h'.r3, scr, scr, hq.a1]
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)
  · rw [h.r6, h'.r6, blk, blk, scr, scr, hq.a1]
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_regs {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

theorem fin_ct {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀)
    (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hz := hH.sizes
  have e : inn s₀' = inn s₀ ∧ blk H s₀' = blk H s₀ ∧ scr s₀' = scr s₀ ∧ hv H s₀' = hv H s₀ := by
    refine ⟨hq.r0.symm, ?_, hq.a1.symm, ?_⟩ <;> simp only [blk, hv, scr, hq.a1]
  have hcnt : count s₀ = count s₀' := by rw [count, count, hq.r2, hq.r3]
  have aw : ∀ {t : State}, Pre H sc t →
      t.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 8⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 8⟩ : Region) = argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_p
    · exact h.a_s
  let P₁ : State → State → Prop := fun t₀ s => KR H sc t₀ s ∧ s.gpr .r0 = inn t₀ ∧ count s = count t₀
  let F₁ : State → State → Prop := fun t₀ s =>
    KR H sc t₀ s ∧ FinArgs hH.stream s (inn t₀) (blk H t₀) (scr t₀) ∧ count s = count t₀
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue) fun s s' => P₁ s₀ s ∧ P₁ s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 8) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
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
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hH hp) fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hH hp') fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
  have f1 := rel_regs (F := P₁ s₀) (F' := P₁ s₀') (G := F₁ s₀) (G' := F₁ s₀') kregs
    (fun _ _ h h' => kr_agree hq h.1 h'.1) hc.fin1
    (fun _ ⟨k, r0, c⟩ => WP.mono (fin1Args_ok hH hp k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
    (fun _ ⟨k, r0, c⟩ => WP.mono (fin1Args_ok hH hp' k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
  have call : RelCT isa (fun s s' => F₁ s₀ s ∧ F₁ s₀' s')
      (.frame (.push Hmac.Generic.Arm.fin2) (.call H.st.finN H.st.finC) (.pop .r1 8))
      fun s s' => KR H sc s₀ s ∧ KR H sc s₀' s' :=
    rel_wp (fin_rel hH.stream (sp := s₀.sp) (st := inn s₀) (o := blk H s₀) (sc := scr s₀) fun s s' ⟨h, h'⟩ =>
      ⟨h.2.1, by rw [← e.1, ← e.2.1, ← e.2.2.1]; exact h'.2.1, by rw [h.2.2, h'.2.2, hcnt], h.1.sp,
        by rw [h'.1.sp, hq.sp]⟩)
      (fun _ h => finCall_ok hH hp h.1 h.2.1 fun _ k _ _ => k)
      (fun _ h => finCall_ok hH hp' h.1 h.2.1 fun _ k _ _ => k)
  have mid := rel_regs (F := KR H sc s₀) (F' := KR H sc s₀') (G := KR' H sc s₀) (G' := KR' H sc s₀') kregs
    (fun _ _ h h' => kr_agree hq h h') hc.mid
    (fun _ h => WP.mono (mid_ok hz hp hH.reloc hH.len h) fun _ h => h.1)
    (fun _ h => WP.mono (mid_ok hz hp' hH.reloc hH.len h) fun _ h => h.1)
  have cmp : RelCT isa (fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s') H.compressBlock
      fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s' :=
    rel_wp (compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := hv H s₀) (scr := scr s₀)
      (src := blk H s₀) fun s s' ⟨h, h'⟩ => by
        have c' := callOk_of hz hp' h'
        rw [e.2.2.2, e.2.2.1, e.2.1] at c'
        exact ⟨callOk_of hz hp h, c'⟩)
      (fun _ h => cmp_ok hz hp hH.comp h fun _ k _ _ => k)
      (fun _ h => cmp_ok hz hp' hH.comp h fun _ k _ _ => k)
  obtain ⟨_, ho⟩ := hc.out
  have out : RelCT isa (fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s') (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsO) (fun _ _ h => Taint.agree_ofRegs (kr'_agree hq h.1 h.2)) ho
  unfold Hash.hmacFin Impl.Hmac.Generic.Arm.Hash.callFin
  exact pro.seq ((f1.seq call).seq (mid.seq (cmp.seq out)))

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (finG S W).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- HMAC's `finalize` is verified against `finG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} (hfit : H.st.buf + H.N + H.B ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified Arm.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (fin_ct hH hc (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.Fin
