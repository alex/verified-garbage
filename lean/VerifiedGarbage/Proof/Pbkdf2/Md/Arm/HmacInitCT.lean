import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacInit
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: constant time

As `finalize` (`HmacFinCT.lean`): correctness determines our registers from
the public arguments alone, so the taint analysis proves the blocks between
the calls constant time from them (`Checks`, evaluated for each hash
function); the calls of the streaming `init` are constant time by its own
proof (`init_rel`, `Proof/Hmac/Generic/Arm/Hash.lean`), and those of the
compression function by its own (`compressBlock_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Hmac.Generic.Arm (initG init_rel covers_one)

/-- The registers that the pieces between the calls use, which hold our
variables: `inner`, `outer`, the key and its length, and `scratch`. -/
abbrev regsK : List Reg := [.r4, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `init` between its calls, which
depend on the hash function's sizes. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block H.initPrologue) hc).isSome = true
  arg : ∀ st ∈ [Reg.r4, .r5], ∃ hc, (taint.check (Taint.ofRegs regsK) (.block [.mov .r0 (.reg st)]) hc).isSome = true
  blocks : ∃ hc, (taint.check (Taint.ofRegs regsK) H.blocks hc).isSome = true
  toOuter : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR H sc s₀ s) (h' : KR H sc s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, out, out, hq.r1]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

/-- `KR`, with the key and its length in `r6` and `r7`. -/
def KK (H : Hash) (sc : Nat) (s₀ s : State) : Prop :=
  KR H sc s₀ s ∧ s.gpr .r6 = kp s₀ ∧ s.gpr .r7 = BitVec.ofNat 32 (kl s₀)

theorem kk_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KK H sc s₀ s) (h' : KK H sc s₀' s') :
    ∀ r ∈ regsK, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kr_agree hq h.1 h'.1 _ (by simp)
  · exact kr_agree hq h.1 h'.1 _ (by simp)
  · rw [h.2.1, h'.2.1, kp, kp, hq.r2]
  · rw [h.2.2, h'.2.2, kl, kl, hq.r3]
  · exact kr_agree hq h.1 h'.1 _ (by simp)

end

section
variable {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀')
  (hq : PubEq s₀ s₀')
include hH hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`r4` for `inner`,
`r5` for `outer`). -/
theorem callInit_rel (hc : Checks H) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) :
    RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') (H.st.callInit st)
      fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s' := by
  have hz := hH.sizes
  have hst' : st = .r4 ∧ p = inn s₀' ∨ st = .r5 ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.r0]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.r1]⟩
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by rcases hst' with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, _, np, hin⟩ := st_facts hz hp hpR
  obtain ⟨_, _, _, _, hin'⟩ := st_facts hz hp' hpR'
  have hS : H.st.S = H.N + H.B := hz.S
  let F : State → State → Prop := fun t₀ s => KR H sc t₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r6 = kp t₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (kl t₀)
  have ha : RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') (.block [.mov .r0 (.reg st)])
      fun s s' => F s₀ s ∧ F s₀' s' :=
    rel_agree (Taint.ofRegs regsK) (fun _ _ h h' => Taint.agree_ofRegs (kk_agree hq h h'))
      (hc.arg st (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp))
      (fun _ ⟨k, r6, r7⟩ => WP.mono (initArg_ok k hst) fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
      (fun _ ⟨k, r6, r7⟩ => WP.mono (initArg_ok k hst') fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
  unfold Impl.Hmac.Generic.Arm.Hash.callInit
  refine ha.seq (rel_wp (init_rel hH.stream (st := p) fun s s' ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ =>
      ⟨d, d', by rw [hS]; exact np, by rw [k.wr, hS]; exact covers_one hin, by rw [k'.wr, hS]; exact covers_one hin'⟩)
    (fun _ ⟨k, d, r6, r7⟩ => initCall_ok hz hp hH k hpR d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
    (fun _ ⟨k, d, r6, r7⟩ => initCall_ok hz hp' hH k hpR' d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩))

/-- The compression of the buffer of the state at `p`. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) (hpR' : p' = inn s₀' ∨ p' = out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = p + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = p' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = p' + BitVec.ofNat 32 H.N))
      H.compressBlock fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀') := by
  have hz := hH.sizes
  have e : scr s₀' = scr s₀ := hq.a0.symm
  exact rel_wp (compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := p) (scr := scr s₀)
      (src := p + BitVec.ofNat 32 H.N) fun s s' ⟨⟨k, a, b, c⟩, ⟨k', a', b', c'⟩⟩ => by
        have c₂ := callOk hz hp' k' hpR' a' b' c'
        rw [he, e] at c₂
        exact ⟨callOk hz hp k hpR a b c, c₂⟩)
    (fun _ ⟨k, a, b, c⟩ => cmpS_ok hz hp hH k hpR a b c fun _ k' r3 _ _ => ⟨k', r3⟩)
    (fun _ ⟨k, a, b, c⟩ => cmpS_ok hz hp' hH k hpR' a b c fun _ k' r3 _ _ => ⟨k', r3⟩)

include hH hp hp' hq in
theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hH.sizes
  have aw : ∀ {t : State}, Pre H sc t →
      t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := fun {t} h => by
    have e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_o
    · exact h.a_s
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hz hp)
      (fun _ e => by rw [e]; exact pro_ok hz hp')
  have blk : RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') H.blocks
      fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = inn s₀ ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = inn s₀' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs regsK) (fun _ _ h h' => Taint.agree_ofRegs (kk_agree hq h h')) hc.blocks
      (fun _ ⟨k, r6, r7⟩ => blocks_ok hz hp k r6 r7)
      (fun _ ⟨k, r6, r7⟩ => blocks_ok hz hp' k r6 r7)
  have tO : RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀'))
      (.block H.toOuter)
      fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = out s₀ ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = out s₀ + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = out s₀' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs kregs) (fun _ _ h h' => Taint.agree_ofRegs (kr_agree hq h.1 h'.1)) hc.toOuter
      (fun _ ⟨k, r3⟩ => WP.mono (toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
      (fun _ ⟨k, r3⟩ => WP.mono (toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀'))
      (.block H.st.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1.1 h.2.1)) hr
  exact pro.seq ((callInit_rel hH hp hp' hq hc (.inl ⟨rfl, rfl⟩)).seq
    ((callInit_rel hH hp hp' hq hc (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((cmpS_rel hH hp hp' hq (.inl rfl) (.inl rfl) hq.r0.symm).seq
    (tO.seq ((cmpS_rel hH hp hp' hq (.inr rfl) (.inr rfl) hq.r1.symm).seq restore))))))

end

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (initG S W).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- HMAC's `init` is verified against `initG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified Arm.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) (pubEq_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.HmacInit
