import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.CallCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Equation
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTReady`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 32)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ m₁ a ∧ Ctx L g₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) c (Two L g₁ g₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

def AllArgs (L : Lay) (args : List (Reg × Value)) (stack : List Value) (s : State) : Prop :=
  OutArgs L args s ∧ StackArgs L stack s

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (stack : List Value) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid p.2) (hs : stack.length ≤ 6)
    (hvs : ∀ v ∈ stack, valid v) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block (setup args stack))
      (Two L g₁ g₂ m₁ m₂ (AllArgs L args stack)) := by
  refine two_wp ((Whole.setup_ct args stack).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hs hvs hr) fun _ ⟨hu, _, hg, ht⟩ => ⟨hu, hg, ht⟩

theorem args_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1.1 p hp).trans (h.2.2.2.1 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem stack_arg_eq {args : List (Reg × Value)} {stack : List Value} {a b : State}
    (h : Two L g₁ g₂ m₁ m₂ (AllArgs L args stack) a b) {j : Nat} (hj : j < stack.length) :
    stackArg a j = stackArg b j := (h.2.2.1.2 j hj).trans (h.2.2.2.2 j hj).symm

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hn : c.noFrames = true)
    (ready : ∀ {g m t}, Ctx L g m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wp hc (ready hc hs) correct hn) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratchWithin L)
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL hd ha, cov, ws⟩

def init_ready (hL : L.Ok) (ha : s.gpr .r0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : s.sp = L.E) {count p len : BitVec 32}
    (hi : Input L p len) (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E p len, Whole.hashWr L.scr, update_pre hL he ha hi, update_covers hi, hw⟩

def finalize_ready (hL : L.Ok) (he : s.sp = L.E) {count : BitVec 32} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs s :=
  ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184), finalize_pre hL he ha,
    finalize_covers hL, final_writes hL⟩

def equation_ready (hL : L.Ok) (ha : EqArgs L s) : Whole.CallReady verifyLocal L.E L.inputs L.outputs s :=
  ⟨equationRd L,equationWr L,equation_pre hL ha,equation_covers,equation_writes⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTHash`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 4 0)] []))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.Arm.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct (Proof.Sha512.Arm.Stream.init_verified _).1
    (Proof.Sha512.Arm.Stream.init_verified _).2.1 rfl
  · intro g m t _ hs
    have h := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at h
    rw [BitVec.add_zero] at h
    exact init_ready hL h
  · intro a b ar aw br bw h
    exact call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs])

theorem update_call_ct (hL : L.Ok) (count : Nat) (p n : Value)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (.call Spec.Sha512.updateApi.name Impl.Sha512.Arm.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Update.update_verified.1
    Proof.Sha512.Arm.Stream.Update.update_verified.2.1 Whole.update_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact update_ready hL hc.sp hi ⟨a0, hs.1 (.r2, .const count) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by simp), hs.2 1 (by simp), hs.2 2 (by simp)⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .const count)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by simp), stack_arg_eq h (j := 1) (by simp), stack_arg_eq h (j := 2) (by simp)⟩

theorem finalize_call_ct (hL : L.Ok) (n : Nat) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L
      [(.r0, .caller 4 0), (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)]
      [.frame 184, .caller 4 192]))
      (.call Spec.Sha512.finalizeApi.name Impl.Sha512.Arm.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct Proof.Sha512.Arm.Stream.Finalize.finalize_verified.1
    Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.1 Whole.finalize_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 4 0) (by simp)
    change t.gpr .r0 = L.scr + 0#32 at a0
    rw [BitVec.add_zero] at a0
    exact finalize_ready hL hc.sp ⟨a0,
      hs.1 (.r2, if b then .caller 2 n else .const n) (by simp),
      hs.1 (.r3, .const 0) (by simp), hs.2 0 (by decide), hs.2 1 (by decide)⟩
  · intro a c ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 4 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, if b then .caller 2 n else .const n)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .const 0)) h (by simp) (by simp [linkRegs]),
      stack_arg_eq h (j := 0) (by decide), stack_arg_eq h (j := 1) (by decide)⟩

theorem init_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) init
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (setup_ct hL ha hb [(.r0, .caller 4 0)] [] (by decide) (by simp [valid])
    (by decide) (by simp) (by simp [preserved])).seq (init_call_ct hL)

theorem update_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (count : Nat) (p n : Value) (hc : count < 65536) (hp : valid p) (hn : valid n)
    (hi : Input L (value L p) (value L n)) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True)
      (update (setup [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] [p,n,.caller 4 192]))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : ∀ x : Reg × Value, x ∈ [(.r0, .caller 4 0), (.r2, .const count), (.r3, .const 0)] →
      valid x.2 := by simp [valid,hc]
  have hvs : ∀ v ∈ [p,n,Value.caller 4 192], valid v := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl)
    · exact hp
    · exact hn
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hv (by simp) hvs (by simp [preserved])).seq
    (update_call_ct hL count p n hi)

theorem finalize_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (n : Nat) (hn : n < 256) (b : Bool) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (finalize n b)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hv : valid (if b then .caller 2 n else .const n) := by
    cases b <;> simp [valid] <;> omega
  have hvall : ∀ p : Reg × Value, p ∈ [(.r0, .caller 4 0),
      (.r2, if b then .caller 2 n else .const n), (.r3, .const 0)] → valid p.2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · simp [valid]
    · exact hv
    · simp [valid]
  exact (setup_ct hL ha hb _ _ (by simp) hvall (by decide) (by simp [valid])
    (by simp [preserved])).seq (finalize_call_ct hL n b)

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTHashPipeline`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem prefix_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (source count : Nat) (hj : source < 5) (hc : count < 65536) (hi : Input L (L.value source) 32) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (prefixArgs source count))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller source 0)) (value L (.const 32)) := by
    change Input L (L.value source+0#32) 32#32
    rw [BitVec.add_zero]
    exact hi
  exact update_ct hL ha hb count (.caller source 0) (.const 32) hc ⟨hj,by decide⟩ (by simp [valid]) inp

theorem message_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (update (messageArgs 64))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have inp : Input L (value L (.caller 1 0)) (value L (.caller 2 0)) := by
    simpa only [value,Lay.value,BitVec.add_zero] using message_input hL
  exact update_ct hL ha hb 64 (.caller 1 0) (.caller 2 0) (by decide)
    (by simp [valid]) (by simp [valid]) inp

theorem hash_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun _ => True) :=
  (init_ct hL ha hb).seq ((prefix_ct hL ha hb 3 0 (by decide) (by decide) (signature_input hL)).seq
    ((prefix_ct hL ha hb 0 32 (by decide) (by decide) (key_input hL)).seq
      ((message_ct hL ha hb).seq (finalize_ct hL ha hb 64 (by decide) true))))

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTScalars`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def reduceValues : List (Reg × Value) := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)]

theorem reduce_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L reduceValues []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct reduce_noFrames
  · intro g m t _ hs
    have a0 := hs.1 (.r0,.frame 120) (by simp [reduceValues])
    have a1 := hs.1 (.r1,.frame 184) (by simp [reduceValues])
    have a2 := hs.1 (.r2,.caller 4 0) (by simp [reduceValues])
    change t.gpr .r2=L.scr+0#32 at a2
    exact reduce_ready hL (by decide) ⟨a0,a1,a2.trans (BitVec.add_zero _)⟩
  · intro a b ar aw br bw h
    simp only [scalarReduceLocal,State.withRegions_gpr,State.withRegions_sp,State.callEntry_sp]
    exact ⟨two_sp h,call_gpr_eq h (p := (.r0,.frame 120)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r1,.frame 184)) (by simp [reduceValues]) (by decide),
      call_gpr_eq h (p := (.r2,.caller 4 0)) (by simp [reduceValues]) (by decide)⟩

theorem reduce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64=digest)
      (callWith reduceArgs "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest) := by
  have hs := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb reduceValues []
    (by decide) (by simp [reduceValues,valid]) (by decide) (by simp)
    (by simp [reduceValues,preserved])
  refine two_wp ((hs.seq (reduce_call_ct hL)).mono
    (fun _ _ h => ⟨h.1,h.2.1,trivial,trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro s hc hd
    exact WP.mono (reduce_step hc hL ha) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩
  · intro s hc hd
    exact WP.mono (reduce_step hc hL hb) fun t ⟨ht,_,hr⟩ => ⟨ht,by rw [hr,hd]⟩

theorem extend_ct (hL : L.Ok) (digest : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32=Spec.Ed25519.scalarReduce digest)
      (.block extendChallenge)
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 64=
        Spec.Ed25519.encodeLE 64 (Spec.Ed25519.decodeLE digest % Spec.Ed25519.L)) := by
  refine two_wp ((Whole.zeroWords_ct 38 8).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro s hc hd
    exact extend_step hc hL hd
  · intro s hc hd
    exact extend_step hc hL hd

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CTEquation`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem equation_setup_wp {g m t} (hc : Ctx L g m t) (hL : L.Ok) (ha : Arguments L m)
    {ch : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = ch) :
    WP isa (.block VerifyMessage.equationArgs) t fun u => Ctx L g m u ∧ EqArgs L u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.E + 120) 64 = ch := by
  refine WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved])) ?_
  intro u ⟨hu,hm,hav⟩
  have a0 := hav (.r0,.caller 0 0) (by simp)
  have a1 := hav (.r1,.caller 3 0) (by simp)
  have a2 := hav (.r2,.frame 120) (by simp)
  have a3 := hav (.r3,.caller 4 0) (by simp)
  change u.gpr .r0 = L.pk+0#32 at a0
  change u.gpr .r1 = L.sig+0#32 at a1
  change u.gpr .r3 = L.scr+0#32 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  exact ⟨hu,⟨a0,a1,a2,a3⟩,hm ▸ hh⟩

theorem equation_call_ct (hL : L.Ok) {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.call "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct verify_ok verify_ct equation_noFrames (fun _ h => equation_ready hL h.1)
  intro a b ar aw br bw h
  have hsp := two_sp h
  have aa := h.2.2.1.1
  have ab := h.2.2.2.1
  have pk₁ := Ctx.input_bytes h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have pk₂ := Ctx.input_bytes h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)
  have sig₁ := Ctx.input_bytes h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  have sig₂ := Ctx.input_bytes h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)
  simp only [verifyLocal, State.withRegions_gpr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    aa.1, aa.2.1, aa.2.2.1, aa.2.2.2, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2]
  have ac : State.addr (L.E+120) = State.addr L.E+120 := frame_addr hL (d := 120) (by decide)
  rw [ac]
  refine ⟨hsp,trivial,trivial,trivial,trivial,?_⟩
  have kp := pk₁.trans (hpk.trans pk₂.symm)
  have ks := sig₁.trans (hsig.trans sig₂.symm)
  have kh := h.2.2.1.2.trans h.2.2.2.2.symm
  change Spec.Ed25519.bytesAt a.mem (State.addr L.pk) 32 = Spec.Ed25519.bytesAt b.mem (State.addr L.pk) 32 at kp
  change Spec.Ed25519.bytesAt a.mem (State.addr L.sig) 64 = Spec.Ed25519.bytesAt b.mem (State.addr L.sig) 64 at ks
  rw [kp,ks,kh]

theorem equation_step_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    {challenge : List Byte}
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32 = Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64 = Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (Whole.callWith VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hs : RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge)
      (.block VerifyMessage.equationArgs)
      (Two L g₁ g₂ m₁ m₂ fun t => EqArgs L t ∧ Spec.Ed25519.bytesAt t.mem (State.addr L.E + 120) 64 = challenge) := by
    apply two_wp ((Whole.setup_ct
      [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)] []).mono
      (fun _ _ h => two_sp h) (fun _ _ _ => True.intro))
    · intro t hc hh
      exact equation_setup_wp hc hL ha hh
    · intro t hc hh
      exact equation_setup_wp hc hL hb hh
  exact hs.seq (equation_call_ct hL hpk hsig)

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem hash_result_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hm : hashInput L m₁ = hashInput L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) VG.Impl.Ed25519.Arm.VerifyMessage.hash
      (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (State.addr L.E+184) 64 =
        Spec.Sha512.sha512 (hashInput L m₁)) := by
  refine two_wp ((hash_ct hL ha hb).mono (fun _ _ h => h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact hash_ok hc hL ha
  · intro t hc _
    refine WP.mono (hash_ok hc hL hb) fun u ⟨hu,hh⟩ => ⟨hu,?_⟩
    rw [hm]
    exact hh

theorem body_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (hpk : Spec.Ed25519.bytesAt m₁ (State.addr L.pk) 32=Spec.Ed25519.bytesAt m₂ (State.addr L.pk) 32)
    (hmsg : Spec.Ed25519.bytesAt m₁ (State.addr L.msg) L.len.toNat=Spec.Ed25519.bytesAt m₂ (State.addr L.msg) L.len.toNat)
    (hsig : Spec.Ed25519.bytesAt m₁ (State.addr L.sig) 64=Spec.Ed25519.bytesAt m₂ (State.addr L.sig) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) body
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hm : hashInput L m₁=hashInput L m₂ := by
    rw [hashInput_eq,hashInput_eq,hpk,hmsg,hsig]
  exact (hash_result_ct hL ha hb hm).seq
    ((reduce_ct hL ha hb _).seq ((extend_ct hL _).seq (equation_step_ct hL ha hb hpk hsig)))

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Entry`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0),32⟩
    let msg : Region := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩
    let sig : Region := ⟨State.addr (s.gpr .r3),64⟩
    let scr : Region := ⟨State.addr (stackArg s 0),8192⟩
    let args : Region := ⟨State.addr s.sp,4⟩
    let stk : Region := ⟨State.addr s.sp - 280,280⟩
    s.rd = [pk,msg,sig,args] ∧ s.wr = [scr] ∧
    pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
    stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
    (s.gpr .r0).toNat+32≤2^32 ∧ (s.gpr .r1).toNat+(s.gpr .r2).toNat≤2^32 ∧
    (s.gpr .r3).toNat+64≤2^32 ∧ (stackArg s 0).toNat+8192≤2^32 ∧
    280≤s.sp.toNat ∧ s.sp.toNat+4≤2^32
  post s t := t.gpr .r0 = if Spec.Ed25519.verify (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64) then 1 else 0
  pub s t := s.sp=t.sp ∧ s.gpr .r0=t.gpr .r0 ∧ s.gpr .r1=t.gpr .r1 ∧
    s.gpr .r2=t.gpr .r2 ∧ s.gpr .r3=t.gpr .r3 ∧ stackArg s 0=stackArg t 0 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r0)) 32 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r1)) (t.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 64 = Spec.Ed25519.bytesAt t.mem (State.addr (t.gpr .r3)) 64

def lay (s : State) : Lay := ⟨s.gpr .r0,s.gpr .r1,s.gpr .r2,s.gpr .r3,stackArg s 0,Whole.base s⟩

theorem entry_below {s : State} (h : verifyMessageLocal.pre s) : 280≤s.sp.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hb,_⟩ := h
  exact hb

theorem entry_top {s : State} (h : verifyMessageLocal.pre s) : s.sp.toNat+4≤2^32 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ht⟩ := h
  exact ht

theorem original_args {s : State} (hb : 280 ≤ s.sp.toNat) :
    (lay s).ORIGINALARGS = ⟨State.addr s.sp,4⟩ := by
  unfold Lay.ORIGINALARGS lay
  rw [Whole.base_addr hb, BitVec.sub_add_cancel]

theorem stack_eq {s : State} (hb : 280 ≤ s.sp.toNat) :
    Whole.stack s = ⟨State.addr s.sp-280,280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr hb]

theorem entry_writes {s : State} (h : verifyMessageLocal.pre s) :
    ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hb := entry_below h
  obtain ⟨_,hw,_,_,_,_,_,_,_,hc,_⟩ := h
  intro r hr
  rw [hw,List.mem_singleton] at hr
  subst r
  rw [stack_eq hb]
  exact hc

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨_,_,pc,mc,sc,ac,kp,km,ks,kc,np,nm,ns,nc,hb,_⟩ := h
  have fr : Region.Sub (Whole.FR (Whole.base s)) (Whole.stack s) := Region.sub_prefix (by decide)
  have ar : Region.Sub (Whole.ARGS (Whole.base s)) (Whole.stack s) := Offset.sub_base _ (by decide)
  rw [← stack_eq hb] at kp km ks kc
  refine ⟨?_,?_,?_,kc.sub_left fr,np,nm,ns,nc⟩
  · have he := Whole.base_top (s := s) hb
    have hs := s.sp.isLt
    change (Whole.base s).toNat+272≤2^32
    omega
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact pc
    · exact mc
    · exact sc
    · rw [original_args hb]; exact ac
    · exact kc.sub_left ar
  · simp only [Lay.inputs,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact kp.sub_left fr
    · exact km.sub_left fr
    · exact ks.sub_left fr
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)

theorem entry_ctx {s p : State} (h : verifyMessageLocal.pre s) (hp : Whole.Saved (Whole.entered s) 5 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  simp only [Lay.inputs, original_args (entry_below h)]
  simpa only [Whole.bodyRd,h.1,Whole.bodyWr,h.2.1,Lay.outputs,
    Lay.PK,Lay.MSG,Lay.SIG,Lay.SCR,Lay.ARGS,Whole.ARGS,show BitVec.ofNat 64 248 = (248 : Addr) from rfl,lay,List.cons_append,List.nil_append] using hc

theorem entry_regions {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args (entry_below h)]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1,
    Lay.SIG, Lay.PK, Lay.MSG, Lay.SCR, Lay.ARGS, Whole.ARGS,
    show BitVec.ofNat 64 248 = (248 : Addr) from rfl, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_args {s p : State} (h : verifyMessageLocal.pre s)
    (hp : Whole.Saved (Whole.entered s) 5 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words (entry_below h) (by decide : 5 ≤ 6) (entry_top h) hp hj
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
      Nat.reduceSub, Nat.mul_zero, BitVec.add_zero, Lay.value, lay,
      stackArg, stackArgAddr] using hw

theorem entry_read {s : State} (h : verifyMessageLocal.pre s) : ∀ j < 5, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4*(j-4)))) 4 := by
  intro j hj h4
  have : j = 4 := by omega
  subst j
  simp only [Nat.reduceSub,Nat.mul_zero,BitVec.add_zero]
  exact ⟨⟨State.addr s.sp,4⟩, List.mem_append_left _ (by rw [h.1]; simp), by simp [Region.Contains]⟩

theorem entry_input {s : State} (h : verifyMessageLocal.pre s) {m : Mem}
    (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd) (hn : r.len≤2^64) :
    Spec.Ed25519.bytesAt m r.base r.len = Spec.Ed25519.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR]
  have hb := entry_below h
  obtain ⟨hrd,_,_,_,_,_,kp,km,ks,_⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rw [← stack_eq hb] at kp km ks
  rcases hr with rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact km.symm
  · exact ks.symm
  · rw [← original_args hb]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.CT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Correct`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ verifyMessageLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 5 ≤ 6) (entry_below h) (entry_top h) (entry_read h) (entry_writes h)
    (P := fun m _ r => r = signWord (Spec.Ed25519.verify
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r0)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) 64)))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args h hp))
      fun u ⟨hu,ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu,ho⟩)
  refine WP.mono hw fun u ⟨hu,m,hf,hp⟩ => ⟨hu,?_⟩
  have pk := entry_input h hf (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [h.1]; simp) (by change 32≤2^64; decide)
  have msg := entry_input h hf (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat≤2^64; have := (s.gpr .r2).isLt; omega)
  have sig := entry_input h hf (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [h.1]; simp) (by change 64≤2^64; decide)
  change u.gpr .r0 = signWord _
  rw [hp,pk,msg,sig]

end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem lay_eq {s t : State} (h : verifyMessageLocal.pub s t) : lay s=lay t := by
  obtain ⟨sp,h0,h1,h2,h3,h4,_⟩ := h
  simp only [lay,Whole.base,sp,h0,h1,h2,h3,h4]

theorem saved_inputs_eq {s t p q : State} (hs : verifyMessageLocal.pre s) (ht : verifyMessageLocal.pre t)
    (hp : verifyMessageLocal.pub s t) (hpa : Whole.Saved (Whole.entered s) 5 p)
    (hqb : Whole.Saved (Whole.entered t) 5 q) :
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).pk) 32 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).pk) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).msg) (lay s).len.toNat =
      Spec.Ed25519.bytesAt q.mem (State.addr (lay s).msg) (lay s).len.toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (lay s).sig) 64 = Spec.Ed25519.bytesAt q.mem (State.addr (lay s).sig) 64 := by
  have fp := Whole.saved_frame (entry_below hs) hpa
  have fq := Whole.saved_frame (entry_below ht) hqb
  obtain ⟨_,h0,h1,h2,h3,_,pk,msg,sig⟩ := hp
  have epk := entry_input hs fp (r := ⟨State.addr (s.gpr .r0),32⟩) (by rw [hs.1]; simp) (by change 32≤2^64; decide)
  have fpk := entry_input ht fq (r := ⟨State.addr (t.gpr .r0),32⟩) (by rw [ht.1]; simp) (by change 32≤2^64; decide)
  have emsg := entry_input hs fp (r := ⟨State.addr (s.gpr .r1),(s.gpr .r2).toNat⟩) (by rw [hs.1]; simp)
    (by have := (s.gpr .r2).isLt; change (s.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have fmsg := entry_input ht fq (r := ⟨State.addr (t.gpr .r1),(t.gpr .r2).toNat⟩) (by rw [ht.1]; simp)
    (by have := (t.gpr .r2).isLt; change (t.gpr .r2).toNat ≤ 2 ^ 64; omega)
  have esig := entry_input hs fp (r := ⟨State.addr (s.gpr .r3),64⟩) (by rw [hs.1]; simp) (by change 64≤2^64; decide)
  have fsig := entry_input ht fq (r := ⟨State.addr (t.gpr .r3),64⟩) (by rw [ht.1]; simp) (by change 64≤2^64; decide)
  change Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r0)) 32=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r0)) 32 ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat ∧
    Spec.Ed25519.bytesAt p.mem (State.addr (s.gpr .r3)) 64=Spec.Ed25519.bytesAt q.mem (State.addr (s.gpr .r3)) 64
  rw [epk,emsg,esig,h0,h1,h2,h3,fpk,fmsg,fsig]
  rw [h0] at pk
  rw [h1,h2] at msg
  rw [h3] at sig
  exact ⟨pk,msg,sig⟩

theorem verifyMessage_ct :
    ConstantTime isa verifyMessageLocal.pre verifyMessageLocal.pub code := by
  refine Whole.wrap_ct (by decide : 5 ≤ 6) (fun _ _ hp => hp.1)
    (fun _ hs => entry_below hs) (fun _ hs => entry_top hs) (fun _ hs => entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p,q,hpa,hqb,rfl,rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    obtain ⟨pk,msg,sig⟩ := saved_inputs_eq hs ht hp hpa hqb
    exact ⟨(body_ct (lay_ok hs) (entry_args hs hpa) hqa pk msg sig _ _ _ _ _ _
      ⟨entry_ctx hs hpa,hq,trivial,trivial⟩ ea eb).1,trivial⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
end

/-! Merged from `Proof.Ed25519.Arm.VerifyMessage.Contract`. -/
section
namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 64 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9001 then 0x40 else 0
  rd := [⟨0x1000,32⟩,⟨0x2000,64⟩,⟨0x3000,64⟩,⟨0x9000,4⟩]
  wr := [⟨0x4000,8192⟩]

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

private theorem pre_bridge (s : State) (h : (Spec.Ed25519.verifyContract Arm.abi 280).pre s) :
    verifyMessageLocal.pre s := by
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyMessageLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verifyMessage_implies : verifyMessageLocal.Implies (Spec.Ed25519.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Arm.abi,Arm.argRegs,Arm.reduceClassify,Arm.Loc.val,Arm.State.addr] at h
    obtain ⟨sp, bytes, pk, msg, len, sig, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range])
    obtain ⟨first, middle⟩ := List.append_inj' first (by
      simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, len])
    exact ⟨sp, pk, msg, len, sig, base, first, middle, last⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig,
        Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel


end VG.Proof.Ed25519.Arm.VerifyMessage
end

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm.VerifyMessage

theorem verifyMessage_verified :
    Verified Arm.target code (Spec.Ed25519.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verifyMessage_ok h) verifyMessage_ct
      (.refl verifyMessage_implies.sat_left)) verifyMessage_implies

end VG.Proof.Ed25519.Arm.VerifyMessage
