import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT

/-! Merged from `Proof.Ed25519.AArch64.VerifyMessage.CTCommon`. -/
section
namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

def Two (L : Lay) (g₁ g₂ : Reg → BitVec 64) (v₁ v₂ : VReg → BitVec 128)
    (m₁ m₂ : Mem) (P : State → Prop) (a b : State) : Prop :=
  Ctx L g₁ v₁ m₁ a ∧ Ctx L g₂ v₂ m₂ b ∧ P a ∧ P b

theorem two_sp {P : State → Prop} {a b : State} (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b) :
    a.sp = b.sp := h.1.sp.trans h.2.1.sp.symm

theorem two_wp {P Q : State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c fun _ _ => True)
    (ha : ∀ t, Ctx L g₁ v₁ m₁ t → P t → WP isa c t fun u => Ctx L g₁ v₁ m₁ u ∧ Q u)
    (hb : ∀ t, Ctx L g₂ v₂ m₂ t → P t → WP isa c t fun u => Ctx L g₂ v₂ m₂ u ∧ Q u) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) c (Two L g₁ g₂ v₁ v₂ m₁ m₂ Q) :=
  (hct.wp fun a b h => ⟨ha a h.1 h.2.2.1, hb b h.2.1 h.2.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2, h.2.2.2⟩

theorem setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂)
    (args : List (Reg × Value)) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, known p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hk hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

theorem args_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value} (hp : p ∈ args) :
    a.gpr p.1 = b.gpr p.1 := (h.2.2.1 p hp).trans (h.2.2.2 p hp).symm

theorem call_gpr_eq {args : List (Reg × Value)} {a b : State}
    (h : Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args) a b) {p : Reg × Value}
    (hp : p ∈ args) (hl : p.1 ∉ linkRegs) : a.callEntry.gpr p.1 = b.callEntry.gpr p.1 := by
  rw [State.callEntry_gpr _ hl, State.callEntry_gpr _ hl]
  exact args_eq h hp

theorem call_ct {P : State → Prop} {k : Contract isa} {c : Prog isa} {name : String}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c) (hd : c.aarch64Depth ≤ 1)
    (ready : ∀ {g v m t}, Ctx L g v m t → P t → Whole.CallReady k L.E L.inputs L.outputs t)
    (kp : ∀ (a b : State) ar aw br bw, Two L g₁ g₂ v₁ v₂ m₁ m₂ P a b →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw)) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ P) (.call name c)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply two_wp
  · refine Whole.callEx correct ct fun a b h => ?_
    let ra := ready h.1 h.2.2.1
    let rb := ready h.2.1 h.2.2.2
    obtain ⟨ca, wa⟩ := Whole.CallReady.covers_state h.1 ra
    obtain ⟨cb, wb⟩ := Whole.CallReady.covers_state h.2.1 rb
    exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ h, ca, wa, cb, wb⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs) correct hd) fun _ hu => ⟨hu, trivial⟩
  · intro t hc hs
    exact WP.mono (Whole.CallReady.wpF hc (ready hc hs) correct hd) fun _ hu => ⟨hu, trivial⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
end

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64
variable {L : Lay} {t : State}

def init_ready (h0 : t.gpr .x0=L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t :=
  ⟨[],Whole.initWr L.scr,Whole.init_pre h0,
    Whole.covers_writes (Whole.init_writes (by simp [Lay.outputs])),
    Whole.init_writes (by simp [Lay.outputs])⟩

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) {p len : Addr} (h0 : t.gpr .x0=L.scr) (h2 : t.gpr .x2=p)
    (h3 : t.gpr .x3=len) (h4 : t.gpr .x4=L.scr+192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  refine ⟨Whole.updateRd p len,Whole.hashWr L.scr,Whole.update_pre h0 h2 h3 h4 hd (by rw [hsp]; exact hL.e16)
    (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.ck_within hi),?_,hash_writes⟩
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    obtain ⟨R,hR,hs⟩ := hi
    exact .inr ⟨R,List.mem_append_left _ hR,hs⟩
  · rcases hash_writes r hr with hf | ⟨R,hR,hs⟩
    · exact .inl hf
    · exact .inr ⟨R,List.mem_append_right _ hR,hs⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (h0 : t.gpr .x0=L.scr)
    (h2 : t.gpr .x2=L.E+192) (h3 : t.gpr .x3=L.scr+192) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t :=
  ⟨[],Whole.finalizeWr L.scr (L.E+192),Whole.finalize_pre h0 h2 h3
    (hL.kc.sub_left (Offset.sub_base _ (by decide))) (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes finalize_writes,finalize_writes⟩

def reduce_ready (hL : L.Ok) (ha : ReduceArgs L 128 t) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs t := by
  refine ⟨reduceRd L,reduceWr L 128,reduce_pre hL ha,?_,?_⟩
  · apply covers
    simp only [reduceRd,reduceWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratch_covered L)
  · apply writes
    simp only [reduceWr,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratchWithin L)

def equation_ready (hL : L.Ok) (ha : EqArgs L t) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs t :=
  ⟨equationRd L,equationWr L,equation_pre hL ha,equation_covers,equation_writes⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
