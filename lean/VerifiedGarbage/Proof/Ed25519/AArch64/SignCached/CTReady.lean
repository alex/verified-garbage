import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.CallCT

/-! Merged from `Proof.Ed25519.AArch64.SignCached.CTCommon`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
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
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (setup args)) hint).isSome = true) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block (setup args))
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L args)) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) ht) ?_ ?_
  · intro s hc _
    exact WP.mono (args_ok hc hL ha hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (args_ok hc hL hb hn hv hr) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

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

end VG.Proof.Ed25519.AArch64.SignCached
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (.inr (scratchWithin L))
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : BaseArgs L s) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
  have cov : Covers (baseRd L ++ baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (baseWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (baseWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨baseRd L, baseWr L, base_pre hL ha, cov, ws⟩

def mul_ready (hL : L.Ok) (ha : MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  exact ⟨mulRd L, mulWr L, mul_pre hL ha, cov, ws⟩

def init_ready (ha : s.gpr .x0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha, Whole.covers_writes hw, hw⟩

def UpdateArgs (L : Lay) (count p len : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = p ∧ s.gpr .x3 = len ∧ s.gpr .x4 = L.scr + 192

def update_ready (hL : L.Ok) (hsp : s.sp = L.E) {count p len : Addr} (hi : Input L p len)
    (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd p len, Whole.hashWr L.scr,
    Whole.update_pre ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hi.scratch (by rw [hsp]; exact hL.e16)
      (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hi.ck hL), update_covers hi, hw⟩

def FinalArgs (L : Lay) (count : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = L.E + 192 ∧ s.gpr .x3 = L.scr + 192

def finalize_ready (hL : L.Ok) (hsp : s.sp = L.E) {count : Addr} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs s :=
  ⟨[], Whole.finalizeWr L.scr (L.E + 192),
    Whole.finalize_pre ha.1 ha.2.2.1 ha.2.2.2 (hL.kc.sub_left (digestWithin L).sub)
      (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
      (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (final_writes L), final_writes L⟩

end VG.Proof.Ed25519.AArch64.SignCached
