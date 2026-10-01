import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Ed25519.Contract

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

def verifyRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
    ⟨(arg s 3).setWidth 64, 64⟩, ⟨argAddr s 0, 20⟩]
def verifyWr (s : State) : List Region := [⟨(arg s 4).setWidth 64, 8192⟩]

def verifyMessageLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let sig : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = verifyRd s ∧ s.wr = verifyWr s ∧
      pk.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := t.gpr .eax = signWord (Spec.Ed25519.verify
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
    (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) (arg t 2).toNat ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 3).setWidth 64) 64

def lay (s : State) : Lay :=
  ⟨arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, s.gpr .esp - BitVec.ofNat 32 256⟩

theorem entry_bounds {s : State} (h : verifyMessageLocal.pre s) :
    280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem lay_base {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).E.setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 :=
  Taint.sub_setWidth (by have := (entry_bounds h).1; omega)

theorem lay_args {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).ARGS = ⟨argAddr s 0, 20⟩ := by
  rw [Lay.ARGS, lay_base h]
  have ha : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := (entry_bounds h).2; omega)
  rw [ha]
  congr 1
  change _ - 256#64 + 260#64 = _ + 4#64
  rw [show BitVec.ofNat 64 260 = BitVec.ofNat 64 256 + BitVec.ofNat 64 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem lay_ret {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  rw [Lay.RET, lay_base h]
  change (⟨(s.gpr .esp).setWidth 64 - 256#64 + 256#64, 4⟩ : Region) = _
  rw [BitVec.sub_add_cancel]

theorem lay_stack {s : State} (h : verifyMessageLocal.pre s) :
    (lay s).STK = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩ := by
  rw [Lay.STK, Whole.STK, lay_base h, BitVec.sub_sub]
  rfl

theorem lay_ok {s : State} (h : verifyMessageLocal.pre s) : (lay s).Ok := by
  obtain ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na⟩ := h
  have h : verifyMessageLocal.pre s := ⟨rd, wr, pc, mc, sc, ac, rp, rm, rs, rc, kp, km, ks, kc, np, nm, ns, nc, nb, na⟩
  have top : (lay s).E.toNat + 280 ≤ 2 ^ 32 := by
    change (s.gpr .esp - BitVec.ofNat 32 256).toNat + 280 ≤ _
    rw [sub_toNat (by omega)]
    omega
  refine ⟨?_, top, ?_, ?_, ?_, ?_, ?_, np, nm, ns, nc⟩
  · change 24 ≤ (s.gpr .esp - BitVec.ofNat 32 256).toNat
    rw [sub_toNat (by omega)]
    omega
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact pc
    · exact mc
    · exact sc
    · rw [lay_args h]; exact ac
  · intro r hr
    rw [lay_stack h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact kp
    · exact km
    · exact ks
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact Offset.disjoint_below_above _ (by decide)
  · intro r hr
    rw [lay_ret h]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact rp
    · exact rm
    · exact rs
    · rw [Lay.ARGS, lay_base h]
      have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256 + 260 =
          (s.gpr .esp).setWidth 64 + 4 := by
        change _ - 256#64 + 260#64 = _ + 4#64
        rw [show (260#64) = 256#64 + 4#64 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      rw [e]
      exact (Offset.disjoint_base _ (by decide) (by decide)).symm
  · rw [lay_stack h]; exact kc
  · rw [lay_ret h]; exact rc

theorem lay_arguments {s : State} (h : verifyMessageLocal.pre s) : Arguments (lay s) s.mem := by
  intro j hj
  have hb := lay_ok h
  have e : (lay s).E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j) = argAddr s j := by
    rw [← addr_eq (by have := hb.top; omega)]
    simp only [addr, lay, argAddr]
    rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rw [e]
  change arg s j = (lay s).value j
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_ctx {s : State} (h : verifyMessageLocal.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed (List.replicate 64 .eax) s) := by
  have hn := (entry_bounds h).1
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨?_, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_rd, h.1]
    rw [Lay.inputs, lay_args h]
    rfl
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate, Whole.FR, Lay.outputs, Lay.SCR, lay, verifyWr]
  · rw [pushed_esp, List.length_replicate]
    rfl
  · refine Frame.sub hf fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine ⟨(lay s).STK, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [lay_stack h, ← Taint.sub_setWidth hn]
    exact below_sub (by simp) hn

end VG.Proof.Ed25519.X86.VerifyMessage
