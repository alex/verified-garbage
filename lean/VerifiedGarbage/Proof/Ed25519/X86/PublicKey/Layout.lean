import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Ed25519.Contract

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86

def pkRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 12⟩]
def pkWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 280
    s.rd = pkRd s ∧ s.wr = pkWr s ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

abbrev esp (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 256
abbrev Ctx (s t : State) : Prop := Whole.Ctx (esp s) s.gpr s.mem (pkRd s) (pkWr s) t

structure Bounds (s : State) : Prop where
  out : (arg s 0).toNat + 32 ≤ 2 ^ 32
  seed : (arg s 1).toNat + 32 ≤ 2 ^ 32
  scratch : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem bounds {s : State} (h : pkLocal.pre s) : Bounds s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, a, b, c, d, e⟩ := h
  exact ⟨a, b, c, d, e⟩

theorem Bounds.frame {s : State} (h : Bounds s) : (esp s).toNat + 272 ≤ 2 ^ 32 := by
  rw [sub_toNat (by have := h.below; omega)]
  have := h.above
  omega

theorem Bounds.call {s : State} (h : Bounds s) : 24 ≤ (esp s).toNat := by
  rw [sub_toNat (by have := h.below; omega)]
  have := h.below
  omega

theorem stack_eq {s : State} (h : Bounds s) : Whole.STK (esp s) = below (s.gpr .esp) 280 := by
  simp only [Whole.STK, below, esp]
  rw [Taint.sub_setWidth (by have := h.below; omega : 256 ≤ (s.gpr .esp).toNat),
    Taint.sub_setWidth h.below, BitVec.sub_sub]
  rfl

/-- Pushing the caller-saved EAX allocates locals without changing callee-saved registers. -/
theorem push_ctx {s : State} (h : pkLocal.pre s) :
    Ctx s (pushed (List.replicate 64 .eax) s) := by
  have hb := bounds h
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; have := hb.below; omega)
  refine ⟨(pushed_rd _ _).trans h.1, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_wr, h.2.1]
    simp only [List.length_replicate]
  · rw [pushed_esp, List.length_replicate]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨Whole.STK (esp s), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [stack_eq hb]
    exact below_sub (by simp) hb.below

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 32⟩
abbrev SEED (s : State) : Region := ⟨(arg s 1).setWidth 64, 32⟩
abbrev SCR (s : State) : Region := ⟨(arg s 2).setWidth 64, 8192⟩
abbrev ARGS (s : State) : Region := ⟨argAddr s 0, 12⟩
abbrev RET (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

structure Facts (s : State) : Prop extends Bounds s where
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR s)
  sc : (SEED s).Disjoint (SCR s)
  ao : (ARGS s).Disjoint (OUT s)
  ac : (ARGS s).Disjoint (SCR s)
  ro : (RET s).Disjoint (OUT s)
  rc : (RET s).Disjoint (SCR s)
  ko : (Whole.STK (esp s)).Disjoint (OUT s)
  ks : (Whole.STK (esp s)).Disjoint (SEED s)
  kc : (Whole.STK (esp s)).Disjoint (SCR s)

theorem facts {s : State} (h : pkLocal.pre s) : Facts s := by
  have hb := bounds h
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, _⟩ := h
  exact ⟨hb, os, oc, sc, ao, ac, ro, rc, stack_eq hb ▸ ko, stack_eq hb ▸ ks, stack_eq hb ▸ kc⟩

theorem arg_address (s : State) (j : Nat) : addr (esp s) (260 + 4 * j) = argAddr s j := by
  simp only [addr, esp, argAddr]
  rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem arg_address64 {s : State} (h : Bounds s) {j : Nat} (hj : j < 3) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by have := h.above; omega)

theorem args_stack {s : State} (h : Bounds s) : (ARGS s).Disjoint (Whole.STK (esp s)) := by
  rw [stack_eq h]
  change Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨((s.gpr .esp) - BitVec.ofNat 32 280).setWidth 64, 280⟩
  rw [arg_address64 h (by decide), Taint.sub_setWidth h.below]
  exact (Offset.disjoint_below_above _ (m := 280) (a := 4) (l := 12) (by decide)).symm

theorem args_contains {s : State} (h : Bounds s) {j : Nat} (hj : j < 3) :
    (ARGS s).Contains (argAddr s j) 4 := by
  change (⟨argAddr s 0, 12⟩ : Region).Contains _ _
  rw [arg_address64 h (by decide), arg_address64 h hj]
  exact Offset.contains _ (by omega) (by omega) (by decide)

theorem original_arg {s t : State} (h : Facts s) (hc : Ctx s t) {j : Nat} (hj : j < 3) :
    t.mem.readW (addr (esp s) (260 + 4 * j)) 32 = arg s j := by
  rw [arg_address]
  exact hc.frame.readW (args_contains h.toBounds hj) (by
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.ao
    · exact h.ac
    · exact args_stack h.toBounds) (by decide)

theorem original_arg_readable {s t : State} (h : Facts s) (hc : Ctx s t) {j : Nat} (hj : j < 3) :
    InRegions (t.rd ++ t.wr) (addr (esp s) (260 + 4 * j)) 4 := by
  rw [arg_address, hc.rd]
  exact ⟨ARGS s, List.mem_append_left _ (by simp [pkRd]), args_contains h.toBounds hj⟩

end VG.Proof.Ed25519.X86.PublicKey
