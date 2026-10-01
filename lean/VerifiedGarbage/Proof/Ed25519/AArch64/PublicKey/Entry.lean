import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 32⟩
    let seed : Region := ⟨s.gpr .x1, 32⟩
    let scr : Region := ⟨s.gpr .x2, 8192⟩
    let stk : Region := below s.sp 336
    s.rd = [seed] ∧ s.wr = [out, scr] ∧
      out.Disjoint seed ∧ out.Disjoint scr ∧ seed.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint scr ∧
      (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ 336 ≤ s.sp.toNat
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

def lay (s : State) : Lay := ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, Whole.base s⟩

theorem lay_ok {s : State} (h : pkLocal.pre s) : (lay s).Ok := by
  obtain ⟨_, _, os, oc, sc, ko, ks, kc, no, ns, nc, _⟩ := h
  exact ⟨os, oc, sc, ko, ks, kc, no, ns, nc⟩

theorem entry_below {s : State} (h : pkLocal.pre s) : 336 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2

theorem entry_writes {s : State} (h : pkLocal.pre s) :
    ∀ r ∈ s.wr, (below s.sp 336).Disjoint r := by
  intro r hr
  rw [h.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (lay_ok h).ko
  · exact (lay_ok h).kc

theorem entry_ctx {s p : State} (h : pkLocal.pre s) (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr s.v p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  simpa only [Whole.bodyRd, h.1, Whole.bodyWr, h.2.1, Ctx, Lay.inputs, Lay.outputs,
    Lay.SEED, Lay.OUT, Lay.SCR, Lay.ARGS, lay, List.cons_append, List.nil_append] using hc

theorem entry_args {s p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  intro j hj
  have hw := Whole.saved_words hp (j := j) (by omega)
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases he with rfl | rfl | rfl <;> exact hw

def satState : State where
  gpr r := match r with | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem pk_implies : pkLocal.Implies (Spec.Ed25519.publicKeyContract AArch64.abi 336) := by
  sig_implies [Spec.Ed25519.publicKeyContract, Spec.Ed25519.publicKeySig,
    Spec.Ed25519.scratchWords, pkLocal, below, AArch64.abi, AArch64.argRegs]
    [satState] using satState

end VG.Proof.Ed25519.AArch64.PublicKey
