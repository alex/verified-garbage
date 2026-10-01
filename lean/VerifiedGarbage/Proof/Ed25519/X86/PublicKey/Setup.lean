import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Layout
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
import VerifiedGarbage.Impl.Ed25519.X86.PublicKey

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)

def argValue (s : State) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => esp s + BitVec.ofNat 32 d
  | .caller i d => arg s i + BitVec.ofNat 32 d

theorem setup_ok {s t : State} (h : Facts s) (hc : Ctx s t) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 3 v) :
    WP isa (.block (setup 0 vs)) t fun u => Ctx s u ∧
      Frame [⟨(esp s).setWidth 64, 24⟩] t.mem u.mem ∧
      ∀ j (hj : j < vs.length), Whole.slots (esp s) u j = argValue s (vs[j]'hj) := by
  refine WP.mono (Whole.Ctx.setup hc (n := 3) (by have := h.toBounds.frame; omega)
    (fun j hj => original_arg_readable h hc hj) (by omega) hv) fun u ⟨hu, hf, hs⟩ => ⟨hu, hf, ?_⟩
  intro j hj
  have e := hs j hj
  simp only [Nat.zero_add] at e
  rw [addr_eq (by have := h.toBounds.frame; omega)] at e
  rw [Whole.slots, e]
  generalize he : vs[j]'hj = v
  have vv := hv (vs[j]'hj) (List.getElem_mem hj)
  rw [he] at vv
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller i d =>
    exact congrArg (· + BitVec.ofNat 32 d) (original_arg h hc vv)

/-- Setup only writes the outgoing argument area, so unrelated buffers survive. -/
theorem setup_disjoint {s : State} (h : Facts s) :
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SCR s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (SEED s) ∧
    (⟨(esp s).setWidth 64, 24⟩ : Region).Disjoint (OUT s) := by
  have sub : Region.Sub ⟨(esp s).setWidth 64, 24⟩ (Whole.STK (esp s)) :=
    fun p hp => Whole.frame_sub (esp s) p (Region.sub_prefix (by decide) p hp)
  exact ⟨h.kc.sub_left sub, h.ks.sub_left sub, h.ko.sub_left sub⟩

end VG.Proof.Ed25519.X86.PublicKey
