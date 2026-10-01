import VerifiedGarbage.Impl.Ed25519.X86.SignCached
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out.setWidth 64, 64⟩
abbrev SEED : Region := ⟨L.seed.setWidth 64, 32⟩
abbrev PK : Region := ⟨L.pk.setWidth 64, 32⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev SCR : Region := ⟨L.scr.setWidth 64, 8192⟩
abbrev ARGS : Region := ⟨L.E.setWidth 64 + 260, 24⟩
abbrev RET : Region := ⟨L.E.setWidth 64 + 256, 4⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := Whole.STK L.E
def inputs : List Region := [L.SEED, L.PK, L.MSG, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.msg | 4 => L.len | _ => L.scr

structure Ok : Prop where
  below : 24 ≤ L.E.toNat
  top : L.E.toNat + 284 ≤ 2 ^ 32
  os : ∀ r ∈ L.inputs, L.OUT.Disjoint r
  oc : L.OUT.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ro : L.RET.Disjoint L.OUT
  no : L.out.toNat + 64 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

namespace Ctx
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem input_bytes (hc : Ctx L g m₀ t) (hL : L.Ok)
    {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt t.mem r.base r.len = Spec.Ed25519.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine Frame.bytes hc.frame ?_ hn (List.mem_range.mp hi)
  intro R hR
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact (hL.os r hr).symm
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 =
      m₀.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 260) (k := 24) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl | rfl
    · exact (hL.os _ ha).symm
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.X86.SignCached
