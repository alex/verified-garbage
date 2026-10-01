import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm

structure Lay where
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : Lay)
abbrev SIG : Region := ⟨State.addr L.sig, 64⟩
abbrev PK : Region := ⟨State.addr L.pk, 32⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := ⟨State.addr L.E + BitVec.ofNat 64 248, 24⟩
abbrev FR : Region := Whole.FR L.E
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.FR.Disjoint r
  kc : L.FR.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 64 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

/-- The scratch allocation leaves enough address space for either hash prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 32 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  have ap : (State.addr L.msg).toNat = L.msg.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have ac : (State.addr L.scr).toNat = L.scr.toNat := BitVec.toNat_setWidth_of_le (by decide)
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : State.addr L.msg ≤ State.addr L.scr
  · have hn : ¬ L.MSG.Contains (State.addr L.scr) 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : (State.addr L.msg).toNat ≤ (State.addr L.scr).toNat := hp
    rw [ap, ac] at hn hp'
    omega
  · have hp' : State.addr L.scr ≤ State.addr L.msg := by
      change (State.addr L.scr).toNat ≤ (State.addr L.msg).toNat
      change ¬ (State.addr L.msg).toNat ≤ (State.addr L.scr).toNat at hp
      omega
    have hn : ¬ L.SCR.Contains (State.addr L.msg) 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : (State.addr L.scr).toNat ≤ (State.addr L.msg).toNat := hp'
    rw [ap, ac] at hn hp''
    omega


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
  rcases hR with rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 6) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.Arm.VerifyMessage
