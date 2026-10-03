import VerifiedGarbage.Impl.Ed25519.X86.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup

/-! Merged from `Proof.Ed25519.X86.VerifyMessage.Layout`. -/
section
/-! Buffer geometry of complete Ed25519 verification on x86. -/
namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86

structure Lay where
  pk : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : Lay)
abbrev PK : Region := ⟨L.pk.setWidth 64, 32⟩
abbrev MSG : Region := ⟨L.msg.setWidth 64, L.len.toNat⟩
abbrev SIG : Region := ⟨L.sig.setWidth 64, 64⟩
abbrev SCR : Region := ⟨L.scr.setWidth 64, 8192⟩
abbrev ARGS : Region := ⟨L.E.setWidth 64 + 260, 20⟩
abbrev RET : Region := ⟨L.E.setWidth 64 + 256, 4⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := Whole.STK L.E
def inputs : List Region := [L.PK, L.MSG, L.SIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.msg | 2 => L.len | 3 => L.sig | _ => L.scr

structure Ok : Prop where
  below : 24 ≤ L.E.toNat
  top : L.E.toNat + 280 ≤ 2 ^ 32
  sc : ∀ r ∈ L.inputs, r.Disjoint L.SCR
  ks : ∀ r ∈ L.inputs, L.STK.Disjoint r
  rs : ∀ r ∈ L.inputs, L.RET.Disjoint r
  kc : L.STK.Disjoint L.SCR
  rc : L.RET.Disjoint L.SCR
  np : L.pk.toNat + 32 ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 64 ≤ 2 ^ 32
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
  rcases hR with rfl | rfl
  · exact hL.sc r hr
  · exact (hL.ks r hr).symm

theorem arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 5) :
    t.mem.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 =
      m₀.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS) ?_ ?_ (by decide)
  · exact Offset.contains _ (e := 260) (k := 20) (by omega) (by omega) (by decide)
  · intro R hR
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hR
    have ha : L.ARGS ∈ L.inputs := by simp [Lay.inputs]
    rcases hR with rfl | rfl
    · exact hL.sc _ ha
    · exact (hL.ks _ ha).symm

end Ctx
end VG.Proof.Ed25519.X86.VerifyMessage
end

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E.setWidth 64 + BitVec.ofNat 64 (260 + 4 * j)) 32 = L.value j

def value (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), s.mem.readW (addr L.E (4 * j)) 32 = value L (vs[j]'hj)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {v : Value} (hv : Whole.valid 5 v) : Whole.value L.E s.mem v = value L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    simp only [Whole.value, VerifyMessage.value]
    rw [addr_eq (by have := hL.top; omega), hc.arg_word hL hv, ha j hv]

theorem args_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {vs : List Value} (hlen : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid 5 v) :
    WP isa (.block (setup 0 vs)) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧ OutArgs L vs t := by
  refine WP.mono (Whole.Ctx.setup hc (by simpa using hL.top) ?_ (by omega) hv)
    fun t ⟨ht, hf, hvals⟩ => ⟨ht, hf, fun j hj => ?_⟩
  · intro j hj
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hc.rd]; exact List.mem_append_left _ (by simp [Lay.inputs])
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 20) (by omega) (by omega) (by decide)
  · simpa only [Nat.zero_add, hc.value hL ha (hv _ (List.getElem_mem _))] using hvals j hj

end VG.Proof.Ed25519.X86.VerifyMessage
