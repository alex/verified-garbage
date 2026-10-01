import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Layout
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup

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
