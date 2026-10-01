import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 6, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def value (L : Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : Lay) (args : List (Reg × Value)) (t : State) : Prop :=
  ∀ p ∈ args, t.gpr p.1 = value L p.2

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {x : Value} (hx : Whole.valid x) : Whole.value L.E s.mem x = value L x := by
  cases x with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hx.1, ha j hx.1]
    rfl

theorem args_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => Ctx L g v m₀ t ∧ t.mem = s.mem ∧ OutArgs L args t := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hr)
    fun t ⟨ht, hm, hs⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hs p hp).trans (hc.value hL ha (hv p hp))

end VG.Proof.Ed25519.AArch64.SignCached
