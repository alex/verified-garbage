import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 5, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def known : Value → Prop
  | .caller j _ => j < 5
  | _ => True

def value (L : Lay) : Value → BitVec 64
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

def OutArgs (L : Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = value L p.2

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem Ctx.value (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {a : Value} (hv : known a) : Whole.value L.E s.mem a = value L a := by
  cases a with
  | const => rfl
  | frame => rfl
  | caller j d =>
    change j < 5 at hv
    change s.mem.readW (L.E + BitVec.ofNat 64 (256 + 8*j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL (by omega), ha j hv]
    rfl

theorem args_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hk : ∀ p ∈ args, known p.2)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) s fun t => Ctx L g v m₀ t ∧
      t.mem = s.mem ∧ OutArgs L args t := by
  refine WP.mono (Whole.Ctx.setup hc hn hv (by simp [Lay.inputs, Lay.ARGS, Whole.ARGS]) hregs)
    fun t ⟨ht, hm, hvals⟩ => ⟨ht, hm, ?_⟩
  intro p hp
  exact (hvals p hp).trans (hc.value hL ha (hk p hp))

end VG.Proof.Ed25519.AArch64.VerifyMessage
