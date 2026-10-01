import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 6, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def value (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

def OutArgs (L : Lay) (args : List (Reg × Value)) (s : State) : Prop :=
  ∀ p ∈ args, s.gpr p.1 = value L p.2

def StackArgs (L : Lay) (vs : List Value) (s : State) : Prop :=
  ∀ j (hj : j < vs.length), stackArg s j = value L (vs[j]'hj)

theorem Ctx.value (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) {v : Value} (hv : Whole.valid v) :
    Whole.value L.E s.mem v = value L v := by
  cases v with
  | const n => rfl
  | frame d => rfl
  | caller j d =>
    change _ + BitVec.ofNat 32 d = _ + BitVec.ofNat 32 d
    rw [hc.arg_word hL hv.1, ha j hv.1]

theorem args_regs_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args [])) s fun t => Ctx L g m₀ t ∧ t.mem = s.mem ∧ OutArgs L args t := by
  have rd : ∀ j < 6, InRegions (s.rd ++ s.wr) (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    intro j hj
    refine ⟨L.ARGS, ?_, Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
    rw [hc.rd]
    exact List.mem_append_left _ (by simp [Lay.inputs])
  refine WP.mono (Whole.setupRegs_ok hc.sp hL.top hn hv rd) fun t ⟨ht, hargs⟩ => ?_
  refine ⟨hc.regs ht.rd ht.wr ht.sp ?_ ht.mem, ht.mem, ?_⟩
  · intro r hpres _
    apply ht.regs
    intro hh
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hh
    exact hr p hp (he ▸ hpres)
  · intro p hp
    exact (hargs p hp).trans (hc.value hL ha (hv p hp))

theorem args_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, Whole.valid v)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args stack)) s fun t => Ctx L g m₀ t ∧
      Frame [⟨State.addr L.E, 24⟩] s.mem t.mem ∧ OutArgs L args t ∧ StackArgs L stack t := by
  refine WP.mono (Whole.Ctx.setup hc hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun t ⟨ht, hf, hg, hstack⟩ => ⟨ht, hf, ?_, ?_⟩
  · intro p hp
    exact (hg p hp).trans (hc.value hL ha (hv p hp))
  · intro j hj
    exact (hstack j hj).trans (hc.value hL ha (hvs _ (List.getElem_mem hj)))

end VG.Proof.Ed25519.Arm.SignCached
