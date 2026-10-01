import VerifiedGarbage.Impl.Ed25519.Arm.PublicKey
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨State.addr L.out, 32⟩
abbrev SEED : Region := ⟨State.addr L.seed, 32⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  top : L.E.toNat + 272 ≤ 2 ^ 32
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 32
  ns : L.seed.toNat + 32 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem Ctx.seed_bytes (hc : Ctx L g m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem (State.addr L.seed) 32 = Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm

theorem Ctx.arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem value_eq (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (v : Value) (hi : ∀ j d, v = .caller j d → j < 3) : Whole.value L.E t.mem v = argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, argValue]
    rw [hc.arg_word hL (hi j d rfl), ha j (hi j d rfl)]

theorem setup_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, Whole.valid v)
    (his : ∀ v ∈ stk, ∀ j d, v = .caller j d → j < 3) :
    WP isa (.block (setup args stk)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = argValue L (stk[j]'hj)) := by
  refine WP.mono (hc.setup hL.top hn hv hs hvs (by simp [Lay.inputs]) hr)
    fun u ⟨hu, hm, hregs, hstk⟩ => ⟨hu, hm, ?_, ?_⟩
  · intro p hp
    rw [hregs p hp, value_eq hc hL ha _ (hi p hp)]
  · intro j hj
    rw [hstk j hj, value_eq hc hL ha _ (his _ (List.getElem_mem hj))]

end VG.Proof.Ed25519.Arm.PublicKey
