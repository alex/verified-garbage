import VerifiedGarbage.Impl.Ed25519.AArch64.PublicKey
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.Bytes

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

structure Lay where
  out : Addr
  seed : Addr
  scr : Addr
  E : Addr

namespace Lay
variable (L : Lay)
abbrev OUT : Region := ⟨L.out, 32⟩
abbrev SEED : Region := ⟨L.seed, 32⟩
abbrev SCR : Region := ⟨L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨L.E, 336⟩
def inputs : List Region := [L.SEED, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : Addr := match j with | 0 => L.out | 1 => L.seed | _ => L.scr
structure Ok : Prop where
  os : L.OUT.Disjoint L.SEED
  oc : L.OUT.Disjoint L.SCR
  sc : L.SEED.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ks : L.STK.Disjoint L.SEED
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 32 ≤ 2 ^ 64
  ns : L.seed.toNat + 32 ≤ 2 ^ 64
  nc : L.scr.toNat + 8192 ≤ 2 ^ 64
end Lay

abbrev Ctx (L : Lay) (g : Reg → Addr) (vec : VReg → BitVec 128) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g vec m₀ L.inputs L.outputs t

def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j < 3, m.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 = L.value j

def argValue (L : Lay) : Value → Addr
  | .const n => BitVec.ofNat 64 n
  | .frame d => L.E + BitVec.ofNat 64 d
  | .caller j d => L.value j + BitVec.ofNat 64 d

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 256 ≤ 336)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 256 + 48 ≤ 336)

theorem Ctx.seed_bytes (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hc.frame.bytes (R := L.SEED) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.os.symm
  · exact hL.sc
  · exact (hL.ks.sub_left (frame_sub L)).symm

theorem Ctx.arg_word (hc : Ctx L g vec m₀ t) (hL : L.Ok) {j : Nat} (hj : j < 3) :
    t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      m₀.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 := by
  refine hc.frame.readW (r := L.ARGS)
    (Offset.contains _ (e := 256) (k := 48) (by omega) (by omega) (by decide)) ?_ (by decide)
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.ko.sub_left (args_sub L)
  · exact hL.kc.sub_left (args_sub L)
  · exact Offset.disjoint_base _ (by decide : 256 ≤ 256) (by decide : 256 + 48 ≤ 2 ^ 64)

theorem setup_ok (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, Whole.valid p.2)
    (hi : ∀ p ∈ args, ∀ j d, p.2 = .caller j d → j < 3)
    (hr : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args)) t fun u => Ctx L g vec m₀ u ∧ u.mem = t.mem ∧
      ∀ p ∈ args, u.gpr p.1 = argValue L p.2 := by
  refine WP.mono (hc.setup hn hv (by simp [Lay.inputs]) hr) fun u ⟨hu, hm, hs⟩ => ⟨hu, hm, ?_⟩
  intro p hp
  rw [hs p hp]
  rcases p with ⟨r, v⟩
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    have hj := hi (r, .caller j d) hp j d rfl
    simp only [Whole.value, argValue]
    change t.mem.readW (L.E + BitVec.ofNat 64 (256 + 8 * j)) 64 + BitVec.ofNat 64 d = _
    rw [hc.arg_word hL hj, ha j hj]

end VG.Proof.Ed25519.AArch64.PublicKey
