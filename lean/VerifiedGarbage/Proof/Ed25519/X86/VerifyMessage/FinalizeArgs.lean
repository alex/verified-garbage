import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Hash
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Count

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole VG.Impl.Ed25519.X86.VerifyMessage

def FinArgs (L : Lay) (count : BitVec 64) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.scr ∧ Whole.slots L.E t 3 = L.E + 192 ∧
    Whole.slots L.E t 4 = L.scr + 192 ∧
    Whole.slots L.E t 2 ++ Whole.slots L.E t 1 = count

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem count_keep {t u : State} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] t.mem u.mem)
    {j : Nat} (hj : j = 0 ∨ j = 3 ∨ j = 4) : Whole.slots L.E u j = Whole.slots L.E t j := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  apply Offset.disjoint (e := 4) (k := 8)
  · rcases hj with rfl | rfl | rfl <;> decide
  · rcases hj with rfl | rfl | rfl <;> decide
  · decide

theorem count_frame {m m' : Mem} (hf : Frame [⟨L.E.setWidth 64 + 4, 8⟩] m m') :
    Frame [⟨L.E.setWidth 64, 24⟩] m m' :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (d := 4) (by decide)⟩

theorem finalizeArgs_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    :
    WP isa (.block finalizeArgs) s fun t => Ctx L g m₀ t ∧
      Frame [⟨L.E.setWidth 64, 24⟩] s.mem t.mem ∧
      FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)) t := by
  rw [finalizeArgs, WP.block_append_iff]
  refine WP.mono (args_ok hc hL ha (vs := [.caller 4 0, .const 0, .const 0, .frame 192, .caller 4 192])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_
  have aa := hs.slot hL (j := 0) (by decide) (by decide)
  have ab := hs.slot hL (j := 1) (by decide) (by decide)
  have ac := hs.slot hL (j := 2) (by decide) (by decide)
  have ad := hs.slot hL (j := 3) (by decide) (by decide)
  have ae := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 0 = L.scr + 0#32 at aa
  rw [BitVec.add_zero] at aa
  change Whole.slots L.E u 1 = 0#32 at ab
  change Whole.slots L.E u 2 = 0#32 at ac
  change Whole.slots L.E u 3 = L.E + 192 at ad
  change Whole.slots L.E u 4 = L.scr + 192 at ae
  have hr : InRegions (u.rd ++ u.wr) (addr L.E 268) 4 := by
    refine ⟨L.ARGS, ?_, ?_⟩
    · rw [hu.rd]; simp [Lay.inputs]
    · rw [addr_eq (by have := hL.top; omega)]
      exact Offset.contains _ (e := 260) (k := 20) (d := 268) (n := 4) (by decide) (by decide) (by decide)
  have hx : u.mem.readW (addr L.E 268) 32 = L.len := by
    rw [addr_eq (by have := hL.top; omega)]
    exact (hu.arg_word hL (j := 2) (by decide)).trans (ha 2 (by decide))
  refine WP.mono (Whole.Ctx.count hu (index := 2) (n := 64) (by have := hL.top; omega) hr hx)
    fun t ⟨ht, hft, hlo, hhi⟩ => ⟨ht, hf.trans (count_frame hft),
      (count_keep hft (.inl rfl)).trans aa,
      (count_keep hft (.inr (.inl rfl))).trans ad,
      (count_keep hft (.inr (.inr rfl))).trans ae, ?_⟩
  show (t.mem.readW (L.E.setWidth 64 + 8#64) 32 ++ t.mem.readW (L.E.setWidth 64 + 4#64) 32) = BitVec.ofNat 64 (L.len.toNat + 64)
  change t.mem.readW (L.E.setWidth 64 + 8#64) 32 = _ at hhi
  change t.mem.readW (L.E.setWidth 64 + 4#64) 32 = _ at hlo
  rw [hhi, hlo]
  exact Whole.count_pair L.len 64 (by decide)

end VG.Proof.Ed25519.X86.VerifyMessage
