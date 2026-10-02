import VerifiedGarbage.Proof.X25519.AArch64.Word.Slots
import VerifiedGarbage.Proof.X25519.AArch64.Ladder

/-! Frames for the ladder, including its saved swap bit. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64

structure LoopKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 712 s.mem t.mem

theorem LoopKeep.refl (base : Addr) (s : State) : LoopKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem LoopKeep.trans {base : Addr} {s t u : State} (h : LoopKeep base s t)
    (k : LoopKeep base t u) : LoopKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem LoopKeep.scratch {base : Addr} {s t : State} (h : LoopKeep base s t)
    (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem LoopKeep.of_field {base : Addr} {s t : State} (h : Keep base s t) : LoopKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem LoopKeep.of_invert {base : Addr} {s t : State} (h : IKeep base s t) : LoopKeep base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem LoopKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hr : ∀ r ∈ rs, r ∈ clob ∨ r = .x19) : LoopKeep base s t := by
  refine ⟨fun r hc hn => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hr r hm with hr | hr
    · exact hc hr
    · exact hn hr
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem LoopKeep.bit {base : Addr} {s t : State} (h : LoopKeep base s t)
    {i : Nat} (hi : i < 255) :
    t.mem (off base (VG.Impl.X25519.AArch64.Word.BITS + i)) =
      s.mem (off base (VG.Impl.X25519.AArch64.Word.BITS + i)) := by
  apply h.mem
  rw [ofs_off' base (by simp [VG.Impl.X25519.AArch64.Word.BITS,
    VG.Impl.X25519.AArch64.BITS, VG.Impl.X25519.AArch64.slot,
    VG.Impl.X25519.AArch64.NSLOT]; omega)]
  right
  simp [VG.Impl.X25519.AArch64.Word.BITS, VG.Impl.X25519.AArch64.BITS,
    VG.Impl.X25519.AArch64.slot, VG.Impl.X25519.AArch64.NSLOT]
  omega

theorem LoopKeep.saved {base : Addr} {s t : State} (h : LoopKeep base s t)
    {i : Nat} (hi : i < 6) : word t.mem base (8*i) = word s.mem base (8*i) :=
  h.mem.word (by omega) (by omega)

theorem LoopKeep.output {base : Addr} {s t : State} (h : LoopKeep base s t) :
    word t.mem base 48 = word s.mem base 48 := h.mem.word (by decide) (by decide)

theorem env_swap_store (m : Mem) (base : Addr) (v : BitVec 64) :
    env (m.writeW (off base 768) v) base = env m base := by
  funext i
  simp only [env, F]
  rw [(writeW_outside m base v (by decide : 768+8<2^64)).fe
    (by simp only [offset]; omega) (by simp only [offset]; omega)]

end VG.Proof.X25519.AArch64.Word
