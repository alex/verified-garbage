import VerifiedGarbage.Proof.Ed25519.AArch64.Field

/-! Field programs which also use the public loop counter x19. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

structure CounterKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CounterKeep.scr {base : Addr} {s t : State} (h : CounterKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CounterKeep.trans {base : Addr} {s t u : State}
    (h : CounterKeep base s t) (k : CounterKeep base t u) : CounterKeep base s u :=
  ⟨fun r hr hb => (k.gpr r hr hb).trans (h.gpr r hr hb), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CounterKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r = .x19 ∨ r ∈ clob) : CounterKeep base s t := by
  refine ⟨fun r hr hb => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h
    · exact hb h
    · exact hr h
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem Keep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob) : Keep base s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (hrs r hm)), h.rd, h.wr, h.sp,
    by rw [h.mem]; exact Outside.refl _ _ _ _⟩

theorem CounterKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : CounterKeep base s t :=
  ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem⟩

end VG.Proof.Ed25519.AArch64
