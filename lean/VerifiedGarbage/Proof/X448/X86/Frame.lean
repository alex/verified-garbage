import VerifiedGarbage.Proof.X448.X86.Contract
import VerifiedGarbage.Proof.X448.X86.Env

/-!
# X448 on x86 (32-bit): memory frames

Scratch-only writes preserve the cdecl arguments, which remain on the
unchanged stack.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m')
    (ho : o + 112 ≤ 8192) : Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem loadArg_ok {s₀ s : State} (hp : Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    (hm : Outside ((arg s₀ 3).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < 4) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact hp.argIn hi) fun t ht => ?_
  rw [hp.arg_same hm.frame hi] at ht
  exact k t ht

end VG.Proof.X448.X86
