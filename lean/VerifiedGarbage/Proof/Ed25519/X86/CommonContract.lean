import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.TCB.X86.Target

/-! Untrusted cdecl facts shared by the Ed25519 primitives. No particular
argument list or output is assumed by scratch setup and register saving. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

structure ScratchPre (s₀ : State) (scidx argc : Nat) : Prop where
  index : scidx < argc
  wr : scR (arg s₀ scidx) ∈ s₀.wr
  fit : (arg s₀ scidx).toNat + 8192 ≤ 2 ^ 32
  args : (⟨argAddr s₀ 0, 4 * argc⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * argc ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * argc⟩ : Region).Disjoint (scR (arg s₀ scidx))
  ret_sc : (⟨(s₀.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (scR (arg s₀ scidx))

theorem ScratchPre.arg_contains {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    (hi : i < argc) : (⟨argAddr s 0, 4 * argc⟩ : Region).Contains
      (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  sub_contains (x := s.gpr .esp) (a := 4) (k := 4 * argc) hp.sp_fit
    (by omega_using []) (by omega_using [hi]) (by decide)

theorem ScratchPre.argIn {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    (hi : i < argc) : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨_, hp.args, hp.arg_contains hi⟩

theorem ScratchPre.arg_same {s : State} {scidx argc i : Nat} (hp : ScratchPre s scidx argc)
    {m : Mem} (hf : Frame [scR (arg s scidx)] s.mem m) (hi : i < argc) :
    m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i :=
  hf.readW (hp.arg_contains hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

def savedReg : Nat → Reg
  | 0 => .ebx
  | 1 => .esi
  | 2 => .edi
  | _ => .ebp

structure Saved (s₀ : State) (x : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = x
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR x] s₀.mem s.mem
  saved : ∀ j < 4, wd s.mem x (4 * j) = s₀.gpr (savedReg j)

theorem Saved.ctx {s₀ s : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hfit : x.toNat + 8192 ≤ 2 ^ 32) (hw : scR x ∈ s₀.wr) : Ctx x s :=
  ⟨h.edi, hfit, h.wr ▸ hw⟩

/-- A component writing above the saved words preserves the common ABI invariant. -/
theorem Saved.of_frame {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hk : ScalarKeep s t) {rs : List Region}
    (hf : Frame rs s.mem t.mem)
    (hsub : ∀ r ∈ rs, r.Sub (scR x))
    (hsep : ∀ j < 4, ∀ r ∈ rs, (sub x (4 * j) 4).Disjoint r) : Saved s₀ x t := by
  refine ⟨hk.edi.trans h.edi, hk.esp.trans h.esp, hk.rd.trans h.rd, hk.wr.trans h.wr,
    h.frame.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hsub r hr⟩), fun j hj => ?_⟩
  rw [wd_frame hf (hsep j hj)]; exact h.saved j hj

theorem Saved.of_offset {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s)
    (hx : x.toNat + 8192 ≤ 2 ^ 32) (hk : ScalarKeep s t) {o n : Nat}
    (hf : Frame [sub x o n] s.mem t.mem) (ho : 16 ≤ o) (hn : o + n ≤ 8192)
    (ho' : o < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr; rw [List.mem_singleton.mp hr, scR_eq]
    exact sub_sub hx (Nat.zero_le _) hn ho'
  · intro j hj r hr; rw [List.mem_singleton.mp hr]
    exact sub_disj (by omega_using [hx, hj]) (by omega_using [hx, hn]) (Or.inl (by omega_using [hj, ho]))

end VG.Proof.Ed25519.X86
