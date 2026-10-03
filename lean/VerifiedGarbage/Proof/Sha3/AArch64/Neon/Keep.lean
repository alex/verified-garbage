import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair

namespace VG.Proof.Sha3.AArch64.Neon
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only VUpd VMem)
open VG.Proof.Sha3.AArch64 (Upd Mupd)
open VG.Proof.Sha3.AArch64.Sha3.Vector (CoreKeep)

/-- Scalar fields preserved by a kernel that may use every vector register. -/
structure RegKeep (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem RegKeep.refl (rs : List Reg) (s : State) : RegKeep rs s s := ⟨fun _ _ => rfl,rfl,rfl,rfl⟩
theorem RegKeep.trans {rs ts : List Reg} {s t u : State} (h : RegKeep rs s t) (k : RegKeep ts t u) :
    RegKeep (rs++ts) s u :=
  ⟨fun r hr => (k.gpr r (fun ht => hr (List.mem_append.mpr (.inr ht)))).trans
    (h.gpr r (fun hs => hr (List.mem_append.mpr (.inl hs)))),k.rd.trans h.rd,k.wr.trans h.wr,k.sp.trans h.sp⟩
theorem RegKeep.mono {rs ts : List Reg} {s t : State} (h : RegKeep rs s t) (hm : ∀ r ∈ rs,r ∈ ts) :
    RegKeep ts s t := ⟨fun r hr => h.gpr r (fun hs => hr (hm r hs)),h.rd,h.wr,h.sp⟩
theorem RegKeep.upd {s t : State} {r : Reg} {v : BitVec 64} (h : Upd s t r v) : RegKeep [r] s t :=
  ⟨fun q hq => h.other q (by simpa using hq),h.rd,h.wr,h.sp⟩
theorem RegKeep.only {rs : List Reg} {s t : State} (h : Only rs s t) : RegKeep rs s t :=
  ⟨h.gpr,h.rd,h.wr,h.sp⟩
theorem RegKeep.vupd {s t : State} {r : VReg} {v : BitVec 128} (h : VUpd s t r v) : RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem RegKeep.vmem {s t : State} {m : Mem} (h : VMem s t m) : RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
theorem RegKeep.mupd {s t : State} {m : Mem} (h : Mupd s t m) : RegKeep [] s t :=
  ⟨fun _ _ => congrFun h.gpr _,h.rd,h.wr,h.sp⟩
end VG.Proof.Sha3.AArch64.Neon
