import VerifiedGarbage.Impl.Ed25519.X86.PointTable
import VerifiedGarbage.Proof.Ed25519.X86.Field

/-! Bounded word copies between disjoint scratch ranges. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem addr_plus (x : BitVec 32) (a b : Nat) :
    addr (x + BitVec.ofNat 32 a) b = addr x (a + b) := by
  simp only [addr]; rw [BitVec.add_assoc, BitVec.ofNat_add]

structure CopyKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x o n] s.mem t.mem

theorem CopyKeep.ctx {x : BitVec 32} {o n : Nat} {s t : State}
    (h : CopyKeep x o n s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep (h.gpr _ (by decide)) h.wr

theorem CopyKeep.refl (x : BitVec 32) (o n : Nat) (s : State) : CopyKeep x o n s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem CopyKeep.trans {x : BitVec 32} {o n : Nat} {s t u : State}
    (h : CopyKeep x o n s t) (k : CopyKeep x o n t u) : CopyKeep x o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans k.frame⟩

theorem copyWorkspaceWord_ok {x : BitVec 32} {s₀ s : State} (hc : Ctx x s)
    (src dst : Reg) (hs : src ≠ .eax) (hd : dst ≠ .eax) (sa da a o n total : Nat)
    (hsa : s₀.gpr src = x + BitVec.ofNat 32 sa) (hda : s₀.gpr dst = x + BitVec.ofNat 32 da)
    (ha : sa + a + 4 * total ≤ 8192) (ho : da + o + 4 * total ≤ 8192)
    (hn : n < total) (hsep : sa + a + 4 * total ≤ da + o ∨ da + o + 4 * total ≤ sa + a)
    (hk : CopyKeep x (da + o) (4 * n) s₀ s)
    (hv : ∀ j < n, wd s.mem x (da + o + 4 * j) = wd s₀.mem x (sa + a + 4 * j)) :
    WP isa (.block (workspaceCopyWord src dst a o n)) s fun t =>
      CopyKeep x (da + o) (4 * (n + 1)) s₀ t ∧
      ∀ j < n + 1, wd t.mem x (da + o + 4 * j) = wd s₀.mem x (sa + a + 4 * j) := by
  have ps : s.gpr src = x + BitVec.ofNat 32 sa := (hk.gpr src hs).trans hsa
  have pd : s.gpr dst = x + BitVec.ofNat 32 da := (hk.gpr dst hd).trans hda
  refine Wp.wp_ldm ps (by rw [addr_plus, ← Nat.add_assoc]; exact hc.inRW (by omega_using [ha, hn]) (by decide))
    fun t ht => ?_
  have pt : t.gpr dst = x + BitVec.ofNat 32 da := (ht.other dst hd).trans pd
  have ct := (updKeep ht).ctx hc
  refine Wp.wp_stm pt (by rw [addr_plus, ← Nat.add_assoc]; exact ct.inW (by omega_using [ho, hn]) (by decide))
    fun u hu => WP.block_nil ?_
  have hvn : wd s.mem x (sa + a + 4 * n) = wd s₀.mem x (sa + a + 4 * n) :=
    wd_frame1 hk.frame hc.fit (by omega_using [ho, hn]) (by omega_using [ha, hn])
      (by omega_using [hsep, hn])
  have hm : u.mem = s.mem.writeW (addr x (da + o + 4 * n)) (wd s₀.mem x (sa + a + 4 * n)) := by
    rw [hu.mem, ht.mem, ht.gpr, addr_plus, addr_plus, ← Nat.add_assoc, ← Nat.add_assoc]
    exact congrArg (s.mem.writeW (addr x (da + o + 4 * n))) hvn
  refine ⟨⟨fun r hr => by rw [hu.gpr, ht.other r hr, hk.gpr r hr],
    by rw [hu.rd, ht.rd, hk.rd], by rw [hu.wr, ht.wr, hk.wr], ?_⟩, fun j hj => ?_⟩
  · rw [hm]
    exact frame_write1 (frameWiden hk.frame hc.fit (Nat.le_refl _) (by omega) (by omega_using [ho, hn]))
      hc.fit (by omega_using [ho, hn]) (by omega) (by omega) _
  · rw [hm]
    by_cases he : j = n
    · subst j; exact wd_write_self _ _ _ _
    · rw [wd_write_ne _ _ (by omega_using [hc.fit, ho, hn, hj])
        (by omega_using [hc.fit, ho, hn]) (by omega_using [he])]
      exact hv j (by omega_using [hj, he])

theorem copyWorkspaceWords_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (src dst : Reg) (hs : src ≠ .eax) (hd : dst ≠ .eax) (sa da a o total : Nat)
    (hsa : s.gpr src = x + BitVec.ofNat 32 sa) (hda : s.gpr dst = x + BitVec.ofNat 32 da)
    (ha : sa + a + 4 * total ≤ 8192) (ho : da + o + 4 * total ≤ 8192)
    (hsep : sa + a + 4 * total ≤ da + o ∨ da + o + 4 * total ≤ sa + a) :
    ∀ n ≤ total, WP isa (.block (workspaceCopyWords src dst a o n)) s fun t =>
      CopyKeep x (da + o) (4 * n) s t ∧
      ∀ j < n, wd t.mem x (da + o + 4 * j) = wd s.mem x (sa + a + 4 * j)
  | 0, _ => WP.block_nil ⟨CopyKeep.refl _ _ _ _, fun j hj => by omega⟩
  | n + 1, hn => by
    rw [workspaceCopyWords, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyWorkspaceWords_ok hc src dst hs hd sa da a o total hsa hda ha ho hsep n (by omega))
      fun t ⟨hk, hv⟩ => ?_
    exact copyWorkspaceWord_ok (hk.ctx hc) src dst hs hd sa da a o n total hsa hda ha ho (by omega) hsep hk hv

end VG.Proof.Ed25519.X86
