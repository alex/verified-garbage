import VerifiedGarbage.Proof.AesGcm.X86.CtrCall
import VerifiedGarbage.Proof.Gcm.Ctr

/-!
# AES-GCM on x86: counter mode over a piece (`crypt`), the definitions

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `nO` bytes at `dO`, where `bO` is
`P mod 16` and the state holds the counter block (`St + 48`) and the
keystream block (`St + 64`) for `P` bytes (`Proof.Gcm.Ctr`). What holds
before (`CrIn`), part of the way (`CrMid`, `CrAt`) and after (`CrOut`), and
the regions it writes (`crFrame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- The counter and keystream blocks of the state at `St`, for `P` bytes. -/
abbrev CtrS (m : Mem) (St : BitVec 32) (ciph : Block → Block) (icb : Block) (P : Nat) : Prop :=
  Ctr m (w64 St + BitVec.ofNat 64 48) (w64 St + BitVec.ofNat 64 64) ciph icb P

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `SP`. -/
structure DataW (Ctx St W SP : BitVec 32) (K : Nat) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  ok : DataOk St W SP K s D n
  wr : Covers [⟨w64 D, n⟩] s.wr
  ctx : (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D, n⟩

theorem DataW.of_eq {Ctx St W SP : BitVec 32} {K : Nat} {s s' : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataW Ctx St W SP K s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.take {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) {k : Nat} (hk : k ≤ n) : DataW Ctx St W SP K s D k :=
  ⟨h.ok.take hk, fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
   h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The bytes `[j, j + k)`, writable and apart from the context. -/
theorem DataW.part {Ctx St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n : Nat}
    (h : DataW Ctx St W SP K s D n) {j k : Nat} (hk : j + k ≤ n) :
    Covers [⟨w64 D + BitVec.ofNat 64 j, k⟩] s.wr ∧
      (⟨w64 Ctx, 256⟩ : Region).Disjoint ⟨w64 D + BitVec.ofNat 64 j, k⟩ :=
  ⟨covers_off h.wr hk h.ok.n_lt, h.ctx.sub_right (Offset.sub_base _ hk)⟩

/-- `[D, D + j)` and `[D + j, D + j + l)` are apart. -/
theorem split_disj {D : Addr} {j l : Nat} (hn : j + l < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, l⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := l) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

theorem ofBytes_zeros : Spec.Gcm.ofBytes (Spec.Gcm.zeros 16) = 0 := by decide

/-- The regions `crypt` writes. -/
abbrev crFrame (St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n : Nat) : List Region :=
  [⟨w64 D, n⟩, ⟨w64 St + BitVec.ofNat 64 48, 32⟩, wsR W, below SP K]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : BitVec 32) (K R : Nat) (D : BitVec 32) (n P : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  bO : slotv s.mem W bO = BitVec.ofNat 32 (P % 16)
  nlt : n < 2 ^ 32
  data : DataW Ctx St W SP K s D n
  rounds : RoundsAt s.mem W R

/-- What holds part of the way, `j` bytes done, from `m₀`, but the slots. -/
structure CrAt (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  data : DataW Ctx St W SP K s D n
  rounds : RoundsAt s.mem W R
  ctr : CtrS m₀ St (ciphOf m₀ Ctx R) icb P → CtrS s.mem St (ciphOf m₀ Ctx R) icb (P + j)
  done : CtrS m₀ St (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) j)
  rest : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  at_ : CrAt Ctx St W SP K R icb D n P m₀ j s
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - j)

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : BitVec 32) (K R : Nat) (icb : Block) (D : BitVec 32) (n P : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  ctr : CtrS m₀ St (ciphOf m₀ Ctx R) icb P → CtrS s.mem St (ciphOf m₀ Ctx R) icb (P + n)
  out : CtrS m₀ St (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem (w64 D) n = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ (w64 D) n)
  frame : Frame (crFrame St W SP K D n) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K)
include L

theorem ctx_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (⟨w64 Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem kept_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (keptR W).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- The context's slot is apart from `crFrame`. -/
theorem ctxSlot_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) :
    ∀ r ∈ crFrame St W SP K D n, (⟨w64 W + BitVec.ofNat 64 ctxO, 4⟩ : Region).Disjoint r :=
  fun r hr => (kept_crFrame L hd r hr).sub_left (Offset.sub _ (by decide) (by decide))

theorem env_crFrame {s s' : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n)
    (he : Env Ctx St W SP s) (hf : Frame (crFrame St W SP K D n) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (slot_frame hf (ctxSlot_crFrame L hd))

theorem ciph_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW Ctx St W SP K s D n) {m m' : Mem}
    (hf : Frame (crFrame St W SP K D n) m m') {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' Ctx R = ciphOf m Ctx R :=
  ciph_frame hf (ctx_crFrame L hd) hR

omit L in
/-- The pieces' slots are within `crFrame`. -/
theorem pslot_crFrame {D : BitVec 32} {n : Nat} {m m' : Mem} (h : Frame [pslotR W] m m') :
    Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, pslot_ws W⟩

omit L in
/-- `[D + j, D + j + k)` is within `crFrame`. -/
theorem part_crFrame {D : BitVec 32} {n j k : Nat} (hk : j + k ≤ n) {m m' : Mem}
    (h : Frame [⟨w64 D + BitVec.ofNat 64 j, k⟩] m m') : Frame (crFrame St W SP K D n) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base _ hk⟩

/-- `CrAt` after code that writes only the slots. -/
theorem CrAt.pslot {R : Nat} {icb : Block} {D : BitVec 32} {n P : Nat} {m₀ : Mem} {j : Nat} {s s' : State}
    (h : CrAt Ctx St W SP K R icb D n P m₀ j s) (hf : Frame [pslotR W] s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : CrAt Ctx St W SP K R icb D n P m₀ j s' := by
  have pS : ∀ {a k : Nat}, a + k ≤ 80 → ∀ r ∈ [pslotR W], (⟨w64 St + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hak (.inr ⟨by decide, by decide⟩)
  have pD : ∀ {a k : Nat}, a + k ≤ n → ∀ r ∈ [pslotR W], (⟨w64 D + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r :=
    fun hak r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.ok.w.sub_left (Offset.sub_base _ hak)).sub_right (Lay.wSub (by decide))
  refine ⟨env_crFrame L h.data h.env (pslot_crFrame hf) hbp hsi hsp hrd hwr, h.le, h.nlt, h.data.of_eq hrd hwr,
    rounds_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) h.rounds,
    fun hc => (h.ctr hc).congr (blockAt_frame hf (pS (by decide))) (blockAt_frame hf (pS (by decide))),
    fun hc => ?_, ?_, h.whole, h.frame.trans (pslot_crFrame hf)⟩
  · have := pD (a := 0) (k := j) (by have := h.le; omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame hf this (by have := h.le; have := h.nlt; omega)]; exact h.done hc
  · rw [bytesAt_frame hf (pD (by have := h.le; omega)) (by have := h.nlt; omega)]; exact h.rest

end

end VG.Proof.AesGcm.X86
