import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Schedule
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Rounds
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# SHA-256 with AVX2 on x86-64: the rounds of the first block

Untrusted: everything here is checked by Lean. Group `n` computes the
message words `4n+16 … 4n+19` of both blocks, stores them, and runs rounds
`4n … 4n+3` of the first block, which read their words from the scratch
space. The words of both blocks are then all stored, for the rounds of the
second one.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W)
open VG.Proof.Sha256.X86_64.ShaNi (quad)
open VG.Proof.Sha256.X86_64 (ofInt_natCast contains_offset')

/-- Where `schedule` and `load` store the words `4k … 4k+3` of both blocks. -/
abbrev wAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofInt 64 ((32 * k : Nat) : Int)

/-- The words `4k … 4k+3` of `M₀` and `M₁` are stored, in lanes 0 and 1. -/
def WMem (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) : Prop :=
  m.readW (wAddr scr k) 256 = quad M₁ k ++ quad M₀ k

/-- The part of the scratch space holding the words. -/
abbrev wRegion (scr : Addr) : Region := ⟨scr, 512⟩

/-- The masks that `schedule` and `load` use. -/
def Masks (s : State) : Prop :=
  s.xmm mBA = maskBA ∧ s.ymmHi mBA = maskBA ∧ s.xmm mDC = maskDC ∧ s.ymmHi mDC = maskDC ∧
    s.xmm mBswap = bswapMask ∧ s.ymmHi mBswap = bswapMask

theorem extract_lane0 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 4) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 0 + 4 * q)) (8 * 4) = dword x₀ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, show 8 * (16 * 0 + 4 * q) + i < 128 by omega,
    ite_true]
  exact congrArg _ (by omega)

theorem extract_lane1 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 4) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 1 + 4 * q)) (8 * 4) = dword x₁ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, show ¬ 8 * (16 * 1 + 4 * q) + i < 128 by omega,
    ite_false]
  exact congrArg _ (by omega)

theorem dword_quad (M : Block) (k : Nat) {q : Nat} (hq : q < 4) : dword (quad M k) q = W M (4 * k + q) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp [quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem wSlot_ea (s : State) (j t : Nat) :
    s.ea (wSlot j t) = wAddr (s.gpr .rcx) (t / 4) + BitVec.ofNat 64 (16 * j + 4 * (t % 4)) := by
  simp only [State.ea, wSlot, at_, wAddr, ofInt_natCast]
  bv_omega

theorem in_scr {s : State} {scr : Addr} (hR : (⟨scr, 560⟩ : Region) ∈ s.wr) {d n : Nat} (hd : d + n ≤ 560) :
    InRegions s.wr (scr + BitVec.ofInt 64 (d : Int)) n :=
  ⟨_, hR, contains_offset' hd (by omega)⟩

/-- Rounds read the words `WMem` says are stored. -/
theorem wok_of_wmem {s : State} {scr : Addr} {M₀ M₁ : Block} {t : Nat} (ht : t < 64)
    (hrcx : s.gpr .rcx = scr) (hR : (⟨scr, 560⟩ : Region) ∈ s.wr) (h : WMem s.mem scr M₀ M₁ (t / 4)) :
    WOk 0 M₀ s t ∧ WOk 1 M₁ s t := by
  have hin : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4 := by
    intro j hj
    have e : s.ea (wSlot j t) = scr + BitVec.ofInt 64 ((32 * (t / 4) + 16 * j + 4 * (t % 4) : Nat) : Int) := by
      simp only [State.ea, wSlot, at_, hrcx]
    rw [e]
    obtain ⟨r, hr, hc⟩ := in_scr hR (d := 32 * (t / 4) + 16 * j + 4 * (t % 4)) (n := 4) (by omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have rd : ∀ j < 2, s.mem.readW (s.ea (wSlot j t)) 32 =
      (quad M₁ (t / 4) ++ quad M₀ (t / 4)).extractLsb' (8 * (16 * j + 4 * (t % 4))) (8 * 4) := by
    intro j hj
    rw [wSlot_ea, hrcx, ← h, readW_extract _ _ (by omega)]
  have et : 4 * (t / 4) + t % 4 = t := by omega
  refine ⟨⟨hin 0 (by omega), ?_⟩, ⟨hin 1 (by omega), ?_⟩⟩
  · rw [rd 0 (by omega), extract_lane0 _ _ (Nat.mod_lt _ (by omega)), dword_quad _ _ (Nat.mod_lt _ (by omega)),
      et]
  · rw [rd 1 (by omega), extract_lane1 _ _ (Nat.mod_lt _ (by omega)), dword_quad _ _ (Nat.mod_lt _ (by omega)),
      et]

theorem wmem_write {m : Mem} {scr : Addr} {M₀ M₁ : Block} {k k' : Nat} (hk : k < 16) (hk' : k' < 16)
    (hne : k ≠ k') (v : BitVec 256) (h : WMem m scr M₀ M₁ k) :
    WMem (m.writeW (wAddr scr k') v) scr M₀ M₁ k := by
  simp only [WMem, wAddr, ofInt_natCast] at h ⊢
  exact (readW_writeW_off m scr v (d := 32 * k) (e := 32 * k') (n := 32) (by omega) (by omega)
    (by omega)).trans h

theorem wmem_self (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) :
    WMem (m.writeW (wAddr scr k) (quad M₁ k ++ quad M₀ k)) scr M₀ M₁ k :=
  Mem.readW_writeW_self m _ 32 _ (by omega)

theorem wAddr_contains (scr : Addr) {k : Nat} (hk : k < 16) : (wRegion scr).Contains (wAddr scr k) (256 / 8) :=
  contains_offset' (by omega) (by omega)

/-! ## The groups -/

/-- What holds of the schedule after `n` groups, relative to the state `sB`
at their start. -/
structure Sched (M₀ M₁ : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop where
  pub : ∀ r ∈ pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  masks : Masks s
  frame : Frame [wRegion scr] sB.mem s.mem
  wmem : ∀ k < 16, k < n + 4 → WMem s.mem scr M₀ M₁ k
  msgs : ∀ k, n ≤ k → k < n + 4 → k < 16 → s.xmm (msg k) = quad M₀ k ∧ s.ymmHi (msg k) = quad M₁ k

theorem Sched.keeps {M₀ M₁ : Block} {scr : Addr} {sB : State} {n : Nat} {s s' : State}
    (h : Sched M₀ M₁ scr sB n s) (hk : Keeps s s') : Sched M₀ M₁ scr sB n s' := by
  obtain ⟨hm, hrd, hwr, hpub, hx, hy⟩ := hk
  refine ⟨fun r hr => (hpub r hr).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_, hm ▸ h.frame,
    fun k hk hk' => hm ▸ h.wmem k hk hk', fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃⟩
  rw [Masks, hx, hy]; exact h.masks

/-- The registers `schedule` writes. -/
theorem sched_other (n : Nat) (r : XReg) (h : r = mBA ∨ r = mDC ∨ r = mBswap ∨ r = tmp) :
    r ≠ msg n ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 := by
  have hd := msg_nodup n
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases h with rfl | rfl | rfl | rfl <;> simp_all [Ne.symm]

theorem msg_ne (n k : Nat) (h₁ : n < k) (h₂ : k ≤ n + 3) : msg k ≠ msg n ∧ msg k ≠ t0 ∧ msg k ≠ t1 ∧
    msg k ≠ t2 ∧ msg k ≠ t3 := by
  have hd := msg_nodup n
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : k = n + 1 ∨ k = n + 2 ∨ k = n + 3) with rfl | rfl | rfl <;> simp_all [Ne.symm]

theorem sched_step {M₀ M₁ : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sB.wr) {n : Nat} (hn : n < 16) {s : State} (h : Sched M₀ M₁ scr sB n s) :
    WP isa (.block (if n < 12 then schedule (n + 4) else [])) s fun s' =>
      Sched M₀ M₁ scr sB (n + 1) s' ∧ s'.gpr = s.gpr := by
  by_cases h12 : n < 12
  · simp only [h12, ↓reduceIte]
    have hrcx' : s.gpr .rcx = scr := (h.pub .rcx (by decide)).trans hrcx
    have m : ∀ q < 4, s.xmm (msg (n + 4 + q)) = quad M₀ (n + q) ∧ s.ymmHi (msg (n + 4 + q)) = quad M₁ (n + q) :=
      fun q hq => by
        rw [show n + 4 + q = n + q + 4 by omega, msg_add4]
        exact h.msgs (n + q) (by omega) (by omega) (by omega)
    obtain ⟨ma, ma'⟩ := m 0 (by omega)
    obtain ⟨mb, mb'⟩ := m 1 (by omega)
    obtain ⟨mc, mc'⟩ := m 2 (by omega)
    obtain ⟨md, md'⟩ := m 3 (by omega)
    obtain ⟨k1, k2, k3, k4, _, _⟩ := h.masks
    simp only [Nat.add_zero] at ma ma'
    refine WP.mono (schedule_ok (n + 4) s _ _ _ _ _ _ _ _ ma mb mc md ma' mb' mc' md' k1 k2 k3 k4
      (by rw [hrcx', h.wr]; exact in_scr hR (by omega)))
      fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hg⟩
    rw [xupd_quad] at ex ey
    rw [xupd_quad, xupd_quad, hrcx'] at hm
    refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
    · have o := fun r hr => hx r (sched_other (n + 4) r hr).1 (sched_other (n + 4) r hr).2.1
        (sched_other (n + 4) r hr).2.2.1 (sched_other (n + 4) r hr).2.2.2.1 (sched_other (n + 4) r hr).2.2.2.2
      have masks := h.masks
      rw [Masks, (o mBA (by simp)).1, (o mBA (by simp)).2, (o mDC (by simp)).1, (o mDC (by simp)).2,
        (o mBswap (by simp)).1, (o mBswap (by simp)).2]
      exact masks
    · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (wAddr_contains scr (by omega))
    · intro k hk hk'
      rw [hm]
      by_cases hkn : k = n + 4
      · subst hkn; exact wmem_self _ _ _ _ _
      · exact wmem_write hk (by omega) hkn _ (h.wmem k hk (by omega))
    · intro k h₁ h₂ h₃
      by_cases hkn : k = n + 4
      · subst hkn; exact ⟨ex, ey⟩
      · have o := msg_ne (n + 4) (k + 4) (by omega) (by omega)
        rw [msg_add4] at o
        rw [(hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).1, (hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).2]
        exact h.msgs k (by omega) (by omega) h₃
  · simp only [h12, ↓reduceIte]
    exact WP.block_nil ⟨⟨h.pub, h.rd, h.wr, h.masks, h.frame, fun k hk _ => h.wmem k hk (by omega),
      fun k h₁ _ h₃ => h.msgs k (by omega) (by omega) h₃⟩, rfl⟩

/-- After `n` groups. -/
def GInv (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop :=
  Vars (4 * n) s (Spec.Sha256.rounds H M₀ (4 * n)) ∧ Sched M₀ M₁ scr sB n s

theorem groups_ok (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sB.wr) (h₀ : GInv H M₀ M₁ scr sB 0 sB) :
    ∀ n ≤ 16, WP isa (groups n) sB (GInv H M₀ M₁ scr sB n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s ⟨hv, hs⟩ => ?_)
    have e : group n = (if n < 12 then schedule (n + 4) else []) ++
        (round 0 (4 * n) ++ round 0 (4 * n + 1) ++ round 0 (4 * n + 2) ++ round 0 (4 * n + 3)) := by
      simp only [group, List.append_assoc]
    rw [e, WP.block_append_iff]
    refine WP.mono (sched_step hrcx hR (by omega) hs) fun s₁ ⟨hs₁, hg₁⟩ => ?_
    have hv₁ : Vars (4 * n) s₁ (Spec.Sha256.rounds H M₀ (4 * n)) := by simp only [Vars, hg₁]; exact hv
    have hrcx₁ : s₁.gpr .rcx = scr := (hs₁.pub .rcx (by decide)).trans hrcx
    have hR₁ : (⟨scr, 560⟩ : Region) ∈ s₁.wr := hs₁.wr ▸ hR
    refine WP.mono (rounds4_ok 0 n H M₀ s₁ hv₁ fun q hq => (wok_of_wmem (by omega) hrcx₁ hR₁
      (hs₁.wmem _ (by omega) (by omega))).1) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    rw [show 4 * n + 4 = 4 * (n + 1) by omega] at hv₂
    exact ⟨hv₂, hs₁.keeps hk₂⟩

end VG.Proof.Sha256.X86_64.Avx2
