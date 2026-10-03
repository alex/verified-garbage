import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Framework.AArch64.Spill

section

/-!
# SHA-3 on AArch64: calling the permutation, and saving registers
-/

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64
open VG.Spec.Sha3 (stateAt keccakF)

theorem preserved_x0_x1 : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 := by decide

/-- Calling `vg_keccak_f1600` on the state at `x0`, with scratch space at
`x1`: the callee-saved registers other than `x30` are kept. -/
theorem call_ok (v : Permutation) {s : State} {st scr : Addr} (h0 : s.gpr .x0 = st) (h1 : s.gpr .x1 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .x1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callV (k := Proof.Sha3.permuteAArch64) v.ok
    (rd := []) (wr := [⟨st, 200⟩, ⟨scr, 512⟩]) ?_ ?_ hw ?_ v.noFrames
  · simp only [Proof.Sha3.permuteAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, d₁⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hv hpost
    simp only [Proof.Sha3.permuteAArch64, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hv hf (by rw [hpost]; rfl)

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `x19`, with
scratch space at `x20`. -/
theorem permuteAt_ok (v : Permutation) {s : State} {st scr : Addr} (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨scr, 512⟩)
    (hw : Covers [⟨st, 200⟩, ⟨scr, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) →
      Frame [⟨st, 200⟩, ⟨scr, 512⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (Impl.Sha3.AArch64.Stream.permuteAtWith v.callee) s Q := by
  unfold Impl.Sha3.AArch64.Stream.permuteAtWith
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine call_ok v (st := st) (scr := scr) (by rw [u₂.other _ (by decide), u₁.gpr, h19])
    (by rw [u₂.gpr, u₁.other _ (by decide), h20]) d₁ (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s' rd' wr' sp' cs' vc' f' e' => ?_
  refine hQ s' (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr]) (by rw [sp', u₂.sp, u₁.sp])
    (fun r hr h30 => ?_) (fun r hr => by rw [vc' r hr, u₂.vec, u₁.vec]) (m₂ ▸ f') (by rw [e', m₂])
  rw [cs' r hr h30, u₂.other _ (preserved_x0_x1 r hr).2, u₁.other _ (preserved_x0_x1 r hr).1]

/-! ## Saving the caller's registers -/


/-- The `k`th callee-saved register saved in the scratch space. -/
def sv (k : Nat) : Reg := (VG.Impl.Sha3.AArch64.Stream.saved.getD k (.x0, 0)).1

/-- Where it is saved. -/
abbrev slot (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofNat 64 (512 + 8 * k)

/-- The registers `m` saves at `scr` are those of `g`. -/
def Saved (scr : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (slot scr k) 64 = g (sv k)

/-- The saved registers lie in the scratch space, past the permutation's. -/
theorem slot_sub (scr : Addr) {k : Nat} (hk : k < 6) : Region.Sub ⟨slot scr k, 8⟩ ⟨scr, 640⟩ :=
  sub_offset (by omega) (by omega)

theorem slot_scr (scr : Addr) {k : Nat} (hk : k < 6) :
    Region.Disjoint ⟨slot scr k, 8⟩ ⟨scr, 512⟩ := Offset.disjoint_base scr (by omega) (by omega)

theorem Saved.frame {scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ k < 6, ∀ r ∈ rs, Region.Disjoint ⟨slot scr k, 8⟩ r) : Saved scr g m' :=
  fun k hk => by
    rw [hf.readW (Region.contains_self _ _) (hd k hk) (by decide)]
    exact h k hk

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem Saved.permute {st scr : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved scr g m)
    (hd : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩) (hf : Frame [⟨st, 200⟩, ⟨scr, 512⟩] m m') :
    Saved scr g m' :=
  h.frame hf fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hd.symm.sub_left (slot_sub scr hk)
    · exact slot_scr scr hk

theorem saved_mem : ∀ k < 6, (sv k, 512 + 8 * k) ∈ VG.Impl.Sha3.AArch64.Stream.saved := by decide

theorem saved_idx : ∀ p ∈ VG.Impl.Sha3.AArch64.Stream.saved, ∃ k < 6, p = (sv k, 512 + 8 * k) := by
  decide

theorem Saved.of_spill {scr : Addr} {g : Reg → BitVec 64} {m : Mem}
    (h : Spill.Saved scr g VG.Impl.Sha3.AArch64.Stream.saved m) : Saved scr g m :=
  fun k hk => h (sv k, 512 + 8 * k) (saved_mem k hk)

theorem Saved.spill {scr : Addr} {g : Reg → BitVec 64} {m : Mem} (h : Saved scr g m) :
    Spill.Saved scr g VG.Impl.Sha3.AArch64.Stream.saved m := fun p hp => by
  obtain ⟨k, hk, rfl⟩ := saved_idx p hp
  exact h k hk

/-- Saving `x19`–`x24` in the scratch space at `x5`. -/
theorem saves_ok {s₀ : State} (hin : ∀ k < 6, InRegions s₀.wr (slot (s₀.gpr .x5) k) 8) :
    WP isa (.block (VG.Impl.Sha3.AArch64.Stream.save .x5)) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨s₀.gpr .x5, 640⟩] s₀.mem s.mem ∧ s.v = s₀.v ∧ Saved (s₀.gpr .x5) s₀.gpr s.mem := by
  rw [← List.append_nil (VG.Impl.Sha3.AArch64.Stream.save .x5)]
  exact Spill.save_ok (b := .x5) (by decide) (fun p hp => by
      obtain ⟨k, hk, rfl⟩ := saved_idx p hp; exact hin k hk)
    (WP.block_nil ⟨rfl, rfl, rfl, rfl, Spill.saveMem_frame_base (by decide) (by decide) _ _ _, rfl,
      .of_spill (Spill.saveMem_saved (by decide) _ _ _)⟩)

/-- The order of the restores: `x20`, the base, last. -/
abbrev restored : List (Reg × Nat) :=
  [(.x19, 512), (.x21, 528), (.x22, 536), (.x23, 544), (.x24, 552), (.x20, 520)]

/-- Restoring `x19`–`x24` from the scratch space at `x20`. -/
theorem restores_ok {s₁ : State} {scr : Addr} (h20 : s₁.gpr .x20 = scr)
    (hin : ∀ k < 6, InRegions (s₁.rd ++ s₁.wr) (slot scr k) 8) {g : Reg → BitVec 64}
    (hsv : Saved scr g s₁.mem) :
    WP isa (.block VG.Impl.Sha3.AArch64.Stream.restore) s₁ fun s =>
      s.gpr .x0 = s₁.gpr .x0 ∧ s.sp = s₁.sp ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.v = s₁.v ∧
      (∀ r, (∀ k < 6, r ≠ sv k) → s.gpr r = s₁.gpr r) ∧ ∀ k < 6, s.gpr (sv k) = g (sv k) := by
  have e : VG.Impl.Sha3.AArch64.Stream.restore = Spill.restoreCode .x20 restored := by decide
  rw [e]
  refine WP.mono (Spill.restore_wp h20 (by decide) (by decide) (fun p hp => by
      obtain ⟨k, hk, rfl⟩ := saved_idx p (by revert p; decide); exact hin k hk)
    (hsv.spill.sub (by decide))) fun s h => ?_
  have h := h.perm (l' := VG.Impl.Sha3.AArch64.Stream.saved) (by decide) (by decide)
  refine ⟨h.other _ (by decide), h.sp, h.mem, h.rd, h.wr, h.v, fun r hr => h.other r fun hm => ?_,
    fun k hk => h.gpr (sv k, 512 + 8 * k) (saved_mem k hk)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨k, hk, rfl⟩ := saved_idx p hp
  exact hr k hk rfl

/-! ## The frame saving `x30` -/

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
def untouched : List Reg := [.x25, .x26, .x27, .x28]

theorem untouched_ne_sv : ∀ r ∈ untouched, ∀ k < 6, r ≠ sv k := by decide

/-- A register of `untouched` is not `d`, for any `d` not in it (decided). -/
theorem ne_of_untouched {r : Reg} (h : r ∈ untouched) {d : Reg}
    (hd : d ∉ untouched := by decide) : r ≠ d :=
  fun e => hd (e ▸ h)

/-- A register of `untouched` is in any list that has them all (decided). -/
theorem mem_of_untouched {r : Reg} (h : r ∈ untouched) {l : List Reg}
    (hl : ∀ r ∈ untouched, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- The callee-saved registers but `x30` are saved or untouched. -/
theorem preserved_cases : ∀ r ∈ preserved, r ≠ .x30 → (∃ k < 6, sv k = r) ∨ r ∈ untouched := by
  decide

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) {x : Addr} (hx : R.Contains x 1) :
    m.write (sp - 16) 8 v x = m x :=
  Mem.write_apply fun h => hd x (by simp only [Region.Contains]; omega) hx

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  write_frame_apply hd (by
    simp only [Region.Contains]
    rw [show R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-- The state is unchanged by the push. -/
theorem write_frame_state {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {st : Addr}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ ⟨st, 200⟩) :
    stateAt (m.write (sp - 16) 8 v) st = stateAt m st :=
  stateAt_congr fun _ hi => write_frame_bytes (R := ⟨st, 200⟩) hd (by simp) hi

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    Spec.Sha3.bytesAt mem' p n = Spec.Sha3.bytesAt mem p n := by
  simp only [Spec.Sha3.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

end VG.Proof.Sha3.AArch64

end
