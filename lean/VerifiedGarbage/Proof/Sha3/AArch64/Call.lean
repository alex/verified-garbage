import VerifiedGarbage.Proof.Sha3.AArch64.Variant

section

/-!
# SHA-3 on AArch64: calling the permutation, and saving registers

Untrusted: everything here is checked by Lean.
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

theorem save_eq : VG.Impl.Sha3.AArch64.Stream.save .x5 = (List.range 6).flatMap fun k => [.str .x (sv k) .x5 (512 + 8 * k)] := by
  decide

/-- During the saves. -/
def SaveInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
    Frame [⟨s₀.gpr .x5, 640⟩] s₀.mem s.mem ∧ s.v = s₀.v ∧
    ∀ j < k, s.mem.readW (slot (s₀.gpr .x5) j) 64 = s₀.gpr (sv j)

/-- Saving `x19`–`x24` in the scratch space at `x5`. -/
theorem saves_ok {s₀ : State} (hin : ∀ k < 6, InRegions s₀.wr (slot (s₀.gpr .x5) k) 8) :
    WP isa (.block (VG.Impl.Sha3.AArch64.Stream.save .x5)) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨s₀.gpr .x5, 640⟩] s₀.mem s.mem ∧ s.v = s₀.v ∧ Saved (s₀.gpr .x5) s₀.gpr s.mem := by
  rw [save_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (SaveInv s₀)
    (fun k s hk ⟨hg, hrd, hwr, hsp, hf, hvec, hv⟩ => ?_) 6 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, rfl, fun _ h => absurd h (by omega)⟩)
    fun s ⟨hg, hrd, hwr, hsp, hf, hvec, hv⟩ => ⟨hg, hrd, hwr, hsp, hf, hvec, hv⟩
  refine wp_str (a := slot (s₀.gpr .x5) k) ⟨by omega, by omega⟩ (by rw [hg])
    (by rw [hwr]; exact hin k hk) fun s' g' => wp_nil ?_
  refine ⟨g'.gpr.trans hg, g'.rd.trans hrd, g'.wr.trans hwr, g'.sp.trans hsp, ?_, g'.vec.trans hvec, fun j hj => ?_⟩
  · rw [g'.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset (by omega) (by omega))
  · rw [g'.mem, hg]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact hv j (by omega)
      · have := off_disjoint (s₀.gpr .x5) (a := 512 + 8 * j) (n := 8) (b := 512 + 8 * k) (k := 8)
          (by omega) (by omega) (by omega)
        exact this.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The order of the restores: `x20`, the base, last. -/
def ri (k : Nat) : Nat := [0, 2, 3, 4, 5, 1].getD k 0

theorem restore_eq : VG.Impl.Sha3.AArch64.Stream.restore = (List.range 6).flatMap fun k =>
    [.ldr .x (sv (ri k)) .x20 (512 + 8 * ri k)] := by
  decide

theorem ri_lt : ∀ k < 6, ri k < 6 := by decide
theorem sv_ri_ne : ∀ j < 6, ∀ k < 6, j ≠ k → sv (ri j) ≠ sv (ri k) := by decide
theorem sv_ri_x20 : ∀ k < 5, sv (ri k) ≠ .x20 := by decide
theorem sv_ri_x0 : ∀ k < 6, sv (ri k) ≠ .x0 := by decide

/-- Every saved register is restored. -/
theorem sv_ri_all : ∀ j < 6, ∃ k < 6, ri k = j := by decide

/-- During the restores. -/
def ResInv (scr : Addr) (s₁ : State) (k : Nat) (s : State) : Prop :=
  (k < 6 → s.gpr .x20 = scr) ∧ s.gpr .x0 = s₁.gpr .x0 ∧ s.sp = s₁.sp ∧ s.mem = s₁.mem ∧
    s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.v = s₁.v ∧ ∀ j < k, s.gpr (sv (ri j)) = s₁.mem.readW (slot scr (ri j)) 64

/-- Restoring `x19`–`x24` from the scratch space at `x20`. -/
theorem restores_ok {s₁ : State} {scr : Addr} (h20 : s₁.gpr .x20 = scr)
    (hin : ∀ k < 6, InRegions (s₁.rd ++ s₁.wr) (slot scr k) 8) :
    WP isa (.block VG.Impl.Sha3.AArch64.Stream.restore) s₁ fun s =>
      s.gpr .x0 = s₁.gpr .x0 ∧ s.sp = s₁.sp ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.v = s₁.v ∧
      (∀ r, (∀ k < 6, r ≠ sv k) → s.gpr r = s₁.gpr r) ∧
      ∀ k < 6, s.gpr (sv k) = s₁.mem.readW (slot scr k) 64 := by
  rw [restore_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s => ResInv scr s₁ k s ∧
      ∀ r, (∀ k < 6, r ≠ sv k) → s.gpr r = s₁.gpr r)
    (fun k s hk ⟨⟨h20', ax, sp, m, rd, wr, hv, v⟩, o⟩ => ?_) 6 (Nat.le_refl _) s₁
    ⟨⟨fun _ => h20, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩, fun _ _ => rfl⟩)
    fun s ⟨⟨_, ax, sp, m, rd, wr, hv, v⟩, o⟩ => ⟨ax, sp, m, rd, wr, hv, o, fun k hk => ?_⟩
  · have hri := ri_lt k hk
    refine wp_ldr (a := slot scr (ri k)) ⟨by omega, by omega⟩ (by rw [h20' hk])
      (by rw [rd, wr]; exact hin _ hri) fun s' u => wp_nil ⟨⟨fun hk' => ?_, ?_, by rw [u.sp, sp],
        by rw [u.mem, m], by rw [u.rd, rd], by rw [u.wr, wr], u.vec.trans hv, fun j hj => ?_⟩, fun r hr => ?_⟩
    · rw [u.other _ (sv_ri_x20 k (by omega)).symm, h20' hk]
    · rw [u.other _ (sv_ri_x0 k hk).symm, ax]
    · by_cases e : j = k
      · subst e; rw [u.gpr, m]
      · rw [u.other _ (sv_ri_ne j (by omega) k hk e), v j (by omega)]
    · rw [u.other _ (hr _ hri), o r hr]
  · obtain ⟨j, hj, rfl⟩ := sv_ri_all k hk
    exact v j hj

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
