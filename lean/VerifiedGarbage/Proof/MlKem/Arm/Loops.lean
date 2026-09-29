import VerifiedGarbage.Proof.MlKem.Arm.Calls

/-!
# ML-KEM-768 on 32-bit ARM: copying bytes and zeroing a polynomial

Untrusted: everything here is checked by Lean. `copy` copies bytes one at
a time (`copy_ok`: the destination holds the source's bytes, and nothing
else changes), and `zeroPoly` stores zero to every coefficient
(`zeroPoly_ok`).
-/

namespace VG.Proof.MlKem.Arm

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Add (ptr_succ)

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, setWidth32_toNat]
  exact Nat.mod_eq_of_lt b.isLt

/-! ## `copy` -/

section
variable {s : State} {x y c : BitVec 32}

theorem copyBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = c)
    (ir : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 1)
    (ow : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block copyBody) s fun s' =>
      s'.gpr .r0 = x + 1 ∧ s'.gpr .r1 = y + 1 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
        (((s.mem (State.addr (x + BitVec.ofNat 32 0))).setWidth 32).setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [copyBody, h0, h1, h2, ir, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : BitVec 32) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = S + BitVec.ofNat 32 (1 * k)
  r1 : s.gpr .r1 = D + BitVec.ofNat 32 (1 * k)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (len - k))
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (State.addr D + BitVec.ofNat 64 t) = s₀.mem (State.addr S + BitVec.ofNat 64 t)

theorem copy_step {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32)
    (hd : (⟨State.addr S, len⟩ : Region).Disjoint ⟨State.addr D, len⟩)
    (cr : Covers [⟨State.addr S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr D, len⟩] s₀.wr)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block copyBody) s fun s' => CopyInv S D len s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = len) := by
  have eS : State.addr (S + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr S + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have eD : State.addr (D + BitVec.ofNat 32 (1 * k) + BitVec.ofNat 32 0) = State.addr D + BitVec.ofNat 64 k := by
    rw [addr_ptr _ _ _ (by omega)]; simp
  have cS : (⟨State.addr S, len⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  have cD : (⟨State.addr D, len⟩ : Region).Contains (State.addr D + BitVec.ofNat 64 k) 1 :=
    contains_off (by omega) (by omega)
  refine WP.mono (copyBody_ok h.r0 h.r1 h.r2 (by rw [eS, h.rd, h.wr]; exact cr _ _ ⟨_, List.mem_singleton_self _, cS⟩)
    (by rw [eD, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cD⟩))
    fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 1 k
  · rw [r1]; exact ptr_succ _ 1 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eD]; exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · rw [m, eD, eS, setWidth_byte, byte_writeW8 _ _ (by omega) (by omega)]
    have hsrc : s.mem (State.addr S + BitVec.ofNat 64 k) = s₀.mem (State.addr S + BitVec.ofNat 64 k) :=
      h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    by_cases e : t = k
    · subst e; rw [ite_eq_left rfl, hsrc]
    · rw [ite_eq_right e]; exact h.bytes t (by omega)
  · rw [z]; exact count_z (k := 1) hk (by decide) (by omega)

/-- `len` bytes copied from `S` to `D`, with the pointers and the count set
up in `r0`–`r2`. -/
theorem copy_loop {S D : BitVec 32} {len : Nat} {s₀ : State} (fS : S.toNat + len ≤ 2 ^ 32)
    (fD : D.toNat + len ≤ 2 ^ 32) (hlen : len < 2 ^ 32) (hl0 : 0 < len)
    (hd : (⟨State.addr S, len⟩ : Region).Disjoint ⟨State.addr D, len⟩)
    (cr : Covers [⟨State.addr S, len⟩] (s₀.rd ++ s₀.wr)) (cw : Covers [⟨State.addr D, len⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = S) (h1 : s₀.gpr .r1 = D) (h2 : s₀.gpr .r2 = BitVec.ofNat 32 len) :
    WP isa (.loop (.block copyBody) .ne) s₀ fun s =>
      (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Frame [⟨State.addr D, len⟩] s₀.mem s.mem ∧ bytesAt s.mem (State.addr D) len = bytesAt s₀.mem (State.addr S) len :=
  wp_loop_ne (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step fS fD hlen hd cr cw hk h)
    (fun s h => ⟨h.cs, h.rd, h.wr, h.sp, h.frame, bytesAt_eq (bytesAt_length _ _ _) fun t ht => by
      rw [h.bytes t ht, bytesAt_getElem]⟩)
    ⟨by rw [h0]; simp, by rw [h1]; simp, by rw [h2]; simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

theorem copy_setup {s : State} {sb db : Reg} {so dO len : Nat} (hsb : sb ∈ preserved ∧ sb ≠ .lr)
    (hdb : db ∈ preserved ∧ db ≠ .lr) (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true) :
    WP isa (.block [ptrTo .r0 sb so, ptrTo .r1 db dO, .mov .r2 (.imm (BitVec.ofNat 32 len))]) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = s.gpr sb + BitVec.ofNat 32 so ∧ s'.gpr .r1 = s.gpr db + BitVec.ofNat 32 dO ∧
      s'.gpr .r2 = BitVec.ofNat 32 len := by
  obtain ⟨-, -, -, -, -⟩ := pres_ne hsb.1 hsb.2
  obtain ⟨n0, -, -, -, -⟩ := pres_ne hdb.1 hdb.2
  run_block [ptrTo, hse, hde, hle, n0]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, -, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, ite_false]

/-- `copy`: `len` bytes from offset `so` of buffer `i` (in `sb`) to offset
`dO` of buffer `j` (in `db`). -/
theorem copyL {L : Lay} {s : State} (hL : L.Ok) {sb db : Reg} {so dO len i j : Nat}
    (hsb : sb ∈ preserved ∧ sb ≠ .lr) (hdb : db ∈ preserved ∧ db ≠ .lr)
    (gs : s.gpr sb = L.ptr i) (gd : s.gpr db = L.ptr j) (hse : encodable (BitVec.ofNat 32 so) = true)
    (hde : encodable (BitVec.ofNat 32 dO) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (hlen : len < 2 ^ 32) (hl0 : 0 < len) (hs : sepB L.sizes (i, so, len) (j, dO, len) = true)
    (ri : L.buf i ∈ s.rd ++ s.wr) (wj : L.buf j ∈ s.wr) :
    WP isa (copy sb so db dO len) s fun s' =>
      Kept (L.RL [(j, dO, len)]) s s' ∧ bytesAt s'.mem (L.A j dO) len = bytesAt s.mem (L.A i so) len := by
  obtain ⟨ea, fa⟩ := Lay.ptr_ok hL (sepB_bounds hs) hl0
  obtain ⟨eb, fb⟩ := Lay.ptr_ok hL (sepB_bounds (sepB_symm hs)) hl0
  refine WP.seq (WP.mono (copy_setup hsb hdb hse hde hle) fun s₁ ⟨o₁, g0, g1, g2⟩ => ?_)
  rw [gs] at g0; rw [gd] at g1
  refine WP.mono (copy_loop fa fb hlen hl0 (by rw [ea, eb]; exact Lay.disj hL hs)
    (by rw [ea, o₁.rd, o₁.wr]; exact Lay.covers ri (sepB_bounds hs).2)
    (by rw [eb, o₁.wr]; exact Lay.covers wj (sepB_bounds (sepB_symm hs)).2) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨?_, ?_⟩
  · refine (o₁.kept _).trans ⟨fun r hr _ => cs r hr, sp, rd, wr, ?_⟩
    rw [eb] at fr; exact fr
  · rw [eb, ea, o₁.mem] at hb; exact hb

/-! ## `zeroPoly` -/

section
variable {s : State} {x c : BitVec 32}

theorem zeroBody_ok (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = 0) (h2 : s.gpr .r2 = c)
    (ow : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block zeroBody) s fun s' =>
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r2 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) (0 : BitVec 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  run_block [zeroBody, h0, h1, h2, ow, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-- After zeroing `k` coefficients of the polynomial at `P`. -/
structure ZeroInv (P : BitVec 32) (s₀ : State) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = P + BitVec.ofNat 32 (4 * k)
  r1 : s.gpr .r1 = 0
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 - k))
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [polyRegion (State.addr P)] s₀.mem s.mem
  zero : ∀ t < 256, coeffAt s.mem (State.addr P) t = if t < k then 0 else coeffAt s₀.mem (State.addr P) t

theorem zero_step {P : BitVec 32} {s₀ : State} (fP : P.toNat + 1024 ≤ 2 ^ 32)
    (cw : Covers [polyRegion (State.addr P)] s₀.wr) {k : Nat} (hk : k < 256) {s : State} (h : ZeroInv P s₀ k s) :
    WP isa (.block zeroBody) s fun s' => ZeroInv P s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = 256) := by
  have eP : State.addr (P + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr P) k :=
    addr_coeff fP (by omega) hk
  have cP : (polyRegion (State.addr P)).Contains (coeffAddr (State.addr P) k) 4 :=
    coeff_contains _ (by rw [VG.Proof.MlKem.n_eq]; exact hk)
  refine WP.mono (zeroBody_ok h.r0 h.r1 h.r2 (by rw [eP, h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩))
    fun s' ⟨r0, r1, r2, z, m, rd, wr, sp, cs⟩ => ⟨⟨?_, r1, ?_, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact ptr_succ _ 4 k
  · rw [r2]; exact count_sub (k := 1) hk
  · rw [m, eP]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, eP]; exact coeff_one hk h.zero rfl
  · rw [z]; exact count_z (k := 1) hk (by decide) (by decide)

theorem zeroPoly_ok {L : Lay} {s : State} (hc : Ctx L s) {off : Nat} (hoff : off + 1024 ≤ 32768)
    (he : encodable (BitVec.ofNat 32 off) = true) :
    WP isa (zeroPoly off) s fun s' => Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) zero := by
  have ea := hc.addr (o := off) (by omega)
  have fa := hc.fitO (o := off) (l := 1024) hoff (by decide)
  have hfin : ∀ s', ZeroInv (L.ptr 0 + BitVec.ofNat 32 off) s 256 s' →
      Kept (L.RL [(0, off, 1024)]) s s' ∧ PolyIs s'.mem (L.A 0 off) zero := fun s' h => by
    refine ⟨⟨fun r hr _ => h.cs r hr, h.sp, h.rd, h.wr, ?_⟩, ?_⟩
    · have := h.frame; rw [ea] at this; exact this
    · refine polyIs_of_coeffAt fun t ht => ?_
      show coeffAt s'.mem (State.addr (L.ptr 0) + BitVec.ofNat 64 off) t = _
      rw [← ea, h.zero t (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht),
        ite_eq_left (by rw [VG.Proof.MlKem.n_eq] at ht; exact ht), zero,
        getElem!_pos (Vector.replicate n (0 : Zq)) t ht, Vector.getElem_replicate]
      rfl
  refine WP.seq ?_
  have e7 := hc.r7
  run_block [ptrTo, he, e7]
  refine wp_loop_ne (ZeroInv (L.ptr 0 + BitVec.ofNat 32 off) s) (N := 256) (by decide)
    (fun k hk s h => zero_step fa (by rw [ea]; exact hc.cs hoff) hk h) hfin ?_
  refine ⟨by simp, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, Frame.refl _ _, fun t _ => by simp⟩
  have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

end VG.Proof.MlKem.Arm
