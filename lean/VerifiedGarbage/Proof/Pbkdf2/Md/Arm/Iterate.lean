import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on ARMv7

The same proof as on x86-64 and AArch64 (`Proof/Pbkdf2/AArch64/Iterate.lean`):
the iteration (`Impl/Pbkdf2/Md/Arm.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose digest code and length field
are as `HashOK` says, with any correct compression function (`CompOk`), used
as a black box through its proof; `Md.hmac_step` says that its two
compressions per step compute HMAC. The contract is `iterG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack,
although the function uses none.
-/

namespace VG.Proof.Pbkdf2.Md.Arm.Iterate

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash copyW padFrom constW xorW lenWords)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (iterG below SavedRegs saveR savedRegs preserved_saved)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_ldrSp wp_cmp wp_subs op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev key : BitVec 32 := s₀.gpr .r0
abbrev up : BitVec 32 := s₀.gpr .r1
/-- The number of steps. -/
abbrev nn : Nat := (s₀.gpr .r2).toNat
abbrev tp : BitVec 32 := s₀.gpr .r3
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev kA : Addr := State.addr (key s₀)
abbrev uA : Addr := State.addr (up s₀)
abbrev tA : Addr := State.addr (tp s₀)
abbrev scA : Addr := State.addr (scr s₀)
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev keyR : Region := ⟨kA s₀, 2 * (H.N + H.B)⟩
abbrev uR : Region := ⟨uA s₀, H.D⟩
abbrev tR : Region := ⟨tA s₀, H.D⟩
abbrev scR : Region := ⟨scA s₀, 8 * sc⟩
/-- The hash value being compressed and the block, as registers hold them. -/
abbrev hv : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.hvO
abbrev blk : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.blkO
/-- And as addresses. -/
abbrev hvA : Addr := scA s₀ + BitVec.ofNat 64 H.hvO
abbrev blkA : Addr := scA s₀ + BitVec.ofNat 64 H.blkO

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR H s₀, uR H s₀, argR s₀]
  wr : s₀.wr = [tR H s₀, scR sc s₀]
  k_t : (keyR H s₀).Disjoint (tR H s₀)
  k_s : (keyR H s₀).Disjoint (scR sc s₀)
  u_t : (uR H s₀).Disjoint (tR H s₀)
  u_s : (uR H s₀).Disjoint (scR sc s₀)
  t_s : (tR H s₀).Disjoint (scR sc s₀)
  a_t : (argR s₀).Disjoint (tR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  nk : (key s₀).toNat + 2 * (H.N + H.B) ≤ 2 ^ 32
  nu : (up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (tp s₀).toNat + H.D ≤ 2 ^ 32
  ns : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc

theorem pre_of {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (h : (iterG hH.SH sc).pre s₀)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -, -, -, -, h13, h14, h15, h16, -, h18⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h13, h14, h15, h16, h18, hfit⟩

/-! ## The parts of the scratch space -/

theorem buf_eq (H : Hash) : H.st.buf = 8 * H.st.W + 36 := rfl

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

omit hz hp in
theorem scr_sub {a n : Nat} (h : a + n ≤ 8 * sc) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 a, n⟩ (scR sc s₀) :=
  Offset.sub_base _ h

omit hz in
theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions s.wr (scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR sc s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have := hp.ns; omega)⟩

omit hz in
theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions (s.rd ++ s.wr) (scA s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := in_scr hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

omit hz in
/-- `scratch` plus an offset within it, as an address. -/
theorem addr_sO {o : Nat} (h : o < 8 * sc) :
    State.addr (scr s₀ + BitVec.ofNat 32 o) = scA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.ns; omega)

omit hz in
theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (scr s₀ + BitVec.ofNat 32 o).toNat = (scr s₀).toNat + o := by
  have := hp.ns
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem addr_hv : State.addr (hv H s₀) = hvA H s₀ := by
  have := hp.fits; have := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact addr_sO hp (by simp only [Hash.hvO]; omega)

theorem addr_blk : State.addr (blk H s₀) = blkA H s₀ := by
  have := hp.fits; have := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega
  exact addr_sO hp (by simp only [Hash.blkO]; omega)

omit hz in
theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ H.B) :
    InRegions s.wr (blkA H s₀ + BitVec.ofNat 64 a) n := by
  have := hp.fits
  rw [Memory.add_ofNat]; exact in_scr hp hwr (by simp only [Hash.blkO]; omega)

end

/-! ## The registers during a step -/

/-- The registers `iterate` keeps between its pieces (but the count). -/
abbrev kept : List Reg := [.r0, .r3, .r4, .r6, .r7, .r11]

theorem kept_pres : ∀ r ∈ kept, r ≠ .r0 → r ≠ .r3 → r ∈ preserved ∧ r ≠ .lr := by decide
theorem ne12 : ∀ r ∈ kept, r ≠ .r12 := by decide
theorem ne1 : ∀ r ∈ kept, r ≠ .r1 := by decide
theorem ne5 : ∀ r ∈ kept, r ≠ .r5 := by decide
theorem ne9 : ∀ r ∈ kept, r ≠ .r9 := by decide
theorem ne10 : ∀ r ∈ kept, r ≠ .r10 := by decide

/-- What holds between the pieces of a step: the regions, our registers,
the stack pointer, and memory outside `T` and the scratch space as on entry. -/
structure Regs (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = hv H s₀
  r3 : s.gpr .r3 = scr s₀
  r4 : s.gpr .r4 = key s₀
  r6 : s.gpr .r6 = blk H s₀
  r7 : s.gpr .r7 = tp s₀
  r11 : s.gpr .r11 = scr s₀
  frame : Frame [tR H s₀, scR sc s₀] s₀.mem s.mem

section
variable {H : Hash} {sc : Nat} {s₀ : State}

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : Regs H sc s₀ s) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hm : Frame [tR H s₀, scR sc s₀] s.mem s'.mem) : Regs H sc s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r0 := (hg _ (by decide)).trans h.r0
  r3 := (hg _ (by decide)).trans h.r3
  r4 := (hg _ (by decide)).trans h.r4
  r6 := (hg _ (by decide)).trans h.r6
  r7 := (hg _ (by decide)).trans h.r7
  r11 := (hg _ (by decide)).trans h.r11
  frame := h.frame.trans hm

/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ 8 * sc)
    (hf : Frame [⟨scA s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [tR H s₀, scR sc s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, scr_sub h⟩

end

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

/-- The hash value at `key + o` into the hash value being compressed. -/
theorem load_ok {md : Md H.B H.N H.L} (hR : md.Reloc) {s : State} (h : Regs H sc s₀ s) {o : Nat}
    (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨hvA H s₀, H.N⟩] s.mem s'.mem →
      md.stateAt s'.mem (hvA H s₀) = md.stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.loadKey o ++ rest)) s Q := by
  have := hz.N64; have := hz.N4; have := hp.fits; have := hp.nk; have := hp.ns; have hB := hz.B
  have hn : 4 * (H.N / 4) = H.N := by omega
  have ahv := addr_hv hz hp
  unfold Hash.loadKey
  refine copyW_ok (by decide) (by decide) o 0 (H.N / 4) ⟨by omega, by omega⟩ rest s Q
    (by rw [h.r4]; omega) (by rw [h.r0, toNat_sO hp (by simp only [Hash.hvO]; omega)]; simp only [Hash.hvO]; omega)
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s' g' rd' wr' sp' m' => ?_
  · rw [h.r4, h.rd, hp.rd, Memory.add_ofNat]
    exact ⟨keyR H s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.r0, ahv, h.wr, Memory.add_ofNat, show hvA H s₀ = scA s₀ + BitVec.ofNat 64 H.hvO from rfl,
      Memory.add_ofNat]
    exact in_scr hp rfl (by simp only [Hash.hvO]; omega)
  · rw [h.r4, h.r0, ahv, hn, add0]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (Offset.contains_base _ (by simp only [Hash.hvO]; omega) (by simp only [Hash.hvO]; omega))
  rw [h.r0, ahv, h.r4, hn, add0] at m'
  refine k s' g' rd' wr' sp' (by rw [m']; exact writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, Memory.add_ofNat]
  exact h.frame.bytes (R := keyR H s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_t
    · exact hp.k_s) (by show 2 * (H.N + H.B) ≤ 2 ^ 64; omega) (by show o + i < 2 * (H.N + H.B); omega)

/-- What the call of the compression function needs. -/
theorem callOk_of {s : State} (h : Regs H sc s₀ s) :
    CallOk s H.N H.B H.so (hv H s₀) (scr s₀) (blk H s₀) := by
  have := hz.N64; have := hp.fits; have := hp.ns; have := hz.so; have hB := hz.B
  have hsc : scR sc s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  rw [buf_eq H] at *
  refine ⟨h.r0, h.r3, h.r6, by rw [toNat_sO hp (by simp only [Hash.hvO, buf_eq H]; omega)]; simp only [Hash.hvO, buf_eq H]; omega,
    by rw [toNat_sO hp (by simp only [Hash.blkO, buf_eq H]; omega)]; simp only [Hash.blkO, buf_eq H]; omega,
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [addr_hv hz hp, addr_blk hz hp, hvA, blkA, Hash.hvO, Hash.blkO, buf_eq H]
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · refine Covers.of_sub fun r hr => ⟨scR sc s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩
  · refine Covers.of_sub fun r hr => ⟨scR sc s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega⟩
    · exact ⟨0, by simp, by dsimp only; omega⟩

/-- A call of the compression function on the block. -/
theorem cmp_ok {md : Md H.B H.N H.L} {name : String} {code : Prog isa} (hf : CompOk md H.so code) {s : State}
    (h : Regs H sc s₀ s) {Q : State → Prop}
    (k : ∀ s', Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 →
      Frame [⟨hvA H s₀, H.N⟩, ⟨scA s₀, H.so⟩] s.mem s'.mem →
      md.stateAt s'.mem (hvA H s₀) = md.compress (md.stateAt s.mem (hvA H s₀)) (md.blockAt s.mem (blkA H s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := hz.N64; have := hp.fits; have := hz.so; have hB := hz.B
  refine compressBlock_ok hf (callOk_of hz hp h) fun s' hrd hwr hcs h0 h3 hsp hfr hst => ?_
  rw [addr_hv hz hp] at hfr
  rw [addr_hv hz hp, addr_blk hz hp] at hst
  refine k s' (h.write (fun r hr => ?_) hrd hwr hsp (hfr.sub fun r hr => ?_))
    (hcs _ (by decide) (by decide)) hfr hst
  · by_cases e0 : r = .r0
    · subst e0; rw [h0, h.r0]
    by_cases e3 : r = .r3
    · subst e3; rw [h3, h.r3]
    exact hcs r (kept_pres r hr e0 e3).1 (kept_pres r hr e0 e3).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [buf_eq H] at *
    rcases hr with rfl | rfl
    · exact ⟨scR sc s₀, by simp, scr_sub (by simp only [Hash.hvO, buf_eq H]; omega)⟩
    · exact ⟨scR sc s₀, by simp, Region.sub_prefix (by omega)⟩

end

/-! ## The digest into the block -/

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {md : Md H.B H.N H.L} (ho : OutOk md H.out) {s : State} (h : Regs H sc s₀ s)
    (hpad : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Frame [⟨blkA H s₀, H.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blkA H s₀) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D →
      bytesAt s'.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D → WP isa (.block rest) s' Q) :
    WP isa (.block (H.digest ++ rest)) s Q := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.NL; have := hz.D4; have := hz.N4; have := hz.pad
  have := hp.ns; have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have ahv := addr_hv hz hp; have ablk := addr_blk hz hp
  have tb : (blk H s₀).toNat = (scr s₀).toNat + H.blkO := toNat_sO hp (by simp only [Hash.blkO]; omega)
  unfold Hash.digest
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ho s ?_ ?_ ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  · rw [h.r0, toNat_sO hp (by simp only [Hash.hvO]; omega)]; simp only [Hash.hvO]; omega
  · rw [h.r6, tb]; simp only [Hash.blkO]; omega
  · rw [h.r0, ahv]; exact in_scr' hp h.wr (by simp only [Hash.hvO]; omega)
  · rw [h.r6, ablk]; exact in_scr hp h.wr (by simp only [Hash.blkO]; omega)
  · rw [h.r0, h.r6, ahv, ablk]; exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega))
      (by simp only [Hash.hvO]; omega) (by simp only [Hash.blkO]; omega)
  rw [h.r6, ablk, h.r0, ahv] at m₁
  have hdl := md.digest_length (md.stateAt s.mem (hvA H s₀))
  have f₁ : Frame [⟨blkA H s₀, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  have b₁ : bytesAt s₁.mem (blkA H s₀) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D := by
    rw [bytesAt_take _ _ hz.DN, m₁, bytesAt_writeBytes_self' hdl (by omega)]
  have r₁ : bytesAt s₁.mem (blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) =
      bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) := by
    rw [m₁]
    refine bytesAt_writeBytes_sep _ _ ?_ (by omega)
    have := Offset.sep (blkA H s₀) (d := H.N) (n := H.B - H.N) (e := 0) (k := H.N) (.inr (by omega))
      (by omega) (by omega)
    rw [add0] at this; rw [hdl]; exact this
  have hsplit : ∀ m : Mem, bytesAt m (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) =
      bytesAt m (blkA H s₀ + BitVec.ofNat 64 H.D) (H.N - H.D) ++
        bytesAt m (blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) := by
    intro m
    rw [show H.B - H.D = (H.N - H.D) + (H.B - H.N) by omega, bytesAt_add, Memory.add_ofNat (blkA H s₀),
      show H.D + (H.N - H.D) = H.N by omega]
  have hY : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.N) (H.B - H.N) = (md.tailPad H.D).drop (H.N - H.D) := by
    rw [← hpad, hsplit, List.drop_left' (bytesAt_length _ _ _)]
  have g₁' : s₁.gpr .r6 = blk H s₀ := by rw [g₁ _ (by decide) (by decide), h.r6]
  by_cases hDN : H.D < H.N
  · simp only [hDN, ↓reduceIte]
    refine padFrom_ok (a := H.D) (b := H.N) (by omega) (by omega) (by omega) (s := s₁) (p := blk H s₀)
      g₁' (by rw [tb]; simp only [Hash.blkO]; omega) (fun j hj => by rw [ablk]; exact in_blk hp (wr₁.trans h.wr) (by omega))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => k s₂ (fun r h9 h10 h12 => (g₂ r h12).trans (g₁ r h9 h10)) (rd₂.trans rd₁)
        (wr₂.trans wr₁) (sp₂.trans sp₁) ?_ ?_ ?_
    · rw [m₂, ablk]
      refine f₁.trans (writeBytes_frame _ _ _ ?_)
      simp only [List.length_append, List.length_singleton, List.length_replicate]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [m₂, ablk, bytesAt_writeBytes_sep _ _ ?_ (by omega), b₁]
      have := Offset.sep (blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.N - H.D) (.inl (by omega))
        (by omega) (by omega)
      rw [add0] at this
      have e : ([0x80] ++ List.replicate (H.N - H.D - 1) 0 : List Byte).length = H.N - H.D := by simp; omega
      rw [e]; exact this
    · have hfix : [(0x80 : Byte)] ++ List.replicate (H.N - H.D - 1) 0 = (md.tailPad H.D).take (H.N - H.D) :=
        (md.tailPad_take (by omega) (by omega)).symm
      have hfl : ((md.tailPad H.D).take (H.N - H.D)).length = H.N - H.D := by
        rw [List.length_take, md.tailPad_length (by omega)]; omega
      rw [hsplit, m₂, ablk, hfix, bytesAt_writeBytes_self' hfl (by omega),
        bytesAt_writeBytes_sep _ _ ?_ (by omega), r₁, hY, List.take_append_drop]
      have := Offset.sep (blkA H s₀) (d := H.N) (n := H.B - H.N) (e := H.D) (k := H.N - H.D) (.inr (by omega))
        (by omega) (by omega)
      rw [hfl]; exact this
  · simp only [hDN, ↓reduceIte, List.nil_append]
    have eDN : H.D = H.N := by omega
    refine k s₁ (fun r h9 h10 _ => g₁ r h9 h10) rd₁ wr₁ sp₁ f₁ b₁ ?_
    rw [hsplit, r₁, hY, eDN, Nat.sub_self, List.drop_zero]
    simp [bytesAt]

end

/-! ## A step -/


section
variable (H : Hash) (md : Md H.B H.N H.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  md.step H.D (md.stateAt s₀.mem (kA s₀)) (md.stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 (H.N + H.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, and `T`. -/
abbrev bodyR : List Region := [⟨scA s₀, H.so⟩, ⟨hvA H s₀, H.N + H.B⟩, tR H s₀]

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (H : Hash) (sc : Nat) (md : Md H.B H.N H.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends Regs H sc s₀ s where
  r5 : s.gpr .r5 = BitVec.ofNat 32 r
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  pad : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM H md s₀) (nn s₀) (bytesAt s₀.mem (uA s₀) H.D) (bytesAt s₀.mem (tA s₀) H.D) =
    Spec.Pbkdf2.iterate (stepM H md s₀) r (bytesAt s.mem (blkA H s₀) H.D) (bytesAt s.mem (tA s₀) H.D)

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_disj : ∀ r ∈ bodyR H s₀, (saveR H.st (scr s₀)).Disjoint r := by
  have := hz.so; have := hz.W; have := hp.fits; have := hp.ns
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega) (by rw [buf_eq H] at *; omega)
  · exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, buf_eq H]; omega)) (by rw [buf_eq H] at *; omega)
      (by simp only [Hash.hvO]; omega)
  · exact (hp.t_s.sub_right (scr_sub (by rw [buf_eq H] at *; omega))).symm

omit hz hp in
/-- A range of the scratch space from the hash value on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : H.hvO ≤ a) (h₂ : a + n ≤ H.hvO + H.N + H.B) :
    ∃ r' ∈ bodyR H s₀, Region.Sub ⟨scA s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨hvA H s₀, H.N + H.B⟩, by simp, Offset.sub _ h₁ (by omega)⟩

/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ H.B) :
    ∀ r ∈ [⟨hvA H s₀, H.N⟩, ⟨scA s₀, H.so⟩], Region.Disjoint ⟨blkA H s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := hz.so; have := hp.fits; have := hp.ns
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [Memory.add_ofNat]
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (by simp only [Hash.hvO, Hash.blkO]; omega)) (by simp only [Hash.blkO]; omega)
      (by simp only [Hash.hvO]; omega)
  · exact Offset.disjoint_base _ (by simp only [Hash.blkO, buf_eq H]; omega) (by simp only [Hash.blkO]; omega)

end

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {md : Md H.B H.N H.L} (hR : md.Reloc) {name : String} {code : Prog isa}
    (hf : CompOk md H.so code) {o : Nat} (ho : o + H.N ≤ 2 * (H.N + H.B)) (ho4 : o % 4 = 0) {s : State}
    (h : Regs H sc s₀ s) (hpad : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D)
    {c : Prog isa} {Q : State → Prop}
    (k : ∀ s', Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 → Frame (bodyR H s₀) s.mem s'.mem →
      Frame [⟨scA s₀, H.so⟩, ⟨hvA H s₀, H.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D →
      bytesAt s'.mem (blkA H s₀) H.D = bytesAt s.mem (blkA H s₀) H.D →
      md.stateAt s'.mem (hvA H s₀) =
        md.compress (md.stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 o)) (md.tailBlock H.D (bytesAt s.mem (blkA H s₀) H.D)) →
      WP isa c s' Q) :
    WP isa (.block (H.loadKey o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := hz.N64; have := hp.fits; have := hz.so; have := hz.DN; have := hz.pad; have := hz.NL
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [← List.append_nil (H.loadKey o)]
  refine load_ok hz hp hR h (o := o) ho ho4 fun s₁ g₁ rd₁ wr₁ sp₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr => g₁ r (ne12 r hr)) rd₁ wr₁ sp₁
    (frame_scr (a := H.hvO) (by simp only [Hash.hvO]; omega) f₁)
  refine WP.seq (cmp_ok hz hp hf h₁ fun s₂ h₂ x5₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ H.B → ∀ r ∈ [(⟨hvA H s₀, H.N⟩ : Region)],
      Region.Disjoint ⟨blkA H s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => blk_disj hz hp h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D :=
    (Memory.frame_bytesAt f₁ (fh₁ (by omega)) (by omega)).trans hpad
  have u₁ : bytesAt s₁.mem (blkA H s₀) H.D = bytesAt s.mem (blkA H s₀) H.D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := H.D) (by omega)) (by omega); rwa [add0] at this
  have u₂ : bytesAt s₂.mem (blkA H s₀) H.D = bytesAt s₁.mem (blkA H s₀) H.D := by
    have := Memory.frame_bytesAt f₂ (blk_disj hz hp (a := 0) (n := H.D) (by omega)) (by omega); rwa [add0] at this
  rw [e₁, blockAt_eq (by omega) p₁, u₁] at e₂
  have f : Frame [⟨scA s₀, H.so⟩, ⟨hvA H s₀, H.N⟩] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine k s₂ h₂ (x5₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (blk_disj hz hp (by omega)) (by omega)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨scA s₀, H.so⟩, by simp, fun _ h => h⟩
  · exact ⟨⟨hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega)⟩

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {md : Md H.B H.N H.L} (ho : OutOk md H.out) {s : State} (h : Regs H sc s₀ s)
    (hpad : bytesAt s.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D) {Q : State → Prop}
    (k : ∀ s', Regs H sc s₀ s' → s'.gpr .r5 = s.gpr .r5 - 1 → s'.z = (s.gpr .r5 - 1 == 0) →
      Frame (bodyR H s₀) s.mem s'.mem →
      bytesAt s'.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D →
      bytesAt s'.mem (blkA H s₀) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D →
      bytesAt s'.mem (tA s₀) H.D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (tA s₀) H.D) ((md.digest (md.stateAt s.mem (hvA H s₀))).take H.D) →
      Q s') :
    WP isa (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++
      ([.subs .r5 .r5 (.imm 1)] : List Instr))) s Q := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.D4; have := hz.pad; have := hz.NL; have := hp.ns
  have := hp.nt
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [List.append_assoc]
  refine digest_ok hz hp ho h hpad fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ p₆ => ?_
  have h₆ := h.write (fun r hr => g₆ r (ne9 r hr) (ne10 r hr) (ne12 r hr)) rd₆ wr₆ sp₆
    (frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega) f₆)
  have hd : Region.Disjoint (tR H s₀) ⟨blkA H s₀, H.D⟩ :=
    hp.t_s.sub_right (scr_sub (by simp only [Hash.blkO]; omega))
  have hD4 : 4 * (H.D / 4) = H.D := by omega
  refine xor_ok (tp := tp s₀) (bp := blk H s₀) (D := H.D) (by rw [addr_blk hz hp]; exact hd) (by omega) hp.nt
    (by rw [toNat_sO hp (by simp only [Hash.blkO]; omega)]; simp only [Hash.blkO]; omega)
    (H.D / 4) (by omega) _ s₆ _ h₆.r6 h₆.r7
    (fun j hj => by
      rw [addr_blk hz hp]
      obtain ⟨r, hr, hc⟩ := in_blk hp h₆.wr (a := 4 * j) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨tR H s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  rw [hD4, addr_blk hz hp] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (tA s₀) H.D) (bytesAt s₆.mem (blkA H s₀) H.D)).length = H.D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [tR H s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr => g₇ r (ne12 r hr) (ne1 r hr)) rd₇ wr₇ sp₇ (f₇.mono (by simp))
  refine wp_subs (op2_imm (by decide)) fun s₈ u₈ z₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r hr => u₈.other r (ne5 r hr)) u₈.rd u₈.wr u₈.sp (by rw [u₈.mem]; exact Frame.refl _ _)
  have x5₇ : s₇.gpr .r5 = s.gpr .r5 := by
    rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide)]
  have hT₆ : bytesAt s₆.mem (tA s₀) H.D = bytesAt s.mem (tA s₀) H.D :=
    Memory.frame_bytesAt f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (scr_sub (a := H.blkO) (n := H.N) (by simp only [Hash.blkO]; omega))) (by omega)
  refine k s₈ h₈ (by rw [u₈.gpr, x5₇]) (by rw [z₈, x5₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_body (by simp only [Hash.hvO, Hash.blkO]; omega) (by simp only [Hash.hvO, Hash.blkO]; omega)
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [Memory.add_ofNat]; exact scr_sub (by simp only [Hash.blkO]; omega))).symm)
      (by omega)).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (by omega), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (by omega), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {md : Md H.B H.N H.L} (ho : OutOk md H.out) (hR : md.Reloc) (hf : CompOk md H.so H.compC)
    {r : Nat} {s : State} (h : Inv H sc md s₀ (r + 1) s) :
    WP isa H.body s fun s' => eval .ne s' = some (r != 0) ∧ Inv H sc md s₀ r s' := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL; have := hz.N4
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  unfold Hash.body
  refine WP.seq (lc_ok hz hp hR hf (o := 0) (by omega) rfl h.toRegs h.pad fun s₂ h₂ x5₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (digest_ok hz hp ho h₂ p₂ fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ p₃ => ?_)
  have h₃ := h₂.write (fun r hr => g₃ r (ne9 r hr) (ne10 r hr) (ne12 r hr)) rd₃ wr₃ sp₃
    (frame_scr (a := H.blkO) (by simp only [Hash.blkO]; omega) f₃)
  refine lc_ok hz hp hR hf (o := H.N + H.B) (by omega) (by omega) h₃ p₃ fun s₅ h₅ x5₅ f₅ g₅ p₅ _ e₅ => ?_
  refine tail_ok hz hp ho h₅ p₅ fun s₈ h₈ x5₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, add0] at b₈ t₈
  have x5₅' : s₅.gpr .r5 = BitVec.ofNat 32 (r + 1) := by
    rw [x5₅, g₃ _ (by decide) (by decide) (by decide), x5₂, h.r5]
  have hlt : r + 1 < 2 ^ 32 := by
    have := h.le; have := (s₀.gpr .r2).isLt; simp only [nn] at *; omega
  have e₈ : s₅.gpr .r5 - 1 = BitVec.ofNat 32 r := by
    rw [x5₅', show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.add_sub_cancel]
  have fb : Frame (bodyR H s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_body (by simp only [Hash.hvO, Hash.blkO]; omega) (by simp only [Hash.hvO, Hash.blkO]; omega))).trans
      f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (tA s₀) H.D = bytesAt s.mem (tA s₀) H.D := by
    refine Memory.frame_bytesAt (rs := [⟨scA s₀, H.so⟩, ⟨hvA H s₀, H.N + H.B⟩])
      (((g₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_)) (fun r hr => ?_)
      (by omega)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · subst hr; exact ⟨⟨hvA H s₀, H.N + H.B⟩, by simp, Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega)
        (by simp only [Hash.hvO, Hash.blkO]; omega)⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hvA H s₀, H.N + H.B⟩, by simp, Region.sub_prefix (by omega)⟩
    · have := hz.so; have := hz.W
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (by rw [buf_eq H] at *; omega))
      · exact hp.t_s.sub_right (scr_sub (by simp only [Hash.hvO]; omega))
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [x5₈, e₈], h.saved.frame H.st fb (saved_disj hz hp), p₈, by have := h.le; omega, ?_⟩
  · simp only [eval_ne, z₈, e₈, ofNat_beq_zero (by omega : r < 2 ^ 32)]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl

theorem loop_ok {md : Md H.B H.N H.L} (ho : OutOk md H.out) (hR : md.Reloc) (hf : CompOk md H.so H.compC)
    {n : Nat} {s : State} (h : Inv H sc md s₀ n s) (hzf : s.z = decide (n = 0)) :
    WP isa (.ite .eq (.block []) (.loop H.body .ne)) s (Inv H sc md s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show eval .eq s = _; rw [eval_eq, hzf]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv H sc md s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hz hp ho hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue -/

/-- After saving our caller's registers and our return address and setting
up our registers. -/
structure Setup (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r0 : s.gpr .r0 = hv H s₀
  r1 : s.gpr .r1 = up s₀
  r3 : s.gpr .r3 = scr s₀
  r4 : s.gpr .r4 = key s₀
  r5 : s.gpr .r5 = s₀.gpr .r2
  r6 : s.gpr .r6 = blk H s₀
  r7 : s.gpr .r7 = tp s₀
  r11 : s.gpr .r11 = scr s₀
  mem : Frame [saveR H.st (scr s₀)] s₀.mem s.mem
  saved : SavedRegs H.st (scr s₀) s₀ s.mem

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

omit hz in
theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  have := hp.fits; rw [buf_eq H] at this; exact scr_sub (by omega)

theorem setup_ok {rest : List Instr} {Q : State → Prop} (k : ∀ s, Setup H s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (([.ldrSp .r12 0] : List Instr) ++ H.st.save ++ ([.mov .r11 (.reg .r12), .mov .r7 (.reg .r3),
      .mov .r3 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r2)] : List Instr) ++ H.atHv ++ rest)) s₀ Q := by
  have := hp.fits; have := hp.ns; have := hz.W; have := hz.N64
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  rw [buf_eq H] at *
  simp only [List.append_assoc, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ⟨argR s₀, by simp [hp.rd], Region.contains_self _ _⟩
    fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.Arm.save_ok H.st (scr := scr s₀) u₁.gpr hz.W (by rw [u₁.wr, hp.wr]; simp) (L := 8 * sc)
    (by omega) hp.ns fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  unfold Hash.atHv
  rw [List.append_assoc]
  refine scrAt_ok (by simp only [Hash.hvO, buf_eq H]; omega) fun s₈ g₈ d₈ m₈ rd₈ wr₈ sp₈ =>
    scrAt_ok (by simp only [Hash.blkO, buf_eq H]; omega) fun s₉ g₉ d₉ m₉ rd₉ wr₉ sp₉ => k s₉ ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have e₇ : ∀ r, r ≠ .r11 → r ≠ .r7 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₇.gpr r = s₂.gpr r :=
    fun r h11 h7 h3 h4 h5 => by rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h7, u₃.other r h11]
  have r11₇ : s₇.gpr .r11 = scr s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂, u₁.gpr]; rfl
  have e₉ : ∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r12 → s₉.gpr r = s₇.gpr r := fun r h0 h6 h12 => by
    rw [g₉ r h6 h12, g₈ r h0 h12]
  have r11₈ : s₈.gpr .r11 = scr s₀ := by rw [g₈ _ (by decide) (by decide), r11₇]
  have hm : s₉.mem = s₂.mem := by rw [m₉, m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  exact {
    rd := by rw [rd₉, rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
    wr := by rw [wr₉, wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
    sp := by rw [sp₉, sp₈, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
    r0 := by rw [g₉ _ (by decide) (by decide), d₈, r11₇]
    r1 := by rw [e₉ _ (by decide) (by decide) (by decide), e₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), e₂ _ (by decide)]
    r3 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl
    r4 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
    r5 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
    r6 := by rw [d₉, r11₈]
    r7 := by rw [e₉ _ (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)]
    r11 := by rw [e₉ _ (by decide) (by decide) (by decide), r11₇]
    mem := by rw [hm]; rw [← u₁.mem]; exact f₂
    saved := by
      rw [hm]
      exact sv₂.of_eq H.st fun r hr => u₁.other r (by
        simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) }

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {md : Md H.B H.N H.L}
    (hlen : wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) {s : State} (h : Setup H s₀ s) :
    WP isa (.block (copyW .r1 .r6 0 0 (H.D / 4) ++ H.pad ++ ([.cmp .r5 (.imm 0)] : List Instr))) s
      fun s' => Inv H sc md s₀ (nn s₀) s' ∧ s'.z = decide (nn s₀ = 0) := by
  have := hz.N64; have := hp.fits; have := hz.DN; have := hz.pad; have := hz.NL; have := hz.D4; have := hz.L4
  have := hz.L16; have := hp.ns; have := hp.nu; have := hz.W
  have hB : 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> omega
  have hB4 : H.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  have hD4 : 4 * (H.D / 4) = H.D := by omega
  have ablk := addr_blk hz hp
  have tb : (blk H s₀).toNat = (scr s₀).toNat + H.blkO := toNat_sO hp (by simp only [Hash.blkO]; omega)
  have hbl : ∀ {a n : Nat}, a + n ≤ H.B → H.blkO + a + n ≤ 8 * sc := fun h' => by simp only [Hash.blkO]; omega
  unfold Hash.pad
  simp only [List.append_assoc]
  refine copyW_ok (by decide) (by decide) 0 0 (H.D / 4) ⟨by omega, by omega⟩ _ s _
    (by rw [h.r1]; omega) (by rw [h.r6, tb]; simp only [Hash.blkO]; omega)
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.r1, h.rd, hp.rd, add0]
    exact ⟨uR H s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · rw [h.r6, ablk, add0]; exact in_blk hp h.wr (by omega)
  · rw [h.r1, h.r6, ablk, add0, add0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _)
      (Offset.contains_base _ (by simp only [Hash.blkO]; omega) (by simp only [Hash.blkO]; omega))
  rw [h.r6, ablk, h.r1, add0, add0, hD4] at m₁
  have g6 : s₁.gpr .r6 = blk H s₀ := by rw [g₁ _ (by decide), h.r6]
  refine padFrom_ok (a := H.D) (b := H.B - H.L) (by omega) (by omega) (by omega) (s := s₁) (p := blk H s₀) g6
    (by rw [tb]; simp only [Hash.blkO]; omega) (fun j hj => by rw [ablk]; exact in_blk hp (wr₁.trans h.wr) (by omega))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  rw [ablk] at m₂
  have lw := HashOK.lenWords_length (H := H)
  refine constW_ok (p := blk H s₀) (lenWords H.be H.L (H.B + H.D)) (H.B - H.L) (by rw [lw]; omega)
    (by rw [lw, tb]; simp only [Hash.blkO]; omega) _ s₂ _ (by rw [g₂ _ (by decide), g6])
    (fun j hj => by rw [lw] at hj; rw [ablk]; exact in_blk hp (wr₂.trans (wr₁.trans h.wr)) (by omega))
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [ablk, hlen] at m₃
  refine wp_cmp (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have lpz : ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0 : List Byte).length = H.B - H.L - H.D := by
    simp; omega
  have hM : s₄.mem = writeBytes (writeBytes (writeBytes s.mem (blkA H s₀) (bytesAt s.mem (uA s₀) H.D))
      (blkA H s₀ + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0))
      (blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) (md.lenBytes (H.B + H.D)) := by
    rw [u₄.mem, m₃, m₂, m₁, show H.B - H.L - H.D - 1 = H.B - H.L - H.D - 1 from rfl]
  have hG : ∀ r, r ≠ .r12 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.gpr, g₃ r hr, g₂ r hr, g₁ r hr]
  have sbB : Region.Sub ⟨blkA H s₀, H.B⟩ (scR sc s₀) := scr_sub (by have := hbl (a := 0) (n := H.B) (by omega); omega)
  have fM : Frame [⟨blkA H s₀, H.B⟩] s.mem s₄.mem := by
    rw [hM]
    refine ((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base (blkA H s₀) (d := 0) (n := H.D) (k := H.B) (by omega) (by omega)
      rwa [add0] at this
    · rw [lpz]; exact Offset.contains_base _ (by omega) (by omega)
    · rw [md.lenBytes_length]; exact Offset.contains_base _ (by omega) (by omega)
  have S1 : Mem.Sep (blkA H s₀) H.D (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.L - H.D) := by
    have := Offset.sep (blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.B - H.L - H.D) (.inl (by omega))
      (by omega) (by omega)
    rwa [add0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ H.B - H.L →
      Mem.Sep (blkA H s₀ + BitVec.ofNat 64 a) n (blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) H.L :=
    fun h' => Offset.sep _ (.inl h') (by omega) (by omega)
  have fS : Frame [tR H s₀, scR sc s₀] s₀.mem s.mem :=
    h.mem.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR sc s₀, by simp, save_sub hp⟩
  have hU : bytesAt s.mem (uA s₀) H.D = bytesAt s₀.mem (uA s₀) H.D :=
    Memory.frame_bytesAt h.mem (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (save_sub hp)) (by omega)
  have hT : bytesAt s₄.mem (tA s₀) H.D = bytesAt s₀.mem (tA s₀) H.D := by
    refine (Memory.frame_bytesAt fM (fun r hr => ?_) (by omega)).trans
      (Memory.frame_bytesAt h.mem (fun r hr => ?_) (by omega))
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.sub_right sbB
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.sub_right (save_sub hp)
  refine ⟨⟨⟨by rw [u₄.rd, rd₃, rd₂, rd₁, h.rd], by rw [u₄.wr, wr₃, wr₂, wr₁, h.wr],
    by rw [u₄.sp, sp₃, sp₂, sp₁, h.sp], by rw [hG _ (by decide), h.r0], by rw [hG _ (by decide), h.r3],
    by rw [hG _ (by decide), h.r4], by rw [hG _ (by decide), h.r6], by rw [hG _ (by decide), h.r7],
    by rw [hG _ (by decide), h.r11], fS.trans (fM.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, sbB⟩)⟩,
    by rw [hG _ (by decide), h.r5, ofNat_toNat32],
    h.saved.frame H.st fM (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := hz.W; have := hp.fits; rw [buf_eq H] at *
      exact Offset.disjoint _ (.inl (by simp only [Hash.blkO, buf_eq H]; omega)) (by omega)
        (by simp only [Hash.blkO, buf_eq H]; omega)), ?_, Nat.le_refl _, ?_⟩, ?_⟩
  · -- The padding and the length field.
    rw [show H.B - H.D = (H.B - H.L - H.D) + H.L by omega, bytesAt_add, Memory.add_ofNat (blkA H s₀),
      show H.D + (H.B - H.L - H.D) = H.B - H.L by omega, hM,
      bytesAt_writeBytes_self' (md.lenBytes_length _) (by omega),
      bytesAt_writeBytes_sep _ _ (by rw [md.lenBytes_length]; exact S2 (by omega)) (by omega),
      bytesAt_writeBytes_self' lpz (by omega), Md.tailPad, show H.B - H.L - 1 - H.D = H.B - H.L - H.D - 1 by omega]
  · -- `U` and `T`.
    have hB' : bytesAt s₄.mem (blkA H s₀) H.D = bytesAt s₀.mem (uA s₀) H.D := by
      rw [hM, bytesAt_writeBytes_sep _ _ (by
          rw [md.lenBytes_length]; have := S2 (a := 0) (n := H.D) (by omega); rwa [add0] at this) (by omega),
        bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega),
        bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), hU]
    rw [hB', hT]
  · have c := MdStream.Arm.cmp0 (s₀.gpr .r2).isLt
    rw [ofNat_toNat32] at c
    rw [z₄, g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r5, c]

theorem prologue_ok {md : Md H.B H.N H.L}
    (hlen : wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) :
    WP isa (.block H.prologue) s₀ fun s' => Inv H sc md s₀ (nn s₀) s' ∧ s'.z = decide (nn s₀ = 0) := by
  have := setup_ok hz hp (rest := copyW .r1 .r6 0 0 (H.D / 4) ++ H.pad ++ [.cmp .r5 (.imm 0)])
    fun s h => fill_ok hz hp hlen h
  unfold Hash.prologue
  simpa only [List.append_assoc] using this


theorem epilogue_ok {md : Md H.B H.N H.L} {S : Spec.Hmac.StreamingHash} {iv : md.HV} (hl : md.Link S iv H.D)
    {s : State} (h : Inv H sc md s₀ 0 s) :
    WP isa (.block H.st.restore) s fun s' => abiPreserved s₀ s' ∧ (iterG S sc).post s₀ s' := by
  have hf := hp.fits; have := hz.W; rw [buf_eq H] at hf
  refine WP.mono (Pbkdf2.Stream.Arm.restore_ok H.st h.r11 hz.W h.saved (by rw [h.wr, hp.wr]; simp) (L := 8 * sc)
    (by omega) hp.ns) fun s' ⟨hm, _, _, hsp, hg, _⟩ =>
      ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, h.sp]⟩, fun k0 hk hi ho => ?_⟩
  have hT := h.val
  simp only [Spec.Pbkdf2.iterate] at hT
  rw [hl.hS] at ho
  show bytesAt s'.mem (tA s₀) S.digestBytes = _
  rw [hl.hD, hm, ← hT, Md.iterate_hmac hl hk hi ho _ (bytesAt_length _ _ _)]

end

/-! ## Correctness -/

theorem correct {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀) :
    WP isa H.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  unfold Hash.iterate
  refine WP.seq (WP.mono (prologue_ok hH.sizes hp hH.len) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hH.sizes hp hH.out hH.reloc hH.comp h₁ z₁) fun s₂ h₂ =>
    epilogue_ok hH.sizes hp hH.link h₂)

end VG.Proof.Pbkdf2.Md.Arm.Iterate
