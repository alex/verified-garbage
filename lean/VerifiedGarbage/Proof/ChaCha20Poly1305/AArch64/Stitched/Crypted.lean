import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypt
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `cryptStitched`

From the state after the lengths, with the ChaCha20 state for counter 0 and
the Poly1305 state for the additional data: after `T` chunks (none for fewer
than 512 bytes), the data's first `512 T` bytes encrypted from counter 1, the
counter advanced past them, the stream's arguments set to the rest, and the
bytes absorbed (`pre`) and the rest's pointer and length in `x22`, `x23`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked Acc rebase rebase_of)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305 (absorbAll)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- The bytes the chunks absorbed: all of them when decrypting, all but the
last chunk when encrypting. -/
def pre (enc : Bool) (T : Nat) : Nat := if enc then 512 * (T - 1) else 512 * T

theorem pre_le (enc : Bool) (T : Nat) : pre enc T ≤ 512 * T := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem pre_zero (enc : Bool) : pre enc 0 = 0 := by cases enc <;> rfl

theorem pre_mod (enc : Bool) (T : Nat) : pre enc T % 16 = 0 := by
  cases enc <;> simp only [pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- The keystream from counter 1. -/
abbrev KS1 (s₀ : State) : List Byte :=
  keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)

/-- What `cryptStitched` leaves, after `T` chunks, from `s`. -/
structure Crypted (enc : Bool) (s₀ s : State) (key msg : List Byte) (T : Nat) (u : State) : Prop where
  inv : Inv0 s₀ u
  le : 512 * T ≤ L s₀
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T)
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T)
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 (pre enc T)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - pre enc T)
  cnt : stateAt u.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T)
  data : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 408, sub s₀ 800 16, dR s₀] s.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key
    (msg ++ bytesAt (if enc then u.mem else s.mem) (dp s₀) (pre enc T))
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-! ## Helpers -/

/-- The vector registers other than `v8` and `v9` are kept. -/
theorem WP.otherV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true) :
    WP isa c s fun u => Q u ∧ ∀ r ∈ preservedV, r ≠ .v8 → r ≠ .v9 → u.v r = s.v r := by
  obtain ⟨t, u, he, hq⟩ := h
  exact ⟨t, u, he, hq, fun r hr h8 h9 => Exec.vec (fun i hi =>
    VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV_ne (List.all_eq_true.mp
      ((Code.allInstrs_eq _ c) ▸ hc) i hi) hr h8 h9) he⟩

theorem bulk_otherV (enc : Bool) :
    (Stitch.bulk enc).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases enc
  · show Stitch.bulkOpen.allInstrs _ = true; lit_decide
  · show Stitch.bulkSeal.allInstrs _ = true; lit_decide

/-- A byte of the data outside a frame of the context. -/
theorem data_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {k : Nat} (hk : k < L s₀) :
    m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k) :=
  hf.bytes hd (Nat.le_of_lt (s₀.gpr .x4).isLt) hk

/-- The parts of the context `cryptStitched` writes, besides the stream's. -/
abbrev ctxW (s₀ : State) : List Region := [sub s₀ 64 408, sub s₀ 800 16]

theorem ctxW_data {s₀ : State} (hp : APre s₀) : ∀ r ∈ ctxW s₀, (dR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))

theorem ctxW_sub (s₀ : State) : ∀ r ∈ ctxW s₀, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩

theorem ctxW_saved (s₀ : State) : ∀ r ∈ ctxW s₀, (sub s₀ 592 48).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-- The state after `cryptSetup`. -/
theorem setup_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptSetup) s fun s₂ =>
      s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s₂.gpr .x0 = off (cx s₀) 64 ∧
      s₂.gpr .x1 = dp s₀ ∧ s₂.gpr .x2 = s₀.gpr .x4 ∧ s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 512 then 1 else 0) ∧
      s₂.gpr .x22 = s.gpr .x22 ∧ s₂.gpr .x23 = s.gpr .x23 ∧
      Kept [sub s₀ 64 64] s s₂ ∧
      ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have core : WP isa (.block cryptSetup) s fun s₂ =>
      s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s₂.gpr .x0 = off (cx s₀) 64 ∧
      s₂.gpr .x1 = dp s₀ ∧ s₂.gpr .x2 = s₀.gpr .x4 ∧ s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 512 then 1 else 0) ∧
      s₂.gpr .x22 = s.gpr .x22 ∧ s₂.gpr .x23 = s.gpr .x23 ∧ Kept [sub s₀ 64 64] s s₂ := by
    refine WP.block_append ((cryptA_ok hp h).mono fun s₁ ⟨m₁, x0₁, x1₁, x2₁, x3₁, k₁⟩ => ?_)
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.check_ok s₁).mono
      fun s₂ ⟨x5₂, g₂, m₂, rd₂, wr₂, _, sp₂⟩ => ?_
    have k : Kept [sub s₀ 64 64] s s₂ :=
      ⟨fun r hr h30 => by
          rw [g₂ r (by intro e; subst e; exact absurd hr (by decide)), k₁.cs r hr h30],
        by rw [sp₂, k₁.sp], by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], by rw [m₂]; exact k₁.frame⟩
    exact ⟨by rw [m₂, m₁], by rw [g₂ _ (by decide), x0₁], by rw [g₂ _ (by decide), x1₁],
      by rw [g₂ _ (by decide), x2₁], by rw [g₂ _ (by decide), x3₁], by rw [x5₂, x2₁],
      k.cs _ (pres .x22) (pres30 .x22), k.cs _ (pres .x23) (pres30 .x23), k⟩
  exact (WP.preservedV core).mono fun _ ⟨⟨a, b, c, d, e, f, g, i, k⟩, hv⟩ => ⟨a, b, c, d, e, f, g, i, k, hv⟩

/-- The ChaCha20 state after `cryptSetup`: counter 1. -/
theorem setup_cnt {s₀ : State} {s : State}
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    stateAt (s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (off (cx s₀) 64) =
      Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
  rw [show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, hst, set12_initState]

/-- Fewer than 512 bytes: no chunks. -/
theorem short_crypted (enc : Bool) {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) {s₂ : State}
    (m₂ : s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32))
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = dp s₀) (x2₂ : s₂.gpr .x2 = s₀.gpr .x4)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [sub s₀ 64 64] s s₂)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    Crypted enc s₀ s key msg 0 s₂ := by
  have i₂ := h.step1 k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  have hd : ∀ r ∈ [sub s₀ 64 64], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine ⟨i₂.inv0, by omega, x0₂, ?_, ?_, x3₂, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, v₂⟩
  · rw [x1₂, Nat.mul_zero, Poly1305.AArch64.add_ofNat_zero]
  · rw [x2₂, Nat.mul_zero, Nat.sub_zero, hL]
  · rw [pre_zero, i₂.x22, Poly1305.AArch64.add_ofNat_zero]
  · rw [pre_zero, i₂.x23, Nat.sub_zero, hL]
  · rw [m₂, setup_cnt hst, Nat.mul_zero, VG.Proof.ChaCha20.ctr_zero]
  · rw [ite_eq_right (by omega)]; exact data_frame k₂.frame hd hk
  · exact k₂.frame.sub fun r hr => by
      rw [List.mem_singleton] at hr; rw [hr]
      exact ⟨sub s₀ 64 408, List.mem_cons_self, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
  · rw [pre_zero, Stitch.bytesAt_zero, List.append_nil]
    exact Repr.frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr

/-! ## The accumulator in registers -/

theorem h2_le {a b c : Nat} (h : a + 2 ^ 64 * b + 2 ^ 128 * c < Spec.Poly1305.P) : c ≤ 4 := by
  have h₁ : 2 ^ 128 * c < 2 ^ 128 * 5 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h₁)

/-- The accumulator's words, from the 24 bytes. -/
theorem leNum_words (m : Mem) (c : Addr) :
    VG.Spec.Poly1305.leNum (bytesAt m (off c 448) 24) = (m.readW (off c 448) 64).toNat +
      2 ^ 64 * (m.readW (off c 456) 64).toNat + 2 ^ 128 * (m.readW (off c 464) 64).toNat := by
  rw [Poly1305.AArch64.leNum_acc]
  simp only [Poly1305.AArch64.w64, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The key's clamped words, as `polyIn` stores them. -/
theorem clamp_words (m : Mem) (c : Addr) :
    Poly1305.AArch64.Rk m (off c 448) = (m.readW (off c 472) 64 &&& M0).toNat +
      2 ^ 64 * (m.readW (off c 480) 64 &&& M1).toNat := by
  simp only [Poly1305.AArch64.Rk, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memIn_288 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 288) 64 = m.readW (off c 472) 64 &&& M0 := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64]

theorem memIn_296 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 296) 64 = m.readW (off c 480) 64 &&& M1 := by
  rw [memIn, Mem.readW_writeW_self64]

theorem memIn_800 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 800) 64 = a := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

theorem memIn_808 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (memIn m c a b).readW (off c 808) 64 = b := by
  rw [memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

/-- The words `polyIn` stores. -/
abbrev inR (s₀ : State) : List Region := [sub s₀ 288 16, sub s₀ 800 16]

theorem memIn_frame {s₀ : State} (m : Mem) (a b : BitVec 64) :
    Frame (inR s₀) m (memIn m (cx s₀) a b) := by
  have c (k d : Nat) (h₁ : k ≤ d) (h₂ : d + 8 ≤ k + 16) (h₃ : k + 16 ≤ 1024) :
      (sub s₀ k 16).Contains (off (cx s₀) d) (64 / 8) :=
    contains_sub s₀ h₁ h₂ h₃
  exact ((((Frame.refl _ m).writeW (by simp) _ (c 800 800 (by decide) (by decide) (by decide))).writeW
    (by simp) _ (c 800 808 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 288 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 296 (by decide) (by decide) (by decide))

theorem storeHm_frame (m : Mem) (p : Addr) (w0 w1 w2 : BitVec 64) :
    Frame [⟨p, 24⟩] m (Poly1305.AArch64.storeHm m p w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (Poly1305.AArch64.hR p).Contains (Poly1305.AArch64.off p d) (64 / 8) :=
    fun d hd => Poly1305.AArch64.hR_contains p hd
  exact (((Frame.refl _ m).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

/-- The pointer and length of the data not yet absorbed. -/
theorem restP_eq (enc : Bool) (d : Addr) {L T : Nat} (hT : 1 ≤ T) (hle : 512 * T ≤ L) :
    restP enc (d + BitVec.ofNat 64 (512 * T)) (BitVec.ofNat 64 (L - 512 * T)) =
      (d + BitVec.ofNat 64 (pre enc T), BitVec.ofNat 64 (L - pre enc T)) := by
  cases enc
  · rfl
  · simp only [restP, pre, ite_true]
    have e : 512 * T = 512 * (T - 1) + 512 := by omega
    refine Prod.ext ?_ ?_
    · show d + BitVec.ofNat 64 (512 * T) - BitVec.ofNat 64 512 = _
      rw [e, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    · show BitVec.ofNat 64 (L - 512 * T) + BitVec.ofNat 64 512 = _
      rw [← BitVec.ofNat_add]; congr 1; omega

/-- The accumulator `polyIn` loads. -/
theorem acc_in {s₀ s₂ s₃ : State} {key msg : List Byte}
    (hr : Repr s₂.mem (off (cx s₀) 448) key msg) (x0₃ : s₃.gpr .x0 = off (cx s₀) 64)
    (a21 : s₃.gpr .x21 = s₂.mem.readW (off (cx s₀) 448) 64)
    (a22 : s₃.gpr .x22 = s₂.mem.readW (off (cx s₀) 456) 64)
    (a23 : s₃.gpr .x23 = s₂.mem.readW (off (cx s₀) 464) 64)
    {a b : BitVec 64} (m₃ : s₃.mem = memIn s₂.mem (cx s₀) a b) :
    Acc (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16)))
      (VG.Spec.Poly1305.accumulate (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg)
      s₃ := by
  have hA := hr.2.2
  rw [leNum_words] at hA
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have r0 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off =
      s₂.mem.readW (off (cx s₀) 472) 64 &&& M0 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 224 = off (cx s₀) 288 from off_off _ 64 224, memIn_288]
  have r1 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off =
      s₂.mem.readW (off (cx s₀) 480) 64 &&& M1 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 232 = off (cx s₀) 296 from off_off _ 64 232, memIn_296]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Poly.hval, a21, a22, a23]; rw [hA]
  · rw [a23]; rw [← hA] at hlt; exact h2_le hlt
  · simp only [Poly.rval, r0, r1]
    rw [← clamp_words, ← Poly1305.AArch64.clamp_key, Poly1305.AArch64.off_24]
    exact congrArg (fun k => VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (List.take 16 k))) hr.2.1
  · rw [r0]; exact Poly1305.AArch64.Radix64.key0_lt _
  · rw [r1]; exact Poly1305.AArch64.Radix64.key1_lt _

/-! ## The chunks -/

theorem data_ctx {s₀ : State} (hp : APre s₀) {k n : Nat} (h : k + n ≤ 1024) :
    (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

/-- A prefix of the data outside a frame of the context. -/
theorem prefix_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {n : Nat} (hn : n ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n :=
  bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hn))
    (Nat.le_trans hn (Nat.le_of_lt (s₀.gpr .x4).isLt))

/-- The saved `x27` and `x28` are outside the stream's regions. -/
theorem saved_bulk {s₀ : State} (hp : APre s₀) {m m' : Mem} (hf : Frame (streamR s₀) m m') {d : Nat}
    (hd : d = 800 ∨ d = 808) : m'.readW (off (cx s₀) d) 64 = m.readW (off (cx s₀) d) 64 := by
  refine hf.readW (r := sub s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
  have h₁ : d + 8 ≤ 1024 := by omega
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)
  · exact (data_ctx hp h₁).symm
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)

/-- At least 512 bytes: the chunks. -/
theorem long_crypted (enc : Bool) {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) {s₂ : State}
    (m₂ : s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32))
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = dp s₀) (x2₂ : s₂.gpr .x2 = s₀.gpr .x4)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [sub s₀ 64 64] s s₂)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hL : 512 ≤ L s₀) :
    WP isa (.seq (.block polyIn) (.seq (Stitch.bulk enc) (.block (polyOut enc)))) s₂
      fun u => ∃ T, Crypted enc s₀ s key msg T u := by
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt (s₀.gpr .x4).isLt
  have i₂ := h.step1 k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  have hr₂ : Repr s₂.mem (off (cx s₀) 448) key msg := Repr.frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr
  refine WP.seq ((polyIn_ok hp i₂.x21 i₂.rd i₂.wr).mono
    fun s₃ ⟨⟨a21, a22, a23, m₃, g₃, rd₃, wr₃⟩, v₃, sp₃, _, _⟩ => ?_)
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃ _ (by decide), x0₂]
  have x1₃ : s₃.gpr .x1 = dp s₀ := by rw [g₃ _ (by decide), x1₂]
  have x2₃ : s₃.gpr .x2 = s₀.gpr .x4 := by rw [g₃ _ (by decide), x2₂]
  have x3₃ : s₃.gpr .x3 = off (cx s₀) 128 := by rw [g₃ _ (by decide), x3₂]
  have ha := acc_in hr₂ x0₃ a21 a22 a23 m₃
  refine WP.seq ((WP.otherV (bulkA_ok enc hp x0₃ x1₃ x2₃ x3₃ hL (by rw [wr₃, i₂.wr]) ha)
    (bulk_otherV enc)).mono fun s₄ ⟨⟨⟨T, hB⟩, rd₄, wr₄, sp₄, f₄⟩, ov₄⟩ => ?_)
  have hi := hB.inv
  have x0₄ : s₄.gpr .x0 = off (cx s₀) 64 := by
    have e := hi.x0; simp only [State.withRegions_gpr, Stitch.st_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.st, x0₃] at e; exact e
  have x1₄ : s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T) := by
    have e := hi.x1; simp only [State.withRegions_gpr, Stitch.dp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.dp, x1₃] at e; exact e
  have hLB : VG.Proof.ChaCha20.AArch64.Xor.L (s₃.withRegions [] (streamR s₀)) = L s₀ := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, x2₃]
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T) := by
    have e := hi.x2; simp only [State.withRegions_gpr, Stitch.L_rebase, hLB] at e; exact e
  have x3₄ : s₄.gpr .x3 = off (cx s₀) 128 := by
    have e := hi.x3; simp only [State.withRegions_gpr, Stitch.bp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.bp, x3₃] at e; exact e
  have le₄ : 512 * T ≤ L s₀ := by have e := hi.le; simp only [Stitch.L_rebase, hLB] at e; exact e
  refine (polyOut_ok hp enc x0₄ (by rw [rd₄, rd₃, i₂.rd]) (by rw [wr₄, wr₃, i₂.wr])).mono
    fun s₅ ⟨⟨hv₅, m₅, x21₅, x27₅, x28₅, x22₅, x23₅, g₅, rd₅, wr₅⟩, vv₅, sp₅, _, _⟩ => ⟨T, ?_⟩
  -- Memory.
  have f₂₃ : Frame (inR s₀) s₂.mem s₃.mem := by rw [m₃]; exact memIn_frame _ _ _
  have f₄₅ : Frame [sub s₀ 448 24] s₄.mem s₅.mem := by rw [m₅]; exact storeHm_frame _ _ _ _ _
  have hF : Frame [sub s₀ 64 408, sub s₀ 800 16, dR s₀] s.mem s₅.mem := by
    have e (r : Region) (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
        ∃ r' ∈ [sub s₀ 64 408, sub s₀ 800 16, dR s₀], Region.Sub r r' :=
      ⟨sub s₀ 64 408, List.mem_cons_self, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩
    refine ((k₂.frame.sub ?_).trans (f₂₃.sub ?_)).trans ((f₄.sub ?_).trans (f₄₅.sub ?_)) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · exact e r 64 64 (by decide) (by decide) hr
    · rcases hr with hr | hr
      · exact e r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 800 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact e r 64 64 (by decide) (by decide) hr
      · exact ⟨dR s₀, by simp, hr ▸ fun _ h => h⟩
      · exact e r 128 320 (by decide) (by decide) hr
    · exact e r 448 24 (by decide) (by decide) hr
  have d₀₃ (k : Nat) (hk : k < L s₀) :
      s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    rw [data_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk,
      data_frame k₂.frame (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
    rw [stateAt_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      m₂, setup_cnt hst]
  -- The data and the counter.
  have data₅ : ∀ k < L s₀, s₅.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    have e := hi.data k (by rw [Stitch.L_rebase, hLB]; exact hk)
    simp only [Stitch.dp_rebase, Stitch.D0_rebase, Stitch.KS_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.D0, VG.Proof.ChaCha20.AArch64.Xor.KS,
      VG.Proof.ChaCha20.AArch64.Xor.S0, VG.Proof.ChaCha20.AArch64.Xor.dp,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, x1₃, hLB, st₃, d₀₃ k hk] at e
    rw [data_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk, e]
  have hd₄₅ : ∀ r ∈ [sub s₀ 448 24], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)
  have hd₂₃ : ∀ r ∈ inR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)
  have hd₂ : ∀ r ∈ [sub s₀ 64 64], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)
  have cnt₅ : stateAt s₅.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T) := by
    have e := hi.cnt
    simp only [Stitch.st_rebase, Stitch.S0_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.S0,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, st₃] at e
    rw [stateAt_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), e]
  have r₄ (d : Nat) (hd : d = 800 ∨ d = 808) :
      s₄.mem.readW (off (cx s₀) d) 64 = s₃.mem.readW (off (cx s₀) d) 64 := saved_bulk hp f₄ hd
  have un₅ : ∀ r ∈ untouched, s₅.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h5 : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28])
        (h3 : r ∉ [Reg.x21, .x22, .x23, .x24, .x25]) (hu : r ∈ untouched) :
        s₅.gpr r = s₀.gpr r := by
      have e := hB.cs r hc
      simp only [State.withRegions_gpr] at e
      rw [g₅ r h5, e, rebase_of hn, State.withRegions_gpr, g₃ r h3,
        k₂.cs r hc (untouched_preserved r hu).2, h.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 800 ∨ d = 808) (hu : r ∈ untouched)
        (hx : s₅.gpr r = s₄.mem.readW (off (cx s₀) d) 64)
        (hm : (memIn s₂.mem (cx s₀) (s₂.gpr .x27) (s₂.gpr .x28)).readW (off (cx s₀) d) 64 = s₂.gpr r) :
        s₅.gpr r = s₀.gpr r := by
      rw [hx, r₄ d hd, m₃, hm, k₂.cs r (untouched_preserved r hu).1 (untouched_preserved r hu).2,
        h.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 800 (.inl rfl) (by decide) x27₅ (memIn_800 _ _ _ _)
    · exact x2728 _ 808 (.inr rfl) (by decide) x28₅ (memIn_808 _ _ _ _)
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have ac₄ := hB.acc
  have hX := hv₅ ac₄.h2
  rw [show hacc s₄ = Poly.hval (s₄.withRegions [] (streamR s₀)) from rfl, ac₄.h,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr.2.1
  rw [k24] at hr1
  refine ⟨⟨x21₅, un₅, by rw [sp₅, sp₄, sp₃, k₂.sp, h.sp], by rw [rd₅, rd₄, rd₃, i₂.rd],
      by rw [wr₅, wr₄, wr₃, i₂.wr], h.saved.frame hF ?_, h.frame.trans (hF.sub ?_)⟩,
    le₄, by rw [g₅ _ (by decide), x0₄], by rw [g₅ _ (by decide), x1₄], by rw [g₅ _ (by decide), x2₄],
    by rw [g₅ _ (by decide), x3₄], by rw [x22₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄],
    by rw [x23₅, x1₄, x2₄, restP_eq enc _ hB.pos le₄], cnt₅, data₅, hF, ⟨?_, ?_, ?_⟩, fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := hr.1; have := pre_mod enc T; omega
  · rw [k24, bytesAt_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (data_ctx hp (by lit_omega)).symm) (by lit_omega)]
    exact hr1
  · rw [m₅, Poly1305.AArch64.storeHm_acc, ← m₅]
    show Poly1305.AArch64.Radix64.hval s₅ = _
    rw [hX, Poly1305.accumulate_append hr.1]
    refine congrArg (absorbAll _ _) ?_
    cases enc
    · simp only [Bool.false_eq_true, ite_false, pre, State.withRegions_mem,
        VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_gpr, x1₃]
      rw [prefix_frame f₂₃ hd₂₃ le₄, prefix_frame k₂.frame hd₂ le₄]
    · simp only [ite_true, pre, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1₃]
      rw [prefix_frame f₄₅ hd₄₅ (by omega)]
  · have e4 : s₄.v r = s₃.v r := by
      by_cases h8 : r = .v8
      · subst h8; simpa using hB.v8
      by_cases h9 : r = .v9
      · subst h9; simpa using hB.v9
      exact ov₄ r hr h8 h9
    rw [vv₅, e4, v₃]; exact v₂ r hr

theorem cryptStitched_ok (enc : Bool) {s₀ : State} (hp : APre s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptStitched enc) s fun u => ∃ T, Crypted enc s₀ s key msg T u := by
  unfold cryptStitched
  refine WP.seq ((setup_ok hp h).mono fun s₂ ⟨m₂, x0₂, x1₂, x2₂, x3₂, x5₂, _, _, k₂, v₂⟩ => ?_)
  apply WP.ite (decide (L s₀ < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro _
    exact WP.block_nil ⟨0, short_crypted enc hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂⟩
  · intro hs
    exact long_crypted enc hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂
      (by have := of_decide_eq_false hs; omega)

end VG.Proof.ChaCha20Poly1305.AArch64
