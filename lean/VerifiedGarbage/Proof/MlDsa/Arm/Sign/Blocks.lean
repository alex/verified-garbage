import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top
import VerifiedGarbage.Proof.MlKem.Arm.Loops

/-!
# ML-DSA signing on ARMv7: the blocks between the calls

Untrusted: everything here is checked by Lean. As on x86-64: what the
function's own instructions do, in its layout: copies (`copy_okB`, with
ML-KEM's `copy_loop`), stores of a byte or of a word (`setB_okB`,
`setW_okB`), the AND of a result into `r11` (`and11_ok`), and the counters
in `scratch` (`addW_ok`, `decW_ok`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Spec.MlDsa (integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-- What a block that writes only registers other than the callee-saved
ones, and memory within `W`, leaves. -/
theorem postB_of_keep {D : Nat} {rs : List Reg} {s s' : State} (k : Keep rs s s')
    (hcs : ∀ r ∈ preserved, r ≠ .lr → r ∉ rs) {W : List Region} (hf : Frame W s.mem s'.mem) :
    PostB D s s' W ∧ CS s s' :=
  have c : CS s s' := fun r hr hl => k.gpr r (hcs r hr hl)
  ⟨PostB.of_cs c k.rd k.wr k.sp hf, c⟩

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s)
include L

/-! ## Copies -/

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  inB wbs dst n && inB bs src n && sepB bs src n dst n && decide (0 < n) && decide (src.1 ∈ bases) &&
    decide (dst.1 ∈ bases)

omit L in
theorem copyChk_spec {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : copyChk bs wbs dst src n = true) :
    inB wbs dst n = true ∧ inB bs src n = true ∧ sepB bs src n dst n = true ∧ 0 < n ∧ src.1 ∈ bases ∧
      dst.1 ∈ bases := by
  simp only [copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

omit L in
theorem copySetup_ok {dst src : Ptr} {n : Nat} (b1 : src.1 ∈ bases) (b2 : dst.1 ∈ bases) (s : State) :
    WP isa (.block (lea .r0 src ++ lea .r1 dst ++ movi .r2 n)) s fun s1 =>
      s1.gpr .r0 = s.gpr src.1 + BitVec.ofNat 32 src.2 ∧ s1.gpr .r1 = s.gpr dst.1 + BitVec.ofNat 32 dst.2 ∧
        s1.gpr .r2 = BitVec.ofNat 32 n ∧ Keep argRegs s s1 := by
  have h := setArgsTo_ok [.r0, .r1, .r2] [.ptr src, .ptr dst, .imm n] (by decide) (by decide)
    (by simp [Arg.ok, b1, b2]) s
  simp only [setArgsTo, List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Arg.mov] at h
  rw [List.append_assoc]
  refine WP.mono h fun s1 ⟨hA, k⟩ => ⟨hA (.r0, .ptr src) (by simp), hA (.r1, .ptr dst) (by simp), hA (.r2, .imm n) (by simp),
    k.mono (by decide)⟩

theorem copy_okB {dst src : Ptr} {n : Nat} (hc : copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPostB D s s' [(dst, n)] ∧ CS s s' ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  obtain ⟨w, i, d, h0, b1, b2⟩ := copyChk_spec hc
  have id : inB (rbs ++ wbs) dst n = true := (sepB_spec d).2.1
  unfold copy
  refine WP.seq (WP.mono (copySetup_ok b1 b2 s) fun s1 ⟨g0, g1, g2, k⟩ => ?_)
  have as := L.pa32 i h0
  have ad := L.pa32 id h0
  refine WP.mono (VG.Proof.MlKem.Arm.copy_loop (L.fit i h0) (L.fit id h0) (L.lenlt i) h0
    (by rw [as, ad]; exact L.disj d) (by rw [as, k.rd, k.wr]; exact L.cR i) (by rw [ad, k.wr]; exact L.cW w)
    g0 g1 g2) fun s' ⟨hcs, rd, wr, sp, hf, hb⟩ => ?_
  rw [ad] at hf
  rw [ad, as, k.mem] at hb
  rw [k.mem] at hf
  have c : CS s s' := fun r hr hl => (hcs r hr).trans (k.cs r hr hl)
  exact ⟨PostB.of_cs c (rd.trans k.rd) (wr.trans k.wr) (sp.trans k.sp) hf, c, hb⟩

/-! ## Stores -/

omit L in
theorem encodable_small {v : Nat} (hv : v < 256) : encodable (BitVec.ofNat 32 v) = true := by
  unfold encodable; rw [List.any_eq_true]
  refine ⟨0, by simp, ?_⟩
  have : (BitVec.ofNat 32 v).rotateLeft 0 = BitVec.ofNat 32 v := by
    rw [BitVec.rotateLeft_def]; simp [BitVec.ushiftRight_eq_zero]
  rw [this]; simp; omega

omit L in
/-- What a store of the block through `r0` leaves. -/
theorem postB_store {s' : State} {p : Ptr} {l : Nat}
    (hg : ∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hf : Frame [⟨pa s p, l⟩] s.mem s'.mem) : PPostB D s s' [(p, l)] ∧ CS s s' :=
  have c : CS s s' := fun r hr _ => hg r fun h => by subst h; exact absurd hr (by decide)
  ⟨PostB.of_cs c hrd hwr hsp hf, c⟩

theorem setB_okB {p : Ptr} {v : Nat} (hv : v < 256) (ho : p.2 < 4096) (hb : p.1 ∈ bases)
    (hc : inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => PPostB D s s' [(p, 1)] ∧ CS s s' ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by
  have e := L.pa32W hc (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 1 := by rw [e]; exact L.iW hc
  have h0 : p.1 ≠ .r0 := fun h => by revert hb; rw [h]; decide
  have enc := encodable_small hv
  have hr : WP isa (.block (setB p v)) s fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    unfold setB
    run_block [hw, ho, enc, h0]
    refine ⟨by rw [e]; congr 1; apply BitVec.eq_of_toNat_eq; simp, fun r hr => by simp [hr], trivial⟩
  refine WP.mono hr fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  have hf : Frame [⟨pa s p, 1⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(postB_store (D := D) hg hrd hwr hsp hf).1, (postB_store (D := D) hg hrd hwr hsp hf).2, hm⟩

theorem setW_okB {p : Ptr} {v : Nat} (ho : p.2 < 4096) (hb : p.1 ∈ bases) (hc : inB wbs p 4 = true) :
    WP isa (.block (setW p v)) s fun s' => PPostB D s s' [(p, 4)] ∧ CS s s' ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 32 v) := by
  have e := L.pa32W hc (by decide)
  have hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := by rw [e]; exact L.iW hc
  have h0 : p.1 ≠ .r0 := fun h => by revert hb; rw [h]; decide
  have hr : WP isa (.block (setW p v)) s fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 32 v) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    unfold setW movi
    run_block [hw, ho, h0]
    refine ⟨by rw [e, movi_val], fun r hr => by simp [hr], trivial⟩
  refine WP.mono hr fun s' ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  have hf : Frame [⟨pa s p, 4⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨(postB_store (D := D) hg hrd hwr hsp hf).1, (postB_store (D := D) hg hrd hwr hsp hf).2, hm⟩

end

/-! ## Results in `r11` -/

/-- A result (1 or 0) as a register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 32 := if b then 1 else 0

theorem and11_ok (s : State) :
    WP isa (.block [.dp .and .r11 .r11 (.reg .r0)]) s fun s' =>
      s'.gpr .r11 = s.gpr .r11 &&& s.gpr .r0 ∧ Keep [.r11] s s' := by
  run_block []
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 32} (hx : x = bit a)
    (hy : y = if b then 1 else 0) : x &&& y = bit (a ∧ b) := by
  subst hx hy
  by_cases ha : a <;> by_cases hb : b <;> simp [bit, ha, hb]

/-- A block that writes `r11` alone, and flags, leaves `PostB` but for `r11`. -/
theorem postB11 {D : Nat} {s s' : State} (k : Keep [.r11] s s') (W : List Region) :
    PostB D s s' W ∧ ∀ r ∈ preserved, r ≠ .lr → r ≠ .r11 → s'.gpr r = s.gpr r :=
  ⟨⟨k.rd, k.wr, fun r hr => k.gpr r (by revert hr; decide +revert), k.sp, by rw [k.mem]; exact Frame.refl _ _⟩,
    fun r _ _ hne => k.gpr r (by simpa using hne)⟩

/-! ## Counters -/

/-- A block writing registers `rs` and memory only. -/
def KeepM (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- `[p] ← [p] + v`, through `r0` (`v` encodable). -/
theorem addW_ok (p : Ptr) (v : Nat) (ho : p.2 < 4096) (h0 : p.1 ≠ .r0) (hv : encodable (BitVec.ofNat 32 v) = true)
    (s : State) (hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4) :
    WP isa (.block [.ldr .r0 p.1 p.2, .dp .add .r0 .r0 (.imm (BitVec.ofNat 32 v)), .str .r0 p.1 p.2]) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2))
        (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 + BitVec.ofNat 32 v) ∧ KeepM [.r0] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := covers_wr (covers_one hw
    (by decide)) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  run_block [hw, hr, ho, h0, hv]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

/-- `[p] ← [p] - 1`, through `r0`, and `Z` set when it is 0. -/
theorem decW_ok (p : Ptr) (ho : p.2 < 4096) (h0 : p.1 ≠ .r0) (s : State)
    (hw : InRegions s.wr (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4) :
    WP isa (.block [.ldr .r0 p.1 p.2, .subs .r0 .r0 (.imm 1), .str .r0 p.1 p.2]) s fun s' =>
      (s'.mem = s.mem.writeW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2))
        (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 - 1) ∧
        s'.z = (s.mem.readW (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 32 - 1 == 0)) ∧ KeepM [.r0] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr p.1 + BitVec.ofNat 32 p.2)) 4 := covers_wr (covers_one hw
    (by decide)) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  run_block [hw, hr, ho, h0]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; simp [hr]

end VG.Proof.MlDsa.Arm.Sign
