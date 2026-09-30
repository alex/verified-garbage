import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_bit_pack`

Untrusted: everything here is checked by Lean. The value of a coefficient
`x` is `b - x`, plus `q` if that is negative (`bm`, as `bMinus` computes it),
which is `b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`). The loop is
proven once for every width (`packLoop_ok`), and the function by its five
cases, in its frame, which saves `r4` in the 4 bytes below the stack pointer.
Constant time: the frame leaks only addresses computed from the stack
pointer, and the taint analysis proves its body constant time
(`RelCT.frame`).
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

/-! ## `b - x` modulo `q` -/

/-- `b - x`, plus `q` if it is negative, as `bMinus` computes it in 32 bits:
`m = (b - x) >> 31`, then `b - x + m + (m << 23) - (m << 13)`. -/
def bm (b x : BitVec 32) : BitVec 32 :=
  b - x + ((b - x) >>> 31) + (((b - x) >>> 31) <<< 23) - (((b - x) >>> 31) <<< 13)

theorem bm_toNat {b x : BitVec 32} (hb : b.toNat ≤ 2 ^ 19) (hx : x.toNat < q) :
    (bm b x).toNat = (b.toNat + q - x.toNat) % q := by
  rw [q_eq] at hx ⊢
  unfold bm
  by_cases h : x.toNat ≤ b.toNat
  · have e : (b - x) >>> 31 = 0#32 := by bv_omega
    rw [e, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have e : (b - x) >>> 31 = 1#32 := by bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega)]
    bv_omega

/-- The value `bpLd B` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (bm (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok {B : Nat} (hB : encodable (BitVec.ofNat 32 B) = true) : LdOk (bpLd B) (bpVal B) :=
  fun j s hj hin => by
    refine WP.keep _ ?_ rfl
    unfold bpLd bMinus addQNeg
    run_block [hj, hin, hB, bm, bpVal, and_true]

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ 2 ^ 19)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, bm_toNat (by omega) hx, hbq, sub_modPm hx (by rw [q_eq]; omega) (hle i hi)]

/-! ## The function -/

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem bpPro_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .r2), .mov .r2 (.reg .r3)]) s fun s' =>
      (s'.gpr .r12 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r3 ∧ s'.mem = s.mem) ∧ Keep [.r12, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

/-- What `bitPack` leaves. -/
def BpPost (s₀ s' : State) : Prop :=
  bytesAt s'.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
    bitPack ((polyAt s₀.mem (State.addr (s₀.gpr .r0))).map fun c => modPm c.val q) (s₀.gpr .r1).toNat
      (s₀.gpr .r2).toNat ∧ abiPreserved s₀ s'

theorem bp_wp {s₀ : State} (hp : BpPre s₀) : WP isa Impl.MlDsa.Arm.Pack.bitPack s₀ (BpPost s₀) := by
  have hsp := hp.sp4
  have hbF : ∀ r ∈ [below4 s₀], (polyRegion (State.addr (s₀.gpr .r0))).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.bF.symm
  have hco : ∀ i < 256, coeffAt (pushed [.r4] s₀).mem (State.addr (s₀.gpr .r0)) i =
      coeffAt s₀.mem (State.addr (s₀.gpr .r0)) i := fun i hi => coeffAt_frame (pushed4_frame hsp) hbF hi
  unfold Impl.MlDsa.Arm.Pack.bitPack
  refine WP.frame (rs := [.r4]) (r := .r4) rfl (by simpa using hsp) (by decide) ?_
  refine WP.seq (WP.mono (bpPro_ok _) fun s₁ ⟨⟨g12, g2, gm⟩, k₁⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have go : ∀ {d c nb B : Nat}, Shape d c nb → (s₀.gpr .r2).toNat = B → B ≤ 2 ^ 19 →
      encodable (BitVec.ofNat 32 B) = true → bitlen ((s₀.gpr .r1).toNat + B) = d → ∀ s : State, Same s₁ s →
      WP isa (packLoop (bpLd B) d c nb) s fun s₂ => BpPost s₀ (popped .r4 4 s₂) := by
    intro d c nb B hs hB hB19 hBe hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
    refine WP.mono (packLoop_ok (bpLd_ok hBe) hs (pf := s₀.gpr .r0) (po := s₀.gpr .r3)
      (m₀ := (pushed [.r4] s₀).mem) (rd := s₀.rd) (wr := (pushed [.r4] s₀).wr)
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..))
      (by rw [pushed_wr, hp.wr, hlen]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (by rw [← hlen]; exact hp.disj) hp.fitF (by rw [← hlen]; exact hp.fitO) (fun i hi => ?_)
      (by rw [hS.1, k₁.gpr (by decide), pushed_gpr]) (by rw [hS.1, g2, pushed_gpr])
      (by rw [hS.2.2.1, k₁.2.1, pushed_rd]) (by rw [hS.2.2.2.1, k₁.2.2.1]) (by rw [hS.2.1, gm]))
      fun s₂ ⟨hbytes, hf, hk⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
    · obtain ⟨h₁, h₂⟩ := hp.bnd i hi
      rw [hB] at h₂
      have hx := hp.red i hi
      rw [hco i hi, bpVal, bm_toNat (by omega) hx, hBq, ← sub_modPm hx (by rw [q_eq]; omega) h₂, ← hd, ← hB]
      exact lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · rw [popped_mem, hlen, hbytes, bitPack_eq, ← hB, ← hd, hB]
      rw [bitPack_vals hp.red hB19 (fun i hi => by rw [← hB]; exact (hp.bnd i hi).2)]
      refine congrArg (fun L => bitsToBytes (fieldBits _ L)) (List.map_congr_left fun i hi => ?_)
      rw [hco i (List.mem_range.mp hi)]
    · -- The registers: `r4` from the frame, the others kept.
      have hsp₂ : s₂.sp = s₀.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₁.2.2.2, pushed4_sp]
      by_cases h4 : r = .r4
      · subst h4
        refine (popped4 hsp hsp₂ ?_).1
        rw [hf.readW (r := below4 s₀) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← hlen]; exact hp.bO) (by decide),
          pushed4_mem hsp, Mem.readW_writeW_self32]
      · have hr' : r ∉ packRegs ++ [.r12, .r2] := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h4 | decide
        rw [popped_gpr h4, hk.gpr (fun h => hr' (List.mem_append_left _ h)), hS.1,
          k₁.gpr (fun h => hr' (List.mem_append_right _ h)), pushed_gpr]
    · have hsp₂ : s₂.sp = s₀.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₁.2.2.2, pushed4_sp]
      rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  have e12 : ∀ s, Same s₁ s → (s.gpr .r12).toNat = (s₀.gpr .r2).toNat := fun s h => by
    rw [h.1, g12, pushed_gpr]
  refine sel_ok .r12 2 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n2 => ?_)
  · rw [e12 s₁ ⟨rfl, rfl, rfl, rfl, rfl⟩] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 2 by omega]; decide) s₂ h₂
  rw [e12 s₁ ⟨rfl, rfl, rfl, rfl, rfl⟩] at n2
  refine sel_ok .r12 4 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n4 => ?_)
  · rw [e12 s₂ h₂] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 4 by omega]; decide) s₃ (h₂.trans h₃)
  rw [e12 s₂ h₂] at n4
  refine sel_ok .r12 4096 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4096 => ?_)
  · rw [e12 s₃ (h₂.trans h₃)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 4095 by omega]; decide) s₄ ((h₂.trans h₃).trans h₄)
  rw [e12 s₃ (h₂.trans h₃)] at n4096
  refine sel_ok .r12 131072 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n17 => ?_)
  · rw [e12 s₄ ((h₂.trans h₃).trans h₄)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 131071 by omega]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)
  · rw [e12 s₄ ((h₂.trans h₃).trans h₄)] at n17
    have e : (s₀.gpr .r2).toNat = 524288 := by omega
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 524287 by omega]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)

/-! ## Constant time -/

theorem push_eq {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) : a = pushed rs s := by
  simp only [isa, push] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A frame `push {r4}; body; pop r4` is constant time if its body is, by
the taint analysis with `rs` public, from states that agree on `rs` and
the stack pointer. -/
theorem frame4_ct {body : Prog isa} (rs : List Reg) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) body hc).isSome = true) {s₁ s₂ : State}
    (hsp : s₁.sp = s₂.sp) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {t₁ t₂ : List Leak} {s₁' s₂' : State}
    (e₁ : Exec isa (.frame (.push [.r4]) body (.pop .r4 4)) s₁ t₁ s₁')
    (e₂ : Exec isa (.frame (.push [.r4]) body (.pop .r4 4)) s₂ t₂ s₂') : t₁ = t₂ :=
  (RelCT.frame (P := fun a b => a = s₁ ∧ b = s₂) (fun a b h => by rw [h.1, h.2]; exact hsp)
    (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b ⟨x₁, x₂, ⟨hx₁, hx₂⟩, pa, pb⟩ => by
      rw [push_eq pa, push_eq pb, hx₁, hx₂]
      exact Taint.agree_ofRegs fun r h => by rw [pushed_gpr, pushed_gpr]; exact hr r h) h)
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem bitPack_ct :
    ConstantTime isa (bitPackContract Arm.abi 4).pre (bitPackContract Arm.abi 4).pub Impl.MlDsa.Arm.Pack.bitPack := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hpub e₁ e₂
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
  obtain ⟨hsp, h0, h1, h2, h3, -⟩ := hpub
  exact frame4_ct [.r0, .r1, .r2, .r3] (by taint_decide) hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption) e₁ e₂

/-! ## `Verified` -/

/-- A state satisfying the precondition: `len` = 96 on the stack. -/
def bpSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 2 | .r2 => 2 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4000 then 96 else 0
  rd := [⟨0x1000, 1024⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 96⟩]

example : ∃ pre post leak, bitPackContract Arm.abi 4 =
    bitPackApi.sig.contract Arm.target.abi pre post bitPackApi.writeArgs 4 leak := ⟨_, _, _, rfl⟩

theorem bitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.bitPack (bitPackContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, bitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hb, habi⟩ := bp_wp (BpPre.of hs)
    refine ⟨t, s', he, habi, ?_⟩
    sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hb
  · refine ⟨bpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | (unfold Reduced; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.Arm.Pack
