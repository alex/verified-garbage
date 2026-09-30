import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/-!
# ML-DSA on x86-64: `vg_mldsa_bit_pack`

Untrusted: everything here is checked by Lean. The value of a coefficient
`x` is `b - x`, plus `q` if that borrows (`subModQ`), which is
`b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`). The loop is proven
once for every width (`packLoop_ok`), and the function by its five cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of toNat_setWidth64)
open VG.Proof.MlDsa.Pack

/-- `b - x`, plus `q` if it borrows, as the code computes it in 32 bits. -/
def subModQ (b x : BitVec 32) : BitVec 32 :=
  b - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm)

theorem subModQ_toNat {b x : BitVec 32} (hb : b.toNat < q) (hx : x.toNat < q) :
    (subModQ b x).toNat = (b.toNat + q - x.toNat) % q := by
  have hq : q = 8380417 := rfl
  rw [hq] at hb hx ⊢
  unfold subModQ
  by_cases h : b.toNat < x.toNat
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 8380417#32 := by
      rw [decide_eq_true h]; decide
    rw [e, Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 0#32 := by
      rw [decide_eq_false h]; decide
    rw [e, show (b.toNat + 8380417 - x.toNat) % 8380417 = b.toNat - x.toNat by omega]
    bv_omega

/-- The value `bpLd B` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (subModQ (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok (B : Nat) : LdOk (bpLd B) (bpVal B) := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold bpLd
  xrun [ea_at', hin]
  rw [toNat_setWidth64]
  rfl

theorem bpPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov .r8 (.reg .rcx)]) s fun s' =>
      (dArg s' .rdx = dArg s .rdx ∧ s'.gpr .r8 = s.gpr .rcx ∧ s'.mem = s.mem) ∧ Keep [.rdx, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) = vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; have : q = 8380417 := rfl; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, subModQ_toNat (by omega) hx, hbq, sub_modPm hx hb (hle i hi)]

theorem bp_wp {s₀ : State} (hp : bitPackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.bitPack s₀ fun s' =>
      bitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hab, hlen, hred, hbnd⟩ := hp
  have go : ∀ {d c nb B : Nat}, Shape d c nb → dArg s₀ .rdx = B → B ≤ 2 ^ 19 →
      bitlen (dArg s₀ .rsi + B) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rcx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (packLoop (bpLd B) d c nb) s fun s' =>
        bitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
    intro d c nb B hs hB hB19 hd s h1 h2 h3 h4 h5
    rw [hB, hd] at hlen
    have hq : q = 8380417 := rfl
    have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
    refine WP.mono (packLoop_ok (bpLd_ok B) hs (f := s₀.gpr .rdi) (o := s₀.gpr .rcx) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => ?_) h1 h2 h3 h4 h5)
      fun s' ⟨hB', hf, _⟩ => ⟨?_, by rw [hlen]; exact hf⟩
    · obtain ⟨h₁, h₂⟩ := hbnd i hi
      rw [hB] at h₂
      have hx := hred i hi
      rw [bpVal, subModQ_toNat (by omega) hx, hBq, ← sub_modPm hx (by omega) h₂, ← hd, ← hB]
      exact lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · show bytesAt s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat = bitPack _ _ _
      rw [hlen, hB', bitPack_eq, bitPack_vals hred (by omega) (fun i hi => (hbnd i hi).2),
        hB, hd]
  unfold Impl.MlDsa.X86_64.Pack.bitPack
  refine WP.seq (WP.mono (bpPro_ok s₀) fun s₁ ⟨⟨dx₁, r8₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have cases := mem_bitPackParams hab
  refine sel_ok .rdx 2 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rdx = 2 := by rw [← dx₁, lo_of_eq h]
    have ea : dArg s₀ .rsi = 2 := by omega
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₂ (by rw [g₂, di₁]) (by rw [g₂, r8₁]) (by rw [rd₂, k₁.2.1])
      (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n2 : dArg s₀ .rdx ≠ 2 := by rw [← dx₁]; exact lo_ne h
  have ds₂ : dArg s₂ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₂]; exact dx₁
  refine sel_ok .rdx 4 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rdx = 4 := by rw [← ds₂, lo_of_eq h]
    have ea : dArg s₀ .rsi = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₃ (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁])
      (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2]) (by rw [m₃, m₂, m₁])
  have n4 : dArg s₀ .rdx ≠ 4 := by rw [← ds₂]; exact lo_ne h
  have ds₃ : dArg s₃ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₃]; exact ds₂
  refine sel_ok .rdx 4096 _ _ s₃ (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_) (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_)
  · have e : dArg s₀ .rdx = 4096 := by rw [← ds₃, lo_of_eq h]
    have ea : dArg s₀ .rsi = 4095 := by omega
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₄ (by rw [g₄, g₃, g₂, di₁]) (by rw [g₄, g₃, g₂, r8₁])
      (by rw [rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₄, m₃, m₂, m₁])
  have n4096 : dArg s₀ .rdx ≠ 4096 := by rw [← ds₃]; exact lo_ne h
  have ds₄ : dArg s₄ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₄]; exact ds₃
  refine sel_ok .rdx 131072 _ _ s₄ (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_) (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_)
  · have e : dArg s₀ .rdx = 131072 := by rw [← ds₄, lo_of_eq h]
    have ea : dArg s₀ .rsi = 131071 := by omega
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, r8₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])
  · have n131072 : dArg s₀ .rdx ≠ 131072 := by rw [← ds₄]; exact lo_ne h
    have e : dArg s₀ .rdx = 524288 := by omega
    have ea : dArg s₀ .rsi = 524287 := by omega
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, r8₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])

theorem bitPack_correct (s : State) (hs : bitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.bitPack s t s' ∧ abiPreserved s s' ∧ bitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.bitPack)
    [.rax, .rcx, .rdx, .rdi, .r8, .r10, .r11] (bp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem bitPack_ct : ConstantTime isa bitPackK.pre bitPackK.pub Impl.MlDsa.X86_64.Pack.bitPack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rcx, .r8, .rsp] [.rsi, .rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.2.2.2.2.1, hp.2.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def bitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 2 | .rdx => 2 | .rcx => 0x2000 | .r8 => 96 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

theorem bitPack_verified : Verified X86_64.target Impl.MlDsa.X86_64.Pack.bitPack (bitPackContract X86_64.abi) :=
  Verified.of_correct bitPack_correct bitPack_ct
    { pre := by sig_implies_pre [bitPackContract, bitPackSig, bitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [bitPackContract, bitPackSig, bitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [bitPackContract, bitPackSig, bitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨bitPackSat, ?_⟩
        sig_pre [bitPackContract, bitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [coeffAt_zero]; decide
          | (simp only [bitPackParams]; decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack
