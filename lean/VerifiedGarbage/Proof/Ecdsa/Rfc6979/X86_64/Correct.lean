import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Loop
import VerifiedGarbage.Proof.Sha256.Md

/-!
# Deterministic ECDSA on x86-64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V` and the count are as RFC 6979's steps a–g make them
(`pre_ok`); and the signature of that candidate is RFC 6979's (`result_eq`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Ecdsa.Rfc6979 (kvAt candAt step)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

theorem sha256_length (m : List Byte) : (Spec.Sha256.hash m).length = 32 :=
  Proof.Sha256.md.digest_length _

theorem mac_length (K t : List Byte) : (mac K t).length = 32 := sha256_length _

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv L m₀ 0 t) :
    WP isa (.loop (cfgOf v).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv L m₀ (8 - n) s ∧ n ≤ 8) ?_ 8 t ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show 8 - (n - 1) = 8 - n + 1 by omega]

/-! ## Steps a–g -/

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq {x : Nat} {dB hB h : List Byte} (hd : dB.length = 32) (hx : x = Spec.Weierstrass.ofBytes dB)
    (hh : Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve hB = h) :
    Spec.Ecdsa.Rfc6979.init Spec.P256.curve Spec.Hmac.sha256 32 x hB =
      let K₁ := mac (List.replicate 32 0) (List.replicate 32 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := mac K₁ (List.replicate 32 1)
      let K₂ := mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets Spec.P256.curve x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_p256, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (L : Lay) (m₀ : Mem) : List Byte := Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve (hBOf L m₀)
abbrev dB (L : Lay) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d 32

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (L : Lay) (m₀ : Mem) : List Byte :=
  mac (List.replicate 32 0) (List.replicate 32 1 ++ [BitVec.ofNat 8 0] ++ (dB L m₀ ++ hSpec L m₀))
abbrev V₁ (L : Lay) (m₀ : Mem) : List Byte := mac (K₁ L m₀) (List.replicate 32 1)

/-- After step c: `h`, `V = 0x01…` and `K = 0x00…`. -/
structure QB (L : Lay) (m₀ : Mem) (u : State) : Prop where
  h : hOf L u.mem = hSpec L m₀
  k : kOf L u.mem = List.replicate 32 0
  v : vOf L u.mem = List.replicate 32 1

/-- After step e. -/
structure QC (L : Lay) (m₀ : Mem) (u : State) : Prop where
  h : hOf L u.mem = hSpec L m₀
  k : kOf L u.mem = K₁ L m₀
  v : vOf L u.mem = V₁ L m₀

/-- After step g. -/
structure QD (L : Lay) (m₀ : Mem) (u : State) : Prop where
  k : kOf L u.mem = (kv0 L m₀).1
  v : vOf L u.mem = (kv0 L m₀).2

theorem kv0_eq' (L : Lay) (m₀ : Mem) :
    kv0 L m₀ = (mac (K₁ L m₀) (V₁ L m₀ ++ [BitVec.ofNat 8 1] ++ (dB L m₀ ++ hSpec L m₀)),
      mac (mac (K₁ L m₀) (V₁ L m₀ ++ [BitVec.ofNat 8 1] ++ (dB L m₀ ++ hSpec L m₀))) (V₁ L m₀)) :=
  kv0_eq (length_bytesAt _ _ _) rfl rfl

theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .rsi = L.dg) :
    WP isa (.block ((cfgOf v).reduce ++ Cfg.initKV)) u fun u' => Ctx L g m₀ u' ∧ QB L m₀ u' := by
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hL hc hsi) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
  refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ => ⟨hc₂, ?_, hk₂, hv₂⟩
  rw [show hOf L u₂.mem = hOf L u₁.mem from bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
  rw [hSpec, bits2octets_eq (length_bytesAt _ _ _), ← hh₁]
  have e := toBytes_ofBytes (hOf L u₁.mem)
  rw [length_bytesAt] at e
  exact e.symm

theorem kvw_h (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 88, 32⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

theorem stageC_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QB L m₀ u) :
    WP isa ((cfgOf v).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC L m₀ u' :=
  WP.mono (rekeyFull_ok hL hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (bytesAt_frame hf' (kvw_h hL) (by omega)).trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL]⟩

theorem stageD_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QC L m₀ u) :
    WP isa ((cfgOf v).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD L m₀ u' :=
  WP.mono (rekeyFull_ok hL hc 1) fun u' ⟨hc', _, hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL]⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD L m₀ u) :
    WP isa (.block (cfgOf v).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', by omega,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by omega)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by omega)).trans hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem stageG_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hx : Exit L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega)).symm) (by omega))⟩

theorem body_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf v).body t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ h₀ =>
    WP.seq (WP.mono (stageB_ok hL h₀.ctx h₀.val) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩))))))

/-! ## RFC 6979's result -/

theorem blocks_p256 : Spec.Ecdsa.Rfc6979.blocks Spec.P256.curve 32 = 1 := by
  rw [Spec.Ecdsa.Rfc6979.blocks, nBits_p256]

theorem bits2int_cand (i : Nat) :
    Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI L m₀ i ++ []) = Spec.Weierstrass.ofBytes (candI L m₀ i) := by
  have hl : (candI L m₀ i).length = 32 := mac_length _ _
  rw [List.append_nil, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_32 hl]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit L m₀ i t) :
    (result m₀ L.d L.dg).1 = sigI L m₀ i := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.P256Sha256.inst,
    Spec.Ecdsa.P256.inst, ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign, hlen]
  by_cases hv : 1 ≤ xOf L m₀ ∧ xOf L m₀ < Spec.P256.curve.n
  · simp only [hv, and_self, ite_true]
    have hf : ∀ j < i, Spec.Ecdsa.signWith Spec.P256.curve (xOf L m₀) (eOf L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hx.fails j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift blocks_p256 i 8 (by have := hx.lt; omega) hf,
      show 8 - i = (7 - i) + 1 by have := hx.lt; omega]
    have hc : Spec.Hmac.hmac Spec.Hmac.sha256 (kvI L m₀ i).1 (kvI L m₀ i).2 = candI L m₀ i := rfl
    cases hs : sigI L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.search_ok blocks_p256 (by rw [hc, bits2int_cand]; exact hs)]
    | none =>
      have h7 : i = 7 := hx.last.resolve_left (by simp [hs])
      subst h7
      rw [Proof.Ecdsa.Rfc6979.search_fail blocks_p256 (by rw [hc, bits2int_cand]; exact hs)]
      rfl
  · symm
    simp only [sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (L : Lay) (m₀ : Mem) : Nat :=
  if (result m₀ L.d L.dg).2 = 0 then 7 else (result m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < 8) (hf : ∀ j < i, sigI L m₀ j = none) :
    (sigI L m₀ i = none ∧ i + 1 < 8) ↔ i < exitAt L m₀ := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  unfold exitAt
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.P256Sha256.inst,
    Spec.Ecdsa.P256.inst, ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign, hlen]
  by_cases hv : 1 ≤ xOf L m₀ ∧ xOf L m₀ < Spec.P256.curve.n
  · simp only [hv, and_self, ite_true]
    have hf' : ∀ j < i, Spec.Ecdsa.signWith Spec.P256.curve (xOf L m₀) (eOf L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hf j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift blocks_p256 i 8 (by omega) hf', show 8 - i = (7 - i) + 1 by omega]
    have hc : Spec.Hmac.hmac Spec.Hmac.sha256 (kvI L m₀ i).1 (kvI L m₀ i).2 = candI L m₀ i := rfl
    cases hs : sigI L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.search_ok blocks_p256 (by rw [hc, bits2int_cand]; exact hs)]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.search_fail blocks_p256 (by rw [hc, bits2int_cand]; exact hs)]
      by_cases h7 : i + 1 < 8
      · have := Proof.Ecdsa.Rfc6979.search_pos (C := Spec.P256.curve) (H := Spec.Hmac.sha256) (hlen := 32)
          (d := xOf L m₀) (e := eOf L m₀) (n := 6 - i)
          (K := (step Spec.Hmac.sha256 (kvI L m₀ i).1 (kvI L m₀ i).2).1)
          (V := (step Spec.Hmac.sha256 (kvI L m₀ i).1 (kvI L m₀ i).2).2) blocks_p256
        rw [show 7 - i = 6 - i + 1 by omega]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · have hi7 : i = 7 := by omega
        subst hi7
        simp [Spec.Ecdsa.Rfc6979.search]
  · simp only [hv, ite_false, ite_true]
    have hs : sigI L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

/-! ## The whole function -/

theorem pop_rsp (B : Addr) : B + BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 17) = B + BitVec.ofNat 64 160 := by
  rw [Offset.add_add]

/-- `vg_ecdsa_p256_sha256_sign` meets `rfcX86_64` and keeps the callee-saved
registers and its return address. -/
theorem sign_ok {s : State} (h : rfcX86_64.pre s) :
    WP isa (cfgOf v).sign s fun s' => gprPreserved s s' ∧ rfcX86_64.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 17 ≤ _; have := h.1; omega)
    (WP.mono (body_ok hL hc) fun u ⟨hu, i, hx⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rcx pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 17 from rfl, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show match (result s.mem (lay s).d (lay s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    exact hx.res.keep (popped_gpr _ _ _ (by decide) (by decide)) (by rw [popped_mem])

end VG.Proof.Ecdsa.Rfc6979.X86_64
