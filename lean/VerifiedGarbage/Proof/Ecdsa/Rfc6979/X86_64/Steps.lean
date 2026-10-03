import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Msg

/-!
# Deterministic ECDSA on x86-64: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `K`, `V` and `h`, in the frame. -/
abbrev kOf (L : Lay) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 24) 32
abbrev vOf (L : Lay) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 56) 32
abbrev hOf (L : Lay) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) 32

/-- HMAC-SHA-256. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac Spec.Hmac.sha256 K text

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW (L : Lay) : List Region := [L.SCR, ⟨L.B, 88⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 88⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 88⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + 32 ≤ 64) :
    ∀ r ∈ [(⟨L.scr, 1024⟩ : Region), ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), 32⟩],
      ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf v).hmacV t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf L t'.mem = kOf L t.mem ∧ vOf L t'.mem = mac (kOf L t.mem) (vOf L t.mem) := by
  refine WP.mono (hmac_ok (v := v) hL hc (da := L.B + BitVec.ofNat 64 (24 + 32)) (len := 32) (dst := 32)
    (fun u hu => fr_ok hL hu (d := .rdx) (by decide) (o := 32) (by decide))
    (.inl ⟨56, rfl, by omega, by omega⟩) (by omega) (by omega)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by omega)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by omega) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), h.mac⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 1024`. -/
theorem hmacK_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 128) :
    WP isa ((cfgOf v).hmac (Cfg.scr .rdx sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf L t'.mem = vOf L t.mem ∧
      kOf L t'.mem = mac (kOf L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 1024) len) := by
  refine WP.mono (hmac_ok (v := v) hL hc (da := L.scr + BitVec.ofNat 64 1024) (len := len) (dst := 0)
    (fun u hu => scr_ok hL hu (d := .rdx) (by decide) (a := 1024) (by decide))
    (.inr ⟨1024, rfl, by omega, by omega⟩) hlen (by omega)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by omega)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by omega) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), h.mac⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool} {len : Nat}
    (hlen : len = if full then 97 else 33) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg b full))
      (.seq ((cfgOf v).hmac (Cfg.scr .rdx sMsg) len fK) (cfgOf v).hmacV))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf L t'.mem = mac (kOf L t.mem) (vOf L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d 32 ++ hOf L t.mem else [])) ∧
        vOf L t'.mem = mac (kOf L t'.mem) (vOf L t.mem) := by
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  rw [← hmp]
  refine WP.seq (WP.mono (msg_ok hL hcp hdip hsip b full) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  refine WP.seq (WP.mono (hmacK_ok (v := v) hL hcu (len := len) (by cases full <;> simp_all))
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hcw) fun t' ⟨hc', hf', hk', hv'⟩ => ⟨hc', ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by omega)))).trans hfw).trans hf'
  · have hku : kOf L u.mem = kOf L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)
    rw [hk', hkw, hku, hlen, hbu]
  · have hvu : vOf L u.mem = vOf L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by omega) (by omega)) (by omega)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (b : Nat) :
    WP isa ((cfgOf v).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf L t'.mem = mac (kOf L t.mem) (vOf L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d 32 ++ hOf L t.mem)) ∧
      vOf L t'.mem = mac (kOf L t'.mem) (vOf L t.mem) :=
  rekey_gen (full := true) hL hc rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf v).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf L t'.mem = mac (kOf L t.mem) (vOf L t.mem ++ [0]) ∧
      vOf L t'.mem = mac (kOf L t'.mem) (vOf L t.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hc rfl) fun _ h => ⟨h.1, h.2.1, by
    rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
